"""Host-safe evidence-binding controls; every compiler subprocess is mocked."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import check_system_infrastructure as gate


class InfrastructureGateTests(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory) / 'repo'
        for folder in ('proofs/systems', 'proofs/wasm', 'systems/out', 'systems/src', 'scripts'):
            (root / folder).mkdir(parents=True)
        for folder in ('proofs/systems', 'proofs/wasm'):
            for source in (ROOT / folder).glob('*.v'):
                shutil.copyfile(source, root / folder / source.name)
        shutil.copyfile(ROOT / 'proofs/wasm/assumptions.allow', root / 'proofs/wasm/assumptions.allow')
        for name in ('check_system_infrastructure.py', 'check_proofs.py', 'check_wasm_proofs.py'):
            shutil.copyfile(ROOT / 'scripts' / name, root / 'scripts' / name)
        files = {'systems/src/main.inf': b'native source', 'systems/Inference.toml': b'project',
                 'systems/out/main.v': b'generated module', 'systems/out/main.wasm': b'wasm'}
        for name, data in files.items():
            (root / name).write_bytes(data)
        digest = lambda name: hashlib.sha256(files[name]).hexdigest()
        (root / 'systems/out/manifest.json').write_text(json.dumps({
            'mode': 'proof', 'source': {'sha256': digest('systems/src/main.inf')},
            'project': {'sha256': digest('systems/Inference.toml')},
            'artifacts': {name: digest('systems/out/' + name) for name in ('main.v', 'main.wasm')},
        }))
        out = root / 'build/gate'
        out.mkdir(parents=True)
        (out / 'report.json').write_text('{"status":"stale_success"}')
        return root, out

    @contextlib.contextmanager
    def mocked_run(self, root, out, after_kernel=lambda: None):
        calls = []

        def run(command, **kwargs):
            # This fake is the only path through the subprocess API in these tests.
            self.assertIn(command[0], ('coqc', 'coqchk'))
            calls.append(command)
            if command[0] == 'coqchk':
                after_kernel()
                output = ''
            elif command[-1] == 'Audit.v':
                count = (out / 'Audit.v').read_text().count('Print Assumptions ')
                output = 'Closed under the global context\n' * count
            elif command[-1] == 'RejectedCertificate.v':
                output = 'Axioms:\nmain.valid_main : True\n'
            else:
                output = ''
            return subprocess.CompletedProcess(command, 0, output)

        checker_inputs = tuple(root / 'scripts' / name for name in
                               ('check_system_infrastructure.py', 'check_proofs.py', 'check_wasm_proofs.py'))
        with mock.patch.object(gate, 'ROOT', root), \
                mock.patch.object(gate, 'CHECKER_INPUTS', checker_inputs, create=True), \
                mock.patch.object(gate, 'pinned_container_error', return_value=None), \
                mock.patch.object(sys, 'argv', ['gate', '--out', str(out)]), \
                mock.patch.object(subprocess, 'run', side_effect=run), \
                mock.patch.object(subprocess, 'check_output', side_effect=AssertionError('No host compiler')), \
                contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            yield calls

    def test_staging_time_edit_uses_snapshot_and_rejects_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            root, out = self.fixture(directory)
            source = root / 'proofs/systems/ReadOnly.v'
            original = source.read_bytes()
            read = Path.read_bytes
            edited = False

            def read_and_edit(path):
                nonlocal edited
                data = read(path)
                if path == source and not edited:
                    edited = True
                    source.write_bytes(data + b'\nDefinition injected := True.\n')
                return data

            with self.mocked_run(root, out), mock.patch.object(Path, 'read_bytes', read_and_edit):
                with self.assertRaisesRegex(RuntimeError, 'changed during'):
                    gate.main()
            self.assertTrue(edited)
            self.assertEqual((out / 'systems/ReadOnly.v').read_bytes(), original)
            self.assertNotIn('ReadOnly.injected', (out / 'Audit.v').read_text())
            self.assertFalse((out / 'report.json').exists())

    def test_late_edits_of_every_bound_input_reject_success(self):
        paths = ['proofs/systems/ReadOnly.v', 'proofs/wasm/CRTExecutionContexts.v',
                 'proofs/systems/InfrastructureTargets.v', 'systems/out/main.v',
                 'systems/out/main.wasm', 'systems/out/manifest.json',
                 'systems/src/main.inf', 'systems/Inference.toml', 'proofs/wasm/assumptions.allow',
                 'scripts/check_system_infrastructure.py', 'scripts/check_proofs.py',
                 'scripts/check_wasm_proofs.py']
        for name in paths:
            with self.subTest(input=name), tempfile.TemporaryDirectory() as directory:
                root, out = self.fixture(directory)
                source = root / name
                def edit():
                    source.write_bytes(source.read_bytes() + b'\nchanged\n')
                with self.mocked_run(root, out, edit):
                    with self.assertRaisesRegex(RuntimeError, 'changed during'):
                        gate.main()
                self.assertFalse((out / 'report.json').exists())

    def test_staged_byte_edit_rejects_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root, out = self.fixture(directory)
            def edit():
                path = out / 'systems/ReadOnly.v'
                path.write_bytes(path.read_bytes() + b'\nchanged\n')
            with self.mocked_run(root, out, edit):
                with self.assertRaisesRegex(RuntimeError, 'changed during'):
                    gate.main()
            self.assertFalse((out / 'report.json').exists())

    def test_success_hashes_bind_all_inputs_and_staged_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root, out = self.fixture(directory)
            with self.mocked_run(root, out) as calls:
                gate.main()
            report = json.loads((out / 'report.json').read_text())
            self.assertEqual(calls[-1][0], 'coqchk')
            for name, digest in report['bound_inputs'].items():
                self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), digest)
            self.assertEqual(set(report['checker_dependencies']),
                             {'scripts/check_system_infrastructure.py', 'scripts/check_proofs.py',
                              'scripts/check_wasm_proofs.py'})
            for name, digest in report['staged_sources'].items():
                self.assertEqual(hashlib.sha256((out / name).read_bytes()).hexdigest(), digest)
            self.assertEqual(len(report['audited_declarations']), 154)
            self.assertIn('systems/out/manifest.json', report['bound_inputs'])

    def test_rejected_environment_invalidates_old_report_without_subprocess(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            (out / 'report.json').write_text('{"status":"stale_success"}')
            with mock.patch.object(gate, 'pinned_container_error', return_value='rejected environment'), \
                    mock.patch.object(sys, 'argv', ['gate', '--out', str(out)]), \
                    mock.patch.object(subprocess, 'run') as run, \
                    mock.patch.object(subprocess, 'check_output') as check_output, \
                    contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as failure:
                    gate.main()
            self.assertEqual(failure.exception.code, 2)
            run.assert_not_called()
            check_output.assert_not_called()
            self.assertFalse((out / 'report.json').exists())


if __name__ == '__main__':
    unittest.main()
