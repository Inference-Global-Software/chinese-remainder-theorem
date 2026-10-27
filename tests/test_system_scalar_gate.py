"""Host-safe fail-closed controls; all compiler subprocesses are mocked."""
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
import check_system_scalars as gate


class ScalarGateTests(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory) / 'repo'
        for name in ['proofs/systems', 'proofs/wasm', 'specifications', 'scripts/wasm_environment',
                     'systems/src', 'systems/out', 'src', 'out']:
            (root / name).mkdir(parents=True)
        for folder in ['proofs/systems', 'proofs/wasm', 'proofs', 'specifications']:
            for source in (ROOT / folder).glob('*.v'):
                shutil.copyfile(source, root / folder / source.name)
        shutil.copyfile(ROOT / 'proofs/wasm/assumptions.allow', root / 'proofs/wasm/assumptions.allow')
        for source in gate.CHECKER_INPUTS:
            shutil.copyfile(source, root / 'scripts' / source.name)
        for name in ['provenance.json', 'worker-opam.lock.json']:
            shutil.copyfile(ROOT / 'scripts/wasm_environment' / name, root / 'scripts/wasm_environment' / name)
        for prefix in ['', 'systems/']:
            files = {'src/main.inf': b'native source', 'Inference.toml': b'project',
                     'out/main.v': b'generated module', 'out/main.wasm': b'wasm'}
            for name, data in files.items():
                (root / (prefix + name)).write_bytes(data)
            digest = lambda name: hashlib.sha256(files[name]).hexdigest()
            (root / (prefix + 'out/manifest.json')).write_text(json.dumps({
                'mode': 'proof', 'source': {'sha256': digest('src/main.inf')},
                'project': {'sha256': digest('Inference.toml')},
                'artifacts': {name: digest('out/' + name) for name in ['main.v', 'main.wasm']},
            }))
        out = root / 'build/check'
        out.mkdir(parents=True)
        (out / 'report.json').write_text('{"status":"stale_success"}')
        return root, out

    @contextlib.contextmanager
    def mocked_run(self, root, out, after_kernel=lambda: None, unapproved=False):
        calls = []

        def run(command, **kwargs):
            self.assertIn(command[0], ['coqc', 'coqchk'])
            calls.append(command)
            if command[0] == 'coqchk':
                after_kernel()
                output = ''
            elif command[-1] == 'Audit.v':
                count = (out / 'Audit.v').read_text().count('Print Assumptions ')
                output = ('Axioms:\ninjected : False\n' if unapproved else 'Closed under the global context\n') * count
            elif command[-1] == 'RejectedCertificate.v':
                output = ''.join('Axioms:\nmain.' + name + ' : True\n' for name in
                                 ['valid_main', 'valid_main__HelperContracts', 'valid_main__PublicContracts'])
            else:
                output = ''
            kwargs['stdout'].write(output)
            return subprocess.CompletedProcess(command, 0)

        inputs = tuple(root / 'scripts' / path.name for path in gate.CHECKER_INPUTS)
        with mock.patch.object(gate, 'ROOT', root), \
                mock.patch.object(gate.infrastructure, 'ROOT', root), \
                mock.patch.object(gate, 'CHECKER_INPUTS', inputs), \
                mock.patch.object(gate, 'pinned_container_error', return_value=None), \
                mock.patch.object(sys, 'argv', ['gate', '--out', str(out)]), \
                mock.patch.object(subprocess, 'run', side_effect=run), \
                mock.patch.object(subprocess, 'check_output', side_effect=AssertionError('No host compiler')), \
                contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            yield calls

    def test_success_binds_both_projects_math_and_all_checker_dependencies(self):
        with tempfile.TemporaryDirectory() as directory:
            root, out = self.fixture(directory)
            with self.mocked_run(root, out) as calls:
                gate.main()
            report = json.loads((out / 'report.json').read_text())
            self.assertFalse(report['batch_execution_correctness_certified'])
            self.assertEqual(calls[-1][0], 'coqchk')
            for name in ['out/manifest.json', 'systems/out/manifest.json', 'proofs/CRTFinite.v',
                         'specifications/CRTSystemStatements.v', 'proofs/systems/MulModExecution.v',
                         'proofs/wasm/assumptions.allow', 'scripts/wasm_environment/provenance.json']:
                self.assertIn(name, report['bound_inputs'])
            for name, digest in report['bound_inputs'].items():
                self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), digest)
            for name, digest in report['staged_sources'].items():
                self.assertEqual(hashlib.sha256((out / name).read_bytes()).hexdigest(), digest)
            self.assertIn('CRT.CRTSystemStatements.FullWidth.mul_mod', report['audited_declarations'])
            self.assertIn('CRTSystems.SystemCalls.system_computes', report['audited_declarations'])

    def test_drift_of_new_dependency_classes_and_generated_wrappers_rejects(self):
        paths = ['out/main.v', 'out/main.wasm', 'specifications/CRTSystemStatements.v',
                 'proofs/CRTSystemArithmetic.v', 'proofs/systems/MulModExecution.v',
                 'scripts/check_system_scalars.py', 'scripts/wasm_environment/provenance.json',
                 'build/check/ExactTypes.v', 'build/check/Audit.v']
        for name in paths:
            with self.subTest(input=name), tempfile.TemporaryDirectory() as directory:
                root, out = self.fixture(directory)
                source = root / name
                def edit():
                    source.write_bytes(source.read_bytes() + b'\nchanged\n')
                with self.mocked_run(root, out, after_kernel=edit):
                    with self.assertRaisesRegex(RuntimeError, 'changed during'):
                        gate.main()
                self.assertFalse((out / 'report.json').exists())

    def test_stale_artifacts_and_source_fail_before_compiler(self):
        for name in ['src/main.inf', 'systems/src/main.inf', 'out/main.wasm', 'systems/out/main.v']:
            with self.subTest(input=name), tempfile.TemporaryDirectory() as directory:
                root, out = self.fixture(directory)
                path = root / name
                path.write_bytes(path.read_bytes() + b'\nmutated')
                with self.mocked_run(root, out) as calls:
                    with self.assertRaises(SystemExit):
                        gate.main()
                self.assertEqual(calls, [])
                self.assertFalse((out / 'report.json').exists())

    def test_admitted_handwritten_declaration_rejected_before_compiler(self):
        with tempfile.TemporaryDirectory() as directory:
            root, out = self.fixture(directory)
            path = root / 'proofs/systems/MulModExecution.v'
            path.write_text(path.read_text() + '\nTheorem leaked : False. Admitted.\n')
            with self.mocked_run(root, out) as calls:
                with self.assertRaises(SystemExit):
                    gate.main()
            self.assertEqual(calls, [])
            self.assertFalse((out / 'report.json').exists())

    def test_unapproved_transitive_assumption_invalidates_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root, out = self.fixture(directory)
            with self.mocked_run(root, out, unapproved=True) as calls:
                with self.assertRaisesRegex(ValueError, 'Unapproved transitive'):
                    gate.main()
            self.assertFalse(any(command[0] == 'coqchk' for command in calls))
            self.assertFalse((out / 'report.json').exists())

    def test_exact_targets_are_closed_and_cover_arbitrary_memory_signed_inputs(self):
        code, names = gate.exact_checks()
        self.assertEqual(len(names), len(set(names)))
        for name in ['gcd', 'normalize', 'inverse', 'add', 'mul', 'merge_solve', 'merge_period']:
            self.assertIn('exact_system_' + name + '_execution', names)
        self.assertEqual(len(names), 14)
        self.assertIn('exact_system_scalar_export_bindings', names)
        self.assertIn('exact_system_scalar_shared_contracts', names)
        self.assertIn('SM.main__HelperContracts_specs = 8%nat', code)
        self.assertIn('SM.main__PublicContracts_specs = 5%nat', code)
        self.assertIn('system_model_interp /' + chr(92) + chr(10), code)
        self.assertNotIn('Check ', code)
        self.assertEqual(code.count('forall mem hs a m b n, word a -> word m -> word b -> word n ->'), 2)
        self.assertEqual(code.count('FiniteSystem.result_post'), 2)

    def test_declaration_discovery_preserves_nested_namespaces(self):
        code = 'Module Outer.\nDefinition f := True.\nSection Host.\nLemma h : True. Proof. exact I. Qed.\nEnd Host.\nEnd Outer.\nDefinition g := True.\n'
        self.assertEqual(gate.declarations('CRT', Path('X.v'), code),
                         ['CRT.X.Outer.f', 'CRT.X.Outer.h', 'CRT.X.g'])


if __name__ == '__main__':
    unittest.main()
