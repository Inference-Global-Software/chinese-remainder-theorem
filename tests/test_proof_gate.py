"""Proof-hole controls run on hosts; compiler controls require the pinned image."""
import contextlib
import importlib.util
import io
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import check_proofs


class ProofGateTests(unittest.TestCase):
    def test_admissions_and_axioms_are_rejected(self):
        for module, hole in ((module, hole) for module in
                             ('CRTMath', 'CRTSystemArithmetic', 'CRTFinite') for hole in
                             ('Axiom injected : False.', 'Lemma injected : False. Admitted.')):
            with self.subTest(module=module, hole=hole), tempfile.TemporaryDirectory() as temporary:
                source = Path(temporary) / 'proofs'
                source.mkdir()
                for file in (ROOT / 'proofs').glob('*.v'):
                    shutil.copyfile(file, source / file.name)
                file = source / f'{module}.v'
                file.write_text(file.read_text() + '\n' + hole + '\n')
                output = Path(temporary) / 'out'
                output.mkdir()
                (output / 'report.json').write_text('{"status": "stale_success"}')
                result = subprocess.run([sys.executable, str(ROOT / 'scripts/check_proofs.py'),
                                         '--proof-dir', str(source), '--out', str(output)],
                                        cwd=ROOT, capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('proof-hole audit', result.stdout + result.stderr)
                self.assertFalse((output / 'report.json').exists())

    def test_exact_targets_are_closed_wrappers(self):
        text, wrappers = check_proofs.exact_target_checks()
        self.assertEqual(len(wrappers), sum(map(len, check_proofs.TARGETS.values())))
        self.assertEqual(len(wrappers), len(set(wrappers)))
        self.assertNotIn('Check ', text)
        for module, endpoints in check_proofs.TARGETS.items():
            for endpoint, target in endpoints.items():
                self.assertIn(f'Theorem exact_{module}_{endpoint} : {target}.\n'
                              f'Proof. exact {module}.{endpoint}. Qed.\n', text)

    def test_host_compiler_on_path_does_not_enable_compiler_controls(self):
        # Re-discover this test module under a host checkout, even with coqc on PATH.
        # No compiler process is launched by discovery or this assertion.
        with mock.patch.object(check_proofs, 'ROOT', Path('/host/crt')), \
                mock.patch.object(shutil, 'which', return_value='/host/bin/coqc') as which:
            self.assertIsNotNone(check_proofs.pinned_container_error())
            spec = importlib.util.spec_from_file_location('host_proof_gate_discovery', __file__)
            discovered = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(discovered)
            for name in ('test_weakened_finite_target_is_rejected',
                         'test_implicit_false_premise_is_rejected'):
                self.assertTrue(getattr(discovered.ProofGateTests, name).__unittest_skip__)
            which.assert_not_called()

    def test_checker_rejects_unselected_environment_before_any_subprocess(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'out'
            output.mkdir()
            (output / 'report.json').write_text('{"status": "stale_success"}')
            with mock.patch.object(check_proofs, 'pinned_container_error',
                                   return_value='requires the pinned project container'), \
                    mock.patch.object(sys, 'argv', ['check_proofs.py', '--out', str(output)]), \
                    mock.patch.object(subprocess, 'run') as run, \
                    mock.patch.object(subprocess, 'check_output') as check_output, \
                    contextlib.redirect_stderr(io.StringIO()) as stderr:
                with self.assertRaises(SystemExit) as failure:
                    check_proofs.main()
            self.assertEqual(failure.exception.code, 2)
            self.assertIn('requires the pinned project container', stderr.getvalue())
            run.assert_not_called()
            check_output.assert_not_called()
            self.assertFalse((output / 'report.json').exists())

    def assert_endpoint_rejected(self, replacement, diagnostic):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'proofs'
            source.mkdir()
            for file in (ROOT / 'proofs').glob('*.v'):
                shutil.copyfile(file, source / file.name)
            file = source / 'CRTFinite.v'
            text = file.read_text()
            begin = text.index('Theorem overflow_exact_proved :')
            end = text.index('Qed.', begin) + len('Qed.')
            file.write_text(text[:begin] + replacement + text[end:])
            output = Path(temporary) / 'out'
            output.mkdir()
            (output / 'report.json').write_text('{"status": "stale_success"}')
            result = subprocess.run([sys.executable, str(ROOT / 'scripts/check_proofs.py'),
                                     '--proof-dir', str(source), '--out', str(output)],
                                    cwd=ROOT, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Audit.v', result.stdout + result.stderr)
            self.assertIn('overflow_exact_proved', result.stdout + result.stderr)
            self.assertIn(diagnostic, result.stdout + result.stderr)
            self.assertFalse((output / 'report.json').exists())

    @unittest.skipUnless(check_proofs.pinned_container_error() is None,
                         'requires verified pinned project container through opam exec --')
    def test_weakened_finite_target_is_rejected(self):
        self.assert_endpoint_rejected(
            'Theorem overflow_exact_proved : True. Proof. exact I. Qed.',
            'T_overflow_exact')

    @unittest.skipUnless(check_proofs.pinned_container_error() is None,
                         'requires verified pinned project container through opam exec --')
    def test_implicit_false_premise_is_rejected(self):
        self.assert_endpoint_rejected(
            'Theorem overflow_exact_proved {missing : False} : T_overflow_exact. '
            'Proof. destruct missing. Qed.', 'implicit parameter missing')


if __name__ == '__main__':
    unittest.main()
