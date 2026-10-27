"""A completed-proof build must refuse admissions and newly asserted axioms."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


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
                                         '--proof-dir', str(source), '--out', str(Path(temporary) / 'out')],
                                        cwd=ROOT, capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('proof-hole audit', result.stdout + result.stderr)
                self.assertFalse((output / 'report.json').exists())


    @unittest.skipUnless(shutil.which('coqc'), 'requires the pinned Rocq container')
    def test_weakened_finite_target_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'proofs'
            source.mkdir()
            for file in (ROOT / 'proofs').glob('*.v'):
                shutil.copyfile(file, source / file.name)
            file = source / 'CRTFinite.v'
            text = file.read_text()
            begin = text.index('Theorem overflow_exact_proved :')
            end = text.index('Qed.', begin) + len('Qed.')
            file.write_text(text[:begin] +
                            'Theorem overflow_exact_proved : True. Proof. exact I. Qed.' +
                            text[end:])
            result = subprocess.run([sys.executable, str(ROOT / 'scripts/check_proofs.py'),
                                     '--proof-dir', str(source), '--out', str(Path(temporary) / 'out')],
                                    cwd=ROOT, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('overflow_exact_proved', result.stdout + result.stderr)
            self.assertIn('T_overflow_exact', result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
