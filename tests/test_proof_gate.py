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
        for hole in ('Axiom injected : False.', 'Lemma injected : False. Admitted.'):
            with self.subTest(hole=hole), tempfile.TemporaryDirectory() as temporary:
                source = Path(temporary) / 'proofs'
                source.mkdir()
                for file in (ROOT / 'proofs').glob('*.v'):
                    shutil.copyfile(file, source / file.name)
                file = source / 'CRTMath.v'
                file.write_text(file.read_text() + '\n' + hole + '\n')
                result = subprocess.run([sys.executable, str(ROOT / 'scripts/check_proofs.py'),
                                         '--proof-dir', str(source), '--out', str(Path(temporary) / 'out')],
                                        cwd=ROOT, capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('proof-hole audit', result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
