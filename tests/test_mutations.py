"""Concrete counterexamples to three faulty CRT implementations."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


class MutationTests(unittest.TestCase):
    def test_faults_have_concrete_counterexamples(self):
        source = (ROOT / 'src/crt.inf').read_text()
        compiler = shutil.which(os.environ.get('INFC', 'infc'))
        self.assertIsNotNone(compiler, 'Test requires a real Inference compiler')
        mutations = [
            ('missing_compatibility', 'if delta % g != 0 { return -1; }', '',
             (2, 6, 4, 9), -1),
            ('negative_remainder', 'if r < 0 { return r + d; }', '',
             (5, 9, 2, 6), 14),
            ('noncanonical_result', 'return a + m * t;',
             'return a + m * t + (m / g) * n;', (2, 3, 3, 5), 8),
        ]
        for name, old, replacement, args, expected in mutations:
            with self.subTest(mutation=name):
                self.assertEqual(source.count(old), 1, 'Mutation no longer selects one site')
                folder = ROOT / 'build/mutations' / name
                folder.mkdir(parents=True, exist_ok=True)
                entry = folder / 'fault.inf'
                entry.write_text(source.replace(old, replacement))
                compilation = subprocess.run([compiler, str(entry), '--mode', 'proof',
                                              '--out-dir', str(folder)], capture_output=True, text=True)
                self.assertEqual(compilation.returncode, 0, compilation.stdout + compilation.stderr)
                vectors = folder / 'vectors.json'
                vectors.write_text(json.dumps([{'fn': 'crt_solve', 'args': list(map(str, args)),
                                                'expected': str(expected)}]))
                outcome = subprocess.run(['node', str(ROOT / 'scripts/check_runtime.mjs'),
                                          str(folder / 'fault.wasm'), str(vectors)],
                                         capture_output=True, text=True)
                self.assertNotEqual(outcome.returncode, 0, 'Fault escaped its counterexample')
                self.assertIn('AssertionError', outcome.stderr)
                self.assertIn('crt_solve(', outcome.stderr)


if __name__ == '__main__':
    unittest.main()
