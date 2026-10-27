"""Actual native counterexamples for overflow guards and summary composition."""
import json
import os
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


class SystemMutationTests(unittest.TestCase):
    def test_guard_and_composition_faults_have_counterexamples(self):
        source = (ROOT / 'systems/src/main.inf').read_text()
        maximum = (1 << 63) - 1
        mutations = [
            ('period_guard_reversed',
             'if factor > 9223372036854775807 / moduli[i] { L = -3; break; }',
             'if factor < 9223372036854775807 / moduli[i] { L = -3; break; }',
             'crt_system_period', [0, 0], [maximum, 2], -3),
            ('period_guard_rejects_equality',
             'if factor > 9223372036854775807 / moduli[i] { L = -3; break; }',
             'if factor >= 9223372036854775807 / moduli[i] { L = -3; break; }',
             'crt_system_period', [0], [maximum], maximum),
            ('composition_loses_previous_summary',
             'let next_r: i64 = crt_merge_solve(r, L, residues[i], moduli[i]);',
             'let next_r: i64 = crt_merge_solve(0, 1, residues[i], moduli[i]);',
             'crt_system_solve', [2, 5, 8], [6, 9, 15], 68),
        ]
        for name, original, replacement, export, residues, moduli, expected in mutations:
            with self.subTest(mutation=name):
                self.assertEqual(source.count(original), 1)
                folder = ROOT / 'build/system-mutations' / name
                (folder / 'src').mkdir(parents=True, exist_ok=True)
                (folder / 'Inference.toml').write_bytes((ROOT / 'systems/Inference.toml').read_bytes())
                (folder / 'src/main.inf').write_text(source.replace(original, replacement))
                compilation = subprocess.run([os.environ.get('INFS', 'infs'), 'build'],
                                             cwd=folder, capture_output=True, text=True)
                self.assertEqual(compilation.returncode, 0, compilation.stdout + compilation.stderr)
                vectors = folder / 'vectors.json'
                vectors.write_text(json.dumps([{'fn': export, 'residues': list(map(str, residues)),
                                                'moduli': list(map(str, moduli)), 'count': len(residues),
                                                'expected': str(expected)}]))
                result = subprocess.run(['node', str(ROOT / 'systems/scripts/check_runtime.mjs'),
                                         str(folder / 'out/main.wasm'), str(vectors)],
                                        capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0, 'Mutation escaped its concrete counterexample')
                self.assertTrue('AssertionError' in result.stderr or 'RuntimeError' in result.stderr,
                                result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
