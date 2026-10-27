"""Finite CRT integration tests using an independent unbounded-integer oracle."""
import itertools
import json
import math
import os
from pathlib import Path
import random
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
SYSTEMS = ROOT / 'systems'
MAX = (1 << 63) - 1
MIN = -(1 << 63)


def reference(residues, moduli, count=None):
    """Classify first, then use Python's modular inverse and arbitrary integers."""
    count = len(residues) if count is None else count
    if count < 0 or count > 16:
        return -2, -2
    pairs = list(zip(residues[:count], moduli[:count]))
    if any(m < 1 or a < 0 or a >= m for a, m in pairs):
        return -2, -2
    if any((b - a) % math.gcd(m, n) for (a, m), (b, n)
           in itertools.combinations(pairs, 2)):
        return -1, -1
    period = math.lcm(*(m for _, m in pairs))
    if period > MAX:
        return -3, -3
    value, step = 0, 1
    for a, m in pairs:
        g = math.gcd(step, m)
        reduced = m // g
        if reduced != 1:
            value += step * (((a - value) // g * pow(step // g, -1, reduced)) % reduced)
        step = math.lcm(step, m)
    return value, period


def batch_vectors(pairs, count=None, tails=None):
    residues = [a for a, _ in pairs]
    moduli = [m for _, m in pairs]
    count = len(pairs) if count is None else count
    expected = reference(residues, moduli, count)
    if tails:
        residues += [a for a, _ in tails]
        moduli += [m for _, m in tails]
    return [{'fn': fn, 'residues': list(map(str, residues)),
             'moduli': list(map(str, moduli)), 'count': count, 'expected': str(want)}
            for fn, want in zip(('crt_system_solve', 'crt_system_period'), expected)]


def scalar_vectors(a, m, b, n):
    expected = reference([a, b], [m, n])
    return [{'fn': fn, 'args': list(map(str, (a, m, b, n))), 'expected': str(want)}
            for fn, want in zip(('crt_merge_solve', 'crt_merge_period'), expected)]


def run(*args, cwd=ROOT):
    return subprocess.run(list(map(str, args)), cwd=cwd, capture_output=True, text=True)


class SystemRuntimeTests(unittest.TestCase):
    def check_vectors(self, vectors):
        path = SYSTEMS / 'out/test-vectors.json'
        path.write_text(json.dumps(vectors))
        result = run('node', SYSTEMS / 'scripts/check_runtime.mjs',
                     SYSTEMS / 'out/main.wasm', path)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(json.loads(result.stdout)['passed'], len(vectors))

    def test_00_native_project_and_build_helper(self):
        self.assertTrue((SYSTEMS / 'Inference.toml').is_file(),
                        'The independent native systems project is missing')
        result = run(os.environ.get('INFS', 'infs'), 'build', cwd=SYSTEMS)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        result = run(sys.executable, 'scripts/build.py', '--project-dir', 'systems')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        manifest = json.loads((SYSTEMS / 'out/manifest.json').read_text())
        self.assertEqual(manifest['compiled_wasm_proof'], 'pending')
        self.assertEqual(manifest['source']['path'], 'src/main.inf')

    def test_boundaries_and_error_precedence(self):
        fixtures = [[], [(8, 9)], [(8, 9)] * 16, [(0, 1)] * 16,
                    [(MAX - 1, MAX)], [(0, MAX), (0, 1)],
                    [(48, 49), (MAX // 49 - 1, MAX // 49)],
                    [(0, MAX), (0, 2)], [(5, 9), (2, 6)],
                    [(0, MAX), (0, 2), (1, 2)],
                    [(0, MAX), (0, 2), (-1, 2)],
                    [(0, 0)], [(MIN, 1)], [(MAX, MAX)],
                    [(0, 2), (1, 2), (0, 0)],
                    [(42 % m, m) for m in range(1, 17)],
                    [(0, 2)] * 15 + [(1, 2)],
                    [(0, 2)] * 15 + [(0, 0)],
                    [(1, 2), (MAX // 2 - 1, MAX // 2)]]
        vectors = [v for pairs in fixtures for v in batch_vectors(pairs)]
        for pairs in fixtures:
            if len(pairs) == 2:
                vectors += scalar_vectors(*pairs[0], *pairs[1])
        vectors += batch_vectors([], -1) + batch_vectors([], 17)
        vectors += batch_vectors([(5, 9)], tails=[(MIN, 0)] * 15)
        # Exact MAX = 49 * 188232082384791343; the solution is MAX-1.
        self.assertEqual(reference([48, MAX // 49 - 1], [49, MAX // 49]), (MAX - 1, MAX))
        self.check_vectors(vectors)

    def test_exhaustive_small_systems_and_scalar_merges(self):
        entries = [(a, m) for m in range(1, 5) for a in range(m)]
        vectors = [v for size in range(4) for pairs in itertools.product(entries, repeat=size)
                   for v in batch_vectors(pairs)]
        vectors += [v for m in range(1, 9) for n in range(1, 9)
                    for a in range(m) for b in range(n) for v in scalar_vectors(a, m, b, n)]
        self.check_vectors(vectors)

    def test_full_width_deterministic_vectors(self):
        rng = random.Random(20261027)
        vectors = []
        for _ in range(160):
            m, n = rng.randint(1, MAX), rng.randint(1, MAX)
            a, b = rng.randrange(m), rng.randrange(n)
            vectors += scalar_vectors(a, m, b, n)
            vectors += batch_vectors([(a, m), (b, n)])
        # Near-square periods, followed by asymmetric full-width products.
        for _ in range(160):
            m, n = rng.randint(1, 3037000499), rng.randint(1, 3037000499)
            vectors += scalar_vectors(rng.randrange(m), m, rng.randrange(n), n)
        for _ in range(160):
            m = rng.randint(1, 1000000)
            n = rng.randint(1, MAX // m)
            a, b = rng.randrange(m), rng.randrange(n)
            vectors += scalar_vectors(a, m, b, n)
            vectors += scalar_vectors(b, n, a, m)
        for m, n in [(2, MAX // 2), (MAX // 2, 2), (MAX, 2), (MAX, MAX), (MAX - 1, MAX // 2),
                     (7540113804746346429, 4660046610375530309), (1, MAX)]:
            for a, b in [(0, 0), (m - 1, n - 1), (0, n - 1), (m - 1, 0)]:
                vectors += scalar_vectors(a, m, b, n)
        self.check_vectors(vectors)

    def test_full_width_arithmetic_helpers(self):
        # Overflowing public merges stop before inverse. This native test-only
        # project reaches the unchanged Euclid helper at full i64 width.
        folder = ROOT / 'build/system-helper-probe'
        (folder / 'src').mkdir(parents=True, exist_ok=True)
        (folder / 'Inference.toml').write_bytes((SYSTEMS / 'Inference.toml').read_bytes())
        wrappers = """
        pub fn inverse_probe(B: i64, A: i64) -> i64 { return inverse_coprime(B, A); }
        pub fn add_probe(x: i64, y: i64, d: i64) -> i64 { return add_mod(x, y, d); }
        pub fn mul_probe(x: i64, y: i64, d: i64) -> i64 { return mul_mod(x, y, d); }
        """
        (folder / 'src/main.inf').write_text((SYSTEMS / 'src/main.inf').read_text() + wrappers)
        result = run(os.environ.get('INFS', 'infs'), 'build', cwd=folder)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        vectors = []
        lo, hi = 1, 2
        while hi <= MAX:
            vectors.append({'fn': 'inverse_probe', 'args': [str(lo), str(hi)],
                            'expected': str(pow(lo, -1, hi))})
            lo, hi = hi, lo + hi
        for B, A in [(1, MAX), (MAX - 1, MAX), (2, MAX), (MAX - 2, MAX)]:
            vectors.append({'fn': 'inverse_probe', 'args': [str(B), str(A)],
                            'expected': str(pow(B, -1, A))})
        rng = random.Random(20261028)
        cases = [(MAX - 1, MAX - 1, MAX), (0, 0, 1), (MAX - 2, MAX - 1, MAX)]
        for _ in range(300):
            d = rng.randint(1, MAX)
            cases.append((rng.randrange(d), rng.randrange(d), d))
        for x, y, d in cases:
            for fn, expected in [('add_probe', (x + y) % d), ('mul_probe', x * y % d)]:
                vectors.append({'fn': fn, 'args': list(map(str, (x, y, d))),
                                'expected': str(expected)})
        for _ in range(150):
            A = rng.randint(2, MAX)
            B = rng.randint(1, A - 1)
            if math.gcd(B, A) == 1:
                vectors.append({'fn': 'inverse_probe', 'args': [str(B), str(A)],
                                'expected': str(pow(B, -1, A))})
        path = folder / 'vectors.json'
        path.write_text(json.dumps(vectors))
        result = run('node', ROOT / 'scripts/check_runtime.mjs', folder / 'out/main.wasm', path)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(json.loads(result.stdout)['passed'], len(vectors))

    def test_permutations_and_successful_partition_composition(self):
        fixtures = [[(2, 6), (5, 9), (4, 5)], [(0, MAX), (0, 2), (1, 2)],
                    [(0, MAX), (0, 2), (-1, 2)], [(0, MAX), (0, 2), (0, 3)],
                    [(48, 49), (MAX // 49 - 1, MAX // 49), (0, 1)]]
        vectors = [v for pairs in fixtures for perm in itertools.permutations(pairs)
                   for v in batch_vectors(perm)]
        for pairs in [fixtures[0], fixtures[-1], [(1, 2), (3, 4), (7, 8), (7, 9)]]:
            expected = reference(*zip(*pairs))
            for perm in itertools.permutations(pairs):
                for cut in range(len(perm) + 1):
                    left, right = perm[:cut], perm[cut:]
                    vectors += batch_vectors(perm) + batch_vectors(left) + batch_vectors(right)
                    a, m = reference(*zip(*left)) if left else (0, 1)
                    b, n = reference(*zip(*right)) if right else (0, 1)
                    self.assertEqual(reference([a, b], [m, n]), expected)
                    vectors += scalar_vectors(a, m, b, n)
        self.check_vectors(vectors)

    def test_cli_decimal_transport_and_classification(self):
        fixtures = [((), 0, {'status': 'solved', 'solution': '0', 'period': '1'}),
                    ((MAX - 1, MAX), 0, {'status': 'solved', 'solution': str(MAX - 1), 'period': str(MAX)}),
                    ((0, MAX, 0, 2), 3, {'status': 'overflow'}),
                    ((0, MAX, 0, 2, 1, 2), 1, {'status': 'incompatible'}),
                    ((48, 49, MAX // 49 - 1, MAX // 49), 0,
                     {'status': 'solved', 'solution': str(MAX - 1), 'period': str(MAX)})]
        for args, code, expected in fixtures:
            result = run('node', SYSTEMS / 'scripts/demo.mjs', '--json', *args)
            self.assertEqual(result.returncode, code, result.stdout + result.stderr)
            self.assertEqual(json.loads(result.stdout), expected)
        invalid = [(0,), (0, 1) * 17, (0, MAX + 1), (0, MIN - 1),
                   (0, 18446744073709551617), (0, '1.0'), (0, '1e0'), (0, '')]
        for args in invalid:
            result = run('node', SYSTEMS / 'scripts/demo.mjs', '--json', *args)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertEqual(json.loads(result.stdout)['status'], 'invalid')


if __name__ == '__main__':
    unittest.main()
