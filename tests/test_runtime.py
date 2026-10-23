"""Integration tests against the actual proof-mode Wasm and user-facing CLI."""
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_specifications import runtime_vectors


def command(*args, env=None):
    return subprocess.run(list(map(str, args)), cwd=ROOT, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)


class BuildTests(unittest.TestCase):
    def test_compiler_name_is_resolved_on_path(self):
        compiler = os.environ.get('INFC', 'infc')
        import shutil
        resolved = shutil.which(compiler)
        self.assertIsNotNone(resolved, 'Test requires a real Inference compiler')
        env = dict(os.environ, PATH=str(Path(resolved).parent) + os.pathsep + os.environ['PATH'])
        result = command(sys.executable, 'scripts/build.py', '--infc', Path(resolved).name, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_build_and_independent_reference_vectors(self):
        result = command(sys.executable, 'scripts/build.py')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        vectors = [v for v in runtime_vectors() if v['fn'].startswith('crt_')]
        path = ROOT / 'build/crt/runtime-vectors.json'
        path.write_text(json.dumps(vectors))
        result = command('node', 'scripts/check_runtime.mjs', 'build/crt/crt.wasm', path)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(json.loads(result.stdout)['passed'], len(vectors))


class DemoTests(unittest.TestCase):
    def demo(self, *args):
        result = command('node', 'scripts/demo.mjs', '--json', *args)
        try:
            payload = json.loads(result.stdout)
        except json.JSONDecodeError:
            self.fail(f'CLI must return a JSON result: {result.stdout!r}; {result.stderr}')
        return result.returncode, payload

    def test_non_coprime_and_negative_difference(self):
        for args in [(2, 6, 5, 9), (5, 9, 2, 6)]:
            with self.subTest(args=args):
                code, result = self.demo(*args)
                self.assertEqual(code, 0)
                self.assertEqual(result, {'status': 'solved', 'solution': '14', 'period': '18'})

    def test_incompatible_is_distinct_from_invalid(self):
        self.assertEqual(self.demo(2, 6, 4, 9),
                         (1, {'status': 'incompatible', 'period': '18'}))
        for args in [(2, 0, 4, 9), (6, 6, 4, 9), (0, 1, -1, 9)]:
            with self.subTest(args=args):
                code, result = self.demo(*args)
                self.assertEqual(code, 2)
                self.assertEqual(result['status'], 'invalid')

    def test_modulus_one_and_equal_moduli(self):
        for args, x, period in [((0, 1, 0, 1), '0', '1'),
                               ((0, 1, 8, 9), '8', '9'),
                               ((8, 9, 0, 1), '8', '9'),
                               ((8, 9, 8, 9), '8', '9')]:
            with self.subTest(args=args):
                self.assertEqual(self.demo(*args),
                                 (0, {'status': 'solved', 'solution': x, 'period': period}))
        self.assertEqual(self.demo(8, 9, 7, 9),
                         (1, {'status': 'incompatible', 'period': '9'}))

    def test_large_solution_preserves_every_digit(self):
        self.assertEqual(self.demo(2147483646, 2147483647, 2147483645, 2147483646),
                         (0, {'status': 'solved', 'solution': '4611686011984936961',
                              'period': '4611686011984936962'}))

    def test_i64_bounds_checked_before_wasm_argument_coercion(self):
        # 2^64+1 would silently become 1 if passed straight to a Wasm i64 export.
        for value in ('18446744073709551617', '-9223372036854775809',
                      '9223372036854775808', '1.0', '1e0', 'NaN', ''):
            with self.subTest(value=value):
                code, result = self.demo(0, value, 0, 1)
                self.assertEqual(code, 2)
                self.assertEqual(result['status'], 'invalid')

    def test_argument_count_and_signed_i64_extremes(self):
        for args in [(), (0, 1, 0), (0, 1, 0, 1, 0),
                     (0, '-9223372036854775808', 0, 1),
                     (0, '9223372036854775807', 0, 1)]:
            with self.subTest(args=args):
                code, result = self.demo(*args)
                self.assertEqual(code, 2)
                self.assertEqual(result['status'], 'invalid')

    def test_human_readable_schedule_demo(self):
        result = command('node', 'scripts/demo.mjs', 2, 6, 5, 9)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('14', result.stdout)
        self.assertIn('18', result.stdout)


if __name__ == '__main__':
    unittest.main()
