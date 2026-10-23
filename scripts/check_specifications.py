#!/usr/bin/env python3
"""Reproduce expressibility checks. This script never claims proof completion."""
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
M = 2**31 - 1
LOW, HIGH = -(2**63), 2**63 - 1


def run(args, cwd=ROOT, expected=0):
    result = subprocess.run(list(map(str, args)), cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode != expected:
        raise RuntimeError(f"Command failed ({result.returncode}): {args}\n{result.stdout}")
    return result.stdout


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def period(m, n):
    return math.lcm(m, n) if 1 <= m <= M and 1 <= n <= M else -2


def oracle(a, m, b, n):
    if not (1 <= m <= M and 1 <= n <= M and 0 <= a < m and 0 <= b < n):
        return -2
    g = math.gcd(m, n)
    if (b - a) % g:
        return -1
    reduced_n = n // g
    if reduced_n == 1:
        return a
    # Python's unbounded builtin modular inverse, independent of the Inf body.
    u = pow(m // g, -1, reduced_n)
    return a + m * (((b - a) // g * u) % reduced_n)


def runtime_vectors():
    vectors = []

    def add(fn, args, expected):
        vectors.append(dict(fn=fn, args=list(map(str, args)), expected=str(expected)))

    # Independent brute-force search; does not use the constructive formula.
    for m in range(1, 17):
        for n in range(1, 17):
            witnesses = {(x % m, x % n): x for x in range(math.lcm(m, n))}
            for a in range(m):
                for b in range(n):
                    add('crt_solve', (a, m, b, n), witnesses.get((a, b), -1))
            add('crt_period', (m, n), math.lcm(m, n))

    edges = (LOW, -1, 0, 1, M, M + 1, HIGH)
    for args in itertools.product(edges, repeat=4):
        add('crt_solve', args, oracle(*args))
    for m, n in itertools.product(edges, repeat=2):
        add('crt_period', (m, n), period(m, n))

    rng = random.Random(20261023)
    for _ in range(1024):
        m, n = rng.randint(1, M), rng.randint(1, M)
        a, b = rng.randrange(m), rng.randrange(n)
        add('crt_solve', (a, m, b, n), oracle(a, m, b, n))
        add('crt_period', (m, n), period(m, n))
    # Worst-size products, negative differences, equal/dividing moduli, modulus 1.
    for a, m, b, n in [(M - 1, M, M - 2, M - 1), (M - 1, M, 0, M - 1),
                        (0, M, M - 2, M - 1), (2, 6, 5, 9), (2, 6, 4, 9),
                        (2, 3, 3, 5), (5, 9, 2, 6), (8, 9, 2, 3),
                        (M - 1, M, M - 1, M), (M - 1, M, M - 2, M),
                        (0, 1, M - 1, M), (M - 1, M, 0, 1)]:
        add('crt_solve', (a, m, b, n), oracle(a, m, b, n))
        add('crt_period', (m, n), period(m, n))
    for m in range(1, 129):
        for n in range(1, 129):
            add('gcd_positive', (m, n), math.gcd(m, n))
            if n < m and math.gcd(m, n) == 1:
                add('inverse_coprime', (n, m), pow(n, -1, m))
    for z, d in itertools.product((LOW, LOW + 1, -M, -1, 0, 1, M, HIGH),
                                  (1, 2, 3, M - 1, M)):
        add('normalize', (z, d), z % d)
    if not any(v['fn'] == 'crt_solve' and int(v['expected']) > 2**53 for v in vectors):
        raise RuntimeError('Missing exact-integer transport coverage')
    return vectors


def audit_invariants():
    """Finite model checks of the written invariants, not inductive proofs."""
    pairs = [(A, B) for A in range(2, 129) for B in range(1, A)]
    rng = random.Random(20261023)
    pairs += [(M, 1), (M, M - 1), (1836311903, 1134903170)]
    for _ in range(1024):
        A = rng.randint(2, M)
        pairs.append((A, rng.randint(1, A - 1)))
    states = steps = 0

    def require(condition, detail):
        if not condition:
            raise RuntimeError(f'Invariant audit failed: {detail}')

    for A, B in pairs:
        r0, r1, s0, s1, t0, t1 = A, B, 1, 0, 0, 1
        while True:
            detail = (A, B, r0, r1, s0, s1, t0, t1)
            conditions = [0 <= r1 < r0 <= A, math.gcd(r0, r1) == math.gcd(A, B),
                          r0 == A * s0 + B * t0, r1 == A * s1 + B * t1,
                          abs(s0 * t1 - s1 * t0) == 1, s0 * s1 <= 0, t0 * t1 <= 0,
                          r0 * abs(s1) + r1 * abs(s0) == B,
                          r0 * abs(t1) + r1 * abs(t0) == A,
                          abs(s0) <= B, abs(s1) <= B, abs(t0) <= A, abs(t1) <= A]
            require(all(conditions), detail)
            states += 1
            if r1 == 0:
                require(r0 == math.gcd(A, B), detail)
                if r0 == 1:
                    require(B * (t0 % A) % A == 1, detail)
                break
            q, r2 = divmod(r0, r1)
            s2, t2 = s0 - q * s1, t0 - q * t1
            require(1 <= q <= A and 0 <= r2 < r1 and 0 <= q * r1 <= A, detail)
            require(abs(q * s1) <= B and abs(s2) <= B, detail)
            require(abs(q * t1) <= A and abs(t2) <= A, detail)
            require(all(LOW <= v <= HIGH for v in (q*s1, s2, q*t1, t2)), detail)
            r0, r1, s0, s1, t0, t1 = r1, r2, s1, s2, t1, t2
            steps += 1
    return dict(input_pairs=len(pairs), visited_states=states, checked_steps=steps)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--infc', required=True, type=Path)
    parser.add_argument('--inference-source', required=True, type=Path,
                        help='Matching compiler checkout, including its public Rocq signature stub')
    parser.add_argument('--out', type=Path, default=ROOT / 'build' / 'specifications')
    args = parser.parse_args()
    infc, source, out = args.infc.resolve(), args.inference_source.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report = {'status': 'expressibility_checked_not_proved', 'compiler': {
        'version': run([infc, '--version']).strip(),
        'reported_commit': run([infc, '--commit-hash']).strip(),
        'abi': run([infc, '--abi-version']).strip(),
        'binary_sha256': digest(infc),
        'source_revision': run(['git', 'rev-parse', 'HEAD'], cwd=source).strip(),
        'source_tree_clean': not run(['git', 'status', '--porcelain'], cwd=source).strip(),
    }, 'tools': {'coqc': run(['coqc', '--version']).strip(),
                 'node': run(['node', '--version']).strip()}, 'inputs': {}}
    if not report['compiler']['source_revision'].startswith(report['compiler']['reported_commit']):
        raise RuntimeError('Compiler reported commit does not match source checkout')

    for path in sorted((ROOT / 'probes').glob('*.inf')):
        report['inputs'][str(path.relative_to(ROOT))] = digest(path)
        # Isolated entry directories avoid unrelated-import warnings.
        entry_dir = out / 'inputs' / path.stem
        entry_dir.mkdir(parents=True, exist_ok=True)
        entry = entry_dir / path.name
        shutil.copyfile(path, entry)
        dest = out / path.stem
        rejected = path.stem.startswith('rejected_')
        log = run([infc, entry, '--mode', 'proof', '--out-dir', dest], expected=int(rejected))
        (out / (path.stem + '.log')).write_text(log)
        if rejected:
            expected = 'P002' if path.stem == 'rejected_loop' else 'P003'
            if f'error[{expected}]' not in log:
                raise RuntimeError(f'Missing expected diagnostic {expected}: {log}')
            report.setdefault('expected_rejections', {})[path.name] = expected

    generated = out / 'crt_contracts' / 'crt_contracts.v'
    wasm = generated.with_suffix('.wasm')
    text = generated.read_text()
    for shape in ('HA_app_ok', 'T_app', 'HA_ex', 'Hall'):
        if shape not in text:
            raise RuntimeError(f'Missing generated assertion shape: {shape}')
    report['translation'] = {
        'source_contracts': len(re.findall(r'^    fn .* forall \{',
                                         (ROOT / 'probes/crt_contracts.inf').read_text(), re.M)),
        'emitted_assertions': len(re.findall(r'^Definition .*_hspec\d+ : hassert', text, re.M)),
        'generated_admissions': len(re.findall(r'^Admitted\.', text, re.M)),
        'wasm_sha256': digest(wasm), 'rocq_sha256': digest(generated)}
    if report['translation']['source_contracts'] != report['translation']['emitted_assertions']:
        raise RuntimeError('Source and emitted contract counts differ')

    formal = ROOT / 'specifications/CRTStatements.v'
    formal_copy = out / formal.name
    shutil.copyfile(formal, formal_copy)
    run(['coqc', formal_copy])
    report['inputs'][str(formal.relative_to(ROOT))] = digest(formal)
    report['mathematical_statements'] = {'elaboration': 'passed', 'proofs_claimed': 0,
        'proposition_definitions': len(re.findall(r'^Definition T_', formal.read_text(), re.M))}

    # This stub checks constructor signatures only. It has NO proof semantics.
    stub = out / 'rocq-signature-stub'
    shutil.copytree(source / 'core/wasm-to-v/rocq-stub', stub, dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns('*.vo', '*.vos', '*.vok', '*.glob', '.*.aux'))
    flags = ['-Q', stub / 'wasm', 'Wasm', '-Q', stub / 'wasm_verifier', 'WasmVerifier']
    for file in ('wasm/bytes.v', 'wasm/numerics.v', 'wasm/datatypes.v', 'wasm/host.v',
                 'wasm_verifier/Assertions.v', 'wasm_verifier/Verifier.v', 'wasm_verifier/Exists.v'):
        run(['coqc', *flags, stub / file])
    run(['coqc', *flags, generated])
    report['generated_rocq_signature_check'] = 'passed_against_compiler_stub_only'

    vectors_path = out / 'runtime-vectors.json'
    vectors_path.write_text(json.dumps(runtime_vectors()))
    report['runtime'] = json.loads(run(['node', ROOT / 'scripts/check_runtime.mjs', wasm, vectors_path]))
    report['invariant_model_checks'] = audit_invariants()
    for path in sorted((ROOT / 'scripts').glob('*')):
        if path.is_file():
            report['inputs'][str(path.relative_to(ROOT))] = digest(path)
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
