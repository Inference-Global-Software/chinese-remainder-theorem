#!/usr/bin/env python3
"""Check the generated CRT module and contracts in the real verifier devcontainer.

Generated Admitted skeletons may be imported, but may never occur among the
transitive assumptions of a checked project theorem.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_proofs import FORBIDDEN, uncomment

ROOT = Path(__file__).resolve().parents[1]
MODULES = ['CRTAPIModel', 'CRTStorePure', 'CRTModule', 'CRTLoopRules', 'CRTExecution',
           'CRTCheckedArithmetic', 'CRTGeneralArithmetic', 'CRTCalls', 'CRTContracts',
           'CRTInverseExecution', 'CRTPublicExecution', 'CRTSolveExecution',
           'CRTSpecPayloads', 'CRTRealization']


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_assumptions(output, count, allowed):
    blocks = re.split(r'(?m)^(Axioms:|Closed under the global context)\s*$', output)
    if (len(blocks) - 1) // 2 != count:
        raise ValueError('Missing or unrecognized Print Assumptions output')
    actual = set()
    for i in range(1, len(blocks), 2):
        if blocks[i] != 'Axioms:':
            continue
        names = re.findall(r"(?m)^([A-Za-z_][A-Za-z0-9_.']*)\s*:", blocks[i + 1])
        if not names:
            raise ValueError('Unparseable assumptions block')
        actual.update(names)
    unexpected = actual - allowed
    if unexpected:
        raise ValueError('Unapproved transitive assumptions: ' + ', '.join(sorted(unexpected)))
    return sorted(actual)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verifier', type=Path, default=Path('/workspaces/wasm-verifier'))
    parser.add_argument('--artifact-dir', type=Path, default=ROOT / 'build/crt')
    parser.add_argument('--out', type=Path, default=ROOT / 'build/wasm-proofs')
    args = parser.parse_args()
    if not Path('/.dockerenv').exists():
        parser.error('Run this checker inside the WasmVerifier devcontainer; see scripts/wasm_environment/README.md')
    verifier, artifacts, out = args.verifier.resolve(), args.artifact_dir.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report_path = out / 'report.json'
    report_path.unlink(missing_ok=True)
    manifest = json.loads((artifacts / 'manifest.json').read_text())
    if manifest['mode'] != 'proof' or manifest['source']['sha256'] != sha256(ROOT / 'src/crt.inf'):
        parser.error('Stale source manifest: rebuild src/crt.inf in proof mode')
    for name in ('crt.v', 'crt.wasm'):
        if sha256(artifacts / name) != manifest['artifacts'][name]:
            parser.error('Stale or modified artifact: ' + name)

    math = out / 'math'
    generated = out / 'generated'
    companions = out / 'companions'
    for directory in (math, generated, companions):
        directory.mkdir(exist_ok=True)
    sources = [ROOT / 'specifications/CRTStatements.v', ROOT / 'proofs/CRTMath.v',
               ROOT / 'proofs/CRTLoops.v']
    modules = MODULES
    proof_sources = [ROOT / f'proofs/wasm/{module}.v' for module in modules]
    declarations = []
    source_hashes = {}
    for source in sources + proof_sources:
        data = source.read_bytes()
        source_hashes[str(source.relative_to(ROOT))] = hashlib.sha256(data).hexdigest()
        code = uncomment(data.decode())
        if FORBIDDEN.search(code):
            parser.error('proof-hole audit failed: ' + source.name)
        if source in proof_sources:
            declarations.extend(f'CRTWasm.{source.stem}.{name}' for name in
                                re.findall(r'^\s*(?:Theorem|Lemma)\s+(\w+)\b', code, re.M))
        ((companions if source in proof_sources else math) / source.name).write_bytes(data)
    if 'CRTModule' in modules:
        declarations.append('CRTWasm.CRTModule.crt_runtime')
    shutil.copyfile(artifacts / 'crt.v', generated / 'crt.v')
    flags = ['-R', str(verifier / '_build/default/theories'), 'WasmVerifier',
             '-Q', str(math), 'CRT', '-Q', str(generated), 'CRTGenerated',
             '-Q', str(companions), 'CRTWasm']

    def run(command, logfile):
        result = subprocess.run(command, cwd=out, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / logfile).write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f'{command[0]} failed; see {out / logfile}\n{result.stdout[-6000:]}')
        return result.stdout

    for source in [math / s.name for s in sources] + [generated / 'crt.v'] + [companions / s.name for s in proof_sources]:
        print('Checking ' + source.name, flush=True)
        run(['coqc', *flags, str(source)], source.stem + '.log')
    audit = 'Set Printing All.\nSet Printing Width 1000000.\n'
    audit += '\n'.join(f'Require Import CRTWasm.{module}.' for module in modules) + '\n'
    if 'CRTModule' in modules:
        audit += ('Check (CRTWasm.CRTModule.checked_valid_module :\n'
                  '  Verifier.ValidModule CRTGenerated.crt.crt).\n')
    audit += '''From Wasm Require Import host.
Section ExactTargets.
Context `{ho : host}.
Check (CRTWasm.CRTRealization.checked_helper_contracts :
  Verifier.ValidSpec CRTGenerated.crt.crt CRTGenerated.crt.crt__HelperContracts_specs).
Check (CRTWasm.CRTRealization.checked_public_contracts :
  Verifier.ValidSpec CRTGenerated.crt.crt CRTGenerated.crt.crt__PublicContracts_specs).
End ExactTargets.
'''
    audit += '\n'.join(f'Print Assumptions {decl}.' for decl in declarations) + '\n'
    (out / 'Audit.v').write_text(audit)
    output = run(['coqc', *flags, 'Audit.v'], 'Audit.log')
    allowfile = ROOT / 'proofs/wasm/assumptions.allow'
    allowed = set(allowfile.read_text().splitlines())
    actual = audit_assumptions(output, len(declarations), allowed)
    # A theorem that merely reuses the generated admitted skeleton compiles,
    # but must fail our transitive-assumption check. Exercise that distinction
    # with real Coq output, in addition to the parser's unit tests.
    (out / 'RejectedCertificate.v').write_text('''From Wasm Require Import host.
From WasmVerifier Require Import Verifier.
From CRTGenerated Require Import crt.
Section Host.
Context `{ho : host}.
Theorem false_certificate : ValidModule crt.crt.
Proof. exact crt.valid_crt. Qed.
End Host.
Set Printing All.
Set Printing Width 1000000.
Print Assumptions false_certificate.
''')
    rejected = run(['coqc', *flags, 'RejectedCertificate.v'], 'RejectedCertificate.log')
    try:
        audit_assumptions(rejected, 1, allowed)
    except ValueError as error:
        if 'valid_crt' not in str(error):
            raise
    else:
        raise RuntimeError('Audit accepted the generated admitted certificate')
    run(['coqchk', '-silent', *flags, *[f'CRTWasm.{module}' for module in modules]], 'coqchk.log')
    tree = hashlib.sha256()
    for source in sorted((verifier / 'theories').rglob('*.v')):
        tree.update(str(source.relative_to(verifier)).encode() + b'\0' + source.read_bytes() + b'\0')
    report = {
        'status': 'generated_module_and_contracts_checked',
        'compiled_wasm_certified': True,
        'certificate_semantics': 'WasmVerifier ValidModule and both exact generated ValidSpec propositions',
        'separate_uninstantiated_targets': ['T_normalize_execution', 'T_gcd_execution',
                                           'T_inverse_execution', 'T_period_execution',
                                           'T_solve_execution'],
        'coqc': subprocess.check_output(['coqc', '--version'], text=True).strip(),
        'modules': modules, 'audited_declarations': declarations,
        'transitive_assumptions': actual, 'assumptions_allowlist_sha256': sha256(allowfile),
        'independent_kernel_check': 'passed', 'build_manifest': manifest,
        'generated_admission_negative_control': 'rejected',
        'verifier_theory_source_tree_sha256': tree.hexdigest(),
        'proof_sources': source_hashes,
    }
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Checked {len(declarations)} declarations and the exact generated contracts.\n{report_path}')


if __name__ == '__main__':
    main()
