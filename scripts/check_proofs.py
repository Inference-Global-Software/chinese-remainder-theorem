#!/usr/bin/env python3
"""Compile and independently kernel-check mathematical proofs; audit assumptions."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    'CRTMath': {
        'normalization_proved': 'T_normalization', 'reduction_proved': 'T_reduction',
        'generalized_crt_proved': 'T_generalized_CRT', 'canonical_unique_proved': 'T_canonical_unique',
        'all_solutions_proved': 'T_all_solutions', 'incompatible_proved': 'T_incompatible',
        'construct_proved': 'T_construct', 'crt_bounds_proved': 'T_crt_bounds',
    },
    'CRTLoops': {
        'normalize_proved': 'T_normalize', 'gcd_init_proved': 'T_gcd_init',
        'gcd_step_proved': 'T_gcd_step', 'gcd_exit_proved': 'T_gcd_exit',
        'eea_init_proved': 'T_eea_init', 'eea_step_proved': 'T_eea_step',
        'eea_step_bounds_proved': 'T_eea_step_bounds', 'eea_exit_proved': 'T_eea_exit',
    },
}
FORBIDDEN = re.compile(r'\b(?:Admitted|Axioms?|Parameters?|Abort|admit|admit_no_check|'
                       r'exact_no_check|vm_cast_no_check|native_cast_no_check)\b')


def uncomment(source):
    # Coq comments nest. Preserve line boundaries for declaration discovery.
    result, depth, i = [], 0, 0
    while i < len(source):
        if source[i:i+2] == '(*':
            depth += 1
            result.append(' ')
            i += 2
        elif depth and source[i:i+2] == '*)':
            depth -= 1
            i += 2
        else:
            if not depth or source[i] == '\n':
                result.append(source[i])
            i += 1
    return ''.join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--proof-dir', type=Path, default=ROOT / 'proofs')
    parser.add_argument('--out', type=Path, default=ROOT / 'build/proofs')
    args = parser.parse_args()
    out = args.out.resolve()
    sources = [ROOT / 'specifications/CRTStatements.v']
    sources += [args.proof_dir.resolve() / f'{module}.v' for module in TARGETS]
    declarations = []
    for source in sources:
        code = uncomment(source.read_text())
        if FORBIDDEN.search(code):
            parser.error(f'proof-hole audit failed: forbidden declaration or tactic in {source.name}')
        if source.stem in TARGETS:
            declarations += [(source.stem, name) for name in
                             re.findall(r'^\s*(?:Theorem|Lemma)\s+(\w+)\b', code, re.M)]
    out.mkdir(parents=True, exist_ok=True)
    for source in sources:
        shutil.copyfile(source, out / source.name)
    flags = ['-Q', str(out), 'CRT']

    def run(command, log_name):
        result = subprocess.run(command, cwd=out, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / log_name).write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f'{command[0]} failed:\n{result.stdout}')
        return result.stdout

    for source in sources:
        run(['coqc', *flags, source.name], source.stem + '.log')
    audit = 'From CRT Require Import CRTStatements CRTMath CRTLoops.\n'
    for module, endpoints in TARGETS.items():
        for name, target in endpoints.items():
            audit += f'Check ({module}.{name} : {target}).\n'
    for module, name in declarations:
        audit += f'Print Assumptions {module}.{name}.\n'
    (out / 'Audit.v').write_text(audit)
    checked = run(['coqc', *flags, 'Audit.v'], 'Audit.log')
    if checked.count('Closed under the global context') != len(declarations) or 'Axioms:' in checked:
        raise RuntimeError('Assumption audit failed; see ' + str(out / 'Audit.log'))
    run(['coqchk', '-silent', *flags, 'CRT.CRTMath', 'CRT.CRTLoops'], 'coqchk.log')
    report = {
        'status': 'mathematical_proofs_checked',
        'coqc': subprocess.check_output(['coqc', '--version'], text=True).strip(),
        'exact_targets': TARGETS,
        'exact_target_count': sum(map(len, TARGETS.values())),
        'assumption_free_declarations': len(declarations),
        'independent_kernel_check': 'passed',
        'sources': {source.name: hashlib.sha256(source.read_bytes()).hexdigest() for source in sources},
        'compiled_wasm_refinement': 'separate_obligation_not_established_by_this_check',
    }
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
