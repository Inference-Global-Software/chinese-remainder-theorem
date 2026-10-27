#!/usr/bin/env python3
"""Check finite-system operational infrastructure, not public CRT correctness.

Run through opam exec in the pinned project container. All handwritten sources
and the minimal unchanged legacy context dependency closure are staged afresh.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess

from check_proofs import FORBIDDEN, pinned_container_error, uncomment
from check_wasm_proofs import audit_assumptions, sha256

ROOT = Path(__file__).resolve().parents[1]
MODULES = ['ReadOnly', 'ReadOnlyDeterminism', 'ReadOnlyFlatJoin',
           'ReadOnlyConfluence', 'SystemRuntime', 'SystemMemory',
           'SystemArrayExecution']
EXACT_TARGETS = {
    'exact_initial_runtime', 'exact_system_valid_module', 'exact_system_store_readonly',
    'exact_ro_reduce_trans_preserved', 'exact_ro_reduce_trans_normal_unique',
    'exact_system_inputs_inhabited', 'exact_classifier_read_exec',
    'exact_classifier_read_all_normal',
}
DECLARATION = re.compile(r'^\s*(?:Theorem|Lemma|Definition|Fixpoint|Corollary|Proposition)\s+(\w+)\b', re.M)
IMPORT = re.compile(r'From CRTWasm Require Import ([\s\w]+)\.')


def legacy_modules(sources):
    ordered = []
    visiting = set()

    def visit(name):
        if name in ordered:
            return
        if name in visiting:
            raise ValueError('Cyclic legacy imports: ' + name)
        visiting.add(name)
        source = ROOT / 'proofs/wasm' / (name + '.v')
        for block in IMPORT.findall(uncomment(source.read_text())):
            for dependency in block.split():
                visit(dependency)
        visiting.remove(name)
        ordered.append(name)

    for source in sources:
        for block in IMPORT.findall(uncomment(source.read_text())):
            for name in block.split():
                visit(name)
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / 'build/system-infrastructure')
    args = parser.parse_args()
    error = pinned_container_error()
    if error:
        parser.error(error)
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report = out / 'report.json'
    report.unlink(missing_ok=True)
    artifacts = ROOT / 'systems/out'
    manifest = json.loads((artifacts / 'manifest.json').read_text())
    for key, source in [('source', ROOT / 'systems/src/main.inf'),
                        ('project', ROOT / 'systems/Inference.toml')]:
        if manifest[key]['sha256'] != sha256(source):
            parser.error('Stale system ' + key + ': rebuild in proof mode')
    if manifest['mode'] != 'proof':
        parser.error('System artifacts must be built in proof mode')
    for name in ('main.v', 'main.wasm'):
        if manifest['artifacts'][name] != sha256(artifacts / name):
            parser.error('Stale or modified system artifact: ' + name)
    system_sources = [ROOT / 'proofs/systems' / (name + '.v') for name in MODULES]
    legacy = legacy_modules(system_sources)
    legacy_sources = [ROOT / 'proofs/wasm' / (name + '.v') for name in legacy]
    generated, old, current = (out / name for name in ('generated', 'legacy', 'systems'))
    for directory in (generated, old, current):
        directory.mkdir(exist_ok=True)
        # Never reuse old compiled objects: every run stages and checks sources.
        for stale in directory.iterdir():
            if stale.is_file():
                stale.unlink()
    declarations, hashes = [], {}
    for namespace, sources, target in [('CRTWasm', legacy_sources, old),
                                        ('CRTSystems', system_sources, current)]:
        for source in sources:
            code = uncomment(source.read_text())
            if FORBIDDEN.search(code):
                parser.error('Proof-hole audit failed: ' + str(source))
            names = DECLARATION.findall(code)
            if not names:
                parser.error('No audited declarations: ' + str(source))
            declarations.extend(f'{namespace}.{source.stem}.{name}' for name in names)
            hashes[str(source.relative_to(ROOT))] = sha256(source)
            shutil.copyfile(source, target / source.name)
    target_source = ROOT / 'proofs/systems/InfrastructureTargets.v'
    target_code = uncomment(target_source.read_text())
    if FORBIDDEN.search(target_code):
        parser.error('Proof-hole audit failed: InfrastructureTargets.v')
    wrappers = DECLARATION.findall(target_code)
    if set(wrappers) != EXACT_TARGETS or len(wrappers) != len(EXACT_TARGETS):
        parser.error('Missing exact infrastructure target wrapper')
    hashes[str(target_source.relative_to(ROOT))] = sha256(target_source)
    shutil.copyfile(target_source, current / target_source.name)
    declarations.extend('CRTSystems.InfrastructureTargets.' + name for name in wrappers)
    shutil.copyfile(artifacts / 'main.v', generated / 'main.v')
    verifier = Path('/workspaces/wasm-verifier')
    flags = ['-w', '-notation-overridden', '-R', str(verifier / '_build/default/theories'),
             'WasmVerifier', '-Q', str(generated), 'CRTSystemGenerated',
             '-Q', str(old), 'CRTWasm', '-Q', str(current), 'CRTSystems']

    def run(command, logfile):
        result = subprocess.run(command, cwd=out, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        (out / logfile).write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f'{command[0]} failed; see {out / logfile}\n{result.stdout[-6000:]}')
        return result.stdout

    for source in [generated / 'main.v', *[old / s.name for s in legacy_sources],
                   *[current / s.name for s in system_sources], current / target_source.name]:
        print('Checking ' + source.name, flush=True)
        run(['coqc', *flags, str(source)], source.stem + '.log')
    audit = 'Set Printing All.\nSet Printing Width 1000000.\n'
    audit += '\n'.join('Require Import CRTSystems.' + name + '.'
                       for name in [*MODULES, 'InfrastructureTargets']) + '\n'
    audit += '\n'.join('Print Assumptions ' + name + '.' for name in declarations) + '\n'
    (out / 'Audit.v').write_text(audit)
    output = run(['coqc', *flags, 'Audit.v'], 'Audit.log')
    allowfile = ROOT / 'proofs/wasm/assumptions.allow'
    allowed = set(allowfile.read_text().splitlines())
    assumptions = audit_assumptions(output, len(declarations), allowed)
    (out / 'RejectedCertificate.v').write_text('''From Wasm Require Import host.
From WasmVerifier Require Import Verifier.
From CRTSystemGenerated Require main.
Section Host.
Context `{ho : host}.
Theorem false_certificate : ValidModule main.main.
Proof. exact main.valid_main. Qed.
End Host.
Set Printing All.
Set Printing Width 1000000.
Print Assumptions false_certificate.
''')
    rejected = run(['coqc', *flags, 'RejectedCertificate.v'], 'RejectedCertificate.log')
    try:
        audit_assumptions(rejected, 1, allowed)
    except ValueError as error:
        if 'valid_main' not in str(error):
            raise
    else:
        raise RuntimeError('Audit accepted generated admitted certificate')
    run(['coqchk', '-silent', *flags[2:], *['CRTSystems.' + name for name in
         [*MODULES, 'InfrastructureTargets']]], 'coqchk.log')
    report.write_text(json.dumps({
        'status': 'operational_infrastructure_checked',
        'public_crt_execution_correctness_certified': False,
        'modules': MODULES, 'legacy_context_modules': legacy,
        'audited_declarations': declarations, 'exact_targets': wrappers,
        'transitive_assumptions': assumptions,
        'independent_kernel_check': 'passed',
        'generated_admission_negative_control': 'rejected',
        'proof_sources': hashes, 'build_manifest': manifest,
        'assumptions_allowlist_sha256': sha256(allowfile),
        'checker_sha256': sha256(Path(__file__)),
    }, indent=2) + '\n')
    print(f'Checked {len(declarations)} declarations and {len(wrappers)} exact infrastructure targets.\n{report}')


if __name__ == '__main__':
    main()
