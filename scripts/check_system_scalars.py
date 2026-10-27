#!/usr/bin/env python3
"""Certify the exact finite-system scalar Wasm exports; no batch execution claim.

Run in the pinned verifier container through opam exec. Every source in the
transitive project dependency closure is rebuilt from a single byte snapshot.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

import check_proofs
import check_wasm_proofs
import check_system_infrastructure as infrastructure
from check_proofs import FORBIDDEN, pinned_container_error, uncomment
from check_wasm_proofs import audit_assumptions
from check_system_infrastructure import InputSnapshot, legacy_modules

ROOT = Path(__file__).resolve().parents[1]
CHECKER_INPUTS = tuple(Path(module.__file__).resolve() for module in
                       (check_proofs, check_wasm_proofs, infrastructure)) + (Path(__file__).resolve(),)
MODULES = [*infrastructure.MODULES,
           'FullWidthExecution', 'FullWidthInversePrefix', 'AddModExecution',
           'SystemCalls', 'FullWidthInverseExecution', 'SystemControl', 'MulLoopState',
           'MulModExecution', 'SystemExecutionBridge', 'MergeValidation',
           'MergeSolvePure', 'MergeSolveExecution', 'MergePeriodExecution',
           'ScalarResultFacts', 'ScalarExecutionTargets', 'SystemSpecModel',
           'SystemSpecRealization', 'SystemSpecPayloads', 'SystemSpecCertificates']
MATH_SOURCES = ['specifications/CRTStatements.v', 'specifications/CRTSystemStatements.v',
                'proofs/CRTMath.v', 'proofs/CRTLoops.v',
                'proofs/CRTSystemArithmetic.v', 'proofs/CRTFinite.v']
DECLARATION = re.compile(r'^\s*(?:Theorem|Lemma|Definition|Fixpoint|Corollary|Proposition|Inductive|Record)\s+(\w+)\b', re.M)


def declarations(namespace, source, code):
    """Include definitions and nested statement namespaces, not only endpoints."""
    scopes = []
    names = []
    for line in code.splitlines():
        enter = re.match(r'^\s*Module\s+(\w+)\s*\.\s*$', line)
        leave = re.match(r'^\s*End\s+(\w+)\s*\.', line)
        if enter:
            scopes.append(enter.group(1))
        elif leave and scopes and scopes[-1] == leave.group(1):
            scopes.pop()
        match = DECLARATION.match(line)
        if match:
            names.append('.'.join([namespace, source.stem, *scopes, match.group(1)]))
    if not names:
        raise ValueError('No audited declarations: ' + str(source))
    return names


def exact_checks():
    """Close fixed signatures independently of the handwritten theorem types."""
    signatures = {
        'gcd': '''forall mem hs m n, FullWidth.moduli m n ->
 total_correct (system_run mem hs 0%num [::SM.Vi64 m;SM.Vi64 n]) (fun r => r = Z.gcd m n)''',
        'normalize': '''forall mem hs z d, word z -> 1 <= d <= FullWidth.MAX ->
 total_correct (system_run mem hs 1%num [::SM.Vi64 z;SM.Vi64 d]) (fun r => r = z mod d)''',
        'inverse': '''forall mem hs B A, FullWidth.eea_inputs A B -> Z.gcd A B = 1 ->
 total_correct (system_run mem hs 2%num [::SM.Vi64 B;SM.Vi64 A]) (fun r => r = FullWidth.inverse_model B A)''',
        'add': '''forall mem hs x y d, 1 <= d <= FullWidth.MAX -> 0 <= x < d -> 0 <= y < d ->
 total_correct (system_run mem hs 3%num [::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d]) (fun r => r = (x+y) mod d)''',
        'mul': '''forall mem hs x y d, 1 <= d <= FullWidth.MAX -> 0 <= x < d -> 0 <= y < d ->
 total_correct (system_run mem hs 4%num [::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d]) (fun r => r = (x*y) mod d)''',
    }
    for suffix, index, projection in [('solve', 5, 'solve_value'), ('period', 6, 'period_value')]:
        signatures['merge_' + suffix] = f'''forall mem hs a m b n, word a -> word m -> word b -> word n ->
 total_correct (system_run mem hs {index}%num [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n])
 (fun r => r = FiniteSystem.{projection} (FiniteSystem.merge a m b n) /\\
 FiniteSystem.result_post [::(a,m);(b,n)] (FiniteSystem.merge a m b n))'''
    code = '''From Coq Require Import ZArith NArith List String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import bytes datatypes numerics operations opsem host.
From WasmVerifier Require Import Assertions Semantics Activation Verifier.
From CRT Require Import CRTStatements CRTSystemStatements.
From CRTSystems Require Import SystemRuntime ScalarExecutionTargets
 SystemSpecModel SystemSpecRealization SystemSpecCertificates.
Module SM := CRTSystemGenerated.main.
Open Scope Z_scope.
Section Host.
Context `{ho : host}.
'''
    names = []
    for name, signature in signatures.items():
        wrapper = 'exact_system_' + name + '_execution'
        names.append(wrapper)
        code += f'Theorem {wrapper} : {signature}.\nProof. exact system_{name}_execution. Qed.\n'
    certificate_types = {
        'exact_system_scalar_export_bindings': (r'''List.firstn 2 (mod_exports SM.main) =
 [::{|modexp_name:=list_byte_of_string "crt_merge_solve"%string;modexp_desc:=MED_func 5%num|};
    {|modexp_name:=list_byte_of_string "crt_merge_period"%string;modexp_desc:=MED_func 6%num|}] /\
 List.firstn 2 (inst_exports (runtime_inst system_initial_runtime)) =
 [::Build_exportinst (list_byte_of_string "crt_merge_solve"%string) (EV_func 5%num);
    Build_exportinst (list_byte_of_string "crt_merge_period"%string) (EV_func 6%num)]''',
                                               'ScalarExecutionTargets.scalar_export_bindings'),
        'exact_system_model_realized': ('interp_realized_at system_initial_runtime system_model_interp',
                                        'SystemSpecRealization.checked_system_model_realized'),
        'exact_system_helper_contracts': ('ValidSpec SM.main SM.main__HelperContracts_specs',
                                         'SystemSpecCertificates.checked_helper_contracts'),
        'exact_system_public_contracts': ('ValidSpec SM.main SM.main__PublicContracts_specs',
                                         'SystemSpecCertificates.checked_public_contracts'),
        'exact_system_scalar_shared_contracts': (r'''interp_realized_at system_initial_runtime system_model_interp /\
 forall V h, val_fun V = system_model_interp ->
 Forall (fun P => hassert_denote V (ktrue P) h) SM.main__HelperContracts_specs /\
 Forall (fun P => hassert_denote V (ktrue P) h) SM.main__PublicContracts_specs''',
                                                'SystemSpecCertificates.checked_scalar_contracts_shared_runtime'),
    }
    for name, (signature, endpoint) in certificate_types.items():
        names.append(name)
        code += f'Theorem {name} : {signature}.\nProof. exact {endpoint}. Qed.\n'
    code += 'End Host.\n'
    for name, count in [('Helper', 8), ('Public', 5)]:
        wrapper = 'exact_system_' + name.lower() + '_contract_count'
        names.append(wrapper)
        code += f'Theorem {wrapper} : List.length SM.main__{name}Contracts_specs = {count}%nat.\nProof. reflexivity. Qed.\n'
    return code, names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / 'build/system-scalars')
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report = out / 'report.json'
    report.unlink(missing_ok=True)
    error = pinned_container_error()
    if error:
        parser.error(error)
    snapshot = InputSnapshot()
    for checker in CHECKER_INPUTS:
        snapshot.read(checker)
    for name in ('provenance.json', 'worker-opam.lock.json'):
        snapshot.read(ROOT / 'scripts/wasm_environment' / name)
    allowfile = ROOT / 'proofs/wasm/assumptions.allow'
    allowed = set(snapshot.text(allowfile).splitlines())
    manifests = {}
    for project, artifact_dir in [('systems', ROOT / 'systems/out'), ('legacy', ROOT / 'out')]:
        manifest = json.loads(snapshot.text(artifact_dir / 'manifest.json'))
        project_root = ROOT / 'systems' if project == 'systems' else ROOT
        for key, path in [('source', project_root / 'src/main.inf'), ('project', project_root / 'Inference.toml')]:
            if manifest[key]['sha256'] != snapshot.digest(path):
                parser.error(f'Stale {project} {key}: rebuild in proof mode')
        if manifest['mode'] != 'proof':
            parser.error(project + ' artifacts must be built in proof mode')
        for name in ('main.v', 'main.wasm'):
            if manifest['artifacts'][name] != snapshot.digest(artifact_dir / name):
                parser.error(f'Stale or modified {project} artifact: {name}')
        manifests[project] = manifest
    system_sources = [ROOT / 'proofs/systems' / (name + '.v') for name in MODULES]
    legacy = legacy_modules(system_sources, snapshot)
    legacy_sources = [ROOT / 'proofs/wasm' / (name + '.v') for name in legacy]
    math_sources = [ROOT / name for name in MATH_SOURCES]
    dirs = {name: out / name for name in ['math', 'generated', 'legacy-generated', 'legacy', 'systems']}
    for directory in dirs.values():
        directory.mkdir(exist_ok=True)
        for stale in directory.iterdir():
            if stale.is_file():
                stale.unlink()
    audited, hashes = [], {}
    for namespace, sources, target in [('CRT', math_sources, dirs['math']),
                                       ('CRTWasm', legacy_sources, dirs['legacy']),
                                       ('CRTSystems', system_sources, dirs['systems'])]:
        for source in sources:
            code = uncomment(snapshot.text(source))
            if FORBIDDEN.search(code):
                parser.error('Proof-hole audit failed: ' + str(source))
            audited.extend(declarations(namespace, source, code))
            hashes[str(source.relative_to(ROOT))] = snapshot.digest(source)
            snapshot.stage(source, target / source.name)
    snapshot.stage(ROOT / 'systems/out/main.v', dirs['generated'] / 'main.v')
    snapshot.stage(ROOT / 'out/main.v', dirs['legacy-generated'] / 'main.v')
    flags = ['-w', '-notation-overridden', '-R', '/workspaces/wasm-verifier/_build/default/theories', 'WasmVerifier']
    for folder, namespace in [('math', 'CRT'), ('generated', 'CRTSystemGenerated'),
                              ('legacy-generated', 'CRTGenerated'), ('legacy', 'CRTWasm'), ('systems', 'CRTSystems')]:
        flags += ['-Q', str(dirs[folder]), namespace]

    def run(command, logfile):
        with (out / logfile).open('w') as output:
            result = subprocess.run(command, cwd=out, text=True, stdout=output, stderr=subprocess.STDOUT)
        output = (out / logfile).read_text()
        if result.returncode:
            raise RuntimeError(f'{command[0]} failed; see {out / logfile}\n{output[-6000:]}')
        return output

    for source in [*[dirs['math'] / s.name for s in math_sources],
                   dirs['generated'] / 'main.v', dirs['legacy-generated'] / 'main.v',
                   *[dirs['legacy'] / s.name for s in legacy_sources],
                   *[dirs['systems'] / s.name for s in system_sources]]:
        print('Checking ' + str(source.relative_to(out)), flush=True)
        run(['coqc', *flags, str(source)], source.parent.name + '-' + source.stem + '.log')
    print('Checking fixed execution, realization, and exact contract signatures', flush=True)
    exact, wrappers = exact_checks()
    snapshot.write_staged(out / 'ExactTypes.v', exact.encode())
    run(['coqc', *flags, 'ExactTypes.v'], 'ExactTypes.log')
    audited += ['ExactTypes.' + name for name in wrappers]
    audit = 'Set Printing All.\nSet Printing Width 1000000.\nRequire Import ExactTypes.\n'
    audit += '\n'.join('Require Import CRTSystems.' + name + '.' for name in MODULES) + '\n'
    audit += '\n'.join('Print Assumptions ' + name + '.' for name in audited) + '\n'
    snapshot.write_staged(out / 'Audit.v', audit.encode())
    print(f'Auditing {len(audited)} handwritten declarations and closed targets', flush=True)
    assumptions = audit_assumptions(run(['coqc', *flags, 'Audit.v'], 'Audit.log'), len(audited), allowed)
    snapshot.write_staged(out / 'RejectedCertificate.v', b'''From Wasm Require Import host.
From WasmVerifier Require Import Verifier.
From CRTSystemGenerated Require main.
Section Host.
Context `{ho : host}.
Theorem false_certificate : ValidModule main.main.
Proof. exact main.valid_main. Qed.
Theorem false_helper_certificate : ValidSpec main.main main.main__HelperContracts_specs.
Proof. exact main.valid_main__HelperContracts. Qed.
Theorem false_public_certificate : ValidSpec main.main main.main__PublicContracts_specs.
Proof. exact main.valid_main__PublicContracts. Qed.
End Host.
Set Printing All.
Set Printing Width 1000000.
Print Assumptions false_certificate.
Print Assumptions false_helper_certificate.
Print Assumptions false_public_certificate.
''')
    rejected = run(['coqc', *flags, 'RejectedCertificate.v'], 'RejectedCertificate.log')
    try:
        audit_assumptions(rejected, 3, allowed)
    except ValueError as error:
        if not all(name in str(error) for name in ('valid_main', 'valid_main__HelperContracts', 'valid_main__PublicContracts')):
            raise
    else:
        raise RuntimeError('Audit accepted generated admitted certificate')
    print('Independent kernel check of scalar proof closure', flush=True)
    run(['coqchk', '-silent', *flags[2:],
         *['CRTSystems.' + name for name in MODULES], 'ExactTypes', 'Audit'], 'coqchk.log')
    snapshot.verify_unchanged()
    report.write_text(json.dumps({
        'status': 'scalar_wasm_execution_checked', 'scalar_exports_certified': ['crt_merge_solve', 'crt_merge_period'],
        'batch_execution_correctness_certified': False,
        'source_contracts': {'helper_assertions': 8, 'public_assertions': 5,
                             'shared_runtime': 'CRTSystems.SystemRuntime.system_initial_runtime'},
        'modules': MODULES, 'legacy_dependency_modules': legacy,
        'audited_declarations': audited, 'exact_targets': wrappers,
        'transitive_assumptions': assumptions, 'independent_kernel_check': 'passed',
        'generated_admission_negative_control': 'rejected',
        'proof_sources': hashes, 'build_manifests': manifests,
        'assumptions_allowlist_sha256': snapshot.digest(allowfile),
        'checker_dependencies': {str(path.relative_to(ROOT)): snapshot.digest(path) for path in CHECKER_INPUTS},
        'bound_inputs': snapshot.input_hashes(),
        'staged_sources': {str(path.relative_to(out)): hashlib.sha256(data).hexdigest() for path, data in snapshot.staged.items()},
        'input_and_staged_drift_check': 'passed',
    }, indent=2) + '\n')
    print(f'Checked {len(audited)} declarations and {len(wrappers)} exact scalar targets.\n{report}')


if __name__ == '__main__':
    main()
