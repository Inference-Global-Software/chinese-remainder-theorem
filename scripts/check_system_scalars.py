#!/usr/bin/env python3
"""Certify the exact finite-system scalar Wasm exports; no batch execution claim.

Run in the pinned verifier container through opam exec. Every source in the
transitive project dependency closure is rebuilt from a single byte snapshot.
"""
from pathlib import Path
import system_proof_engine as engine
import re

import check_proofs
import check_wasm_proofs
import check_system_infrastructure as infrastructure
from check_proofs import FORBIDDEN, pinned_container_error, uncomment
from check_wasm_proofs import audit_assumptions
from check_system_infrastructure import InputSnapshot, legacy_modules

ROOT = Path(__file__).resolve().parents[1]
CHECKER_INPUTS = tuple(Path(module.__file__).resolve() for module in
                       (check_proofs, check_wasm_proofs, infrastructure, engine)) + (Path(__file__).resolve(),)
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
    return engine.run_gate(root=ROOT, checker_inputs=CHECKER_INPUTS, modules=MODULES,
                           math_sources_names=MATH_SOURCES, exact_checks=exact_checks,
                           declarations=declarations, description=__doc__,
                           default_out='build/system-scalars', report_metadata={'status': 'scalar_wasm_execution_checked', 'scalar_exports_certified': ['crt_merge_solve', 'crt_merge_period'], 'batch_execution_correctness_certified': False},
                           target_label='scalar', environment_check=pinned_container_error)


if __name__ == '__main__':
    main()
