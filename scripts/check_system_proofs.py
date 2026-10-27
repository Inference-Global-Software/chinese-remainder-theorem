#!/usr/bin/env python3
"""Fail-closed certificate gate for all scalar and batch native CRT exports.

Run only in the pinned verifier container. Exact target signatures are fixed
below; every declaration, snapshot input and generated wrapper is audited.
"""
from pathlib import Path
import system_proof_engine as engine
import check_system_scalars as scalars
from check_system_scalars import (ROOT, MATH_SOURCES, declarations, infrastructure,
    InputSnapshot, legacy_modules, pinned_container_error, FORBIDDEN, uncomment,
    audit_assumptions)
CHECKER_INPUTS = scalars.CHECKER_INPUTS + (Path(__file__).resolve(),)
MODULES = scalars.MODULES + [
    'ArrayAccess', 'BatchArithmetic', 'BatchCount', 'BatchValidation', 'BatchPair',
    'BatchClassState', 'BatchValidateLoop', 'BatchPairRow', 'BatchPairLoop',
    'BatchClassModel', 'BatchClassExecution', 'BatchPublicPrefix',
    'BatchPeriodFold', 'BatchPeriodExecution', 'BatchSolveFold',
    'BatchSolveExecution', 'BatchExecutionAlgebra', 'BatchExecutionTargets']


def exact_checks():
    code, names = scalars.exact_checks()
    code += """
From Coq Require Import Sorting.Permutation.
From CRTSystems Require Import SystemMemory BatchArithmetic BatchClassModel
 BatchExecutionAlgebra BatchExecutionTargets.
Import FullWidth FiniteSystem.
Section BatchHost.
Context `{ho : host}.
"""
    signatures = {
        'batch_export_bindings': r"""List.firstn 2 (List.skipn 2 (mod_exports SM.main)) =
 [::{|modexp_name:=list_byte_of_string "crt_system_solve"%string;modexp_desc:=MED_func 8%num|};
    {|modexp_name:=list_byte_of_string "crt_system_period"%string;modexp_desc:=MED_func 9%num|}] /\
 List.firstn 2 (List.skipn 2 (inst_exports (runtime_inst system_initial_runtime))) =
 [::Build_exportinst (list_byte_of_string "crt_system_solve"%string) (EV_func 8%num);
    Build_exportinst (list_byte_of_string "crt_system_period"%string) (EV_func 9%num)]""",
        'system_batch_solve_execution': r"""forall mem hs rb mb c rs ms, system_input_memory mem rb mb rs ms -> batch_word32 c ->
 total_correct (system_run mem hs 8%num (be_args rb mb c))
 (fun r => r=solve_value (be_batch_result c rs ms) /\ (0<=c<=16 -> result_post (be_active c rs ms) (be_batch_result c rs ms)))""",
        'system_batch_period_execution': r"""forall mem hs rb mb c rs ms, system_input_memory mem rb mb rs ms -> batch_word32 c ->
 total_correct (system_run mem hs 9%num (be_args rb mb c))
 (fun p => p=period_value (be_batch_result c rs ms) /\ (0<=c<=16 -> result_post (be_active c rs ms) (be_batch_result c rs ms)))""",
        'system_batch_permutation': r"""forall memA memB hsA hsB ptrRA ptrMA ptrRB ptrMB c rsA msA rsB msB rA pA rB pB, system_input_memory memA ptrRA ptrMA rsA msA -> batch_word32 c -> system_input_memory memB ptrRB ptrMB rsB msB -> batch_word32 c ->
 Permutation (be_active c rsA msA) (be_active c rsB msB) ->
 system_run memA hsA 8%num (be_args ptrRA ptrMA c) rA -> system_run memA hsA 9%num (be_args ptrRA ptrMA c) pA ->
 system_run memB hsB 8%num (be_args ptrRB ptrMB c) rB -> system_run memB hsB 9%num (be_args ptrRB ptrMB c) pB ->
 rA=rB /\ pA=pB""",
        'system_batch_success_summary': r"""forall mem hs ptrR ptrM c rs ms r p, system_input_memory mem ptrR ptrM rs ms -> batch_word32 c ->
 system_run mem hs 8%num (be_args ptrR ptrM c) r -> system_run mem hs 9%num (be_args ptrR ptrM c) p ->
 0<=r -> 0<=c<=16 /\ valid (be_active c rs ms) /\ p<=MAX /\ Rep (be_active c rs ms) r p""",
        'system_batch_composition': r"""forall memA memB memM hsA hsB hsM ptrRA ptrMA ptrRB ptrMB ca cb rsA msA rsB msB r p s q, system_input_memory memA ptrRA ptrMA rsA msA -> batch_word32 ca -> system_input_memory memB ptrRB ptrMB rsB msB -> batch_word32 cb ->
 system_run memA hsA 8%num (be_args ptrRA ptrMA ca) r -> system_run memA hsA 9%num (be_args ptrRA ptrMA ca) p ->
 system_run memB hsB 8%num (be_args ptrRB ptrMB cb) s -> system_run memB hsB 9%num (be_args ptrRB ptrMB cb) q ->
 0<=r -> 0<=s ->
 total_correct (system_run memM hsM 5%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q])
 (fun x => x=solve_value (system_model (be_active ca rsA msA ++ be_active cb rsB msB)) /\
 result_post (be_active ca rsA msA ++ be_active cb rsB msB) (system_model (be_active ca rsA msA ++ be_active cb rsB msB))) /\
 total_correct (system_run memM hsM 6%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q])
 (fun x => x=period_value (system_model (be_active ca rsA msA ++ be_active cb rsB msB)) /\
 result_post (be_active ca rsA msA ++ be_active cb rsB msB) (system_model (be_active ca rsA msA ++ be_active cb rsB msB)))""",
        'system_batch_concat': r"""forall memA memB memC memM hsA hsB hsC hsM ptrRA ptrMA ptrRB ptrMB ptrRC ptrMC ca cb cc rsA msA rsB msB rsC msC r p s q xM pM xC pC, system_input_memory memA ptrRA ptrMA rsA msA -> batch_word32 ca -> system_input_memory memB ptrRB ptrMB rsB msB -> batch_word32 cb ->
 system_input_memory memC ptrRC ptrMC rsC msC -> batch_word32 cc -> 0<=cc<=16 ->
 Permutation (be_active ca rsA msA ++ be_active cb rsB msB) (be_active cc rsC msC) ->
 system_run memA hsA 8%num (be_args ptrRA ptrMA ca) r -> system_run memA hsA 9%num (be_args ptrRA ptrMA ca) p ->
 system_run memB hsB 8%num (be_args ptrRB ptrMB cb) s -> system_run memB hsB 9%num (be_args ptrRB ptrMB cb) q ->
 0<=r -> 0<=s ->
 system_run memM hsM 5%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q] xM ->
 system_run memM hsM 6%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q] pM ->
 system_run memC hsC 8%num (be_args ptrRC ptrMC cc) xC -> system_run memC hsC 9%num (be_args ptrRC ptrMC cc) pC ->
 xM=xC /\ pM=pC""",
    }
    for endpoint, signature in signatures.items():
        name = 'exact_' + endpoint
        names.append(name)
        code += f'Theorem {name} : {signature}.\nProof. exact BatchExecutionTargets.{endpoint}. Qed.\n'
    code += 'End BatchHost.\n'
    return code, names


def main():
    return engine.run_gate(root=ROOT, checker_inputs=CHECKER_INPUTS, modules=MODULES,
                           math_sources_names=MATH_SOURCES, exact_checks=exact_checks,
                           declarations=declarations, description=__doc__,
                           default_out='build/system-proofs', report_metadata={'status': 'finite_system_wasm_execution_checked', 'scalar_exports_certified': ['crt_merge_solve', 'crt_merge_period'], 'batch_execution_correctness_certified': True, 'batch_exports_certified': ['crt_system_solve', 'crt_system_period'], 'execution_strength': 'normal execution exists; every normal result is correct', 'runtime_capacity': 16, 'mathematical_capacity': 'unbounded'},
                           target_label='scalar and batch', environment_check=pinned_container_error)


if __name__ == '__main__':
    main()
