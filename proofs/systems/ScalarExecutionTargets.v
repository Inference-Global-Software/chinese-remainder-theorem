(* Existence of normal native execution and correctness of every normal result.
   The relation contains only actual Wasm reduction and signed result decoding. *)
From Coq Require Import ZArith NArith Lia List String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import bytes datatypes numerics operations opsem host.
From WasmVerifier Require Import Assertions Semantics Activation Verifier.
From CRT Require Import CRTStatements CRTSystemStatements CRTSystemArithmetic CRTFinite.
From CRTSystems Require Import SystemRuntime FullWidthExecution SystemCalls
 FullWidthInverseExecution MulModExecution MergePeriodExecution MergeSolveExecution SystemExecutionBridge ScalarResultFacts.
Module SM := CRTSystemGenerated.main.
Import FullWidth FiniteSystem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Section Host.
Context `{ho : host}.
Theorem scalar_export_bindings :
 List.firstn 2 (mod_exports SM.main) =
 [::{|modexp_name:=list_byte_of_string "crt_merge_solve"%string;modexp_desc:=MED_func 5%num|};
    {|modexp_name:=list_byte_of_string "crt_merge_period"%string;modexp_desc:=MED_func 6%num|}] /\
 List.firstn 2 (inst_exports (runtime_inst system_initial_runtime)) =
 [::Build_exportinst (list_byte_of_string "crt_merge_solve"%string) (EV_func 5%num);
    Build_exportinst (list_byte_of_string "crt_merge_period"%string) (EV_func 6%num)].
Proof. split; reflexivity. Qed.
Context (mem : meminst).
Lemma system_mul_exec_exists hs x y d : 1 <= d <= MAX -> 0 <= x < d -> 0 <= y < d ->
 system_run mem hs 4%num [::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d] (FullWidth.mul_mod x y d).
Proof.
 move=> Hd Hx Hy. have [_ [_ Wr]] := mul_mod_proved x y d Hd Hx Hy.
 apply: system_run_of_call; first exact Wr.
 apply: crt_mul_call; [reflexivity|exact Hd|exact Hx|exact Hy].
Qed.
Lemma system_merge_solve_exec_exists hs a m b n : word a -> word m -> word b -> word n ->
 system_run mem hs 5%num [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n]
 (solve_value (merge a m b n)).
Proof.
 move=> Wa Wm Wb Wn. apply: system_run_of_call; first exact (proj1 (scalar_result_values_word a m b n)).
 apply: crt_merge_solve_call; [reflexivity|exact Wa|exact Wm|exact Wb|exact Wn].
Qed.
Theorem system_gcd_execution hs m n : moduli m n ->
 total_correct (system_run mem hs 0%num [::SM.Vi64 m;SM.Vi64 n]) (fun r => r = Z.gcd m n).
Proof. move=> H. apply: system_run_total_correct; [exact: system_gcd_exec_exists|reflexivity]. Qed.
Theorem system_normalize_execution hs z d : word z -> 1 <= d <= MAX ->
 total_correct (system_run mem hs 1%num [::SM.Vi64 z;SM.Vi64 d]) (fun r => r = z mod d).
Proof. move=> Hz Hd. apply: system_run_total_correct; [exact: system_normalize_exec_exists|reflexivity]. Qed.
Theorem system_inverse_execution hs B A : eea_inputs A B -> Z.gcd A B = 1 ->
 total_correct (system_run mem hs 2%num [::SM.Vi64 B;SM.Vi64 A]) (fun r => r = inverse_model B A).
Proof. move=> Hi Hc. apply: system_run_total_correct; [exact: system_inverse_exec_exists|reflexivity]. Qed.
Theorem system_add_execution hs x y d : 1 <= d <= MAX -> 0 <= x < d -> 0 <= y < d ->
 total_correct (system_run mem hs 3%num [::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d]) (fun r => r = (x+y) mod d).
Proof.
 move=> Hd Hx Hy. apply: (system_run_total_correct (result:=FullWidth.add_mod x y d)).
 - exact: system_add_exec_exists.
 - exact (proj1 (add_mod_proved x y d Hd Hx Hy)).
Qed.
Theorem system_mul_execution hs x y d : 1 <= d <= MAX -> 0 <= x < d -> 0 <= y < d ->
 total_correct (system_run mem hs 4%num [::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d]) (fun r => r = (x*y) mod d).
Proof.
 move=> Hd Hx Hy. apply: (system_run_total_correct (result:=FullWidth.mul_mod x y d)).
 - exact: system_mul_exec_exists.
 - exact (proj1 (mul_mod_proved x y d Hd Hx Hy)).
Qed.
Theorem system_merge_solve_execution hs a m b n : word a -> word m -> word b -> word n ->
 total_correct (system_run mem hs 5%num [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n])
 (fun r => r = solve_value (merge a m b n) /\ result_post [::(a,m);(b,n)] (merge a m b n)).
Proof.
 move=> Wa Wm Wb Wn. apply: system_run_total_correct; first exact: system_merge_solve_exec_exists.
 split; [reflexivity|exact: scalar_model_proved].
Qed.
Lemma system_merge_period_exec_exists hs a m b n : word a -> word m -> word b -> word n ->
 system_run mem hs 6%num [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n]
 (period_value (merge a m b n)).
Proof.
 move=> Wa Wm Wb Wn. apply: system_run_of_call; first exact (proj2 (scalar_result_values_word a m b n)).
 apply: crt_merge_period_call; [reflexivity|exact Wa|exact Wm|exact Wb|exact Wn].
Qed.
Theorem system_merge_period_execution hs a m b n : word a -> word m -> word b -> word n ->
 total_correct (system_run mem hs 6%num [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n])
 (fun r => r = period_value (merge a m b n) /\ result_post [::(a,m);(b,n)] (merge a m b n)).
Proof.
 move=> Wa Wm Wb Wn. apply: system_run_total_correct; first exact: system_merge_period_exec_exists.
 split; [reflexivity|exact: scalar_model_proved].
Qed.
End Host.
