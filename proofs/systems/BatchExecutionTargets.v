(* Closed public batch execution and algebra targets. Raw ABI premises are explicit. *)
From Coq Require Import ZArith NArith Lia List String Sorting.Permutation.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import bytes datatypes numerics operations opsem host.
From WasmVerifier Require Import Assertions Semantics Activation Verifier.
From CRT Require Import CRTStatements CRTSystemStatements CRTSystemArithmetic CRTFinite.
From CRTSystems Require Import SystemRuntime SystemMemory SystemCalls FullWidthExecution SystemExecutionBridge BatchArithmetic BatchClassModel BatchSolveExecution BatchPeriodExecution BatchExecutionAlgebra.
Module SM := CRTSystemGenerated.main.
Import FullWidth FiniteSystem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Lemma batch_count_bools c : ((c <? 0) || (16 <? c)) = negb ((0 <=? c) && (c <=? 16)).
Proof.
 case E:((c <? 0) || (16 <? c)); case F:((0 <=? c) && (c <=? 16)); try reflexivity.
 - apply Bool.orb_true_iff in E. apply Bool.andb_true_iff in F as [F0 F16].
   apply Z.leb_le in F0. apply Z.leb_le in F16. destruct E as [E|E]; apply Z.ltb_lt in E; lia.
 - apply Bool.orb_false_iff in E as [E0 E16]. apply Bool.andb_false_iff in F.
   apply Z.ltb_ge in E0. apply Z.ltb_ge in E16. destruct F as [F|F]; apply Z.leb_gt in F; lia.
Qed.
Lemma batch_solve_result c rs ms : bs_result c rs ms = solve_value (be_batch_result c rs ms).
Proof. rewrite /bs_result /be_batch_result /be_active batch_count_bools. case: ((0 <=? c) && (c <=? 16)); reflexivity. Qed.
Lemma batch_period_result c rs ms : bp_result c rs ms = period_value (be_batch_result c rs ms).
Proof. rewrite /bp_result /be_batch_result /be_active batch_count_bools. case: ((0 <=? c) && (c <=? 16)); [exact: period_model_proved|reflexivity]. Qed.
Lemma batch_result_post c rs ms : 0<=c<=16 -> result_post (be_active c rs ms) (be_batch_result c rs ms).
Proof. move=> Hc. rewrite (be_result_count rs ms Hc). exact: finite_model_proved. Qed.
Lemma batch_result_words c rs ms : word (solve_value (be_batch_result c rs ms)) /\ word (period_value (be_batch_result c rs ms)).
Proof.
 rewrite /be_batch_result. case: ((0<=?c)&&(c<=?16)); last (cbn;unfold word,i64_min,i64_max;lia).
 have H := finite_model_proved (be_active c rs ms).
 destruct (system_model (be_active c rs ms)) as [| | |r p]; cbn in *; try (unfold word,i64_min,i64_max;lia).
 destruct H as [_ [_ [Hp [HL [Hr Hsol]]]]]. split; apply nonnegative_word; lia.
Qed.
Section Host.
Context `{ho:host}.
Theorem batch_export_bindings :
 List.firstn 2 (List.skipn 2 (mod_exports SM.main)) =
 [::{|modexp_name:=list_byte_of_string "crt_system_solve"%string;modexp_desc:=MED_func 8%num|};
    {|modexp_name:=list_byte_of_string "crt_system_period"%string;modexp_desc:=MED_func 9%num|}] /\
 List.firstn 2 (List.skipn 2 (inst_exports (runtime_inst system_initial_runtime))) =
 [::Build_exportinst (list_byte_of_string "crt_system_solve"%string) (EV_func 8%num);
    Build_exportinst (list_byte_of_string "crt_system_period"%string) (EV_func 9%num)].
Proof. split; reflexivity. Qed.
Lemma system_batch_solve_exec_exists mem hs rb mb c rs ms :
 system_input_memory mem rb mb rs ms -> batch_word32 c ->
 system_run mem hs 8%num (be_args rb mb c) (solve_value (be_batch_result c rs ms)).
Proof.
 move=> [_ [Hr Hm]] Wc. apply: system_run_of_call; first exact (proj1 (batch_result_words c rs ms)).
 rewrite -batch_solve_result. apply: crt_batch_solve_call; try assumption; reflexivity.
Qed.
Lemma system_batch_period_exec_exists mem hs rb mb c rs ms :
 system_input_memory mem rb mb rs ms -> batch_word32 c ->
 system_run mem hs 9%num (be_args rb mb c) (period_value (be_batch_result c rs ms)).
Proof.
 move=> [_ [Hr Hm]] Wc. apply: system_run_of_call; first exact (proj2 (batch_result_words c rs ms)).
 rewrite -batch_period_result. apply: crt_batch_period_call; try assumption; reflexivity.
Qed.
Theorem system_batch_solve_execution mem hs rb mb c rs ms :
 system_input_memory mem rb mb rs ms -> batch_word32 c ->
 total_correct (system_run mem hs 8%num (be_args rb mb c))
 (fun r => r=solve_value (be_batch_result c rs ms) /\ (0<=c<=16 -> result_post (be_active c rs ms) (be_batch_result c rs ms))).
Proof.
 move=> Hmem Wc. apply: (system_run_total_correct (result:=solve_value (be_batch_result c rs ms))); first exact: (system_batch_solve_exec_exists hs Hmem Wc).
 split; first reflexivity. exact: batch_result_post.
Qed.
Theorem system_batch_period_execution mem hs rb mb c rs ms :
 system_input_memory mem rb mb rs ms -> batch_word32 c ->
 total_correct (system_run mem hs 9%num (be_args rb mb c))
 (fun p => p=period_value (be_batch_result c rs ms) /\ (0<=c<=16 -> result_post (be_active c rs ms) (be_batch_result c rs ms))).
Proof.
 move=> Hmem Wc. apply: (system_run_total_correct (result:=period_value (be_batch_result c rs ms))); first exact: (system_batch_period_exec_exists hs Hmem Wc).
 split; first reflexivity. exact: batch_result_post.
Qed.
Lemma system_batch_refines mem hs rb mb c rs ms :
 system_input_memory mem rb mb rs ms -> batch_word32 c -> be_refines mem hs rb mb c rs ms.
Proof.
 move=> Hmem Wc. split.
 - move=> r Hr. exact (proj1 (proj2 (proj2 (system_batch_solve_execution hs Hmem Wc) r Hr))).
 - move=> p Hp. exact (proj1 (proj2 (proj2 (system_batch_period_execution hs Hmem Wc) p Hp))).
Qed.
Theorem system_batch_permutation memA memB hsA hsB ptrRA ptrMA ptrRB ptrMB c rsA msA rsB msB rA pA rB pB :
 system_input_memory memA ptrRA ptrMA rsA msA -> batch_word32 c -> system_input_memory memB ptrRB ptrMB rsB msB -> batch_word32 c ->
 Permutation (be_active c rsA msA) (be_active c rsB msB) ->
 system_run memA hsA 8%num (be_args ptrRA ptrMA c) rA -> system_run memA hsA 9%num (be_args ptrRA ptrMA c) pA ->
 system_run memB hsB 8%num (be_args ptrRB ptrMB c) rB -> system_run memB hsB 9%num (be_args ptrRB ptrMB c) pB ->
 rA=rB /\ pA=pB.
Proof. move=> HA WA HB WB. exact: (be_execution_permutation (system_batch_refines hsA HA WA) (system_batch_refines hsB HB WB)). Qed.
Theorem system_batch_success_summary mem hs ptrR ptrM c rs ms r p :
 system_input_memory mem ptrR ptrM rs ms -> batch_word32 c ->
 system_run mem hs 8%num (be_args ptrR ptrM c) r -> system_run mem hs 9%num (be_args ptrR ptrM c) p ->
 0<=r -> 0<=c<=16 /\ valid (be_active c rs ms) /\ p<=MAX /\ Rep (be_active c rs ms) r p.
Proof. move=> HA WA. exact: (be_execution_success (system_batch_refines hs HA WA)). Qed.
Theorem system_batch_composition memA memB memM hsA hsB hsM ptrRA ptrMA ptrRB ptrMB ca cb rsA msA rsB msB r p s q :
 system_input_memory memA ptrRA ptrMA rsA msA -> batch_word32 ca -> system_input_memory memB ptrRB ptrMB rsB msB -> batch_word32 cb ->
 system_run memA hsA 8%num (be_args ptrRA ptrMA ca) r -> system_run memA hsA 9%num (be_args ptrRA ptrMA ca) p ->
 system_run memB hsB 8%num (be_args ptrRB ptrMB cb) s -> system_run memB hsB 9%num (be_args ptrRB ptrMB cb) q ->
 0<=r -> 0<=s ->
 total_correct (system_run memM hsM 5%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q])
 (fun x => x=solve_value (system_model (be_active ca rsA msA ++ be_active cb rsB msB)) /\
 result_post (be_active ca rsA msA ++ be_active cb rsB msB) (system_model (be_active ca rsA msA ++ be_active cb rsB msB))) /\
 total_correct (system_run memM hsM 6%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q])
 (fun x => x=period_value (system_model (be_active ca rsA msA ++ be_active cb rsB msB)) /\
 result_post (be_active ca rsA msA ++ be_active cb rsB msB) (system_model (be_active ca rsA msA ++ be_active cb rsB msB))).
Proof. move=> HA WA HB WB. exact: (be_execution_composition memM hsM (system_batch_refines hsA HA WA) (system_batch_refines hsB HB WB)). Qed.
Theorem system_batch_concat memA memB memC memM hsA hsB hsC hsM ptrRA ptrMA ptrRB ptrMB ptrRC ptrMC ca cb cc rsA msA rsB msB rsC msC r p s q xM pM xC pC :
 system_input_memory memA ptrRA ptrMA rsA msA -> batch_word32 ca -> system_input_memory memB ptrRB ptrMB rsB msB -> batch_word32 cb ->
 system_input_memory memC ptrRC ptrMC rsC msC -> batch_word32 cc -> 0<=cc<=16 ->
 Permutation (be_active ca rsA msA ++ be_active cb rsB msB) (be_active cc rsC msC) ->
 system_run memA hsA 8%num (be_args ptrRA ptrMA ca) r -> system_run memA hsA 9%num (be_args ptrRA ptrMA ca) p ->
 system_run memB hsB 8%num (be_args ptrRB ptrMB cb) s -> system_run memB hsB 9%num (be_args ptrRB ptrMB cb) q ->
 0<=r -> 0<=s ->
 system_run memM hsM 5%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q] xM ->
 system_run memM hsM 6%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q] pM ->
 system_run memC hsC 8%num (be_args ptrRC ptrMC cc) xC -> system_run memC hsC 9%num (be_args ptrRC ptrMC cc) pC ->
 xM=xC /\ pM=pC.
Proof. move=> HA WA HB WB HC WC. exact: (be_execution_concat (system_batch_refines hsA HA WA) (system_batch_refines hsB HB WB) (system_batch_refines hsC HC WC)). Qed.
End Host.
Print Assumptions system_batch_solve_execution.
Print Assumptions system_batch_period_execution.
