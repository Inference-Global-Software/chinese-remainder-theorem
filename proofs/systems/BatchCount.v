From Coq Require Import ZArith NArith Lia List Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRTWasm Require Import CRTPublicExecution.
From CRTSystems Require Import SystemRuntime FullWidthExecution SystemControl MergePeriodExecution.
From CRTSystems Require Import BatchArithmetic.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition batch_count_test := [::BI_local_get 2%num;BI_const_num (SM.Vi32 0);
 BI_relop T_i32 (Relop_i (ROI_lt SX_S));BI_if (BT_valtype (Some (T_num T_i32)))
 [::BI_const_num (SM.Vi32 1)] [::BI_local_get 2%num;BI_const_num (SM.Vi32 16);BI_relop T_i32 (Relop_i (ROI_gt SX_S))]].
Definition batch_count_prefix := batch_count_test ++
 [::BI_if (BT_valtype None) [::BI_const_num (SM.Vi64 (-2));BI_return] [::]].
Lemma batch_classifier_count_prefix : List.firstn 5 (modfunc_body SM.system_classify) = batch_count_prefix.
Proof. reflexivity. Qed.
Lemma batch_solve_count_prefix : List.firstn 5 (modfunc_body SM.crt_system_solve) = batch_count_prefix.
Proof. reflexivity. Qed.
Lemma batch_period_count_prefix : List.firstn 5 (modfunc_body SM.crt_system_period) = batch_count_prefix.
Proof. reflexivity. Qed.
Definition batch_loop_condition idx := [::BI_local_get idx;BI_local_get 2%num;
 BI_relop T_i32 (Relop_i (ROI_lt SX_S));BI_testop T_i32 TO_eqz].
Section Host.
Context `{ho:host}.
Lemma batch_count_sem G H c : batch_word32 c -> pinned 2%num (SM.Vi32 c) H ->
 sem_triple G (AS_base [::] H) batch_count_test
 (AS_base [::T_const (VAL_int32 (wasm_bool ((c <? 0) || (16 <? c))))] H).
Proof.
 move=> Wc Hc. have Wzero : batch_word32 0 by unfold batch_word32; lia.
 have Wsixteen : batch_word32 16 by unfold batch_word32; lia.
 rewrite /batch_count_test.
 apply: (sem_seq (es1:=[::BI_local_get 2%num;BI_const_num (SM.Vi32 0);BI_relop T_i32 (Relop_i (ROI_lt SX_S))])
 (Q:=AS_base [::T_const (VAL_int32 (wasm_bool (c <? 0)))] H)).
 - rewrite -(batch_i32_lt Wc Wzero). apply: test_pin_const; try reflexivity. exact Hc.
 - apply: crt_or_sem. rewrite -(batch_i32_gt Wc Wsixteen). apply: test_pin_const; try reflexivity. exact Hc.
Qed.
Lemma batch_count_valid G H c : 0 <= c <= 16 -> pinned 2%num (SM.Vi32 c) H ->
 sem_triple G (AS_base [::] H) batch_count_prefix (AS_base [::] H).
Proof.
 move=> Hc Hpin. have Wc : batch_word32 c by unfold batch_word32; lia.
 have Ec : ((c <? 0) || (16 <? c)) = false by rewrite orb_false_iff !Z.ltb_ge; lia.
 rewrite /batch_count_prefix.
 apply: (sem_seq (Q:=AS_base [::T_const (VAL_int32 (wasm_bool false))] H)).
 - rewrite -Ec. exact: batch_count_sem.
 - apply: guard_if_false. exact: sem_nil_same.
Qed.
Lemma batch_count_invalid G H c tail Qn Qb : batch_word32 c -> (c < 0 \/ 16 < c) ->
 pinned 2%num (SM.Vi32 c) H ->
 sem_mx G (AS_base [::] H) (batch_count_prefix ++ tail) Qn
 (AS_base [::T_const (SM.Vi64 (-2))] HA_true) Qb.
Proof.
 move=> Wc Hbad Hpin. have Ec : ((c <? 0) || (16 <? c)) = true.
 { rewrite orb_true_iff !Z.ltb_lt. exact Hbad. }
 rewrite /batch_count_prefix -catA.
 apply: (sem_mx_seq (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] H)).
 - apply: sem_mx_lift. rewrite -Ec. exact: batch_count_sem.
 - apply: (sem_mx_seq (Q1:=AS_base [::] HA_false)).
   + apply: crt_if_true_returns. exact: p_const_return.
   + apply: sem_mx_lift. exact: sem_false.
Qed.
Lemma batch_loop_condition_sem G H idx i count : batch_word32 i -> batch_word32 count ->
 pinned idx (SM.Vi32 i) H -> pinned 2%num (SM.Vi32 count) H ->
 sem_triple G (AS_base [::] H) (batch_loop_condition idx)
 (AS_base [::T_const (VAL_int32 (wasm_bool (negb (i <? count))))] H).
Proof.
 move=> Wi Wcount Pi Pcount. rewrite /batch_loop_condition.
 apply: (sem_seq (es1:=[::BI_local_get idx;BI_local_get 2%num;BI_relop T_i32 (Relop_i (ROI_lt SX_S))])
 (Q:=AS_base [::T_const (VAL_int32 (wasm_bool (i <? count)))] H)).
 - apply: (sem_seq (es1:=[::BI_local_get idx]) (Q:=AS_base [::T_const (SM.Vi32 i)] H)); first exact: get_pinned_frame.
   apply: (sem_seq (es1:=[::BI_local_get 2%num]) (Q:=AS_base [::T_const (SM.Vi32 i);T_const (SM.Vi32 count)] H)); first exact: get_pinned_frame.
   rewrite -(batch_i32_lt Wi Wcount). apply: relop_consts; reflexivity.
 - exact: crt_eqz_bool_sem.
Qed.
End Host.
