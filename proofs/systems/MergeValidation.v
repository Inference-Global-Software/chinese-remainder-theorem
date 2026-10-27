(* Shared full-width validation for the two exact scalar exports. *)
From Coq Require Import ZArith NArith Lia List Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTSystemStatements CRTSystemArithmetic.
From CRTWasm Require Import CRTContracts CRTPublicExecution CRTSolveExecution.
From CRTSystems Require Import FullWidthExecution.
Module SM := CRTSystemGenerated.main.
Import FullWidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition merge_bad a m b n := (m <? 1) || (n <? 1) || (a <? 0) || (m <=? a) || (b <? 0) || (n <=? b).
Definition merge_validation := List.firstn 8 (modfunc_body SM.crt_merge_solve).
Lemma merge_period_validation_same : List.firstn 8 (modfunc_body SM.crt_merge_period) = merge_validation.
Proof. reflexivity. Qed.
Lemma merge_bad_false_domain a m b n : word a -> word m -> word b -> word n ->
 merge_bad a m b n = false <-> FullWidth.domain a m b n.
Proof.
 move=> Wa Wm Wb Wn. rewrite /merge_bad !Bool.orb_false_iff !Z.ltb_ge !Z.leb_gt.
 unfold FullWidth.domain,FullWidth.moduli,word,MAX in *. tauto || lia.
Qed.
Lemma merge_bad_model a m b n : word a -> word m -> word b -> word n ->
 merge_bad a m b n = negb (FiniteSystem.validb (a,m) && FiniteSystem.validb (b,n)).
Proof.
 move=> Wa Wm Wb Wn.
 have Hlt : forall x y, (x <? y) = negb (y <=? x).
 { move=> x y. case E: (x <? y); case F: (y <=? x); try reflexivity;
   [apply Z.ltb_lt in E; apply Z.leb_le in F | apply Z.ltb_ge in E; apply Z.leb_gt in F]; lia. }
 have Hm : (m <=? MAX) = true by apply/Z.leb_le; exact (proj2 Wm).
 have Hn : (n <=? MAX) = true by apply/Z.leb_le; exact (proj2 Wn).
 rewrite /merge_bad /FiniteSystem.validb /= Hm Hn !Hlt.
 by case: (1 <=? m); case: (1 <=? n); case: (0 <=? a); case: (m <=? a); case: (0 <=? b); case: (n <=? b).
Qed.
Section Host.
Context `{ho : host}.
Lemma merge_validation_sem G H a m b n :
 pinned 0%num (SM.Vi64 a) H -> pinned 1%num (SM.Vi64 m) H ->
 pinned 2%num (SM.Vi64 b) H -> pinned 3%num (SM.Vi64 n) H ->
 word a -> word m -> word b -> word n ->
 sem_triple G (AS_base [::] H) merge_validation
 (AS_base [::T_const (VAL_int32 (wasm_bool (merge_bad a m b n)))] H).
Proof.
 move=> Pa Pm Pb Pn Wa Wm Wb Wn.
 have Wzero : word 0 by unfold word,i64_min,i64_max; lia.
 have Wone : word 1 by unfold word,i64_min,i64_max; lia.
 rewrite /merge_validation /SM.crt_merge_solve /merge_bad /=.
 apply: (sem_seq (es1:=[::BI_local_get 1%num;BI_const_num (SM.Vi64 1);BI_relop T_i64 (Relop_i (ROI_lt SX_S))]) (Q:=AS_base [::T_const (VAL_int32 (wasm_bool ((m <? 1))))] H)).
 { rewrite -(crt_public_lt Wm Wone). apply: test_pin_const; try assumption; reflexivity. }
 apply: (sem_seq (es1:=[::BI_if (BT_valtype (Some (T_num T_i32))) [::BI_const_num (SM.Vi32 1)] [::BI_local_get 3%num;BI_const_num (SM.Vi64 1);BI_relop T_i64 (Relop_i (ROI_lt SX_S))]]) (Q:=AS_base [::T_const (VAL_int32 (wasm_bool ((m <? 1) || (n <? 1))))] H)).
 { apply: crt_or_sem. rewrite -(crt_public_lt Wn Wone). apply: test_pin_const; try assumption; reflexivity. }
 apply: (sem_seq (es1:=[::BI_if (BT_valtype (Some (T_num T_i32))) [::BI_const_num (SM.Vi32 1)] [::BI_local_get 0%num;BI_const_num (SM.Vi64 0);BI_relop T_i64 (Relop_i (ROI_lt SX_S))]]) (Q:=AS_base [::T_const (VAL_int32 (wasm_bool ((m <? 1) || (n <? 1) || (a <? 0))))] H)).
 { apply: crt_or_sem. rewrite -(crt_public_lt Wa Wzero). apply: test_pin_const; try assumption; reflexivity. }
 apply: (sem_seq (es1:=[::BI_if (BT_valtype (Some (T_num T_i32))) [::BI_const_num (SM.Vi32 1)] [::BI_local_get 0%num;BI_local_get 1%num;BI_relop T_i64 (Relop_i (ROI_ge SX_S))]]) (Q:=AS_base [::T_const (VAL_int32 (wasm_bool ((m <? 1) || (n <? 1) || (a <? 0) || (m <=? a))))] H)).
 { apply: crt_or_sem. rewrite -(solver_public_ge Wa Wm). apply: solver_two_pin_test; try assumption; reflexivity. }
 apply: (sem_seq (es1:=[::BI_if (BT_valtype (Some (T_num T_i32))) [::BI_const_num (SM.Vi32 1)] [::BI_local_get 2%num;BI_const_num (SM.Vi64 0);BI_relop T_i64 (Relop_i (ROI_lt SX_S))]]) (Q:=AS_base [::T_const (VAL_int32 (wasm_bool ((m <? 1) || (n <? 1) || (a <? 0) || (m <=? a) || (b <? 0))))] H)).
 { apply: crt_or_sem. rewrite -(crt_public_lt Wb Wzero). apply: test_pin_const; try assumption; reflexivity. }
 apply: crt_or_sem. rewrite -(solver_public_ge Wb Wn). apply: solver_two_pin_test; try assumption; reflexivity.
Qed.
End Host.
Print Assumptions merge_validation_sem.
