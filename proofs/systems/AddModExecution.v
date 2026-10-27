From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit
 NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTSystemStatements CRTSystemArithmetic.
From CRTWasm Require Import CRTGeneralArithmetic CRTContracts.
From CRTSystems Require Import FullWidthExecution.
From CRTSystemGenerated Require Import main.
Module SM := CRTSystemGenerated.main.
Import FullWidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Section Host.
Context `{ho : host}.
Ltac pinned_tac := solve [exact: pinned_bare | apply: pinned_left; pinned_tac | apply: pinned_right; pinned_tac].
Ltac present_tac := solve [exact: loc_present_defined | exact: loc_present_pin | apply: loc_present_left; present_tac | apply: loc_present_right; present_tac].
Lemma add_stable_true i c : loc_stable i c HA_true. Proof. by []. Qed.
Ltac stable_tac := solve [exact: add_stable_true | exact: loc_stable_defined_self | exact: loc_stable_pin_self | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other | apply: loc_stable_and; stable_tac].
Lemma add_checked_sub_Z G H x y :
  loc_stable 3%num (SM.Vi64 x) H -> loc_stable 4%num (SM.Vi64 y) H ->
  loc_stable 5%num (SM.Vi64 (x - y)) H ->
  loc_present 3%num H -> loc_present 4%num H -> loc_present 5%num H ->
  word x -> word y -> word (x - y) ->
  sem_triple G (AS_base [:: T_const (SM.Vi64 x); T_const (SM.Vi64 y)] H)
    (crt_general_checked_sub_code 3%num 4%num 5%num) (AS_base [:: T_const (SM.Vi64 (x - y))] H).
Proof.
  move=> SA SB SR PA PB PR Wx Wy Wxy.
  have E := crt_i64_sub_repr Wx Wy.
  have Range : Wasm_int.Int64.min_signed <=
    Wasm_int.Int64.signed (Wasm_int.Int64.repr x) -
    Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy)
      i64_min_signed_val i64_max_signed_val. exact Wxy. }
  have SR' : loc_stable 5%num (VAL_int64
    (Wasm_int.Int64.sub (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y))) H.
  { rewrite E. exact SR. }
  have P := crt_general_checked_sub_sem (ia := 3%num) (ib := 4%num) (ir := 5%num) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) SA SB SR' PA PB PR Range.
  rewrite E in P. exact: P.
Qed.

Lemma add_checked_add_Z G H x y :
  loc_stable 3%num (SM.Vi64 x) H -> loc_stable 4%num (SM.Vi64 y) H ->
  loc_stable 5%num (SM.Vi64 (x + y)) H ->
  loc_present 3%num H -> loc_present 4%num H -> loc_present 5%num H ->
  word x -> word y -> word (x + y) ->
  sem_triple G (AS_base [:: T_const (SM.Vi64 x); T_const (SM.Vi64 y)] H)
    (crt_general_checked_add_code 3%num 4%num 5%num) (AS_base [:: T_const (SM.Vi64 (x + y))] H).
Proof.
  move=> SA SB SR PA PB PR Wx Wy Wxy.
  have E := crt_i64_add_repr Wx Wy.
  have Range : Wasm_int.Int64.min_signed <=
    Wasm_int.Int64.signed (Wasm_int.Int64.repr x) +
    Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy)
      i64_min_signed_val i64_max_signed_val. exact Wxy. }
  have SR' : loc_stable 5%num (VAL_int64
    (Wasm_int.Int64.add (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y))) H.
  { rewrite E. exact SR. }
  have P := crt_general_checked_add_sem (ia := 3%num) (ib := 4%num) (ir := 5%num) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) SA SB SR' PA PB PR Range.
  rewrite E in P. exact: P.
Qed.


Definition AddEntry x y d :=
 HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 x)))
 (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 y)))
 (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 d)))
 (HA_and (HA_defined (T_local 3%num))
 (HA_and (HA_defined (T_local 4%num))
 (HA_and (HA_defined (T_local 5%num)) HA_true))))).
Definition diff_code := [:: BI_local_get 2%num; BI_local_get 1%num] ++
 crt_general_checked_sub_code 3%num 4%num 5%num.
Definition pair_code := [:: BI_local_get 0%num] ++ diff_code.
Definition add_condition_code := pair_code ++ [::BI_relop T_i64 (Relop_i (ROI_ge SX_S))].
Definition add_then_code := pair_code ++
 crt_general_checked_sub_code 3%num 4%num 5%num ++ [:: BI_return].
Definition add_else_code := [::BI_local_get 0%num; BI_local_get 1%num] ++
 crt_general_checked_add_code 3%num 4%num 5%num ++ [::BI_return; BI_unreachable].
Lemma add_body_shape : modfunc_body SM.add_mod =
 add_condition_code ++ [::BI_if (BT_valtype None) add_then_code [::]] ++ add_else_code.
Proof. reflexivity. Qed.

Lemma diff_sem x y d : word d -> word y -> word (d-y) ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (AddEntry x y d))
 diff_code (AS_base [::T_const (SM.Vi64 (d-y))] (AddEntry x y d)).
Proof.
 move=> Wd Wy Wdy. rewrite /diff_code.
 apply: (sem_seq (es1 := [::BI_local_get 2%num;BI_local_get 1%num])
  (Q := AS_base [::T_const (SM.Vi64 d);T_const (SM.Vi64 y)] (AddEntry x y d))).
 - apply: (sem_seq (es1 := [::BI_local_get 2%num])
    (Q := AS_base [::T_const (SM.Vi64 d)] (AddEntry x y d)));
   apply: get_pinned_frame; rewrite /AddEntry; pinned_tac.
 - apply: add_checked_sub_Z; try assumption; rewrite /AddEntry; first [stable_tac|present_tac].
Qed.
Lemma pair_sem x y d : word d -> word y -> word (d-y) ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (AddEntry x y d))
 pair_code (AS_base [::T_const (SM.Vi64 x); T_const (SM.Vi64 (d-y))] (AddEntry x y d)).
Proof.
 move=> Wd Wy Wdy. rewrite /pair_code.
 apply: (sem_seq (es1 := [::BI_local_get 0%num])
  (Q := AS_base [::T_const (SM.Vi64 x)] (AddEntry x y d))).
 - apply: get_pinned_frame. rewrite /AddEntry; pinned_tac.
 - apply: (sem_frame_consts (vf := [::SM.Vi64 x])). exact: diff_sem.
Qed.
Lemma add_condition_sem x y d : word x -> word d -> word y -> word (d-y) ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (AddEntry x y d))
 add_condition_code
 (AS_base [::T_const (VAL_int32 (wasm_bool (d-y <=? x)))] (AddEntry x y d)).
Proof.
 move=> Wx Wd Wy Wdy. rewrite /add_condition_code.
 apply: (sem_seq (es1:=pair_code)
  (Q:=AS_base [::T_const (SM.Vi64 x);T_const (SM.Vi64 (d-y))] (AddEntry x y d))).
 - exact: pair_sem.
 - have E : app_relop (Relop_i (ROI_ge SX_S)) (SM.Vi64 x) (SM.Vi64 (d-y)) = (d-y <=? x).
   { rewrite /SM.Vi64 crt_contract_ge (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wdy). reflexivity. }
   rewrite -E. apply: relop_consts; reflexivity.
Qed.
Lemma add_then_sem x y d Qn Qb : word x -> word y -> word d ->
 word (d-y) -> word (x-(d-y)) ->
 sem_mx (triv_ctx SM.main) (AS_base [::] (AddEntry x y d)) add_then_code
 Qn (AS_base [::T_const (SM.Vi64 (x-(d-y)))] HA_true) Qb.
Proof.
 move=> Wx Wy Wd Wdy Wr. rewrite /add_then_code.
 apply: (sem_mx_seq (es1:=pair_code)
  (Q1:=AS_base [::T_const (SM.Vi64 x);T_const (SM.Vi64 (d-y))] (AddEntry x y d))).
 - apply: sem_mx_lift. exact: pair_sem.
 - apply: (sem_mx_seq (es1:=crt_general_checked_sub_code 3%num 4%num 5%num)
    (Q1:=AS_base [::T_const (SM.Vi64 (x-(d-y)))] HA_true)).
   + apply: sem_mx_lift. apply: (sem_conseq
      (P':=AS_base [::T_const (SM.Vi64 x);T_const (SM.Vi64 (d-y))] (AddEntry x y d))
      (Q':=AS_base [::T_const (SM.Vi64 (x-(d-y)))] (AddEntry x y d))).
     * by [].
     * move=> V [vs h] [Hs _]. by split.
     * apply: add_checked_sub_Z; try assumption; rewrite /AddEntry; first [stable_tac|present_tac].
   + exact: sem_mx_return_suffix.
Qed.
Lemma add_else_sem x y d Qn Qb : word x -> word y -> word (x+y) ->
 sem_mx (triv_ctx SM.main) (AS_base [::] (AddEntry x y d)) add_else_code
 Qn (AS_base [::T_const (SM.Vi64 (x+y))] HA_true) Qb.
Proof.
 move=> Wx Wy Wr. rewrite /add_else_code.
 apply: (sem_mx_seq (es1:=[::BI_local_get 0%num;BI_local_get 1%num])
  (Q1:=AS_base [::T_const (SM.Vi64 x);T_const (SM.Vi64 y)] (AddEntry x y d))).
 - apply: sem_mx_lift. apply: (sem_seq (es1:=[::BI_local_get 0%num])
    (Q:=AS_base [::T_const (SM.Vi64 x)] (AddEntry x y d)));
   apply: get_pinned_frame; rewrite /AddEntry; pinned_tac.
 - apply: (sem_mx_seq (es1:=crt_general_checked_add_code 3%num 4%num 5%num)
    (Q1:=AS_base [::T_const (SM.Vi64 (x+y))] HA_true)).
   + apply: sem_mx_lift. apply: (sem_conseq
      (P':=AS_base [::T_const (SM.Vi64 x);T_const (SM.Vi64 y)] (AddEntry x y d))
      (Q':=AS_base [::T_const (SM.Vi64 (x+y))] (AddEntry x y d))).
     * by [].
     * move=> V [vs h] [Hs _]. by split.
     * apply: add_checked_add_Z; try assumption; rewrite /AddEntry; first [stable_tac|present_tac].
   + exact: sem_mx_return_suffix.
Qed.
Theorem add_mod_machine_computes x y d :
 1 <= d <= MAX -> 0 <= x < d -> 0 <= y < d ->
 fun_computes SM.main 3%nat [::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d]
 [::SM.Vi64 (FullWidth.add_mod x y d)].
Proof.
 move=> Hd Hx Hy.
 have Wx : word x by unfold word, MAX, i64_min, i64_max in *; lia.
 have Wy : word y by unfold word, MAX, i64_min, i64_max in *; lia.
 have Wd := crt_modulus_word Hd.
 have [Eadd [Hrange [Wdy [Wr Hsum]]]] := add_mod_proved x y d Hd Hx Hy.
 rewrite /FullWidth.add_mod in Wr *.
 prepare_fun_computes
  (AS_base [::] (AddEntry x y d))
  (AS_base [::T_const (SM.Vi64 (if d-y <=? x then x-(d-y) else x+y))] HA_true).
 - move=> V [vs h] /= [Hs [[P0 [P1 [P2 _]]] [[T0 [T1 [T2 _]]] [T3 [T4 [T5 _]]]]]].
   split; first exact Hs. repeat split; try assumption.
   + by case: T3 => [w [Ew _]]; exists w.
   + by case: T4 => [w [Ew _]]; exists w.
   + by case: T5 => [w [Ew _]]; exists w.
 - rewrite add_body_shape.
   apply: (sem_mx_seq (es1:=add_condition_code)
    (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool (d-y <=? x)))] (AddEntry x y d))).
   + apply: sem_mx_lift. exact: add_condition_sem.
   + case E: (d-y <=? x) in Wr *.
     * apply: (sem_mx_seq (es1:=[::BI_if (BT_valtype None) add_then_code [::]])
        (Q1:=AS_base [::] HA_false)).
       -- apply: crt_if_true_returns. exact: add_then_sem.
       -- apply: sem_mx_lift. exact: sem_false.
     * apply: (sem_mx_seq (es1:=[::BI_if (BT_valtype None) add_then_code [::]])
        (Q1:=AS_base [::] (AddEntry x y d))).
       -- apply: sem_mx_lift. apply: guard_if_false. exact: sem_nil_same.
       -- exact: add_else_sem.
Qed.
End Host.
Print Assumptions add_mod_machine_computes.
