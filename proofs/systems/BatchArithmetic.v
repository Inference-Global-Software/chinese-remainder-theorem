From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRTSystemGenerated Require main.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition batch_word32 z := -2147483648 <= z <= 2147483647.
Lemma batch_i32_signed_repr z : batch_word32 z -> Wasm_int.Int32.signed (Wasm_int.Int32.repr z) = z.
Proof. move=> Hz. apply: Wasm_int.Int32.signed_repr. rewrite i32_min_signed_val i32_max_signed_val. exact Hz. Qed.
Lemma batch_i32_add_repr x y : batch_word32 x -> batch_word32 y ->
 Wasm_int.Int32.add (Wasm_int.Int32.repr x) (Wasm_int.Int32.repr y) = Wasm_int.Int32.repr (x+y).
Proof. move=> Hx Hy. by rewrite Wasm_int.Int32.add_signed (batch_i32_signed_repr Hx) (batch_i32_signed_repr Hy). Qed.
Lemma batch_i32_lt x y : batch_word32 x -> batch_word32 y ->
 app_relop (Relop_i (ROI_lt SX_S)) (SM.Vi32 x) (SM.Vi32 y) = (x <? y).
Proof.
 move=> Hx Hy. rewrite i32_lt_s_app /Wasm_int.Int32.lt (batch_i32_signed_repr Hx) (batch_i32_signed_repr Hy).
 case: Coqlib.zlt => Hxy; symmetry; [apply/Z.ltb_lt|apply/Z.ltb_ge]; lia.
Qed.
Lemma batch_i32_gt x y : batch_word32 x -> batch_word32 y ->
 app_relop (Relop_i (ROI_gt SX_S)) (SM.Vi32 x) (SM.Vi32 y) = (y <? x).
Proof. move=> Hx Hy. exact: batch_i32_lt. Qed.
Section Host.
Context `{ho:host}.
Context (ia ib ir:N).
Context (IndexAB:ib<>ia) (IndexAR:ia<>ir) (IndexBR:ib<>ir).
Ltac pinned_tac :=
  solve [ exact: pinned_bare | apply: pinned_left; pinned_tac
        | apply: pinned_right; pinned_tac ].
Ltac present_tac :=
  solve [ exact: loc_present_defined | exact: loc_present_pin
        | apply: loc_present_left; present_tac
        | apply: loc_present_right; present_tac ].
Local Notation ArithB H cb :=
  (HA_and (term_eq (T_local ib) (T_const (VAL_int32 cb))) H).
Local Notation ArithA H ca cb :=
  (HA_and (term_eq (T_local ia) (T_const (VAL_int32 ca))) (ArithB H cb)).
Local Notation ArithR H ca cb cr :=
  (HA_and (term_eq (T_local ir) (T_const (VAL_int32 cr))) (ArithA H ca cb)).

Definition batch_checked_add_code : seq basic_instruction :=
  [:: BI_local_set ib; BI_local_tee ia; BI_local_get ib;
      BI_binop T_i32 (Binop_i BOI_add); BI_local_tee ir;
      BI_local_get ia; BI_relop T_i32 (Relop_i (ROI_lt SX_S));
      BI_local_get ib; BI_const_num (Issue316OverflowExample.Vi32 0);
      BI_relop T_i32 (Relop_i (ROI_lt SX_S)); BI_relop T_i32 (Relop_i ROI_ne);
      BI_if (BT_valtype None) [:: BI_unreachable] [::]; BI_local_get ir].
Lemma batch_checked_add_sem G H (ca cb : i32) :
  loc_stable ia (VAL_int32 ca) H ->
  loc_stable ib (VAL_int32 cb) H ->
  loc_stable ir (VAL_int32 (Wasm_int.Int32.add ca cb)) H ->
  loc_present ia H -> loc_present ib H -> loc_present ir H ->
  (Wasm_int.Int32.min_signed <=
     Wasm_int.Int32.signed ca + Wasm_int.Int32.signed cb <=
     Wasm_int.Int32.max_signed)%Z ->
  sem_triple G (AS_base [:: T_const (VAL_int32 ca); T_const (VAL_int32 cb)] H)
    batch_checked_add_code
    (AS_base [:: T_const (VAL_int32 (Wasm_int.Int32.add ca cb))] H).
Proof.
  move=> StA StB StR PrA PrB PrR Hrange.
  rewrite /batch_checked_add_code.
  apply: (sem_seq (es1 := [:: BI_local_set ib])
    (Q := AS_base [:: T_const (VAL_int32 ca)] (ArithB H cb))).
  { apply: (sem_frame_consts (vf := [:: VAL_int32 ca])).
    exact: (sem_local_set_const_frame StB PrB). }
  apply: (sem_seq (es1 := [:: BI_local_tee ia])
    (Q := AS_base [:: T_const (VAL_int32 ca)] (ArithA H ca cb))).
  { apply: sem_local_tee_const_frame.
    - apply: loc_stable_and; [by apply: loc_stable_pin_other | exact StA].
    - apply: loc_present_right. exact PrA. }
  apply: (sem_seq (es1 := [:: BI_local_get ib])
    (Q := AS_base [:: T_const (VAL_int32 ca); T_const (VAL_int32 cb)] (ArithA H ca cb))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_binop T_i32 (Binop_i BOI_add)])
    (Q := AS_base [:: T_const (VAL_int32 (Wasm_int.Int32.add ca cb))] (ArithA H ca cb))).
  { apply: binop_consts; [by vm_compute | by [] | by [] | exact: i32_add_some]. }
  apply: (sem_seq (es1 := [:: BI_local_tee ir])
    (Q := AS_base [:: T_const (VAL_int32 (Wasm_int.Int32.add ca cb))]
      (ArithR H ca cb (Wasm_int.Int32.add ca cb)))).
  { apply: sem_local_tee_const_frame.
    - apply: loc_stable_and; first by apply: loc_stable_pin_other.
      apply: loc_stable_and; first by apply: loc_stable_pin_other. exact StR.
    - apply: loc_present_right. apply: loc_present_right. exact PrR. }
  apply: (sem_seq (es1 := [:: BI_local_get ia])
    (Q := AS_base [:: T_const (VAL_int32 (Wasm_int.Int32.add ca cb)); T_const (VAL_int32 ca)] (ArithR H ca cb (Wasm_int.Int32.add ca cb)))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_relop T_i32 (Relop_i (ROI_lt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int32 (Wasm_int.Int32.add ca cb)) (VAL_int32 ca))))] (ArithR H ca cb (Wasm_int.Int32.add ca cb)))).
  { apply: relop_consts; by []. }
  apply: (sem_seq (es1 := [:: BI_local_get ib])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int32 (Wasm_int.Int32.add ca cb)) (VAL_int32 ca)))); T_const (VAL_int32 cb)] (ArithR H ca cb (Wasm_int.Int32.add ca cb)))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_const_num (Issue316OverflowExample.Vi32 0)])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int32 (Wasm_int.Int32.add ca cb)) (VAL_int32 ca)))); T_const (VAL_int32 cb); T_const (Issue316OverflowExample.Vi32 0)] (ArithR H ca cb (Wasm_int.Int32.add ca cb)))).
  { exact: sem_const_framed. }
  apply: (sem_seq (es1 := [:: BI_relop T_i32 (Relop_i (ROI_lt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int32 (Wasm_int.Int32.add ca cb)) (VAL_int32 ca)))); T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int32 cb) (Issue316OverflowExample.Vi32 0))))] (ArithR H ca cb (Wasm_int.Int32.add ca cb)))).
  { apply: (sem_frame_consts (vf := [:: VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int32 (Wasm_int.Int32.add ca cb)) (VAL_int32 ca)))])). apply: relop_consts; by []. }
  apply: (sem_seq (es1 := [:: BI_relop T_i32 (Relop_i ROI_ne)])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i ROI_ne) (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int32 (Wasm_int.Int32.add ca cb)) (VAL_int32 ca)))) (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int32 cb) (Issue316OverflowExample.Vi32 0)))))))] (ArithR H ca cb (Wasm_int.Int32.add ca cb)))).
  { apply: relop_consts; by []. }
  have Hguard := i32_add_signed_guard_false Hrange.
  rewrite Hguard.
  apply: (sem_seq (es1 := [:: BI_if (BT_valtype None) [:: BI_unreachable] [::]])
    (Q := AS_base [::] (ArithR H ca cb (Wasm_int.Int32.add ca cb)))).
  { apply: guard_if_false. exact: sem_nil_same. }
  apply: (sem_conseq
    (P' := AS_base [::] (ArithR H ca cb (Wasm_int.Int32.add ca cb)))
    (Q' := AS_base [:: T_const (VAL_int32 (Wasm_int.Int32.add ca cb))]
      (ArithR H ca cb (Wasm_int.Int32.add ca cb)))).
  - by [].
  - move=> V [vs h] [Hs [_ [_ [_ HH]]]]. by split.
  - apply: get_pinned_frame. pinned_tac.
Qed.
Lemma batch_checked_add_Z G H x y :
 loc_stable ia (SM.Vi32 x) H -> loc_stable ib (SM.Vi32 y) H ->
 loc_stable ir (SM.Vi32 (x+y)) H -> loc_present ia H -> loc_present ib H -> loc_present ir H ->
 batch_word32 x -> batch_word32 y -> batch_word32 (x+y) ->
 sem_triple G (AS_base [::T_const (SM.Vi32 x);T_const (SM.Vi32 y)] H)
 batch_checked_add_code (AS_base [::T_const (SM.Vi32 (x+y))] H).
Proof.
 move=> SA SB SR PA PB PR Wx Wy Wxy. have E := batch_i32_add_repr Wx Wy.
 have Hr : Wasm_int.Int32.min_signed <= Wasm_int.Int32.signed (Wasm_int.Int32.repr x) +
 Wasm_int.Int32.signed (Wasm_int.Int32.repr y) <= Wasm_int.Int32.max_signed.
 { rewrite (batch_i32_signed_repr Wx) (batch_i32_signed_repr Wy) i32_min_signed_val i32_max_signed_val. exact Wxy. }
 have SR' : loc_stable ir (VAL_int32 (Wasm_int.Int32.add (Wasm_int.Int32.repr x) (Wasm_int.Int32.repr y))) H by rewrite E.
 have Hsem := batch_checked_add_sem SA SB SR' PA PB PR Hr.
 by rewrite E in Hsem.
Qed.
End Host.
