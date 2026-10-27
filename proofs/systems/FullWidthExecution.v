(* Proofs over the exact compiler-emitted definitions in systems/out/main.v.
   The generated skeleton theorems are never used by these endpoints. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit
  NumericDischarge Automation Activation Verifier MultiExitK Loop.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTLoops CRTSystemStatements CRTSystemArithmetic.
From CRTWasm Require Import CRTLoopRules.
From CRTSystemGenerated Require Import main.
Module SM := CRTSystemGenerated.main.
Import FullWidth.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.

Theorem gcd_run_terminates : forall m n a b,
  gcd_inv m n a b ->
  exists result, gcd_run a b result /\ result = Z.gcd m n /\ word result.
Proof.
  intros m n a b.
  remember (Z.to_nat b) as k eqn:Hk.
  revert a b Hk.
  induction k as [k IH] using lt_wf_ind.
  intros a b Hk Hinv.
  destruct (Z.eq_dec b 0) as [Hzero | Hnonzero].
  - subst b. exists a. split. constructor.
    split. apply (gcd_exit_proved m n a Hinv).
    destruct Hinv as (Ha & _). unfold word, MAX, i64_min, i64_max in *. lia.
  - assert (Hpos : 0 < b) by (destruct Hinv as (_ & Hb & _); lia).
    destruct (gcd_step_proved m n a b Hinv Hpos) as (Hnext & Hmod & Hless).
    destruct (IH (Z.to_nat (a mod b)) ltac:(lia) b (a mod b) Logic.eq_refl Hnext)
      as (result & Hrun & Hresult & Hword).
    exists result. repeat first [assumption | split].
    apply gcd_run_next; assumption.
Qed.

Theorem gcd_initial_run_correct : forall m n, moduli m n ->
  exists result, gcd_run m n result /\ result = Z.gcd m n /\ word result.
Proof.
  intros m n Hin. apply gcd_run_terminates. apply gcd_init_proved. exact Hin.
Qed.


Lemma crt_i64_signed_repr z : word z ->
  Wasm_int.Int64.signed (Wasm_int.Int64.repr z) = z.
Proof.
  move=> Hz. apply: Wasm_int.Int64.signed_repr.
  rewrite i64_min_signed_val i64_max_signed_val.
  exact Hz.
Qed.

Lemma crt_modulus_word d : 1 <= d <= MAX -> word d.
Proof. unfold word, MAX, i64_min, i64_max. lia. Qed.

Lemma crt_rem_word z d : word z -> 1 <= d <= MAX -> word (Z.rem z d).
Proof. move=> Hz Hd. exact (proj1 (proj2 (proj2 (normalize_proved z d Hz Hd)))). Qed.

(* WasmCert expresses rem_s using a floor remainder and a sign correction.
   This bridge proves that its value is exactly Coq's truncating remainder. *)
Lemma crt_i64_rem_exact z d : word z -> 1 <= d <= MAX ->
  app_binop (Binop_i (BOI_rem SX_S)) (SM.Vi64 z) (SM.Vi64 d) =
  Some (SM.Vi64 (Z.rem z d)).
Proof.
  move=> Hz Hd.
  have Hdw := crt_modulus_word Hd.
  have Hdpos : 0 < d by lia.
  have Hmod := Z.mod_pos_bound z d Hdpos.
  have Hnorm := proj1 (normalize_proved z d Hz Hd).
  have Hdz : (d == 0) = false.
  { case E: (d == 0); last by [].
    have Hd0 : d = 0 by apply/eqP.
    lia. }
  have Hmodsign : (z mod d >=? 0) = true by apply/Z.geb_le; lia.
  rewrite /SM.Vi64 /app_binop /app_binop_i /= /Wasm_int.Int64.irem_s /=.
  rewrite (crt_i64_signed_repr Hz) (crt_i64_signed_repr Hdw) Hdz.
  case Hmz: (z mod d == 0).
  - have Hmzero : z mod d = 0 by apply/eqP.
    have Hrzero : Z.rem z d = 0.
    { apply (proj2 (Z.rem_mod_eq_0 z d ltac:(lia))). exact Hmzero. }
    by rewrite Hmzero Hrzero.
  - rewrite Hmodsign.
    case Hzsign: (z >=? 0).
    + have Hzpos : 0 <= z by apply/Z.geb_le.
      by rewrite (Z.rem_mod_nonneg z d Hzpos Hdpos).
    + have Hzneg : z < 0.
      { apply Z.nle_gt. move=> Hzpos.
        have Htrue : (z >=? 0) = true by apply/Z.geb_le.
        congruence. }
      have Hrnonpos := Z.rem_nonpos z d ltac:(lia) ltac:(lia).
      have Hrnonzero : Z.rem z d <> 0.
      { move=> Hrzero. have Hmzero := proj1 (Z.rem_mod_eq_0 z d ltac:(lia)) Hrzero.
        move: Hmz. by rewrite Hmzero eqxx. }
      have Hrneg : (Z.rem z d <? 0) = true by apply/Z.ltb_lt; lia.
      rewrite Hrneg in Hnorm.
      have -> : z mod d - d = Z.rem z d by lia.
      by [].
Qed.

Lemma crt_i64_lt_zero z : word z ->
  app_relop (Relop_i (ROI_lt SX_S)) (SM.Vi64 z) (SM.Vi64 0) = (z <? 0).
Proof.
  move=> Hz. rewrite i64_lt_s_app /Wasm_int.Int64.lt.
  have Hzero : word 0 by unfold word, i64_min, i64_max; lia.
  rewrite (crt_i64_signed_repr Hz) (crt_i64_signed_repr Hzero).
  case: Coqlib.zlt => H; [symmetry; apply/Z.ltb_lt | symmetry; apply/Z.ltb_ge]; lia.
Qed.

Lemma crt_i64_add_repr x y : word x -> word y ->
  Wasm_int.Int64.add (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y) =
    Wasm_int.Int64.repr (x + y).
Proof.
  move=> Hx Hy. by rewrite Wasm_int.Int64.add_signed
    (crt_i64_signed_repr Hx) (crt_i64_signed_repr Hy).
Qed.

Section Host.
Context `{ho : host}.

Ltac pinned_tac :=
  solve [ exact: pinned_bare
        | apply: pinned_left; pinned_tac
        | apply: pinned_right; pinned_tac ].
Ltac present_tac :=
  solve [ exact: loc_present_defined
        | exact: loc_present_pin
        | apply: loc_present_left; present_tac
        | apply: loc_present_right; present_tac ].
Ltac stable_tac :=
  solve [ exact: loc_stable_defined_self
        | exact: loc_stable_pin_self
        | by apply: loc_stable_defined_other
        | by apply: loc_stable_pin_other
        | apply: loc_stable_and; stable_tac ].

(* A local frame describing exactly the arguments and the existence of every
   scratch local touched by the generated normalization body. *)
Local Notation NormEntry z d :=
  (HA_and (HA_defined (T_local 2%num))
    (HA_and (HA_defined (T_local 3%num))
      (HA_and (HA_defined (T_local 4%num))
        (HA_and (HA_defined (T_local 5%num))
          (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 z)))
                  (term_eq (T_local 1%num) (T_const (SM.Vi64 d)))))))).
Local Notation NormRem z d :=
  (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (Z.rem z d))))
    (NormEntry z d)).
Local Notation NormB z d :=
  (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 d))) (NormRem z d)).
Local Notation NormA z d :=
  (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (Z.rem z d)))) (NormB z d)).
Local Notation NormR z d :=
  (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (Z.rem z d + d)))) (NormA z d)).

Lemma normalize_prologue_sem z d : word z -> 1 <= d <= MAX ->
  sem_triple (triv_ctx SM.main) (AS_base [::] (NormEntry z d))
    [:: BI_local_get 0%num; BI_local_get 1%num;
        BI_binop T_i64 (Binop_i (BOI_rem SX_S)); BI_local_set 2%num]
    (AS_base [::] (NormRem z d)).
Proof.
  move=> Hz Hd.
  apply: (sem_seq (es1 := [:: BI_local_get 0%num])
    (Q := AS_base [:: T_const (SM.Vi64 z)] (NormEntry z d))).
  - apply: get_pinned_frame. pinned_tac.
  - apply: (sem_seq (es1 := [:: BI_local_get 1%num])
      (Q := AS_base [:: T_const (SM.Vi64 z); T_const (SM.Vi64 d)] (NormEntry z d))).
    + apply: get_pinned_frame. pinned_tac.
    + apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_rem SX_S))])
        (Q := AS_base [:: T_const (SM.Vi64 (Z.rem z d))] (NormEntry z d))).
      * apply: binop_consts; [by vm_compute | by [] | by [] | exact: crt_i64_rem_exact].
      * apply: sem_local_set_const_frame; [stable_tac | present_tac].
Qed.

Definition normalize_guard (z d : Z) : bool :=
  app_relop (Relop_i ROI_ne)
    (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S))
      (SM.Vi64 (Z.rem z d + d)) (SM.Vi64 (Z.rem z d)))))
    (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S))
      (SM.Vi64 d) (SM.Vi64 0)))).

Lemma normalize_guard_false z d : word z -> 1 <= d <= MAX ->
  Z.rem z d < 0 -> normalize_guard z d = false.
Proof.
  move=> Hz Hd Hrneg.
  have Hrw := crt_rem_word Hz Hd.
  have Hdw := crt_modulus_word Hd.
  have Hsum : word (Z.rem z d + d).
  { unfold word, MAX, i64_min, i64_max in *. lia. }
  have Hrange : Wasm_int.Int64.min_signed <=
      Wasm_int.Int64.signed (Wasm_int.Int64.repr (Z.rem z d)) +
      Wasm_int.Int64.signed (Wasm_int.Int64.repr d) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Hrw) (crt_i64_signed_repr Hdw)
      i64_min_signed_val i64_max_signed_val. exact Hsum. }
  have Hguard := i64_add_signed_guard_false Hrange.
  rewrite (crt_i64_add_repr Hrw Hdw) in Hguard.
  exact Hguard.
Qed.

Lemma normalize_add_prefix_sem z d : word z -> 1 <= d <= MAX ->
  sem_triple (triv_ctx SM.main) (AS_base [::] (NormRem z d))
    [:: BI_local_get 2%num; BI_local_get 1%num; BI_local_set 4%num;
        BI_local_tee 3%num; BI_local_get 4%num;
        BI_binop T_i64 (Binop_i BOI_add); BI_local_tee 5%num;
        BI_local_get 3%num; BI_relop T_i64 (Relop_i (ROI_lt SX_S));
        BI_local_get 4%num; BI_const_num (SM.Vi64 0);
        BI_relop T_i64 (Relop_i (ROI_lt SX_S)); BI_relop T_i32 (Relop_i ROI_ne)]
    (AS_base [:: T_const (VAL_int32 (wasm_bool (normalize_guard z d)))] (NormR z d)).
Proof.
  move=> Hz Hd.
  have Hrw := crt_rem_word Hz Hd.
  have Hdw := crt_modulus_word Hd.
  apply: (sem_seq (es1 := [:: BI_local_get 2%num])
    (Q := AS_base [:: T_const (SM.Vi64 (Z.rem z d))] (NormRem z d))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_get 1%num])
    (Q := AS_base [:: T_const (SM.Vi64 (Z.rem z d)); T_const (SM.Vi64 d)] (NormRem z d))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 4%num])
    (Q := AS_base [:: T_const (SM.Vi64 (Z.rem z d))] (NormB z d))).
  { apply: (sem_frame_consts (vf := [:: SM.Vi64 (Z.rem z d)])).
    apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_tee 3%num])
    (Q := AS_base [:: T_const (SM.Vi64 (Z.rem z d))] (NormA z d))).
  { apply: sem_local_tee_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 4%num])
    (Q := AS_base [:: T_const (SM.Vi64 (Z.rem z d)); T_const (SM.Vi64 d)] (NormA z d))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i BOI_add)])
    (Q := AS_base [:: T_const (SM.Vi64 (Z.rem z d + d))] (NormA z d))).
  { apply: binop_consts; [by vm_compute | by [] | by [] |].
    change (app_binop (Binop_i BOI_add)
      (VAL_int64 (Wasm_int.Int64.repr (Z.rem z d)))
      (VAL_int64 (Wasm_int.Int64.repr d)) =
      Some (VAL_int64 (Wasm_int.Int64.repr (Z.rem z d + d)))).
    rewrite -(crt_i64_add_repr Hrw Hdw). exact: i64_add_some. }
  apply: (sem_seq (es1 := [:: BI_local_tee 5%num])
    (Q := AS_base [:: T_const (SM.Vi64 (Z.rem z d + d))] (NormR z d))).
  { apply: sem_local_tee_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 3%num])
    (Q := AS_base [:: T_const (SM.Vi64 (Z.rem z d + d)); T_const (SM.Vi64 (Z.rem z d))] (NormR z d))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_relop T_i64 (Relop_i (ROI_lt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (SM.Vi64 (Z.rem z d + d)) (SM.Vi64 (Z.rem z d)))))] (NormR z d))).
  { apply: relop_consts; by []. }
  apply: (sem_seq (es1 := [:: BI_local_get 4%num])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (SM.Vi64 (Z.rem z d + d)) (SM.Vi64 (Z.rem z d))))); T_const (SM.Vi64 d)] (NormR z d))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_const_num (SM.Vi64 0)])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (SM.Vi64 (Z.rem z d + d)) (SM.Vi64 (Z.rem z d))))); T_const (SM.Vi64 d); T_const (SM.Vi64 0)] (NormR z d))).
  { exact: sem_const_framed. }
  apply: (sem_seq (es1 := [:: BI_relop T_i64 (Relop_i (ROI_lt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (SM.Vi64 (Z.rem z d + d)) (SM.Vi64 (Z.rem z d))))); T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (SM.Vi64 d) (SM.Vi64 0))))] (NormR z d))).
  { apply: (sem_frame_consts (vf := [:: VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (SM.Vi64 (Z.rem z d + d)) (SM.Vi64 (Z.rem z d))))])).
    apply: relop_consts; by []. }
  apply: relop_consts; by [].
Qed.

Lemma crt_pinned_return G H i c tail Qn Qb :
  pinned i c H ->
  sem_mx G (AS_base [::] H) (BI_local_get i :: BI_return :: tail)
    Qn (AS_base [:: T_const c] HA_true) Qb.
Proof.
  move=> Hpin.
  apply: (sem_mx_seq (es1 := [:: BI_local_get i])
    (Q1 := AS_base [:: T_const c] HA_true)).
  - apply: sem_mx_lift.
    apply: (sem_conseq (P' := AS_base [::] H)
      (Q' := AS_base [:: T_const c] H)).
    + by move=> V vh.
    + move=> V [vs h] /= [Hs _]. by split.
    + apply: get_pinned_frame. exact Hpin.
  - exact: sem_mx_return_suffix.
Qed.

Lemma crt_if_true_returns G H yes no Qr Qb :
  sem_mx G (AS_base [::] H) yes (AS_base [::] HA_false) Qr (AS_base [::] HA_false) ->
  sem_mx G (AS_base [:: T_const (VAL_int32 (wasm_bool true))] H)
    [:: BI_if (BT_valtype None) yes no] (AS_base [::] HA_false) Qr Qb.
Proof.
  move=> Hyes.
  apply: (sem_mx_conseq
    (P' := AS_base [:: T_const (VAL_int32 (wasm_bool true))]
      (HA_and (HA_has_type (T_const (VAL_int32 (wasm_bool true))) T_i32) H))
    (Qn' := AS_base [::] HA_false) (Qr' := Qr) (Qb' := Qb)).
  - move=> V [vs h] /= [Hs HH]. split; first exact Hs.
    split; last exact HH. by exists (VAL_int32 (wasm_bool true)).
  - by [].
  - by [].
  - by [].
  - eapply sem_mx_if with (t2s := [::]).
    + by [].
    + move=> V vs h /= [Hs _]. by case: Hs => <-.
    + apply: (sem_mx_conseq (P' := AS_base [::] H)
        (Qn' := AS_base [::] HA_false) (Qr' := Qr) (Qb' := AS_base [::] HA_false)).
      * move=> V [vs h] /= [Hs [HH _]]. by split.
      * by [].
      * by [].
      * by [].
      * exact Hyes.
    + apply: (sem_mx_conseq (P' := AS_base [::] HA_false)
        (Qn' := AS_base [::] HA_false) (Qr' := Qr) (Qb' := AS_base [::] HA_false)).
      * move=> V [vs h] [Hs HH]. split; first exact Hs.
        exact: (false_of_true_cond HH).
      * by [].
      * by [].
      * by [].
      * apply: sem_mx_lift. exact: sem_false.
Qed.

(* Exact then-arm emitted inside normalize, including its signed-add check. *)
Definition normalize_then : seq basic_instruction :=
  [:: BI_local_get 2%num; BI_local_get 1%num; BI_local_set 4%num;
      BI_local_tee 3%num; BI_local_get 4%num;
      BI_binop T_i64 (Binop_i BOI_add); BI_local_tee 5%num;
      BI_local_get 3%num; BI_relop T_i64 (Relop_i (ROI_lt SX_S));
      BI_local_get 4%num; BI_const_num (SM.Vi64 0);
      BI_relop T_i64 (Relop_i (ROI_lt SX_S)); BI_relop T_i32 (Relop_i ROI_ne);
      BI_if (BT_valtype None) [:: BI_unreachable] [::];
      BI_local_get 5%num; BI_return].

Lemma normalize_then_sem z d Qn Qb : word z -> 1 <= d <= MAX ->
  Z.rem z d < 0 ->
  sem_mx (triv_ctx SM.main) (AS_base [::] (NormRem z d)) normalize_then
    Qn (AS_base [:: T_const (SM.Vi64 (Z.rem z d + d))] HA_true) Qb.
Proof.
  move=> Hz Hd Hrneg.
  rewrite /normalize_then.
  apply: (sem_mx_seq
    (es1 := [:: BI_local_get 2%num; BI_local_get 1%num; BI_local_set 4%num;
      BI_local_tee 3%num; BI_local_get 4%num;
      BI_binop T_i64 (Binop_i BOI_add); BI_local_tee 5%num;
      BI_local_get 3%num; BI_relop T_i64 (Relop_i (ROI_lt SX_S));
      BI_local_get 4%num; BI_const_num (SM.Vi64 0);
      BI_relop T_i64 (Relop_i (ROI_lt SX_S)); BI_relop T_i32 (Relop_i ROI_ne)])
    (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool false))] (NormR z d))).
  - apply: sem_mx_lift.
    have Hprefix := normalize_add_prefix_sem Hz Hd.
    by rewrite (normalize_guard_false Hz Hd Hrneg) in Hprefix.
  - apply: (sem_mx_seq
      (es1 := [:: BI_if (BT_valtype None) [:: BI_unreachable] [::]])
      (Q1 := AS_base [::] (NormR z d))).
    + apply: sem_mx_lift. apply: guard_if_false. exact: sem_nil_same.
    + apply: crt_pinned_return. pinned_tac.
Qed.

Lemma normalize_body_shape : modfunc_body SM.normalize =
  [:: BI_local_get 0%num; BI_local_get 1%num;
      BI_binop T_i64 (Binop_i (BOI_rem SX_S)); BI_local_set 2%num;
      BI_local_get 2%num; BI_const_num (SM.Vi64 0);
      BI_relop T_i64 (Relop_i (ROI_lt SX_S));
      BI_if (BT_valtype None) normalize_then [::];
      BI_local_get 2%num; BI_return; BI_unreachable].
Proof. by []. Qed.

Theorem normalize_machine_computes z d : word z -> 1 <= d <= MAX ->
  fun_computes SM.main 1%nat [:: SM.Vi64 z; SM.Vi64 d] [:: SM.Vi64 (z mod d)].
Proof.
  move=> Hz Hd.
  have Hrw := crt_rem_word Hz Hd.
  have Hnormalized := proj1 (normalize_proved z d Hz Hd).
  rewrite -Hnormalized.
  prepare_fun_computes
    (AS_base [::] (NormEntry z d))
    (AS_base [:: T_const (SM.Vi64
      (if Z.rem z d <? 0 then Z.rem z d + d else Z.rem z d))] HA_true).
  - move=> V [vs h] /= [Hs [[P0 [P1 _]] [[T0 [T1 _]] [T2 [T3 [T4 [T5 _]]]]]]].
    split; first exact Hs.
    split; first by case: T2 => [w [Ew _]]; exists w.
    split; first by case: T3 => [w [Ew _]]; exists w.
    split; first by case: T4 => [w [Ew _]]; exists w.
    split; first by case: T5 => [w [Ew _]]; exists w.
    by split.
  - rewrite normalize_body_shape.
    apply: (sem_mx_seq
      (es1 := [:: BI_local_get 0%num; BI_local_get 1%num;
        BI_binop T_i64 (Binop_i (BOI_rem SX_S)); BI_local_set 2%num])
      (Q1 := AS_base [::] (NormRem z d))).
    + apply: sem_mx_lift. exact: normalize_prologue_sem.
    + apply: (sem_mx_seq
        (es1 := [:: BI_local_get 2%num; BI_const_num (SM.Vi64 0);
          BI_relop T_i64 (Relop_i (ROI_lt SX_S))])
        (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool (Z.rem z d <? 0)))] (NormRem z d))).
      * apply: sem_mx_lift. rewrite -(crt_i64_lt_zero Hrw).
        apply: test_pin_const; [pinned_tac | by [] | by [] | by []].
      * case Hrlt: (Z.rem z d <? 0).
        -- apply: (sem_mx_seq
             (es1 := [:: BI_if (BT_valtype None) normalize_then [::]])
             (Q1 := AS_base [::] HA_false)).
           ++ apply: crt_if_true_returns. apply: normalize_then_sem; [exact Hz | exact Hd |].
              apply/Z.ltb_lt. exact Hrlt.
           ++ apply: sem_mx_lift. exact: sem_false.
        -- apply: (sem_mx_seq
             (es1 := [:: BI_if (BT_valtype None) normalize_then [::]])
             (Q1 := AS_base [::] (NormRem z d))).
           ++ apply: sem_mx_lift. apply: guard_if_false. exact: sem_nil_same.
           ++ apply: crt_pinned_return. pinned_tac.
Qed.


(* The two-index branch rule is essential for the compiler's outer-block /
   inner-loop shape: br 0 repeats and br 1 leaves the enclosing loop. *)
Lemma crt_eqz_bool_sem G H b :
  sem_triple G (AS_base [:: T_const (VAL_int32 (wasm_bool b))] H)
    [:: BI_testop T_i32 TO_eqz]
    (AS_base [:: T_const (VAL_int32 (wasm_bool (negb b)))] H).
Proof.
  move=> hs s f V vs h /= [Hs HH] Hr Hagree.
  case: Hs => ?; subst vs.
  exists s, f, V, [:: VAL_int32 (wasm_bool (negb b))], h.
  split; first by []. split.
  - rewrite /vn_to_e /to_e_list /=.
    apply: rtt_step1. apply: r_simple.
    have -> : wasm_bool (negb b) =
      wasm_bool (app_testop_i i32m TO_eqz (wasm_bool b)).
    { by case: b. }
    exact: rs_testop_i32.
  - split; last exact Hr. by split.
Qed.

Lemma crt_br_if_false_sem G H k :
  sem_triple G (AS_base [:: T_const (VAL_int32 (wasm_bool false))] H)
    [:: BI_br_if k] (AS_base [::] H).
Proof.
  move=> hs s f V vs h /= [Hs HH] Hr Hagree.
  case: Hs => ?; subst vs.
  exists s, f, V, [::], h. split; first by []. split.
  - rewrite /vn_to_e /to_e_list /=.
    apply: rtt_step1. apply: r_simple. apply: rs_br_if_false. by [].
  - split; last exact Hr. by split.
Qed.

Lemma crt_br_if_true_sem G H k Qn Qr Qb :
  aentails (AS_base [::] H) (Qb k) ->
  sem_mxk G (AS_base [:: T_const (VAL_int32 (wasm_bool true))] H)
    [:: BI_br_if (N.of_nat k)] Qn Qr Qb.
Proof.
  move=> Hent hs s f V vs h /= [Hs HH] Hr Hagree.
  case: Hs => ?; subst vs.
  exists s, f, V, [::], h. split; first by []. split; first exact Hr.
  right; right. exists k, 0%nat, (LH_base [::] [::]). split.
  - rewrite /vn_to_e /to_e_list /lfill /= ?add0n ?cats0.
    apply: rtt_step1. apply: r_simple. apply: rs_br_if_true. discriminate.
  - apply: (Hent V ([::], h)). by split.
Qed.

Local Notation GcdHead a b :=
  (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 a)))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 b)))
      (HA_defined (T_local 4%num)))).
Local Notation GcdRem a b :=
  (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (a mod b)))) (GcdHead a b)).
Local Notation GcdReadyA a b :=
  (HA_and (HA_defined (T_local 2%num))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 b)))
      (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (a mod b))))
        (HA_defined (T_local 4%num))))).
Local Notation GcdSetA a b :=
  (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 b))) (GcdReadyA a b)).
Local Notation GcdReadyB b :=
  (HA_and (HA_defined (T_local 3%num))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 b)))
      (HA_defined (T_local 4%num)))).

Ltac crt_heap_from HH :=
  lazymatch type of HH with
  | hassert_denote ?V ?H ?h =>
    lazymatch goal with
    | |- hassert_denote V (HA_and ?P ?Q) h =>
        split; crt_heap_from HH
    | |- hassert_denote V (HA_defined (T_local ?i)) h =>
        let Hp := fresh "Hp" in
        assert (Hp : loc_present i H) by present_tac;
        exact (Hp V h HH)
    | |- hassert_denote V (term_eq (T_local ?i) (T_const ?c)) h =>
        let Hp := fresh "Hp" in
        assert (Hp : pinned i c H) by pinned_tac;
        exists c; split; first exact (Hp V h HH); reflexivity
    end
  end.

Lemma gcd_update_sem a b : 1 <= a <= MAX -> 1 <= b <= MAX ->
  sem_triple (triv_ctx SM.main) (AS_base [::] (GcdHead a b))
    [:: BI_local_get 2%num; BI_local_get 3%num;
      BI_binop T_i64 (Binop_i (BOI_rem SX_S)); BI_local_set 4%num;
      BI_local_get 3%num; BI_local_set 2%num;
      BI_local_get 4%num; BI_local_set 3%num]
    (AS_base [::] (GcdHead b (a mod b))).
Proof.
  move=> Ha Hb.
  have Haw := crt_modulus_word Ha.
  have Hrem := crt_i64_rem_exact Haw Hb.
  rewrite (Z.rem_mod_nonneg a b ltac:(lia) ltac:(lia)) in Hrem.
  apply: (sem_seq (es1 := [:: BI_local_get 2%num])
    (Q := AS_base [:: T_const (SM.Vi64 a)] (GcdHead a b))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_get 3%num])
    (Q := AS_base [:: T_const (SM.Vi64 a); T_const (SM.Vi64 b)] (GcdHead a b))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_rem SX_S))])
    (Q := AS_base [:: T_const (SM.Vi64 (a mod b))] (GcdHead a b))).
  { apply: binop_consts; [by vm_compute | by [] | by [] | exact Hrem]. }
  apply: (sem_seq (es1 := [:: BI_local_set 4%num])
    (Q := AS_base [::] (GcdRem a b))).
  { apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 3%num])
    (Q := AS_base [:: T_const (SM.Vi64 b)] (GcdRem a b))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 2%num])
    (Q := AS_base [::] (GcdSetA a b))).
  { apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 b)] (GcdReadyA a b))
      (Q' := AS_base [::] (GcdSetA a b))).
    - move=> V [vs h] [Hs HH]. split; first exact Hs. crt_heap_from HH.
    - by [].
    - apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 4%num])
    (Q := AS_base [:: T_const (SM.Vi64 (a mod b))] (GcdSetA a b))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 (a mod b))] (GcdReadyB b))
    (Q' := AS_base [::] (HA_and
      (term_eq (T_local 3%num) (T_const (SM.Vi64 (a mod b)))) (GcdReadyB b)))).
  - move=> V [vs h] [Hs HH]. split; first exact Hs. crt_heap_from HH.
  - move=> V [vs h] [Hs HH]. split; first exact Hs. crt_heap_from HH.
  - apply: sem_local_set_const_frame; [stable_tac | present_tac].
Qed.


Lemma crt_i64_gt_zero z : word z ->
  app_relop (Relop_i (ROI_gt SX_S)) (SM.Vi64 z) (SM.Vi64 0) = (0 <? z).
Proof.
  move=> Hz. rewrite i64_gt_s_app /Wasm_int.Int64.lt.
  have Hzero : word 0 by unfold word, i64_min, i64_max; lia.
  rewrite (crt_i64_signed_repr Hz) (crt_i64_signed_repr Hzero).
  case: Coqlib.zlt => H; [symmetry; apply/Z.ltb_lt | symmetry; apply/Z.ltb_ge]; lia.
Qed.

Lemma gcd_condition_sem a b : word b ->
  sem_triple (triv_ctx SM.main) (AS_base [::] (GcdHead a b))
    [:: BI_local_get 3%num; BI_const_num (SM.Vi64 0);
      BI_relop T_i64 (Relop_i (ROI_gt SX_S)); BI_testop T_i32 TO_eqz]
    (AS_base [:: T_const (VAL_int32 (wasm_bool (negb (0 <? b))))] (GcdHead a b)).
Proof.
  move=> Hbw.
  apply: (sem_seq (es1 := [:: BI_local_get 3%num; BI_const_num (SM.Vi64 0);
    BI_relop T_i64 (Relop_i (ROI_gt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (0 <? b)))] (GcdHead a b))).
  - rewrite -(crt_i64_gt_zero Hbw).
    apply: test_pin_const; [pinned_tac | by [] | by [] | by []].
  - exact: crt_eqz_bool_sem.
Qed.

Definition gcd_update_code : seq basic_instruction :=
  [:: BI_local_get 2%num; BI_local_get 3%num;
      BI_binop T_i64 (Binop_i (BOI_rem SX_S)); BI_local_set 4%num;
      BI_local_get 3%num; BI_local_set 2%num;
      BI_local_get 4%num; BI_local_set 3%num].
Definition gcd_loop_code : seq basic_instruction :=
  [:: BI_local_get 3%num; BI_const_num (SM.Vi64 0);
      BI_relop T_i64 (Relop_i (ROI_gt SX_S)); BI_testop T_i32 TO_eqz;
      BI_br_if 1%num] ++ gcd_update_code ++ [:: BI_br 0%num].
Definition crt_false_assert := AS_base [::] HA_false.

Lemma gcd_loop_run_sem a b result : gcd_run a b result ->
  1 <= a <= MAX -> 0 <= b <= MAX ->
  sem_mxk (triv_ctx SM.main) (AS_base [::] (GcdHead a b))
    [:: BI_loop (BT_valtype None) gcd_loop_code]
    (AS_base [::] (GcdHead result 0)) crt_false_assert
    (fun k => if k is 0%nat then AS_base [::] (GcdHead result 0) else crt_false_assert).
Proof.
  move=> Hrun. induction Hrun as [a | a b result Hpos Hrun IH]; intros Ha Hb.
  - apply: (crt_loop_unroll (Pback := crt_false_assert) (t1s := [::]) (t2s := [::])).
    + by [].
    + move=> V vs h [Hs _]. by case: Hs => <-.
    + move=> V vs h [_ Hfalse]. by case: Hfalse.
    + rewrite /gcd_loop_code.
      apply: (sem_mxk_seq
        (es1 := [:: BI_local_get 3%num; BI_const_num (SM.Vi64 0);
          BI_relop T_i64 (Relop_i (ROI_gt SX_S)); BI_testop T_i32 TO_eqz])
        (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool true))] (GcdHead a 0))).
      * apply: sem_mxk_lift. apply: gcd_condition_sem.
        unfold word, i64_min, i64_max. lia.
      * apply: (sem_mxk_seq (es1 := [:: BI_br_if 1%num]) (Q1 := crt_false_assert)).
        -- apply: (crt_br_if_true_sem (k := 1%nat)). by [].
        -- apply: sem_mxk_lift. exact: sem_false.
    + apply: sem_mxk_lift. exact: sem_false.
  - have Hmod := Z.mod_pos_bound a b Hpos.
    have Hbw : word b by apply: crt_modulus_word; lia.
    have Htest : (0 <? b) = true by apply/Z.ltb_lt.
    apply: (crt_loop_unroll (Pback := AS_base [::] (GcdHead b (a mod b)))
      (t1s := [::]) (t2s := [::])).
    + by [].
    + move=> V vs h [Hs _]. by case: Hs => <-.
    + move=> V vs h [Hs _]. by case: Hs => <-.
    + rewrite /gcd_loop_code.
      apply: (sem_mxk_seq
        (es1 := [:: BI_local_get 3%num; BI_const_num (SM.Vi64 0);
          BI_relop T_i64 (Relop_i (ROI_gt SX_S)); BI_testop T_i32 TO_eqz])
        (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool false))] (GcdHead a b))).
      * apply: sem_mxk_lift.
        have Hcond := gcd_condition_sem (a := a) Hbw.
        by rewrite Htest in Hcond.
      * apply: (sem_mxk_seq (es1 := [:: BI_br_if 1%num])
          (Q1 := AS_base [::] (GcdHead a b))).
        -- apply: sem_mxk_lift. exact: crt_br_if_false_sem.
        -- apply: (sem_mxk_seq (es1 := gcd_update_code)
             (Q1 := AS_base [::] (GcdHead b (a mod b)))).
           ++ apply: sem_mxk_lift. apply: gcd_update_sem; lia.
           ++ apply: (sem_mxk_br_k (k := 0%nat)). by [].
    + apply: IH; lia.
Qed.

Lemma gcd_block_run_sem a b result : gcd_run a b result ->
  1 <= a <= MAX -> 0 <= b <= MAX ->
  sem_mxk (triv_ctx SM.main) (AS_base [::] (GcdHead a b))
    [:: BI_block (BT_valtype None) [:: BI_loop (BT_valtype None) gcd_loop_code]]
    (AS_base [::] (GcdHead result 0)) crt_false_assert (fun _ => crt_false_assert).
Proof.
  move=> Hrun Ha Hb.
  apply: (sem_mxk_block (t1s := [::]) (t2s := [::])
    (Qb := fun k => if k is 0%nat then AS_base [::] (GcdHead result 0) else crt_false_assert)).
  - by [].
  - by [].
  - move=> V vs h [Hs _]. by case: Hs => <-.
  - by [].
  - exact: (gcd_loop_run_sem Hrun Ha Hb).
Qed.


Local Notation GcdEntry m n :=
  (HA_and (HA_defined (T_local 2%num))
    (HA_and (HA_defined (T_local 3%num))
      (HA_and (HA_defined (T_local 4%num))
        (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 m)))
          (term_eq (T_local 1%num) (T_const (SM.Vi64 n))))))).
Local Notation GcdInitialA m n :=
  (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 m))) (GcdEntry m n)).

Lemma gcd_prologue_sem m n :
  sem_triple (triv_ctx SM.main) (AS_base [::] (GcdEntry m n))
    [:: BI_local_get 0%num; BI_local_set 2%num;
      BI_local_get 1%num; BI_local_set 3%num]
    (AS_base [::] (GcdHead m n)).
Proof.
  apply: (sem_seq (es1 := [:: BI_local_get 0%num])
    (Q := AS_base [:: T_const (SM.Vi64 m)] (GcdEntry m n))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 2%num])
    (Q := AS_base [::] (GcdInitialA m n))).
  { apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 1%num])
    (Q := AS_base [:: T_const (SM.Vi64 n)] (GcdInitialA m n))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 n)] (GcdInitialA m n))
    (Q' := AS_base [::] (HA_and
      (term_eq (T_local 3%num) (T_const (SM.Vi64 n))) (GcdInitialA m n)))).
  - by [].
  - move=> V [vs h] [Hs HH]. split; first exact Hs. crt_heap_from HH.
  - apply: sem_local_set_const_frame; [stable_tac | present_tac].
Qed.

Lemma gcd_body_shape : modfunc_body SM.gcd_positive =
  [:: BI_local_get 0%num; BI_local_set 2%num;
      BI_local_get 1%num; BI_local_set 3%num;
      BI_block (BT_valtype None) [:: BI_loop (BT_valtype None) gcd_loop_code];
      BI_local_get 2%num; BI_return; BI_unreachable].
Proof. by []. Qed.

Theorem gcd_machine_computes m n : moduli m n ->
  fun_computes SM.main 0%nat [:: SM.Vi64 m; SM.Vi64 n] [:: SM.Vi64 (Z.gcd m n)].
Proof.
  move=> Hin.
  have [result [Hrun [Hresult Hword]]] := @gcd_initial_run_correct m n Hin.
  subst result.
  have [Hm Hn] := Hin.
  prepare_fun_computes
    (AS_base [::] (GcdEntry m n))
    (AS_base [:: T_const (SM.Vi64 (Z.gcd m n))] HA_true).
  - move=> V [vs h] /= [Hs [[P0 [P1 _]] [[T0 [T1 _]] [T2 [T3 [T4 _]]]]]].
    split; first exact Hs.
    split; first by case: T2 => [w [Ew _]]; exists w.
    split; first by case: T3 => [w [Ew _]]; exists w.
    split; first by case: T4 => [w [Ew _]]; exists w.
    by split.
  - rewrite gcd_body_shape.
    apply: (sem_mx_seq
      (es1 := [:: BI_local_get 0%num; BI_local_set 2%num;
        BI_local_get 1%num; BI_local_set 3%num])
      (Q1 := AS_base [::] (GcdHead m n))).
    + apply: sem_mx_lift. exact: gcd_prologue_sem.
    + apply: (sem_mx_seq
        (es1 := [:: BI_block (BT_valtype None)
          [:: BI_loop (BT_valtype None) gcd_loop_code]])
        (Q1 := AS_base [::] (GcdHead (Z.gcd m n) 0))).
      * apply: sem_mx_of_mxk_pure_normal. apply: gcd_block_run_sem; [exact Hrun | lia | lia].
      * apply: crt_pinned_return. pinned_tac.
Qed.


(* Arithmetic refinement for the extended-Euclid iteration.  These lemmas
   concern the actual Wasm numeric operators and the emitted guard values;
   the complete inverse function still requires a control/call realization. *)
Lemma crt_i64_mul_repr x y : word x -> word y ->
  Wasm_int.Int64.mul (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y) =
    Wasm_int.Int64.repr (x * y).
Proof.
  move=> Hx Hy. by rewrite Wasm_int.Int64.mul_signed
    (crt_i64_signed_repr Hx) (crt_i64_signed_repr Hy).
Qed.

Lemma crt_i64_sub_repr x y : word x -> word y ->
  Wasm_int.Int64.sub (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y) =
    Wasm_int.Int64.repr (x - y).
Proof.
  move=> Hx Hy. by rewrite Wasm_int.Int64.sub_signed
    (crt_i64_signed_repr Hx) (crt_i64_signed_repr Hy).
Qed.

Lemma crt_i64_div_positive_exact a b : 0 <= a <= MAX -> 1 <= b <= MAX ->
  app_binop (Binop_i (BOI_div SX_S)) (SM.Vi64 a) (SM.Vi64 b) =
    Some (SM.Vi64 (a / b)).
Proof.
  move=> Ha Hb.
  have Haw : word a by unfold word, MAX, i64_min, i64_max in *; lia.
  have Hbw := crt_modulus_word Hb.
  have Hquot : (Wasm_int.Int64.signed (Wasm_int.Int64.repr a) ÷
      Wasm_int.Int64.signed (Wasm_int.Int64.repr b)) = a / b.
  { rewrite (crt_i64_signed_repr Haw) (crt_i64_signed_repr Hbw).
    apply: Z.quot_div_nonneg; lia. }
  have Hqlo : 0 <= a / b by apply: Z.div_pos; lia.
  have Hqhi : a / b <= a by apply: Z.div_le_upper_bound; nia.
  have Hnz : Wasm_int.Int64.signed (Wasm_int.Int64.repr b) <> 0.
  { rewrite (crt_i64_signed_repr Hbw). lia. }
  have Hov : (Wasm_int.Int64.signed (Wasm_int.Int64.repr a) ÷
      Wasm_int.Int64.signed (Wasm_int.Int64.repr b)) <> Wasm_int.Int64.half_modulus.
  { rewrite Hquot i64_half_modulus_val. unfold MAX, i64_max in *. lia. }
  by rewrite (i64_div_s_some Hnz Hov) Hquot.
Qed.

Lemma crt_i64_mul_roundtrip x y : word x -> word y -> word (x * y) -> y <> 0 ->
  app_binop (Binop_i (BOI_div SX_S)) (SM.Vi64 (x * y)) (SM.Vi64 y) =
    Some (SM.Vi64 x).
Proof.
  move=> Hx Hy Hxy Hynz.
  have Hnz : Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <> 0.
  { rewrite (crt_i64_signed_repr Hy). exact Hynz. }
  have Hrange : Wasm_int.Int64.min_signed <=
      Wasm_int.Int64.signed (Wasm_int.Int64.repr x) *
      Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Hx) (crt_i64_signed_repr Hy)
      i64_min_signed_val i64_max_signed_val. exact Hxy. }
  have Hround := i64_mul_div_s_roundtrip Hnz Hrange.
  by rewrite (crt_i64_mul_repr Hx Hy) in Hround.
Qed.

Definition crt_subtraction_guard (x y : Z) : bool :=
  app_relop (Relop_i ROI_ne)
    (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S))
      (SM.Vi64 (x - y)) (SM.Vi64 x))))
    (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_gt SX_S))
      (SM.Vi64 y) (SM.Vi64 0)))).

Lemma crt_subtraction_guard_false x y : word x -> word y -> word (x - y) ->
  crt_subtraction_guard x y = false.
Proof.
  move=> Hx Hy Hxy.
  have Hrange : Wasm_int.Int64.min_signed <=
      Wasm_int.Int64.signed (Wasm_int.Int64.repr x) -
      Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Hx) (crt_i64_signed_repr Hy)
      i64_min_signed_val i64_max_signed_val. exact Hxy. }
  have Hguard := i64_sub_signed_guard_false Hrange.
  rewrite (crt_i64_sub_repr Hx Hy) in Hguard.
  exact Hguard.
Qed.

Theorem eea_iteration_numeric_refinement A B e :
  eea_inputs A B -> eea_inv A B e -> 0 < r1 e ->
  let q := r0 e / r1 e in
  app_binop (Binop_i (BOI_div SX_S)) (SM.Vi64 (r0 e)) (SM.Vi64 (r1 e)) =
    Some (SM.Vi64 q) /\
  app_binop (Binop_i (BOI_rem SX_S)) (SM.Vi64 (r0 e)) (SM.Vi64 (r1 e)) =
    Some (SM.Vi64 (r0 e mod r1 e)) /\
  (s1 e <> 0 ->
    app_binop (Binop_i (BOI_div SX_S)) (SM.Vi64 (q * s1 e)) (SM.Vi64 (s1 e)) =
      Some (SM.Vi64 q)) /\
  (t1 e <> 0 ->
    app_binop (Binop_i (BOI_div SX_S)) (SM.Vi64 (q * t1 e)) (SM.Vi64 (t1 e)) =
      Some (SM.Vi64 q)) /\
  crt_subtraction_guard (s0 e) (q * s1 e) = false /\
  crt_subtraction_guard (t0 e) (q * t1 e) = false.
Proof.
  move=> Hin Hinv Hpos /=.
  have Hbounds := eea_step_bounds_proved A B e Hin Hinv Hpos.
  destruct Hbounds as (Hq & Hqr & Hsp & Hsn & Htp & Htn & Wsp & Wsn & Wtp & Wtn).
  destruct Hinv as (Hr1 & Hr01 & Hr0 & Hg & Hbez0 & Hbez1 & Hdet &
    Hs & Ht & Hws & Hwt & Hs0 & Hs1 & Ht0 & Ht1).
  have HA : A <= MAX by exact (proj2 Hin).
  have HB : B <= MAX by clear -Hin; destruct Hin as [[_ HBA] HAmax]; lia.
  have Wq : word (r0 e / r1 e) by clear -Hq HA; apply: crt_modulus_word; lia.
  have Ws0 : word (s0 e) by apply: (abs_word_small _ B); assumption.
  have Ws1 : word (s1 e) by apply: (abs_word_small _ B); assumption.
  have Wt0 : word (t0 e) by apply: (abs_word_small _ A); assumption.
  have Wt1 : word (t1 e) by apply: (abs_word_small _ A); assumption.
  split.
  - clear -Hr1 Hr01 Hr0 HA Hpos. apply: crt_i64_div_positive_exact; lia.
  - split.
    + have W0 : word (r0 e) by clear -Hr1 Hr01 Hr0 HA; apply: crt_modulus_word; lia.
      have Hd : 1 <= r1 e <= MAX by clear -Hr01 Hr0 HA Hpos; lia.
      have Hrem := crt_i64_rem_exact W0 Hd.
      by rewrite (Z.rem_mod_nonneg (r0 e) (r1 e) ltac:(clear -Hr1 Hr01; lia) Hpos) in Hrem.
    + split.
      * move=> Hnz. exact: (crt_i64_mul_roundtrip Wq Ws1 Wsp Hnz).
      * split.
        -- move=> Hnz. exact: (crt_i64_mul_roundtrip Wq Wt1 Wtp Hnz).
        -- split; apply: crt_subtraction_guard_false; assumption.
Qed.

End Host.

Print Assumptions crt_i64_rem_exact.
Print Assumptions normalize_machine_computes.
Print Assumptions gcd_machine_computes.
Print Assumptions eea_iteration_numeric_refinement.
