(* Execution proofs for the exact generated public functions. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Semantics Pure Control MultiExit
  NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTMath CRTLoops.
From CRTGenerated Require Import main.
From CRTWasm Require Import CRTAPIModel CRTContracts CRTStorePure CRTModule CRTExecution CRTCalls.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.

Lemma crt_public_eq x y : word x -> word y ->
  app_relop (Relop_i ROI_eq) (main.Vi64 x) (main.Vi64 y) = (x =? y).
Proof.
  move=> Hx Hy. rewrite /main.Vi64 crt_contract_eq.
  by rewrite (crt_contract_signed_repr Hx) (crt_contract_signed_repr Hy).
Qed.

Lemma crt_public_ne x y : word x -> word y ->
  app_relop (Relop_i ROI_ne) (main.Vi64 x) (main.Vi64 y) = negb (x =? y).
Proof.
  move=> Hx Hy. rewrite /main.Vi64 crt_contract_ne.
  by rewrite (crt_contract_signed_repr Hx) (crt_contract_signed_repr Hy).
Qed.

Lemma crt_public_lt x y : word x -> word y ->
  app_relop (Relop_i (ROI_lt SX_S)) (main.Vi64 x) (main.Vi64 y) = (x <? y).
Proof.
  move=> Hx Hy. rewrite /main.Vi64 crt_contract_lt.
  by rewrite (crt_contract_signed_repr Hx) (crt_contract_signed_repr Hy).
Qed.

Lemma crt_public_gt x y : word x -> word y ->
  app_relop (Relop_i (ROI_gt SX_S)) (main.Vi64 x) (main.Vi64 y) = (y <? x).
Proof. move=> Hx Hy. exact: (crt_public_lt Hy Hx). Qed.

Lemma crt_period_intermediate_bounds m n : moduli m n ->
  1 <= Z.gcd m n <= M /\ 1 <= m / Z.gcd m n <= M /\
  word (m / Z.gcd m n) /\ word (period m n).
Proof.
  move=> Hmn. have [Hm Hn] := Hmn.
  have [Hg [Hgm [Hgn [Hq _]]]] := reduction_proved m n ltac:(lia) ltac:(lia).
  have Heq := exact_division _ _ Hg Hgm.
  have HBq : 1 <= m / Z.gcd m n <= M by nia.
  have HBg : 1 <= Z.gcd m n <= M by nia.
  split; first exact HBg. split; first exact HBq.
  split; first exact: crt_modulus_word.
  exact (proj2 (crt_period_bounds m n Hmn)).
Qed.

Section Host.
Context `{ho : host}.

Ltac pinned_tac :=
  solve [ exact: pinned_bare | apply: pinned_left; pinned_tac
        | apply: pinned_right; pinned_tac ].
Ltac present_tac :=
  solve [ exact: loc_present_defined | exact: loc_present_pin
        | apply: loc_present_left; present_tac | apply: loc_present_right; present_tac ].
Ltac stable_tac :=
  solve [ exact: loc_stable_defined_self | exact: loc_stable_pin_self
        | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other
        | apply: loc_stable_and; stable_tac ].

Definition PeriodEntry m n :=
  HA_and (HA_defined (T_local 2%num))
    (HA_and (HA_defined (T_local 3%num))
      (HA_and (HA_defined (T_local 4%num))
        (HA_and (HA_defined (T_local 5%num))
          (HA_and (term_eq (T_local 0%num) (T_const (main.Vi64 m)))
                  (term_eq (T_local 1%num) (T_const (main.Vi64 n))))))).
Definition PeriodReady m n :=
  HA_and (term_eq (T_local 2%num) (T_const (main.Vi64 (Z.gcd m n)))) (PeriodEntry m n).
Definition PeriodN m n :=
  HA_and (term_eq (T_local 4%num) (T_const (main.Vi64 n))) (PeriodReady m n).
Definition PeriodQ m n :=
  HA_and (term_eq (T_local 3%num) (T_const (main.Vi64 (m / Z.gcd m n)))) (PeriodN m n).
Definition PeriodProduct m n :=
  HA_and (term_eq (T_local 5%num) (T_const (main.Vi64 (period m n)))) (PeriodQ m n).

Lemma period_product_sem m n : moduli m n ->
  sem_triple (triv_ctx main.main) (AS_base [::] (PeriodReady m n))
    [:: BI_local_get 0%num; BI_local_get 2%num;
      BI_binop T_i64 (Binop_i (BOI_div SX_S));
      BI_local_get 1%num; BI_local_set 4%num; BI_local_tee 3%num;
      BI_local_get 4%num; BI_binop T_i64 (Binop_i BOI_mul); BI_local_set 5%num]
    (AS_base [::] (PeriodProduct m n)).
Proof.
  move=> Hmn. have [Hm Hn] := Hmn.
  have [Hg [Hq [Hqw Hpw]]] := crt_period_intermediate_bounds Hmn.
  have Hnw := crt_modulus_word Hn.
  apply: (sem_seq (es1 := [:: BI_local_get 0%num])
    (Q := AS_base [:: T_const (main.Vi64 m)] (PeriodReady m n))).
  { apply: get_pinned_frame. rewrite /PeriodReady /PeriodEntry. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_get 2%num])
    (Q := AS_base [:: T_const (main.Vi64 m); T_const (main.Vi64 (Z.gcd m n))] (PeriodReady m n))).
  { apply: get_pinned_frame. rewrite /PeriodReady. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))])
    (Q := AS_base [:: T_const (main.Vi64 (m / Z.gcd m n))] (PeriodReady m n))).
  { apply: binop_consts; [by vm_compute | by [] | by [] |].
    apply: crt_i64_div_positive_exact; lia. }
  apply: (sem_seq (es1 := [:: BI_local_get 1%num])
    (Q := AS_base [:: T_const (main.Vi64 (m / Z.gcd m n)); T_const (main.Vi64 n)] (PeriodReady m n))).
  { apply: get_pinned_frame. rewrite /PeriodReady /PeriodEntry. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 4%num])
    (Q := AS_base [:: T_const (main.Vi64 (m / Z.gcd m n))] (PeriodN m n))).
  { apply: (sem_frame_consts (vf := [:: main.Vi64 (m / Z.gcd m n)])).
    apply: sem_local_set_const_frame; rewrite /PeriodReady /PeriodEntry;
      [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_tee 3%num])
    (Q := AS_base [:: T_const (main.Vi64 (m / Z.gcd m n))] (PeriodQ m n))).
  { apply: sem_local_tee_const_frame; rewrite /PeriodN /PeriodReady /PeriodEntry;
      [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 4%num])
    (Q := AS_base [:: T_const (main.Vi64 (m / Z.gcd m n)); T_const (main.Vi64 n)] (PeriodQ m n))).
  { apply: get_pinned_frame. rewrite /PeriodQ /PeriodN. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i BOI_mul)])
    (Q := AS_base [:: T_const (main.Vi64 (period m n))] (PeriodQ m n))).
  { apply: binop_consts; [by vm_compute | by [] | by [] |].
    change (app_binop (Binop_i BOI_mul)
      (VAL_int64 (Wasm_int.Int64.repr (m / Z.gcd m n)))
      (VAL_int64 (Wasm_int.Int64.repr n)) =
      Some (VAL_int64 (Wasm_int.Int64.repr ((m / Z.gcd m n) * n)))).
    rewrite -(crt_i64_mul_repr Hqw Hnw). exact: i64_mul_some. }
  apply: sem_local_set_const_frame; rewrite /PeriodQ /PeriodN /PeriodReady /PeriodEntry;
    [stable_tac | present_tac].
Qed.

Definition period_mul_check :=
  [:: BI_local_get 4%num; BI_const_num (main.Vi64 (-1));
      BI_relop T_i64 (Relop_i ROI_eq);
      BI_if (BT_valtype None)
        [:: BI_local_get 3%num; BI_const_num (main.Vi64 i64_min);
            BI_relop T_i64 (Relop_i ROI_eq);
            BI_if (BT_valtype None) [:: BI_unreachable] [::]]
        [:: BI_local_get 5%num; BI_local_get 4%num;
            BI_binop T_i64 (Binop_i (BOI_div SX_S));
            BI_local_get 3%num; BI_relop T_i64 (Relop_i ROI_ne);
            BI_if (BT_valtype None) [:: BI_unreachable] [::]]].

Lemma period_mul_check_sem m n : moduli m n ->
  sem_triple (triv_ctx main.main) (AS_base [::] (PeriodProduct m n))
    period_mul_check (AS_base [::] (PeriodProduct m n)).
Proof.
  move=> Hmn. have [Hm Hn] := Hmn.
  have [Hg [Hq [Hqw Hpw]]] := crt_period_intermediate_bounds Hmn.
  have Hnw := crt_modulus_word Hn.
  have Hminus : word (-1) by unfold word, i64_min, i64_max; lia.
  have Hne : app_relop (Relop_i ROI_eq) (main.Vi64 n) (main.Vi64 (-1)) = false.
  { rewrite (crt_public_eq Hnw Hminus). apply/Z.eqb_neq; lia. }
  rewrite /period_mul_check.
  apply: (sem_seq
    (es1 := [:: BI_local_get 4%num; BI_const_num (main.Vi64 (-1)); BI_relop T_i64 (Relop_i ROI_eq)])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool false))] (PeriodProduct m n))).
  { rewrite -Hne. apply: test_pin_const; [rewrite /PeriodProduct /PeriodQ /PeriodN; pinned_tac | by [] | by [] | by []]. }
  apply: guard_if_false.
  apply: (sem_seq (es1 := [:: BI_local_get 5%num])
    (Q := AS_base [:: T_const (main.Vi64 (period m n))] (PeriodProduct m n))).
  { apply: get_pinned_frame. rewrite /PeriodProduct. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_get 4%num])
    (Q := AS_base [:: T_const (main.Vi64 (period m n)); T_const (main.Vi64 n)] (PeriodProduct m n))).
  { apply: get_pinned_frame. rewrite /PeriodProduct /PeriodQ /PeriodN. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))])
    (Q := AS_base [:: T_const (main.Vi64 (m / Z.gcd m n))] (PeriodProduct m n))).
  { apply: binop_consts; [by vm_compute | by [] | by [] |].
    apply: crt_i64_mul_roundtrip; [exact Hqw | exact Hnw | exact Hpw | lia]. }
  apply: (sem_seq (es1 := [:: BI_local_get 3%num])
    (Q := AS_base [:: T_const (main.Vi64 (m / Z.gcd m n)); T_const (main.Vi64 (m / Z.gcd m n))] (PeriodProduct m n))).
  { apply: get_pinned_frame. rewrite /PeriodProduct /PeriodQ. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_relop T_i64 (Relop_i ROI_ne)])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool false))] (PeriodProduct m n))).
  { have Heq : app_relop (Relop_i ROI_ne) (main.Vi64 (m / Z.gcd m n)) (main.Vi64 (m / Z.gcd m n)) = false.
    { by rewrite (crt_public_ne Hqw Hqw) Z.eqb_refl. }
    rewrite -Heq. apply: relop_consts; by []. }
  apply: guard_if_false. exact: sem_nil_same.
Qed.

Definition period_tail := List.skipn 11 (modfunc_body main.crt_period).

Lemma period_tail_sem m n Qn Qb : moduli m n ->
  sem_mx (triv_ctx main.main) (AS_base [::] (PeriodReady m n)) period_tail
    Qn (AS_base [:: T_const (main.Vi64 (period m n))] HA_true) Qb.
Proof.
  move=> Hmn. have [Hm Hn] := Hmn.
  have Hnw := crt_modulus_word Hn.
  have Hzero : word 0 by unfold word, i64_min, i64_max; lia.
  have Hne : app_relop (Relop_i ROI_ne) (main.Vi64 n) (main.Vi64 0) = true.
  { rewrite (crt_public_ne Hnw Hzero). have -> : (n =? 0) = false by apply/Z.eqb_neq; lia. by []. }
  change (sem_mx (triv_ctx main.main) (AS_base [::] (PeriodReady m n))
    ([:: BI_local_get 0%num; BI_local_get 2%num;
      BI_binop T_i64 (Binop_i (BOI_div SX_S)); BI_local_get 1%num;
      BI_local_set 4%num; BI_local_tee 3%num; BI_local_get 4%num;
      BI_binop T_i64 (Binop_i BOI_mul); BI_local_set 5%num] ++
     [:: BI_local_get 4%num; BI_const_num (main.Vi64 0);
       BI_relop T_i64 (Relop_i ROI_ne);
       BI_if (BT_valtype None) period_mul_check [::];
       BI_local_get 5%num; BI_return; BI_unreachable])
    Qn (AS_base [:: T_const (main.Vi64 (period m n))] HA_true) Qb).
  apply: (sem_mx_seq (Q1 := AS_base [::] (PeriodProduct m n))).
  - apply: sem_mx_lift. exact: period_product_sem.
  - apply: (sem_mx_seq
      (es1 := [:: BI_local_get 4%num; BI_const_num (main.Vi64 0); BI_relop T_i64 (Relop_i ROI_ne)])
      (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool true))] (PeriodProduct m n))).
    + apply: sem_mx_lift. rewrite -Hne. apply: test_pin_const;
        [rewrite /PeriodProduct /PeriodQ /PeriodN; pinned_tac | by [] | by [] | by []].
    + apply: (sem_mx_seq
        (es1 := [:: BI_if (BT_valtype None) period_mul_check [::]])
        (Q1 := AS_base [::] (PeriodProduct m n))).
      * apply: sem_mx_lift. apply: guard_if_true. exact: period_mul_check_sem.
      * apply: crt_pinned_return. rewrite /PeriodProduct. pinned_tac.
Qed.

Lemma crt_if_const_true G H tb ts yes no Q :
  expand_ctx G tb = Some (Tf [::] ts) ->
  sem_triple G (AS_base [::] H) yes Q ->
  sem_triple G (AS_base [:: T_const (VAL_int32 (wasm_bool true))] H)
    [:: BI_if tb yes no] Q.
Proof.
  move=> Htype Hyes.
  apply: (sem_conseq
    (P' := AS_base [:: T_const (VAL_int32 (wasm_bool true))]
      (HA_and (HA_has_type (T_const (VAL_int32 (wasm_bool true))) T_i32) H))
    (Q' := Q)).
  - move=> V [vs h] /= [Hs HH]. split; first exact Hs.
    split; last exact HH. by exists (VAL_int32 (wasm_bool true)).
  - by [].
  - apply: sem_if; first exact Htype.
    + apply: (sem_conseq (P' := AS_base [::] H) (Q' := Q)).
      * move=> V [vs h] /= [Hs [HH _]]. by split.
      * by [].
      * exact Hyes.
    + apply: (sem_conseq (P' := AS_base [::] HA_false) (Q' := Q)).
      * move=> V [vs h] [Hs HH]. split; first exact Hs.
        exact: (false_of_true_cond HH).
      * by [].
      * exact: sem_false.
Qed.

Lemma crt_if_const_false G H tb ts yes no Q :
  expand_ctx G tb = Some (Tf [::] ts) ->
  sem_triple G (AS_base [::] H) no Q ->
  sem_triple G (AS_base [:: T_const (VAL_int32 (wasm_bool false))] H)
    [:: BI_if tb yes no] Q.
Proof.
  move=> Htype Hno.
  apply: (sem_conseq
    (P' := AS_base [:: T_const (VAL_int32 (wasm_bool false))]
      (HA_and (HA_has_type (T_const (VAL_int32 (wasm_bool false))) T_i32) H))
    (Q' := Q)).
  - move=> V [vs h] /= [Hs HH]. split; first exact Hs.
    split; last exact HH. by exists (VAL_int32 (wasm_bool false)).
  - by [].
  - apply: sem_if; first exact Htype.
    + apply: (sem_conseq (P' := AS_base [::] HA_false) (Q' := Q)).
      * move=> V [vs h] [Hs HH]. split; first exact Hs.
        exact: (false_of_false_cond HH).
      * by [].
      * exact: sem_false.
    + apply: (sem_conseq (P' := AS_base [::] H) (Q' := Q)).
      * move=> V [vs h] /= [Hs [HH _]]. by split.
      * by [].
      * exact Hno.
Qed.

Lemma crt_or_sem G H b c es :
  sem_triple G (AS_base [::] H) es
    (AS_base [:: T_const (VAL_int32 (wasm_bool c))] H) ->
  sem_triple G (AS_base [:: T_const (VAL_int32 (wasm_bool b))] H)
    [:: BI_if (BT_valtype (Some (T_num T_i32)))
      [:: BI_const_num (main.Vi32 1)] es]
    (AS_base [:: T_const (VAL_int32 (wasm_bool (b || c)))] H).
Proof.
  move=> Hc. case: b => /=.
  - apply: crt_if_const_true; first by []. exact: sem_const_framed.
  - apply: crt_if_const_false; first by []. exact Hc.
Qed.

Definition period_bad m n := ((m <? 1) || (M <? m) || (n <? 1) || (M <? n)).
Definition period_validation := List.firstn 6 (modfunc_body main.crt_period).

Lemma period_validation_sem m n : word m -> word n ->
  sem_triple (triv_ctx main.main) (AS_base [::] (PeriodEntry m n))
    period_validation
    (AS_base [:: T_const (VAL_int32 (wasm_bool (period_bad m n)))] (PeriodEntry m n)).
Proof.
  move=> Hm Hn.
  have Hone : word 1 by unfold word, i64_min, i64_max; lia.
  have HM : word M by unfold word, i64_min, i64_max, M; lia.
  rewrite /period_validation /main.crt_period /period_bad /=.
  apply: (sem_seq
    (es1 := [:: BI_local_get 0%num; BI_const_num (main.Vi64 1);
      BI_relop T_i64 (Relop_i (ROI_lt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (m <? 1)))] (PeriodEntry m n))).
  { rewrite -(crt_public_lt Hm Hone). apply: test_pin_const;
      [rewrite /PeriodEntry; pinned_tac | by [] | by [] | by []]. }
  apply: (sem_seq
    (es1 := [:: BI_if (BT_valtype (Some (T_num T_i32))) [:: BI_const_num (main.Vi32 1)]
      [:: BI_local_get 0%num; BI_const_num (main.Vi64 M); BI_relop T_i64 (Relop_i (ROI_gt SX_S))]])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool ((m <? 1) || (M <? m))))] (PeriodEntry m n))).
  { apply: crt_or_sem. rewrite -(crt_public_gt Hm HM). apply: test_pin_const;
      [rewrite /PeriodEntry; pinned_tac | by [] | by [] | by []]. }
  apply: (sem_seq
    (es1 := [:: BI_if (BT_valtype (Some (T_num T_i32))) [:: BI_const_num (main.Vi32 1)]
      [:: BI_local_get 1%num; BI_const_num (main.Vi64 1); BI_relop T_i64 (Relop_i (ROI_lt SX_S))]])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool ((m <? 1) || (M <? m) || (n <? 1))))] (PeriodEntry m n))).
  { apply: crt_or_sem. rewrite -(crt_public_lt Hn Hone). apply: test_pin_const;
      [rewrite /PeriodEntry; pinned_tac | by [] | by [] | by []]. }
  apply: crt_or_sem. rewrite -(crt_public_gt Hn HM). apply: test_pin_const;
    [rewrite /PeriodEntry; pinned_tac | by [] | by [] | by []].
Qed.

Lemma period_bad_spec m n : period_bad m n = negb (crt_moduli_b m n).
Proof.
  have Hlt : forall x y, (x <? y) = negb (y <=? x).
  { move=> x y. case E: (x <? y); case F: (y <=? x); try reflexivity.
    - apply Z.ltb_lt in E. apply Z.leb_le in F. lia.
    - apply Z.ltb_ge in E. apply Z.leb_gt in F. lia. }
  rewrite /period_bad /crt_moduli_b !Hlt.
  by case: (1 <=? m); case: (m <=? M); case: (1 <=? n); case: (n <=? M).
Qed.

Definition period_reject :=
  [:: BI_const_num (main.Vi64 (-2)); BI_return].

Lemma period_valid_prefix_sem m n : moduli m n ->
  sem_triple (triv_ctx main.main) (AS_base [::] (PeriodEntry m n))
    (period_validation ++ [:: BI_if (BT_valtype None) period_reject [::]])
    (AS_base [::] (PeriodEntry m n)).
Proof.
  move=> Hmn. have [Hm Hn] := Hmn.
  have Hb : period_bad m n = false.
  { rewrite period_bad_spec (proj2 (crt_moduli_b_spec m n) Hmn). by []. }
  apply: (sem_seq (Q := AS_base [:: T_const (VAL_int32 (wasm_bool false))] (PeriodEntry m n))).
  - rewrite -Hb. apply: period_validation_sem; exact: crt_modulus_word.
  - apply: guard_if_false. exact: sem_nil_same.
Qed.

Lemma period_invalid_body_sem m n Qn Qb : word m -> word n ->
  crt_moduli_b m n = false ->
  sem_mx (triv_ctx main.main) (AS_base [::] (PeriodEntry m n))
    (modfunc_body main.crt_period)
    Qn (AS_base [:: T_const (main.Vi64 (-2))] HA_true) Qb.
Proof.
  move=> Hm Hn Hbad.
  have Hb : period_bad m n = true by rewrite period_bad_spec Hbad.
  change (sem_mx (triv_ctx main.main) (AS_base [::] (PeriodEntry m n))
    (period_validation ++ [:: BI_if (BT_valtype None) period_reject [::]] ++
      List.skipn 7 (modfunc_body main.crt_period))
    Qn (AS_base [:: T_const (main.Vi64 (-2))] HA_true) Qb).
  apply: (sem_mx_seq (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool true))] (PeriodEntry m n))).
  - apply: sem_mx_lift. rewrite -Hb. exact: period_validation_sem.
  - apply: (sem_mx_seq (Q1 := AS_base [::] HA_false)).
    + apply: crt_if_true_returns.
      apply: (sem_mx_seq (es1 := [:: BI_const_num (main.Vi64 (-2))])
        (Q1 := AS_base [:: T_const (main.Vi64 (-2))] HA_true)).
      * apply: sem_mx_lift.
        apply: (sem_conseq (P' := AS_base [::] HA_true)
          (Q' := AS_base [:: T_const (main.Vi64 (-2))] HA_true)).
        -- move=> V [vs h] /= [Hs _]. by split.
        -- by [].
        -- exact: sem_const_framed.
      * exact: sem_mx_return_suffix.
    + apply: sem_mx_lift. exact: sem_false.
Qed.

(* Shared-runtime sequencing. The resource-free store theorem is what permits
   a verified native call to be followed by another verified computation in
   the same runtime. *)
Definition crt_runtime_triple P es Q :=
  forall f, f_inst f = crt_inst -> sem_triple_at crt_store f P es Q.
Definition crt_runtime_mx P es Qn Qr Qb :=
  forall f, f_inst f = crt_inst -> sem_mx_at crt_store f P es Qn Qr Qb.

Lemma crt_runtime_triple_of_triple P es Q :
  sem_triple (triv_ctx main.main) P es Q -> crt_runtime_triple P es Q.
Proof.
  move=> H f Hinst. apply: sem_triple_at_of_triple; first exact H.
  by rewrite /frame_agrees Hinst /crt_inst /triv_ctx.
Qed.

Lemma crt_runtime_mx_of_mx P es Qn Qr Qb :
  sem_mx (triv_ctx main.main) P es Qn Qr Qb -> crt_runtime_mx P es Qn Qr Qb.
Proof.
  move=> H f Hinst. apply: sem_mx_at_of_mx; first exact H.
  by rewrite /frame_agrees Hinst /crt_inst /triv_ctx.
Qed.

Lemma crt_runtime_mx_after_triple P Q1 Qn Qr Qb es1 es2 :
  crt_runtime_triple P es1 Q1 -> crt_runtime_mx Q1 es2 Qn Qr Qb ->
  crt_runtime_mx P (es1 ++ es2) Qn Qr Qb.
Proof.
  move=> H1 H2 f Hinst hs V vs h HP Hr.
  have [s1 [f1 [V1 [vs1 [h1 [Hrig1 [Hred1 [HQ1 Hr1]]]]]]]] :=
    H1 f Hinst hs V vs h HP Hr.
  have Hstore : s1 = crt_store :=
    crt_reduce_trans_preserves_resource_free_store crt_store_resource_free Hred1.
  subst s1.
  have Hinst1 : f_inst f1 = crt_inst.
  { by rewrite (reduce_trans_frame_inst Hred1) Hinst. }
  have [s2 [f2 [V2 [vs2 [h2 [Hrig2 [Hr2 Hd2]]]]]]] :=
    H2 f1 Hinst1 hs V1 vs1 h1 HQ1 Hr1.
  have Hsuffix := reduce_trans_suffix (to_e_list es2) Hred1.
  exists s2, f2, V2, vs2, h2.
  split; first by rewrite Hrig2 Hrig1. split; first exact Hr2.
  have Hcompose : forall X,
      reduce_trans (hs, crt_store, f1, vn_to_e vs1 ++ to_e_list es2) X ->
      reduce_trans (hs, crt_store, f, vn_to_e vs ++ to_e_list (es1 ++ es2)) X.
  { move=> X HX. apply: (rtt_trans (y := (hs, crt_store, f1, vn_to_e vs1 ++ to_e_list es2))).
    - rewrite to_e_list_cat catA. exact Hsuffix.
    - exact HX. }
  case: Hd2 => [[Hred2 HQ2]|[[i2 [lh2 [Hred2 HQ2]]]|[rest2 [Hred2 HQ2]]]].
  - left. by split; [apply: Hcompose |].
  - right; left. exists i2, lh2. by split; [apply: Hcompose |].
  - right; right. exists rest2. by split; [apply: Hcompose |].
Qed.

Lemma period_entry_entails m n :
  aentails (AS_base [::] (HA_and (args_pinned [:: main.Vi64 m; main.Vi64 n] 0%num)
    (func_pre_h main.main main.crt_period))) (AS_base [::] (PeriodEntry m n)).
Proof.
  move=> V [vs h] /= [Hs [[P0 [P1 _]] [[T0 [T1 _]] [T2 [T3 [T4 [T5 _]]]]]]].
  split; first exact Hs.
  split; first by case: T2 => [w [Ew _]]; exists w.
  split; first by case: T3 => [w [Ew _]]; exists w.
  split; first by case: T4 => [w [Ew _]]; exists w.
  split; first by case: T5 => [w [Ew _]]; exists w.
  by split.
Qed.

Theorem period_invalid_machine_computes m n : word m -> word n ->
  crt_moduli_b m n = false ->
  fun_computes main.main 3%nat [:: main.Vi64 m; main.Vi64 n] [:: main.Vi64 (-2)].
Proof.
  move=> Hm Hn Hbad.
  prepare_fun_computes
    (AS_base [::] (PeriodEntry m n))
    (AS_base [:: T_const (main.Vi64 (-2))] HA_true).
  - exact: period_entry_entails.
  - exact: period_invalid_body_sem.
Qed.

Lemma period_body_to_computation m n r :
  crt_runtime_mx (AS_base [::] (PeriodEntry m n)) (modfunc_body main.crt_period)
    (AS_base [:: T_const (main.Vi64 r)] HA_true)
    (AS_base [:: T_const (main.Vi64 r)] HA_true)
    (AS_base [:: T_const (main.Vi64 r)] HA_true) ->
  fun_computes_at crt_runtime 3%nat [:: main.Vi64 m; main.Vi64 n] [:: main.Vi64 r].
Proof.
  move=> Hbody.
  change (args_typed [:: main.Vi64 m; main.Vi64 n] [:: T_num T_i64; T_num T_i64] /\
    results_typed [:: main.Vi64 r] [:: T_num T_i64] /\
    exists defaults, default_vals (modfunc_locals main.crt_period) = Some defaults /\
      sem_mx_at crt_store (activation_frame crt_runtime [:: main.Vi64 m; main.Vi64 n] defaults)
        (AS_base [::] (HA_and (args_pinned [:: main.Vi64 m; main.Vi64 n] 0%num)
          (func_pre_h main.main main.crt_period)))
        (modfunc_body main.crt_period)
        (AS_base [:: T_const (main.Vi64 r)] HA_true)
        (AS_base [:: T_const (main.Vi64 r)] HA_true)
        (AS_base [:: T_const (main.Vi64 r)] HA_true)).
  split; first by repeat split. split; first by repeat split.
  exists [:: VAL_num (main.Vi64 0); VAL_num (main.Vi64 0);
    VAL_num (main.Vi64 0); VAL_num (main.Vi64 0)].
  split; first by [].
  move=> hs V vs h HP Hr. apply: Hbody; [by [] | | exact Hr].
  exact: (period_entry_entails HP).
Qed.

Theorem period_machine_computes m n : word m -> word n ->
  fun_computes_at crt_runtime 3%nat [:: main.Vi64 m; main.Vi64 n]
    [:: main.Vi64 (crt_period_Z m n)].
Proof.
  move=> Hm Hn. rewrite /crt_period_Z.
  case Hvalid: (crt_moduli_b m n).
  - have Hmn := proj1 (crt_moduli_b_spec m n) Hvalid.
    apply: period_body_to_computation.
    change (crt_runtime_mx (AS_base [::] (PeriodEntry m n))
      ((period_validation ++ [:: BI_if (BT_valtype None) period_reject [::]]) ++
       [:: BI_local_get 0%num; BI_local_get 1%num; BI_call 0%num; BI_local_set 2%num] ++ period_tail)
      (AS_base [:: T_const (main.Vi64 (period m n))] HA_true)
      (AS_base [:: T_const (main.Vi64 (period m n))] HA_true)
      (AS_base [:: T_const (main.Vi64 (period m n))] HA_true)).
    apply: (crt_runtime_mx_after_triple (Q1 := AS_base [::] (PeriodEntry m n))).
    + apply: crt_runtime_triple_of_triple. exact: period_valid_prefix_sem.
    + apply: (crt_runtime_mx_after_triple (es1 := [:: BI_local_get 0%num])
        (Q1 := AS_base [:: T_const (main.Vi64 m)] (PeriodEntry m n))).
      * apply: crt_runtime_triple_of_triple. apply: get_pinned_frame.
        rewrite /PeriodEntry. pinned_tac.
      * apply: (crt_runtime_mx_after_triple (es1 := [:: BI_local_get 1%num])
          (Q1 := AS_base [:: T_const (main.Vi64 m); T_const (main.Vi64 n)] (PeriodEntry m n))).
        -- apply: crt_runtime_triple_of_triple. apply: get_pinned_frame.
           rewrite /PeriodEntry. pinned_tac.
        -- apply: (crt_runtime_mx_after_triple (es1 := [:: BI_call 0%num])
             (Q1 := AS_base [:: T_const (main.Vi64 (Z.gcd m n))] (PeriodEntry m n))).
           ++ move=> f Hinst. exact: (crt_gcd_call Hinst Hmn).
           ++ apply: (crt_runtime_mx_after_triple (es1 := [:: BI_local_set 2%num])
                (Q1 := AS_base [::] (PeriodReady m n))).
              ** apply: crt_runtime_triple_of_triple. apply: sem_local_set_const_frame;
                   rewrite /PeriodEntry; [stable_tac | present_tac].
              ** apply: crt_runtime_mx_of_mx. exact: period_tail_sem.
  - apply: fun_computes_at_of_computes; last exact: period_invalid_machine_computes.
    exists main.crt_period. eexists. split; reflexivity.
Qed.

Theorem period_machine_computes_i64 (m n : i64) :
  fun_computes_at crt_runtime 3%nat [:: VAL_int64 m; VAL_int64 n]
    [:: main.Vi64 (crt_period_Z (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n))].
Proof.
  have H := period_machine_computes (crt_contract_signed_word m) (crt_contract_signed_word n).
  change (fun_computes_at crt_runtime 3%nat
    [:: VAL_int64 (Wasm_int.Int64.repr (Wasm_int.Int64.signed m));
        VAL_int64 (Wasm_int.Int64.repr (Wasm_int.Int64.signed n))]
    [:: main.Vi64 (crt_period_Z (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n))]) in H.
  by rewrite !Wasm_int.Int64.repr_signed in H.
Qed.

End Host.

Print Assumptions period_product_sem.
Print Assumptions period_mul_check_sem.
Print Assumptions period_tail_sem.
Print Assumptions period_machine_computes.
Print Assumptions period_machine_computes_i64.
