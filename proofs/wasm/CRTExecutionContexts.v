(* Operational facts about actual WasmCert reductions. *)
From Coq Require Import NArith List Relations.Relation_Operators.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties contexts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Lemma crt_lfill_const_inv k (lh : lholed k) es :
  const_list (lfill lh es) -> const_list es.
Proof.
  destruct lh; simpl; intros H.
  - apply const_list_split in H as [_ H].
    exact (proj1 (const_list_split H)).
  - apply const_list_split in H as [_ H].
    discriminate H.
Qed.

Ltac crt_const_source_contradiction H :=
  repeat match type of H with
  | is_true (const_list (_ ++ _)) =>
      apply const_list_split in H; destruct H as [? H]
  end;
  rewrite /const_list /= ?andbF ?andbT in H;
  discriminate H.

Lemma crt_reduce_simple_nonconstant es es' :
  reduce_simple es es' -> ~ const_list es.
Proof.
  intros Hred Hconst. destruct Hred;
    try (crt_const_source_contradiction Hconst).
  subst es. apply crt_lfill_const_inv in Hconst.
  discriminate Hconst.
Qed.

Lemma crt_reduce_nonconstant hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' -> ~ const_list es.
Proof.
  intros Hred. induction Hred; intros Hconst;
    try (crt_const_source_contradiction Hconst).
  - exact (crt_reduce_simple_nonconstant H Hconst).
  - subst les. apply IHHred. exact (crt_lfill_const_inv Hconst).
Qed.

Lemma crt_const_prefix_split vs1 vs2 e1 e2 es1 es2 :
  const_list vs1 -> const_list vs2 ->
  ~ is_const e1 -> ~ is_const e2 ->
  vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
  vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  intros Hvs1 Hvs2 He1 He2 H.
  destruct (const_es_exists Hvs1) as [vals1 E1].
  destruct (const_es_exists Hvs2) as [vals2 E2].
  subst vs1 vs2.
  destruct (v_to_e_split_eq He1 He2 H) as [-> [-> ->]].
  repeat split; reflexivity.
Qed.

Lemma crt_equal_length_suffix (xs ys zs ws : seq administrative_instruction) :
  xs ++ ys = zs ++ ws -> length ys = length ws -> ys = ws.
Proof.
  intros HE HL.
  apply (f_equal (@rev administrative_instruction)) in HE.
  rewrite !rev_cat in HE.
  have HL' : size (rev ys) = size (rev ws).
  { by rewrite !size_rev -!length_is_size HL. }
  have /andP [/eqP H _] := concat_cancel_first_n HE HL'.
  by apply (f_equal (@rev administrative_instruction)) in H; rewrite !revK in H.
Qed.

Lemma crt_escape_nonconst e : ~ lfill_ctx_instr e -> ~ is_const e.
Proof. destruct e; simpl; auto; intros H; exfalso; apply H; reflexivity. Qed.

Lemma crt_lfill_escape_unique k (lh : lholed k) :
  forall k' (lh' : lholed k') vs vs' e e',
  const_list vs -> const_list vs' -> length vs = length vs' ->
  ~ lfill_ctx_instr e -> ~ lfill_ctx_instr e' ->
  lfill lh (vs ++ [:: e]) = lfill lh' (vs' ++ [:: e']) ->
  vs = vs' /\ e = e' /\ k = k'.
Proof.
  induction lh as [pre post | k pre n cont lh IH post];
    intros k' lh' vs vs' e e' Hvs Hvs' Hlen He He' Hfill;
    destruct lh' as [pre' post' | k' pre' n' cont' lh' post'];
    simpl in Hfill.
  - rewrite -!catA in Hfill.
    rewrite (catA (v_to_e_list pre) vs) (catA (v_to_e_list pre') vs') in Hfill.
    have Hpre : const_list (v_to_e_list pre ++ vs).
    { apply const_list_concat; [apply v_to_e_const | exact Hvs]. }
    have Hpre' : const_list (v_to_e_list pre' ++ vs').
    { apply const_list_concat; [apply v_to_e_const | exact Hvs']. }
    destruct (crt_const_prefix_split Hpre Hpre'
      (crt_escape_nonconst He) (crt_escape_nonconst He') Hfill)
      as [Hprefix [-> _]].
    split; [exact (crt_equal_length_suffix Hprefix Hlen) | auto].
  - rewrite -!catA in Hfill.
    rewrite (catA (v_to_e_list pre) vs) in Hfill.
    have Hpre : const_list (v_to_e_list pre ++ vs).
    { apply const_list_concat; [apply v_to_e_const | exact Hvs]. }
    destruct (crt_const_prefix_split (e2 := AI_label n' cont' (lfill lh' (vs' ++ [:: e']))) Hpre (v_to_e_const pre')
      (crt_escape_nonconst He) ltac:(discriminate) Hfill)
      as [_ [HE _]].
    subst e. exfalso. apply He. reflexivity.
  - rewrite -!catA in Hfill.
    rewrite (catA (v_to_e_list pre') vs') in Hfill.
    have Hpre' : const_list (v_to_e_list pre' ++ vs').
    { apply const_list_concat; [apply v_to_e_const | exact Hvs']. }
    destruct (crt_const_prefix_split (e1 := AI_label n cont (lfill lh (vs ++ [:: e]))) (v_to_e_const pre) Hpre'
      ltac:(discriminate) (crt_escape_nonconst He') Hfill)
      as [_ [HE _]].
    subst e'. exfalso. apply He'. reflexivity.
  - destruct (v_to_e_split_eq (e1 := AI_label n cont (lfill lh (vs ++ [:: e]))) (e2 := AI_label n' cont' (lfill lh' (vs' ++ [:: e']))) ltac:(discriminate) ltac:(discriminate) Hfill)
      as [_ [HE _]].
    injection HE as Hn Hcont Hbody.
    subst n' cont'.
    destruct (IH _ lh' vs vs' e e' Hvs Hvs' Hlen He He' Hbody)
      as [-> [-> ->]].
    repeat split; reflexivity.
Qed.

Lemma crt_lfill_escape_head_unique k (lh : lholed k) k'
    (lh' : lholed k') vs vs' e e' :
  const_list vs -> const_list vs' ->
  ~ lfill_ctx_instr e -> ~ lfill_ctx_instr e' ->
  lfill lh (vs ++ [:: e]) = lfill lh' (vs' ++ [:: e']) ->
  e = e' /\ k = k'.
Proof.
  intros Hvs Hvs' He He' Hfill.
  destruct (const_es_exists Hvs) as [vals E].
  destruct (const_es_exists Hvs') as [vals' E'].
  rewrite (lfill_push_base_vs lh [::e] E)
    (lfill_push_base_vs lh' [::e'] E') in Hfill.
  have [_ H] := crt_lfill_escape_unique
    (lh := lh_push_base_vs lh vals) (lh' := lh_push_base_vs lh' vals')
    (vs := [::]) (vs' := [::]) erefl erefl erefl He He' Hfill.
  exact H.
Qed.

Lemma crt_escape_in_flat_source k (lh : lholed k) escape vs op :
  const_list vs -> ~ lfill_ctx_instr escape -> ~ lfill_ctx_instr op ->
  lfill lh [:: escape] = vs ++ [:: op] -> escape = op /\ k = 0%nat.
Proof.
  intros Hvs He Hop H.
  destruct (const_es_exists Hvs) as [vals E]. subst vs.
  apply (crt_lfill_escape_head_unique
    (lh := lh) (lh' := LH_base vals [::])
    (vs := [::]) (vs' := [::]) erefl erefl He Hop).
  simpl. exact H.
Qed.

End Host.

Print Assumptions crt_reduce_nonconstant.
