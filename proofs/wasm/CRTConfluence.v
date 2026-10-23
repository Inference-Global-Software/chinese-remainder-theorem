(* A reusable normal-result uniqueness argument. The operational proof must
   supply the one-step diamond; this file introduces no execution assumptions. *)
From Coq Require Import Relations.Relation_Operators.

Set Implicit Arguments.

Section Confluence.
Context {A : Type} (step : A -> A -> Prop) (P : A -> Prop).

Definition crt_normal (x : A) : Prop := forall y, ~ step x y.
Definition crt_step_or_same (x y : A) : Prop := x = y \/ step x y.

Lemma crt_rtc_preserves
    (preserves : forall x y, P x -> step x y -> P y) :
  forall x y, clos_refl_trans A step x y -> P x -> P y.
Proof.
  intros x y H. induction H; intro HP.
  - exact (preserves _ _ HP H).
  - exact HP.
  - apply IHclos_refl_trans2, IHclos_refl_trans1, HP.
Qed.

Lemma crt_step_or_same_rtc x y :
  crt_step_or_same x y -> clos_refl_trans A step x y.
Proof. intros [-> | H]; [apply rt_refl | apply rt_step; exact H]. Qed.

Lemma crt_normal_rtc x y :
  clos_refl_trans A step x y -> crt_normal x -> x = y.
Proof.
  intro H. induction H; intro Hnormal.
  - exfalso. exact (Hnormal _ H).
  - reflexivity.
  - specialize (IHclos_refl_trans1 Hnormal). subst y.
    exact (IHclos_refl_trans2 Hnormal).
Qed.

Hypothesis preserves : forall x y, P x -> step x y -> P y.
Hypothesis diamond : forall x y z,
  P x -> step x y -> step x z ->
  exists u, crt_step_or_same y u /\ crt_step_or_same z u.

Lemma crt_reflexive_diamond x y z :
  P x -> crt_step_or_same x y -> crt_step_or_same x z ->
  exists u, crt_step_or_same y u /\ crt_step_or_same z u.
Proof.
  intros HP [Hxy | Hxy] [Hxz | Hxz].
  - subst y z. exists x. split; left; reflexivity.
  - subst y. exists z. split; [right; exact Hxz | left; reflexivity].
  - subst z. exists y. split; [left; reflexivity | right; exact Hxy].
  - exact (@diamond x y z HP Hxy Hxz).
Qed.

Lemma crt_strip x y :
  clos_refl_trans A step x y -> P x ->
  forall z, crt_step_or_same x z ->
  exists u, crt_step_or_same y u /\ clos_refl_trans A step z u.
Proof.
  intro H. induction H; intros HP z0 Hz.
  - destruct (crt_reflexive_diamond HP (or_intror H) Hz) as [u [Hyu Hzu]].
    exists u. split; [exact Hyu | apply crt_step_or_same_rtc; exact Hzu].
  - exists z0. split; [exact Hz | apply rt_refl].
  - destruct (IHclos_refl_trans1 HP _ Hz) as [u [Hyu Hzu]].
    pose proof (crt_rtc_preserves preserves H HP) as HPy.
    destruct (IHclos_refl_trans2 HPy _ Hyu) as [v [Hzv Huv]].
    exists v. split; [exact Hzv | eapply rt_trans; eauto].
Qed.

Theorem crt_rtc_confluent x y :
  clos_refl_trans A step x y -> P x ->
  forall z, clos_refl_trans A step x z ->
  exists u, clos_refl_trans A step y u /\ clos_refl_trans A step z u.
Proof.
  intro H. induction H; intros HP z0 Hz.
  - destruct (crt_strip Hz HP (or_intror H)) as [u [Hzu Hyu]].
    exists u. split; [exact Hyu | apply crt_step_or_same_rtc; exact Hzu].
  - exists z0. split; [exact Hz | apply rt_refl].
  - destruct (IHclos_refl_trans1 HP _ Hz) as [u [Hyu Hzu]].
    pose proof (crt_rtc_preserves preserves H HP) as HPy.
    destruct (IHclos_refl_trans2 HPy _ Hyu) as [v [Hzv Huv]].
    exists v. split; [exact Hzv | eapply rt_trans; eauto].
Qed.

Theorem crt_normal_results_unique x y z :
  P x -> clos_refl_trans A step x y -> clos_refl_trans A step x z ->
  crt_normal y -> crt_normal z -> y = z.
Proof.
  intros HP Hxy Hxz Hny Hnz.
  destruct (crt_rtc_confluent Hxy HP Hxz) as [u [Hyu Hzu]].
  pose proof (crt_normal_rtc Hyu Hny) as Hy.
  pose proof (crt_normal_rtc Hzu Hnz) as Hz.
  congruence.
Qed.

End Confluence.

Print Assumptions crt_normal_results_unique.
