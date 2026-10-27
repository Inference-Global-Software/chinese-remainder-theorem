(* Lift the primitive diamond through arbitrary nested labels and frames. *)
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties contexts.
From CRTWasm Require Import CRTStorePure CRTExecutionContexts CRTDirectDeterminism
  CRTDirectDeepOverlap CRTSurfaceReduction CRTConfluence.
From CRTSystems Require Import ReadOnly ReadOnlyFlatJoin.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Definition crt_label_cfg pre n cont post
    (cfg : host_state * store_record * frame * seq administrative_instruction) :=
  let '(hs, s, f, es) := cfg in
  (hs, s, f, v_to_e_list pre ++ AI_label n cont es :: post).

Definition crt_frame_cfg pre n (caller : frame) post
    (cfg : host_state * store_record * frame * seq administrative_instruction) :=
  let '(hs, s, inner, es) := cfg in
  (hs, s, caller, v_to_e_list pre ++ AI_frame n inner es :: post).

Lemma crt_label_step_or_same pre n cont post x y :
  crt_step_or_same reduce_tuple x y ->
  crt_step_or_same reduce_tuple (crt_label_cfg pre n cont post x)
    (crt_label_cfg pre n cont post y).
Proof.
  intros [-> | Hstep]; [left; reflexivity | right].
  destruct x as [[[hs s] f] es], y as [[[hs' s'] f'] es'].
  simpl in *. apply crt_surface_sound. exact (csr_label pre n cont post Hstep).
Qed.

Lemma crt_frame_step_or_same pre n caller post x y :
  crt_step_or_same reduce_tuple x y ->
  crt_step_or_same reduce_tuple (crt_frame_cfg pre n caller post x)
    (crt_frame_cfg pre n caller post y).
Proof.
  intros [-> | Hstep]; [left; reflexivity | right].
  destruct x as [[[hs s] f] es], y as [[[hs' s'] f'] es'].
  simpl in *. apply crt_surface_sound. exact (csr_frame pre n caller post Hstep).
Qed.

Lemma ro_reduce_diamond_bounded bound :
  forall es hs s f hs1 s1 f1 es1 hs2 s2 f2 es2,
  (ais_measure es < bound)%coq_nat -> ro_store s -> ro_es es ->
  reduce hs s f es hs1 s1 f1 es1 -> reduce hs s f es hs2 s2 f2 es2 ->
  exists u, crt_step_or_same reduce_tuple (hs1, s1, f1, es1) u /\
    crt_step_or_same reduce_tuple (hs2, s2, f2, es2) u.
Proof.
  induction bound as [|bound IH]; intros es hs s f hs1 s1 f1 es1 hs2 s2 f2 es2 Hsize HP Hro H1 H2.
  { lia. }
  apply crt_reduce_surface in H1. apply crt_reduce_surface in H2.
  destruct H1; inversion H2; subst; clear H2.
  - eapply ro_direct_flat_join; [exact HP | exact (ro_es_subseq Hro) | exact H | exact H5 | symmetry; exact H0].
  all: try solve [exfalso; eapply crt_direct_flat_label_no_inner;
    [eassumption | first [eassumption | symmetry; eassumption] | eassumption]].
  all: try solve [exfalso; eapply crt_direct_flat_frame_no_inner;
    [eassumption | first [eassumption | symmetry; eassumption] | eassumption]].
  all: match goal with
  | HE : v_to_e_list ?pre1 ++ ?ctrl1 :: ?post1 = v_to_e_list ?pre2 ++ ?ctrl2 :: ?post2 |- _ =>
    have [Hv [Hctrl Hpost]] := crt_const_prefix_split
      (e1 := ctrl1) (e2 := ctrl2) (v_to_e_const pre1) (v_to_e_const pre2)
      ltac:(discriminate) ltac:(discriminate) HE;
    apply v_to_e_inj in Hv; subst; inversion Hctrl; subst; clear Hctrl
  end.
  all: assert (Hsmall : (ais_measure body < bound)%coq_nat) by
    (rewrite ais_measure_cat ais_measure_cons in Hsize;
     change (Nat.add (ais_measure (v_to_e_list pre))
      (Nat.add (S (ais_measure body)) (ais_measure post)) < S bound)%coq_nat in Hsize; lia).
  - have Hbody : ro_es body.
    { move: Hro; rewrite ro_es_cat ro_es_values /= /ro_es /=.
      by move/andP=> [/andP [_ HB] _]. }
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ Hsmall HP Hbody H H5) as [u [Hu1 Hu2]].
    exists (crt_label_cfg pre n cont post u). split.
    + exact (crt_label_step_or_same pre n cont post Hu1).
    + exact (crt_label_step_or_same pre n cont post Hu2).
  - have Hbody : ro_es body.
    { move: Hro; rewrite ro_es_cat ro_es_values /= /ro_es /=.
      by move/andP=> [HB _]. }
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ Hsmall HP Hbody H H5) as [u [Hu1 Hu2]].
    exists (crt_frame_cfg pre n f2 post u). split.
    + exact (crt_frame_step_or_same pre n f2 post Hu1).
    + exact (crt_frame_step_or_same pre n f2 post Hu2).
Qed.

Definition ro_cfg (cfg : host_state * store_record * frame * seq administrative_instruction) : Prop :=
  let '(_, s, _, es) := cfg in ro_store s /\ ro_es es.

Lemma ro_cfg_preserved x y :
  ro_cfg x -> reduce_tuple x y -> ro_cfg y.
Proof.
  destruct x as [[[hs s] f] es], y as [[[hs' s'] f'] es'].
  simpl. intros [HP Hro] Hred.
  destruct (ro_reduce_preserved Hred HP Hro) as [_ [-> Hout]]. by split.
Qed.

Theorem ro_reduce_tuple_diamond x y z :
  ro_cfg x -> reduce_tuple x y -> reduce_tuple x z ->
  exists u, crt_step_or_same reduce_tuple y u /\ crt_step_or_same reduce_tuple z u.
Proof.
  destruct x as [[[hs s] f] es], y as [[[hs1 s1] f1] es1], z as [[[hs2 s2] f2] es2].
  intros [HP Hro] H1 H2. eapply (ro_reduce_diamond_bounded (bound := S (ais_measure es)) (es := es));
    [lia | exact HP | exact Hro | exact H1 | exact H2].
Qed.

Lemma crt_values_normal hs s f vs :
  crt_normal reduce_tuple (hs, s, f, v_to_e_list vs).
Proof.
  intros [[[hs' s'] f'] es'] Hred.
  exact (crt_reduce_nonconstant Hred (v_to_e_const vs)).
Qed.

Theorem ro_reduce_trans_normal_unique hs s f es hs1 s1 f1 vs1 hs2 s2 f2 vs2 :
  ro_store s -> ro_es es ->
  reduce_trans (hs, s, f, es) (hs1, s1, f1, v_to_e_list vs1) ->
  reduce_trans (hs, s, f, es) (hs2, s2, f2, v_to_e_list vs2) -> vs1 = vs2.
Proof.
  intros HP Hro H1 H2.
  have HE : (hs1, s1, f1, v_to_e_list vs1) = (hs2, s2, f2, v_to_e_list vs2).
  { eapply (@crt_normal_results_unique _ reduce_tuple ro_cfg
      ro_cfg_preserved ro_reduce_tuple_diamond (hs, s, f, es));
      [exact (conj HP Hro) | exact H1 | exact H2 | apply crt_values_normal | apply crt_values_normal]. }
  apply v_to_e_inj. congruence.
Qed.

End Host.

