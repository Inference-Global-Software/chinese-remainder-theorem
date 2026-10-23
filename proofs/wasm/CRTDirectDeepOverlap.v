(* A direct control contraction has no competing reduction in its body. *)
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties.
From CRTWasm Require Import CRTExecutionContexts CRTExecutionEscapes
  CRTSimpleDeterminism CRTDirectDeterminism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Lemma crt_pending_values_stuck hs s f k (lh : lholed k) vs e hs' s' f' es' :
  const_list vs -> crt_pending_escape e k ->
  ~ reduce hs s f (lfill lh (vs ++ [::e])) hs' s' f' es'.
Proof.
  intros Hv He Hred.
  destruct (const_es_exists Hv) as [vals E].
  rewrite (lfill_push_base_vs lh [::e] E) in Hred.
  exact (crt_reduce_pending_stuck Hred erefl He).
Qed.

Lemma crt_simple_label_no_inner hs s f n cont body es' hs' s' f' body' :
  reduce_simple [::AI_label n cont body] es' ->
  ~ reduce hs s f body hs' s' f' body'.
Proof.
  intros Hsimple Hinner. inversion Hsimple; subst; clear Hsimple.
  - apply (crt_reduce_nonconstant Hinner); assumption.
  - exact (crt_reduce_trap_irreducible Hinner erefl).
  - eapply crt_pending_values_stuck; [eassumption | constructor; apply N.le_refl | exact Hinner].
  - match goal with HE : lfill ?lh [::AI_trap] = _ |- _ =>
      have Hin := crt_lfill0_trap_present lh erefl;
      rewrite HE in Hin; simpl in Hin; intuition discriminate end.
Qed.

Lemma crt_simple_frame_no_inner hs s f n inner body es' hs' s' f' body' :
  reduce_simple [::AI_frame n inner body] es' ->
  ~ reduce hs s f body hs' s' f' body'.
Proof.
  intros Hsimple Hinner. inversion Hsimple; subst; clear Hsimple.
  - apply (crt_reduce_nonconstant Hinner); assumption.
  - exact (crt_reduce_trap_irreducible Hinner erefl).
  - eapply crt_pending_values_stuck; [eassumption | constructor | exact Hinner].
  - match goal with HE : lfill ?lh [::AI_trap] = _ |- _ =>
      have Hin := crt_lfill0_trap_present lh erefl;
      rewrite HE in Hin; simpl in Hin; intuition discriminate end.
Qed.

Lemma crt_direct_label_no_inner hs s f n cont body hs1 s1 f1 es1 hs2 s2 f2 body2 :
  crt_direct_reduce hs s f [::AI_label n cont body] hs1 s1 f1 es1 ->
  ~ reduce hs s f body hs2 s2 f2 body2.
Proof.
  intros Hdirect Hinner. inversion Hdirect; subst; clear Hdirect;
    try match goal with HE : _ ++ [::_] = [::_] |- _ =>
      apply extract_list1 in HE as [? HE]; discriminate HE end.
  eapply crt_simple_label_no_inner; eassumption.
Qed.

Lemma crt_direct_frame_no_inner hs s f n inner body hs1 s1 f1 es1 hs2 s2 f2 body2 :
  crt_direct_reduce hs s f [::AI_frame n inner body] hs1 s1 f1 es1 ->
  ~ reduce hs s inner body hs2 s2 f2 body2.
Proof.
  intros Hdirect Hinner. inversion Hdirect; subst; clear Hdirect;
    try match goal with HE : _ ++ [::_] = [::_] |- _ =>
      apply extract_list1 in HE as [? HE]; discriminate HE end.
  - eapply crt_simple_frame_no_inner; eassumption.
  - eapply crt_pending_values_stuck; [eassumption | constructor | exact Hinner].
Qed.

Lemma crt_lfill_zero_shape k (lh : lholed k) :
  k = 0%nat -> exists pre post,
    forall es, lfill lh es = v_to_e_list pre ++ es ++ post.
Proof.
  destruct lh as [pre post | d pre n cont inner post]; intros Hk;
    try discriminate Hk.
  exists pre, post. intros; reflexivity.
Qed.

Ltac crt_deep_const_list :=
  first [assumption | apply v_to_e_const |
    solve [rewrite /const_list /= /is_const ?v2e2v; reflexivity] |
    match goal with H : ?ves = v_to_e_list ?vs |- _ =>
      rewrite H; apply v_to_e_const end |
    match goal with r : value_ref |- _ => destruct r; reflexivity end].

Ltac crt_deep_split_last src :=
  lazymatch src with
  | [::?e] => constr:((([::] : seq administrative_instruction), e))
  | ?e :: ?es =>
      let p := crt_deep_split_last es in
      lazymatch p with (?pre, ?op) => constr:(((e :: pre), op)) end
  | ?pre ++ [::?op] => constr:(((pre : seq administrative_instruction), op))
  end.

Ltac crt_deep_compare_flat Hdirect HE :=
  lazymatch type of Hdirect with
  | crt_direct_reduce _ _ _ ?src _ _ _ _ =>
    let p := crt_deep_split_last src in
    lazymatch p with (?args, ?op) =>
      lazymatch type of HE with
      | v_to_e_list ?pre ++ _ ++ ?post = v_to_e_list ?pre2 ++ ?ctrl :: ?post2 =>
        change (v_to_e_list pre ++ (args ++ [::op]) ++ post =
          v_to_e_list pre2 ++ ctrl :: post2) in HE;
        rewrite -!catA (catA (v_to_e_list pre) args) in HE;
        let Hargs := fresh "Hargs" in
        assert (Hargs : const_list args) by crt_deep_const_list;
        let HP := fresh "HP" in
        assert (HP : const_list (v_to_e_list pre ++ args))
          by (apply const_list_concat; [apply v_to_e_const | exact Hargs]);
        let Hop := fresh "Hop" in
        destruct (crt_const_prefix_split (e1 := op) (e2 := ctrl)
          HP (v_to_e_const pre2) ltac:(discriminate) ltac:(discriminate) HE)
          as [_ [Hop _]];
        inversion Hop; subst; clear Hop
      end
    end
  end.

Ltac crt_deep_trap_contradiction HE :=
  match goal with HT : lfill ?lh [::AI_trap] = ?es |- _ =>
    let p := fresh "p" in let q := fresh "q" in
    let Hshape := fresh "Hshape" in
    destruct (crt_lfill_zero_shape lh erefl) as [p [q Hshape]];
    rewrite -(HT) Hshape in HE;
    rewrite -!catA in HE;
    match type of HE with
    | v_to_e_list ?pre ++ v_to_e_list ?pre0 ++ _ = v_to_e_list ?pre2 ++ ?ctrl :: ?post2 =>
      rewrite (catA (v_to_e_list pre) (v_to_e_list pre0)) in HE;
      let HP := fresh "HP" in let Hop := fresh "Hop" in
      assert (HP : const_list (v_to_e_list pre ++ v_to_e_list pre0))
        by (apply const_list_concat; apply v_to_e_const);
      destruct (crt_const_prefix_split (e1 := AI_trap) (e2 := ctrl)
        HP (v_to_e_const pre2) ltac:(discriminate) ltac:(discriminate) HE)
        as [_ [Hop _]];
      discriminate Hop
    end
  end.

Lemma crt_direct_flat_label_no_inner hs s f es hs1 s1 f1 es1
    pre post pre2 n cont body post2 hs2 s2 f2 body2 :
  crt_direct_reduce hs s f es hs1 s1 f1 es1 ->
  v_to_e_list pre ++ es ++ post = v_to_e_list pre2 ++ AI_label n cont body :: post2 ->
  ~ reduce hs s f body hs2 s2 f2 body2.
Proof.
  intros Hdirect HE Hinner. pose proof Hdirect as Hkeep.
  destruct Hdirect.
  all: try crt_deep_compare_flat Hkeep HE.
  all: try solve [eapply crt_direct_label_no_inner; [exact Hkeep | exact Hinner]].
  all: try match goal with HS : reduce_simple _ _ |- _ => destruct HS end.
  all: try crt_deep_compare_flat Hkeep HE.
  all: try solve [eapply crt_direct_label_no_inner; [exact Hkeep | exact Hinner]].
  all: crt_deep_trap_contradiction HE.
Qed.

Lemma crt_direct_flat_frame_no_inner hs s f es hs1 s1 f1 es1
    pre post pre2 n inner body post2 hs2 s2 f2 body2 :
  crt_direct_reduce hs s f es hs1 s1 f1 es1 ->
  v_to_e_list pre ++ es ++ post = v_to_e_list pre2 ++ AI_frame n inner body :: post2 ->
  ~ reduce hs s inner body hs2 s2 f2 body2.
Proof.
  intros Hdirect HE Hinner. pose proof Hdirect as Hkeep.
  destruct Hdirect.
  all: try crt_deep_compare_flat Hkeep HE.
  all: try solve [eapply crt_direct_frame_no_inner; [exact Hkeep | exact Hinner]].
  all: try match goal with HS : reduce_simple _ _ |- _ => destruct HS end.
  all: try crt_deep_compare_flat Hkeep HE.
  all: try solve [eapply crt_direct_frame_no_inner; [exact Hkeep | exact Hinner]].
  all: crt_deep_trap_contradiction HE.
Qed.

End Host.

Print Assumptions crt_direct_frame_no_inner.
