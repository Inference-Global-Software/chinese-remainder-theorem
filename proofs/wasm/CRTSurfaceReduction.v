(* Normalize arbitrary Wasm evaluation contexts at their outer active instruction. *)
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties contexts.
From CRTWasm Require Import CRTDirectDeterminism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Inductive crt_surface_reduce : host_state -> store_record -> frame -> seq administrative_instruction ->
    host_state -> store_record -> frame -> seq administrative_instruction -> Prop :=
| csr_direct hs s f es hs' s' f' es' pre post :
    crt_direct_reduce hs s f es hs' s' f' es' ->
    crt_surface_reduce hs s f (v_to_e_list pre ++ es ++ post)
      hs' s' f' (v_to_e_list pre ++ es' ++ post)
| csr_label hs s f body hs' s' f' body' pre n cont post :
    reduce hs s f body hs' s' f' body' ->
    crt_surface_reduce hs s f (v_to_e_list pre ++ AI_label n cont body :: post)
      hs' s' f' (v_to_e_list pre ++ AI_label n cont body' :: post)
| csr_frame hs s inner body hs' s' inner' body' pre n caller post :
    reduce hs s inner body hs' s' inner' body' ->
    crt_surface_reduce hs s caller (v_to_e_list pre ++ AI_frame n inner body :: post)
      hs' s' caller (v_to_e_list pre ++ AI_frame n inner' body' :: post).

Lemma crt_surface_direct hs s f es hs' s' f' es' :
  crt_direct_reduce hs s f es hs' s' f' es' ->
  crt_surface_reduce hs s f es hs' s' f' es'.
Proof.
  intro H. have HR := csr_direct [::] [::] H.
  by rewrite /= !cats0 in HR.
Qed.

Lemma crt_surface_frame hs s inner body hs' s' inner' body' n caller :
  reduce hs s inner body hs' s' inner' body' ->
  crt_surface_reduce hs s caller [::AI_frame n inner body]
    hs' s' caller [::AI_frame n inner' body'].
Proof. intro H. exact (csr_frame [::] n caller [::] H). Qed.

Lemma crt_surface_sequence hs s f es hs' s' f' es' pre post :
  crt_surface_reduce hs s f es hs' s' f' es' ->
  crt_surface_reduce hs s f (v_to_e_list pre ++ es ++ post)
    hs' s' f' (v_to_e_list pre ++ es' ++ post).
Proof.
  intro H. destruct H.
  - have HR := csr_direct (pre ++ pre0) (post0 ++ post) H.
    by rewrite -v_to_e_cat -!catA in HR *.
  - have HR := csr_label (pre ++ pre0) n cont (post0 ++ post) H.
    by rewrite -v_to_e_cat -!catA in HR *.
  - have HR := csr_frame (pre ++ pre0) n caller (post0 ++ post) H.
    by rewrite -v_to_e_cat -!catA in HR *.
Qed.

Lemma crt_surface_label_context hs s f es hs' s' f' es' k (lh : lholed k) :
  reduce hs s f es hs' s' f' es' ->
  crt_surface_reduce hs s f es hs' s' f' es' ->
  crt_surface_reduce hs s f (lfill lh es) hs' s' f' (lfill lh es').
Proof.
  intros Hred Hsurface. destruct lh as [pre post | d pre n cont inner post].
  - exact (crt_surface_sequence pre post Hsurface).
  - simpl. apply csr_label.
    eapply r_label; [exact Hred | reflexivity | reflexivity].
Qed.

Local Hint Constructors crt_direct_reduce : crt_direct.

Theorem crt_reduce_surface hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  crt_surface_reduce hs s f es hs' s' f' es'.
Proof.
  intro H. induction H;
    try solve [apply crt_surface_direct; eauto 2 with crt_direct].
  - subst les les'. exact (crt_surface_label_context lh H IHreduce).
  - exact (crt_surface_frame n f0 H).
Qed.

Lemma crt_surface_sound hs s f es hs' s' f' es' :
  crt_surface_reduce hs s f es hs' s' f' es' ->
  reduce hs s f es hs' s' f' es'.
Proof.
  intro H. destruct H.
  - eapply r_label with (lh := LH_base pre post); try reflexivity.
    exact (crt_direct_reduce_sound H).
  - eapply r_label with (lh := LH_rec pre n cont (LH_base [::] [::]) post);
      simpl; rewrite ?cats0; [exact H | reflexivity | reflexivity].
  - eapply r_label with (lh := LH_base pre post); try reflexivity.
    + exact (r_frame n caller H).
    + reflexivity.
    + reflexivity.
Qed.

End Host.

Print Assumptions crt_reduce_surface.
