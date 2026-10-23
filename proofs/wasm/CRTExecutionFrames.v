(* Observable host-state preservation for the actual CRT runtime. *)
From Coq Require Import List Relations.Relation_Operators.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host.
From CRTWasm Require Import CRTStorePure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Theorem crt_reduce_preserves_host_state hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  crt_resource_free_native_store s -> hs' = hs.
Proof.
  move=> Hred. induction Hred; intros Hpure; try reflexivity;
    try (apply IHHred; exact Hpure).
  all: subst cl; exfalso; exact (crt_no_host_function Hpure H).
Qed.

Definition crt_cfg_host
    (c : host_state * store_record * frame * seq administrative_instruction)
    : host_state := let '(hs, _, _, _) := c in hs.

Theorem crt_reduce_trans_preserves_host_state hs s f es hs' s' f' es' :
  crt_resource_free_native_store s ->
  reduce_trans (hs, s, f, es) (hs', s', f', es') -> hs' = hs.
Proof.
  move=> Hpure Hred.
  have Hgeneral : forall c c', reduce_trans c c' ->
      crt_resource_free_native_store (crt_cfg_store c) ->
      crt_cfg_host c' = crt_cfg_host c.
  { intros c c' HR. induction HR; intros HP.
    - destruct x as [[[hs0 s0] f0] es0].
      destruct y as [[[hs1 s1] f1] es1].
      exact (crt_reduce_preserves_host_state H HP).
    - reflexivity.
    - have HE : crt_cfg_store y = crt_cfg_store x.
      { destruct x as [[[hs0 s0] f0] es0].
        destruct y as [[[hs1 s1] f1] es1].
        exact (crt_reduce_trans_preserves_resource_free_store HP HR1). }
      have HM : crt_resource_free_native_store (crt_cfg_store y).
      { rewrite HE. exact HP. }
      rewrite (IHHR2 HM). exact (IHHR1 HP). }
  exact (Hgeneral _ _ Hred Hpure).
Qed.

End Host.

Print Assumptions crt_reduce_preserves_host_state.
Print Assumptions crt_reduce_trans_preserves_host_state.
