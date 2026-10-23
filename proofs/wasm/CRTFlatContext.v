(* Decomposition of a reduction context around a flat instruction. *)
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties.
From CRTWasm Require Import CRTExecutionContexts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Lemma crt_lfill_flat_nonconstant k (lh : lholed k) es vs op :
  ~ const_list es -> ~ lfill_ctx_instr op ->
  lfill lh es = v_to_e_list vs ++ [::op] ->
  exists prefix suffix,
    vs = prefix ++ suffix /\ es = v_to_e_list suffix ++ [::op] /\
    forall out, lfill lh out = v_to_e_list prefix ++ out.
Proof.
  intros Hnon Hop HE. destruct lh as [pre post | k pre n cont inner post].
  - destruct (split_vals_e es) as [vals tail] eqn:Hsplit.
    have Hshape := split_vals_inv Hsplit.
    destruct tail as [|e tail].
    { rewrite cats0 in Hshape. subst es. exfalso; apply Hnon; apply v_to_e_const. }
    have He := split_vals_nconst Hsplit.
    rewrite Hshape in HE. simpl in HE. rewrite -!catA in HE.
    rewrite (catA (v_to_e_list pre) (v_to_e_list vals)) in HE.
    have Hprefix : const_list (v_to_e_list pre ++ v_to_e_list vals).
    { apply const_list_concat; apply v_to_e_const. }
    destruct (crt_const_prefix_split Hprefix (v_to_e_const vs) He
      (crt_escape_nonconst Hop) HE) as [Hpre [Heq Htail]].
    apply List.app_eq_nil in Htail as [Htail Hpost]. subst e tail post.
    rewrite v_to_e_cat in Hpre. apply v_to_e_inj in Hpre.
    exists pre, vals. split; [symmetry; exact Hpre |].
    split; [exact Hshape | intros out; simpl; rewrite cats0; reflexivity].
  - simpl in HE.
    destruct (crt_const_prefix_split (v_to_e_const pre) (v_to_e_const vs)
      (e1 := AI_label n cont (lfill inner es)) ltac:(discriminate)
      (crt_escape_nonconst Hop) HE) as [_ [Heq _]].
    subst op. exfalso; apply Hop; reflexivity.
Qed.

Lemma crt_lfill_singleton_identity k (lh : lholed k) es op :
  ~ const_list es -> ~ lfill_ctx_instr op -> lfill lh es = [::op] ->
  es = [::op] /\ forall out, lfill lh out = out.
Proof.
  intros Hnon Hop HE.
  destruct (crt_lfill_flat_nonconstant (vs := [::]) Hnon Hop HE)
    as [pre [post [Hnil [Hes Hout]]]].
  symmetry in Hnil. apply List.app_eq_nil in Hnil as [Hpre Hpost].
  subst pre post. split; assumption.
Qed.

End Host.

Print Assumptions crt_lfill_flat_nonconstant.
