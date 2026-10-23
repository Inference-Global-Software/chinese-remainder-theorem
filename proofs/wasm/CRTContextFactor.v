(* A nonconstant reduction hole contains the active escape instruction. *)
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties.
From CRTWasm Require Import CRTExecutionContexts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Lemma crt_lfill_escape_factor k (lh : lholed k) :
  forall j (outer : lholed j) es escape,
  ~ const_list es -> ~ lfill_ctx_instr escape ->
  lfill lh es = lfill outer [:: escape] ->
  exists d (inner : lholed d), j = Nat.add k d /\ es = lfill inner [:: escape].
Proof.
  induction lh as [pre post | k pre n cont lh IH post];
    intros j outer es escape Hnon Hescape HE.
  - destruct (split_vals_e es) as [vs tail] eqn:Hsplit.
    have Hshape := split_vals_inv Hsplit.
    destruct tail as [| e tail].
    { rewrite cats0 in Hshape. subst es. exfalso. apply Hnon. apply v_to_e_const. }
    have He := split_vals_nconst Hsplit.
    rewrite Hshape in HE.
    destruct outer as [pre' post' | j pre' n' cont' inner post']; simpl in HE.
    + rewrite -!catA in HE.
      rewrite (catA (v_to_e_list pre) (v_to_e_list vs)) in HE.
      have Hprefix : const_list (v_to_e_list pre ++ v_to_e_list vs).
      { apply const_list_concat; apply v_to_e_const. }
      destruct (crt_const_prefix_split Hprefix (v_to_e_const pre') He
        (crt_escape_nonconst Hescape) HE) as [_ [Heq _]].
      subst e. exists 0%nat, (LH_base vs tail). split; [reflexivity | exact Hshape].
    + rewrite -!catA in HE.
      rewrite (catA (v_to_e_list pre) (v_to_e_list vs)) in HE.
      have Hprefix : const_list (v_to_e_list pre ++ v_to_e_list vs).
      { apply const_list_concat; apply v_to_e_const. }
      destruct (crt_const_prefix_split Hprefix (v_to_e_const pre') He
        (e2 := AI_label n' cont' (lfill inner [:: escape])) ltac:(discriminate) HE)
        as [_ [Heq _]].
      subst e. exists (S j), (LH_rec vs n' cont' inner tail).
      split; [reflexivity | exact Hshape].
  - destruct outer as [pre' post' | j pre' n' cont' outer post']; simpl in HE.
    + destruct (crt_const_prefix_split (v_to_e_const pre) (v_to_e_const pre')
        (e1 := AI_label n cont (lfill lh es)) ltac:(discriminate)
        (crt_escape_nonconst Hescape) HE) as [_ [Hbad _]].
      subst escape. exfalso. apply Hescape. reflexivity.
    + destruct (crt_const_prefix_split (v_to_e_const pre) (v_to_e_const pre')
        (e1 := AI_label n cont (lfill lh es)) ltac:(discriminate)
        (e2 := AI_label n' cont' (lfill outer [:: escape])) ltac:(discriminate) HE)
        as [_ [Hlabels _]].
      injection Hlabels as Hn Hcont Hbody.
      destruct (IH _ outer es escape Hnon Hescape Hbody) as [d [inner [Hdepth Hfill]]].
      exists d, inner. split; [simpl; now rewrite Hdepth | exact Hfill].
Qed.

End Host.

Print Assumptions crt_lfill_escape_factor.
