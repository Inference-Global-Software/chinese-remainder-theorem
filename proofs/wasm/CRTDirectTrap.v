(* All competing flat trap collapses join at the same trapped configuration. *)
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties.
From CRTWasm Require Import CRTExecutionContexts CRTDirectDeterminism CRTConfluence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Lemma crt_trap_vref_const r : is_const (vref_to_e r) = true.
Proof. destruct r; reflexivity. Qed.

Ltac crt_trap_const_list :=
  first [assumption | apply v_to_e_const |
    solve [rewrite /const_list /= ?crt_trap_vref_const /is_const ?v2e2v; reflexivity] |
    match goal with H : ?ves = v_to_e_list ?vs |- _ =>
      rewrite H; apply v_to_e_const end].

Ltac crt_trap_split_last src :=
  lazymatch src with
  | [::?e] => constr:((([::] : seq administrative_instruction), e))
  | ?e :: ?es =>
      let p := crt_trap_split_last es in
      lazymatch p with (?pre, ?op) => constr:(((e :: pre), op)) end
  | ?pre ++ [::?op] => constr:(((pre : seq administrative_instruction), op))
  end.

Ltac crt_trap_direct_contradiction Hdirect HE :=
  lazymatch type of Hdirect with
  | crt_direct_reduce _ _ _ ?src _ _ _ _ =>
    let p := crt_trap_split_last src in
    lazymatch p with (?args, ?op) =>
      lazymatch type of HE with
      | _ = v_to_e_list ?vs ++ AI_trap :: ?post =>
        change (args ++ [::op] = v_to_e_list vs ++ AI_trap :: post) in HE;
        let Hargs := fresh "Hargs" in
        assert (Hargs : const_list args) by crt_trap_const_list;
        let Hop := fresh "Hop" in
        destruct (crt_const_prefix_split (e1 := op) (e2 := AI_trap)
          Hargs (v_to_e_const vs) ltac:(discriminate) ltac:(discriminate) HE)
          as [_ [Hop _]];
        discriminate Hop
      end
    end
  end.

Lemma crt_direct_active_trap hs s f es hs' s' f' es' pre post :
  crt_direct_reduce hs s f es hs' s' f' es' ->
  es = v_to_e_list pre ++ AI_trap :: post ->
  hs' = hs /\ s' = s /\ f' = f /\ es' = [::AI_trap].
Proof.
  intros Hdirect HE. pose proof Hdirect as Hkeep.
  destruct Hdirect.
  all: try crt_trap_direct_contradiction Hkeep HE.
  all: try match goal with HS : reduce_simple _ _ |- _ => destruct HS end.
  all: try crt_trap_direct_contradiction Hkeep HE.
  repeat split; reflexivity.
Qed.

Lemma crt_flat_trap_step_or_same hs s f pre post :
  crt_step_or_same reduce_tuple
    (hs, s, f, v_to_e_list pre ++ AI_trap :: post)
    (hs, s, f, [::AI_trap]).
Proof.
  destruct (v_to_e_list pre ++ AI_trap :: post == [::AI_trap]) eqn:HE.
  - move/eqP in HE. left. by rewrite HE.
  - right. apply r_simple. eapply rs_trap with (lh := LH_base pre post).
    + intros H. rewrite H eq_refl in HE. discriminate HE.
    + reflexivity.
Qed.

Lemma crt_flat_trap_join hs s f pre1 post1 pre2 post2 :
  exists c,
    crt_step_or_same reduce_tuple
      (hs, s, f, v_to_e_list pre1 ++ AI_trap :: post1) c /\
    crt_step_or_same reduce_tuple
      (hs, s, f, v_to_e_list pre2 ++ AI_trap :: post2) c.
Proof.
  exists (hs, s, f, [::AI_trap]); split; apply crt_flat_trap_step_or_same.
Qed.

End Host.

Print Assumptions crt_direct_active_trap.
Print Assumptions crt_flat_trap_join.
