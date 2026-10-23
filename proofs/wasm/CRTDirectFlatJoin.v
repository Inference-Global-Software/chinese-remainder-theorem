(* Competing primitive reductions in flat evaluation contexts join in at most
   one step. Their active operations and consumed operand lists coincide,
   except that trap propagation may discard different surrounding contexts. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties.
From CRTWasm Require Import CRTStorePure CRTExecutionContexts CRTConfluence
  CRTDirectDeterminism CRTDirectShape CRTDirectTrap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Host.
Context `{ho : host}.

Lemma crt_shape_lfill0_flat k (lh : lholed k) :
  k = 0%nat -> exists pre post,
  lfill lh [::AI_trap] = v_to_e_list pre ++ AI_trap :: post.
Proof.
  destruct lh; intros HK; [|discriminate].
  exists l, l0. reflexivity.
Qed.

Lemma crt_direct_active_shape hs s f es hs' s' f' es' :
  crt_direct_reduce hs s f es hs' s' f' es' ->
  exists vs op tail, const_list vs /\ ~ is_const op /\
    es = vs ++ op :: tail /\ (tail = [::] \/ op = AI_trap).
Proof.
  intro HD. destruct (crt_direct_source_shape HD) as [[vs [op [HC [HN HE]]]] | [lh [HE HO]]].
  - exists vs, op, [::]. repeat split; auto.
  - destruct (crt_shape_lfill0_flat lh erefl) as [pre [post HF]].
    exists (v_to_e_list pre), AI_trap, post. split; [apply v_to_e_const |].
    split; [discriminate |]. split; [congruence | auto].
Qed.

Theorem crt_direct_flat_join hs s f es1 hs1 s1 f1 out1 es2 hs2 s2 f2 out2
    (pre1 pre2 : seq value) (post1 post2 : seq administrative_instruction) :
  crt_resource_free_native_store s ->
  crt_direct_reduce hs s f es1 hs1 s1 f1 out1 ->
  crt_direct_reduce hs s f es2 hs2 s2 f2 out2 ->
  v_to_e_list pre1 ++ es1 ++ post1 = v_to_e_list pre2 ++ es2 ++ post2 ->
  exists u,
    crt_step_or_same reduce_tuple (hs1,s1,f1,v_to_e_list pre1 ++ out1 ++ post1) u /\
    crt_step_or_same reduce_tuple (hs2,s2,f2,v_to_e_list pre2 ++ out2 ++ post2) u.
Proof.
  intros HP D1 D2 HE.
  destruct (crt_direct_active_shape D1) as [vs1 [op1 [tail1 [HC1 [HN1 [ES1 HT1]]]]]].
  destruct (crt_direct_active_shape D2) as [vs2 [op2 [tail2 [HC2 [HN2 [ES2 HT2]]]]]].
  have HCpre1 : const_list (v_to_e_list pre1 ++ vs1) by apply const_list_concat; [apply v_to_e_const | exact HC1].
  have HCpre2 : const_list (v_to_e_list pre2 ++ vs2) by apply const_list_concat; [apply v_to_e_const | exact HC2].
  rewrite ES1 ES2 !catA in HE.
  have HEactive : (v_to_e_list pre1 ++ vs1) ++ op1 :: (tail1 ++ post1) =
    (v_to_e_list pre2 ++ vs2) ++ op2 :: (tail2 ++ post2).
  { rewrite -!catA. rewrite -!catA in HE. exact HE. }
  destruct (crt_const_prefix_split HCpre1 HCpre2 HN1 HN2 HEactive) as [Hpre [Hop Htail]].
  subst op2.
  destruct (op1 == AI_trap) eqn:Htrap.
  - move/eqP in Htrap. subst op1.
    destruct (const_es_exists HC1) as [vals1 HV1].
    destruct (const_es_exists HC2) as [vals2 HV2].
    rewrite HV1 in ES1. rewrite HV2 in ES2.
    destruct (crt_direct_active_trap D1 ES1) as [-> [-> [-> ->]]].
    destruct (crt_direct_active_trap D2 ES2) as [-> [-> [-> ->]]].
    apply crt_flat_trap_join.
  - have Hnot : op1 <> AI_trap.
    { intro E. rewrite E eq_refl in Htrap. discriminate. }
    destruct HT1 as [-> | HC]; [|contradiction].
    destruct HT2 as [-> | HC]; [|contradiction].
    cbn in Htail. subst post2.
    have HA1 := crt_direct_source_arity D1 HC1 HN1 Hnot ES1.
    have HA2 := crt_direct_source_arity D2 HC2 HN2 Hnot ES2.
    have HL : length vs1 = length vs2 by congruence.
    have HV : vs1 = vs2 := crt_equal_length_suffix Hpre HL.
    subst vs2.
    have HEP : v_to_e_list pre1 = v_to_e_list pre2.
    { apply app_inv_tail in Hpre. exact Hpre. }
    have Hsource : es1 = es2 by congruence.
    subst es1 es2.
    have Hout := crt_direct_reduce_deterministic HP D1 D2.
    inversion Hout; subst.
    eexists. split; left; [reflexivity | by rewrite HEP].
Qed.
End Host.
Print Assumptions crt_direct_flat_join.
