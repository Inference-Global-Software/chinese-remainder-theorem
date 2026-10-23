(* Inversion of actual call reductions, including contextual derivations. *)
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties.
From CRTWasm Require Import CRTExecutionContexts CRTFlatContext CRTStorePure CRTResourceReads.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Lemma crt_simple_call_stuck i es' :
  ~ reduce_simple [::AI_basic (BI_call i)] es'.
Proof.
  intros Hred. inversion Hred; subst; clear Hred.
  have [HE _] := crt_lfill_singleton_identity (lh := lh)
    (es := [::AI_trap]) (op := AI_basic (BI_call i))
    ltac:(discriminate) ltac:(discriminate) H0.
  discriminate HE.
Qed.

Lemma crt_reduce_call_inv hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  forall i, es = [::AI_basic (BI_call i)] ->
  exists a, lookup_N (inst_funcs (f_inst f)) i = Some a /\
    hs' = hs /\ s' = s /\ f' = f /\ es' = [::AI_invoke a].
Proof.
  intros Hred. induction Hred; intros index HE; try discriminate HE.
  - subst e. exfalso. exact (crt_simple_call_stuck H).
  all: try (apply extract_list1 in HE as [Hpre Hlast]; discriminate Hlast).
  - inversion HE; subst. exists a. repeat split; assumption.
  - have Hfill : lfill lh es = [::AI_basic (BI_call index)] by congruence.
    have [Hes Hout] := crt_lfill_singleton_identity
      (op := AI_basic (BI_call index)) (crt_reduce_nonconstant Hred) ltac:(discriminate) Hfill.
    destruct (IHHred _ Hes) as [a [Ha [Hhs [Hs [Hf Hresult]]]]].
    exists a. repeat split; try assumption. rewrite -H0 Hout. exact Hresult.
Qed.

Ltac crt_call_split_last src :=
  lazymatch src with
  | [::?e] => constr:((([::] : seq administrative_instruction), e))
  | ?e :: ?es =>
      let p := crt_call_split_last es in
      lazymatch p with (?pre, ?op) => constr:(((e :: pre), op)) end
  | ?pre ++ [::?op] => constr:(((pre : seq administrative_instruction), op))
  end.

Ltac crt_call_sources HE :=
  lazymatch type of HE with
  | @eq (seq administrative_instruction) ?src1 ?src2 =>
    let p1 := crt_call_split_last src1 in
    let p2 := crt_call_split_last src2 in
    lazymatch p1 with (?pre1, ?op1) =>
    lazymatch p2 with (?pre2, ?op2) =>
      change (pre1 ++ [::op1] = pre2 ++ [::op2]) in HE;
      let Hpre := fresh "Hpre" in let Hop := fresh "Hop" in
      apply List.app_inj_tail in HE as [Hpre Hop]; discriminate Hop
    end end
  end.

Lemma crt_simple_indirect_stuck vs x y es' :
  ~ reduce_simple (v_to_e_list vs ++ [::AI_basic (BI_call_indirect x y)]) es'.
Proof.
  intros Hred. remember (v_to_e_list vs ++ [::AI_basic (BI_call_indirect x y)]) as source eqn:HE.
  destruct Hred; try (crt_call_sources HE).
  subst es.
  have Hfill : lfill lh [::AI_trap] = v_to_e_list vs ++ [::AI_basic (BI_call_indirect x y)] by congruence.
  have [Hop _] := crt_escape_in_flat_source (lh := lh)
    (escape := AI_trap) (op := AI_basic (BI_call_indirect x y))
    (v_to_e_const vs) ltac:(discriminate) ltac:(discriminate) Hfill.
  discriminate Hop.
Qed.

Lemma crt_reduce_indirect_no_operand hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  forall x y, es = [::AI_basic (BI_call_indirect x y)] -> False.
Proof.
  intros Hred. induction Hred; intros x0 y0 HE; try discriminate HE.
  - subst e. exact (crt_simple_indirect_stuck (vs := [::]) H).
  all: try (apply extract_list1 in HE as [Hpre Hlast]; discriminate Hlast).
  - have Hfill : lfill lh es = [::AI_basic (BI_call_indirect x0 y0)] by congruence.
    have [Hes _] := crt_lfill_singleton_identity
      (op := AI_basic (BI_call_indirect x0 y0))
      (crt_reduce_nonconstant Hred) ltac:(discriminate) Hfill.
    exact (IHHred _ _ Hes).
Qed.

Lemma crt_reduce_indirect_empty_inv hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  crt_resource_free_native_store s ->
  forall v x y, es = [::v_to_e v; AI_basic (BI_call_indirect x y)] ->
    hs' = hs /\ s' = s /\ f' = f /\ es' = [::AI_trap].
Proof.
  intros Hred. induction Hred; intros HP val x0 y0 HE;
    try discriminate HE.
  - subst e. exfalso. exact (crt_simple_indirect_stuck (vs := [::val]) H).
  all: try (crt_call_sources HE).
  all: try match goal with Hread : stab_elem _ _ _ _ = Some _ |- _ =>
    rewrite (crt_empty_stab_elem _ _ _ HP) in Hread; discriminate Hread end.
  - repeat split; reflexivity.
  - have Hfill : lfill lh es = v_to_e_list [::val] ++ [::AI_basic (BI_call_indirect x0 y0)].
    { rewrite H HE. reflexivity. }
    destruct (crt_lfill_flat_nonconstant
      (op := AI_basic (BI_call_indirect x0 y0))
      (crt_reduce_nonconstant Hred) ltac:(discriminate) Hfill)
      as [pre [post [Hvals [Hes Hout]]]].
    destruct pre as [|vpre pre].
    + simpl in Hvals. subst post.
      have [Hhs [Hs [Hf Hr]]] := IHHred HP val x0 y0 Hes.
      repeat split; try assumption. rewrite -H0 Hout. exact Hr.
    + simpl in Hvals. injection Hvals as Hv Htail.
      symmetry in Htail. apply List.app_eq_nil in Htail as [Hpre Hpost].
      subst pre post. exfalso. exact (crt_reduce_indirect_no_operand Hred Hes).
Qed.

End Host.

Print Assumptions crt_reduce_call_inv.
