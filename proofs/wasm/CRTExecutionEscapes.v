(* Irreducibility of escapes before their matching label or frame. *)
From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties contexts.
From CRTWasm Require Export CRTExecutionContexts.
From CRTWasm Require Import CRTContextFactor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Inductive crt_pending_escape : administrative_instruction -> nat -> Prop :=
| crt_pending_return k : crt_pending_escape (AI_basic BI_return) k
| crt_pending_br k j : N.le (N.of_nat k) j ->
    crt_pending_escape (AI_basic (BI_br j)) k
| crt_pending_tail k a : crt_pending_escape (AI_return_invoke a) k.

Lemma crt_pending_noncontext e k :
  crt_pending_escape e k -> ~ lfill_ctx_instr e.
Proof. intros H; destruct H; discriminate. Qed.

Lemma crt_lfill_single_label_inv k (lh : lholed k) e n cont body :
  ~ lfill_ctx_instr e -> lfill lh [::e] = [::AI_label n cont body] ->
  exists d (inner : lholed d), k = S d /\ body = lfill inner [::e].
Proof.
  intros He Hfill. destruct lh as [pre post | d pre n' cont' inner post];
    simpl in Hfill.
  - have [_ [HE _]] := crt_const_prefix_split (vs2 := [::]) (e2 := AI_label n cont body)
      (v_to_e_const pre) erefl (crt_escape_nonconst He)
      ltac:(discriminate) Hfill.
    subst e. exfalso; apply He; reflexivity.
  - have [_ [HE _]] := crt_const_prefix_split (vs2 := [::]) (e1 := AI_label n' cont' (lfill inner [::e])) (e2 := AI_label n cont body)
      (v_to_e_const pre) erefl ltac:(discriminate)
      ltac:(discriminate) Hfill.
    injection HE as Hn Hcont Hbody.
    exists d, inner. split; [reflexivity | congruence].
Qed.

Lemma crt_vref_const r : is_const (vref_to_e r) = true.
Proof. destruct r; reflexivity. Qed.

Ltac crt_prove_const_list :=
  first [assumption | apply v_to_e_const |
    match goal with H : ?xs = v_to_e_list ?vs |- const_list ?xs =>
      rewrite H; apply v_to_e_const end |
    rewrite /const_list /= ?crt_vref_const /is_const ?v2e2v; reflexivity].

Ltac crt_flat_pending_contradiction Hpending Hfill :=
  let rec split_last src :=
    lazymatch src with
    | [::?e] => constr:((([::] : seq administrative_instruction), e))
    | ?e :: ?es =>
        let p := split_last es in
        lazymatch p with (?pre, ?op) => constr:(((e :: pre), op)) end
    | ?pre ++ [::?op] => constr:(((pre : seq administrative_instruction), op))
    end in
  lazymatch type of Hfill with
  | lfill ?lh [::?escape] = ?src =>
    let p := split_last src in
    lazymatch p with (?pre, ?op) =>
      let Hp := fresh "Hprefix" in
      assert (Hp : const_list pre) by crt_prove_const_list;
      let HE := fresh "Hescape" in
      let HK := fresh "Hdepth" in
      destruct (crt_escape_in_flat_source (lh := lh) (vs := pre) (op := op)
        Hp (crt_pending_noncontext Hpending) ltac:(discriminate) Hfill)
        as [HE HK];
      destruct Hpending; discriminate HE
    end
  end.

Lemma crt_simple_pending_stuck es es' :
  reduce_simple es es' ->
  forall k (lh : lholed k) e,
    lfill lh [:: e] = es -> crt_pending_escape e k -> False.
Proof.
  intros Hred. destruct Hred; intros k0 lh0 e Hfill Hpending;
    try (crt_flat_pending_contradiction Hpending Hfill).
  - destruct (crt_lfill_single_label_inv (crt_pending_noncontext Hpending) Hfill)
      as [d [inner [Hdepth Hbody]]].
    rewrite Hbody in H. apply crt_lfill_const_inv in H.
    rewrite /const_list /= andbT in H.
    exact (crt_escape_nonconst (crt_pending_noncontext Hpending) H).
  - destruct (crt_lfill_single_label_inv (crt_pending_noncontext Hpending) Hfill)
      as [d [inner [Hdepth Hbody]]].
    have [HE _] := crt_escape_in_flat_source
      (vs := [::]) (op := AI_trap) erefl
      (crt_pending_noncontext Hpending) ltac:(discriminate) (Logic.eq_sym Hbody).
    destruct Hpending; discriminate HE.
  - destruct (crt_lfill_single_label_inv (crt_pending_noncontext Hpending) Hfill)
      as [d [inner [Hdepth Hbody]]].
    have Hfills : lfill inner ([::] ++ [::e]) =
      lfill lh (vs ++ [:: AI_basic (BI_br (N.of_nat i))]).
    { simpl. congruence. }
    have [HE HK] := crt_lfill_escape_head_unique
      (lh := inner) (lh' := lh) (vs := [::]) (vs' := vs)
      (e' := AI_basic (BI_br (N.of_nat i))) erefl H
      (crt_pending_noncontext Hpending) ltac:(discriminate) Hfills.
    destruct Hpending; try discriminate HE.
    inversion HE; subst. lia.
  - subst es.
    have [HE HK] := crt_lfill_escape_head_unique
      (lh := lh0) (lh' := lh) (vs := [::]) (vs' := [::])
      (e' := AI_trap) erefl erefl
      (crt_pending_noncontext Hpending) ltac:(discriminate) Hfill.
    destruct Hpending; discriminate HE.
Qed.

Lemma crt_reduce_pending_stuck hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  forall k (lh : lholed k) e,
    lfill lh [:: e] = es -> crt_pending_escape e k -> False.
Proof.
  intros Hred. induction Hred; intros k0 lh0 e0 Hfill Hpending;
    try (crt_flat_pending_contradiction Hpending Hfill).
  all: try match goal with H : ?ves = v_to_e_list ?vs |- _ =>
    subst ves; crt_flat_pending_contradiction Hpending Hfill end.
  - exact (crt_simple_pending_stuck H Hfill Hpending).
  - have HE : lfill lh es = lfill lh0 [::e0] by congruence.
    destruct (crt_lfill_escape_factor (lh := lh) (crt_reduce_nonconstant Hred)
      (crt_pending_noncontext Hpending) HE) as [d [inner [Hdepth Hbody]]].
    apply (IHHred _ inner e0 (Logic.eq_sym Hbody)).
    destruct Hpending; constructor; try lia.
Qed.

Lemma crt_lfill_singleton_hole k (lh : lholed k) es e :
  ~ const_list es -> ~ lfill_ctx_instr e ->
  lfill lh es = [::e] -> es = [::e].
Proof.
  intros Hnon He Hfill.
  destruct lh as [pre post | d pre n cont inner post]; simpl in Hfill.
  - destruct pre as [|v pre].
    + simpl in Hfill. destruct es as [|a es].
      { exfalso; apply Hnon; reflexivity. }
      simpl in Hfill. injection Hfill as Ha Htail.
      apply List.app_eq_nil in Htail as [Hes Hpost].
      subst; reflexivity.
    + simpl in Hfill. injection Hfill as Ha Htail.
      exfalso. apply (crt_escape_nonconst He).
      rewrite -Ha /is_const v2e2v. reflexivity.
  - destruct pre as [|v pre].
    + simpl in Hfill. injection Hfill as Ha Htail.
      subst e. exfalso. apply He. reflexivity.
    + simpl in Hfill. injection Hfill as Ha Htail.
      exfalso. apply (crt_escape_nonconst He).
      rewrite -Ha /is_const v2e2v. reflexivity.
Qed.

Lemma crt_simple_trap_irreducible es' :
  ~ reduce_simple [::AI_trap] es'.
Proof. intros Hred. inversion Hred; subst; contradiction. Qed.

Lemma crt_reduce_trap_irreducible hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' -> es = [::AI_trap] -> False.
Proof.
  intros Hred. induction Hred; intros HE; try discriminate HE.
  - subst e. exact (crt_simple_trap_irreducible H).
  all: try (apply extract_list1 in HE as [Hpre Hlast]; discriminate Hlast).
  - apply IHHred. apply (crt_lfill_singleton_hole (lh := lh) (crt_reduce_nonconstant Hred)
      (e := AI_trap) ltac:(discriminate)). congruence.
Qed.

End Host.

Print Assumptions crt_reduce_pending_stuck.
