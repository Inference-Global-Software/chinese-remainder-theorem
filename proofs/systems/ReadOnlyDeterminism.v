From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties.
From CRTWasm Require Import CRTExecutionContexts CRTExecutionEscapes CRTFlatContext CRTCallInversion CRTSimpleDeterminism CRTDirectDeterminism.
From CRTSystems Require Import ReadOnly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Host.
Context `{ho : host}.
Ltac ro_direct_resources HP Hro :=
  first [solve [move: Hro; rewrite ?ro_es_cat /ro_es /= ?andbF; discriminate] |
    match goal with H : lookup_N (s_funcs _) _ = Some (FC_func_host _ _) |- _ =>
      exfalso; exact (HP _ _ H)
    end].
Lemma crt_append_singleton_inj (xs ys : seq administrative_instruction) x y :
  xs ++ [:: x] = ys ++ [:: y] -> xs = ys /\ x = y.
Proof. exact: app_inj_tail. Qed.

Ltac crt_direct_split_last src :=
  lazymatch src with
  | [::?e] => constr:((([::] : seq administrative_instruction), e))
  | ?e :: ?es =>
      let p := crt_direct_split_last es in
      lazymatch p with (?pre, ?op) => constr:(((e :: pre), op)) end
  | ?pre ++ [::?op] => constr:(((pre : seq administrative_instruction), op))
  end.

Ltac crt_direct_split_sources :=
  match goal with
  | H : @eq (seq administrative_instruction) ?src1 ?src2 |- _ =>
    let p1 := crt_direct_split_last src1 in
    let p2 := crt_direct_split_last src2 in
    lazymatch p1 with (?pre1, ?op1) =>
    lazymatch p2 with (?pre2, ?op2) =>
      change (pre1 ++ [::op1] = pre2 ++ [::op2]) in H;
      let Hpre := fresh "Hpre" in let Hop := fresh "Hop" in
      apply crt_append_singleton_inj in H as [Hpre Hop];
      inversion Hop; subst; clear Hop
    end end
  end.

Lemma crt_direct_vref_const r : is_const (vref_to_e r) = true.
Proof. destruct r; reflexivity. Qed.

Ltac crt_direct_prove_const_list :=
  first [assumption | apply v_to_e_const |
    rewrite /const_list /= ?crt_direct_vref_const /is_const ?v2e2v; reflexivity].

Ltac crt_direct_trap_absent :=
  match goal with
  | H : lfill ?lh [:: AI_trap] = ?src |- _ =>
    let p := crt_direct_split_last src in
    lazymatch p with (?pre, ?op) =>
      let Hp := fresh "Hprefix" in
      assert (Hp : const_list pre) by crt_direct_prove_const_list;
      let HE := fresh "Htrap" in
      have [HE _] := crt_escape_in_flat_source
        (lh := lh) (escape := AI_trap) (vs := pre) (op := op) Hp
        ltac:(discriminate) ltac:(discriminate) H;
      discriminate HE
    end
  end.


Lemma ro_direct_reduce_deterministic hs s f es hs1 s1 f1 es1 hs2 s2 f2 es2 :
  ro_store s -> ro_es es ->
  crt_direct_reduce hs s f es hs1 s1 f1 es1 ->
  crt_direct_reduce hs s f es hs2 s2 f2 es2 ->
  (hs1, s1, f1, es1) = (hs2, s2, f2, es2).
Proof.
  move=> HP Hro H1 H2.
  inversion H1; subst; clear H1; try (ro_direct_resources HP Hro);
    inversion H2; subst; clear H2; try (ro_direct_resources HP Hro);
    try reflexivity; try congruence; try lia.
  all: try match goal with
  | H : reduce_simple ?es ?es1, H' : reduce_simple ?es ?es2 |- _ =>
    have -> := crt_simple_deterministic H H'; reflexivity
  end.
  all: repeat crt_direct_split_sources.
  all: try reflexivity; try congruence.
  all: try match goal with H : reduce_simple _ _ |- _ => inversion H; subst; clear H end.
  all: repeat crt_direct_split_sources.
  all: try reflexivity; try congruence.
  all: try crt_direct_trap_absent.
  all: try match goal with H : ?src = lfill ?lh [:: AI_trap] |- _ =>
    symmetry in H; crt_direct_trap_absent end.
  all: try match goal with H : is_true (const_list (lfill ?lh ?es)) |- _ =>
    exfalso; apply crt_lfill_const_inv in H;
    apply const_list_split in H as [_ H]; discriminate H end.
  all: try match goal with H : [:: AI_trap] = lfill ?lh ?es |- _ => symmetry in H end.
  all: try match goal with
  | H : lfill ?lh (?vs ++ [:: ?e]) = [:: AI_trap],
    Hc : is_true (const_list ?vs) |- _ =>
    exfalso; exact (crt_lfill_escape_not_trap (lh := lh) (e := e) Hc
      ltac:(discriminate) ltac:(discriminate) H)
  end.
  all: try match goal with
  | H : lfill ?lh (?vs ++ [:: ?e]) = lfill ?lh' (?vs' ++ [:: ?e']),
    Hc : is_true (const_list ?vs), Hc' : is_true (const_list ?vs') |- _ =>
    let HE := fresh "Hescape" in
    have [HE _] := crt_lfill_escape_head_unique
      (lh := lh) (lh' := lh') (vs := vs) (vs' := vs') (e := e) (e' := e')
      Hc Hc' ltac:(discriminate) ltac:(discriminate) H;
    discriminate HE
  end.
  all: repeat match goal with
  | H : v_to_e_list ?vs = v_to_e_list ?vs' |- _ => apply v_to_e_inj in H; subst
  | H : v_to_e ?v = v_to_e ?v' |- _ => apply ve_inj in H; subst
  end; try reflexivity; try congruence.
  all: try match goal with
  | H : lfill ?lh (?vs ++ [:: AI_return_invoke ?a]) =
        lfill ?lh' (?vs' ++ [:: AI_return_invoke ?a']),
    Hc : is_true (const_list ?vs), Hc' : is_true (const_list ?vs') |- _ =>
    let HE := fresh "Hescape" in
    have [HE _] := crt_lfill_escape_head_unique
      (lh := lh) (lh' := lh') (vs := vs) (vs' := vs')
      (e := AI_return_invoke a) (e' := AI_return_invoke a')
      Hc Hc' ltac:(discriminate) ltac:(discriminate) H;
    inversion HE; subst;
    let HL := fresh "Hlength" in
    assert (HL : length vs = length vs') by congruence;
    let HV := fresh "Hvalues" in
    have [HV _] := crt_lfill_escape_unique
      (lh := lh) (lh' := lh') (vs := vs) (vs' := vs')
      (e := AI_return_invoke a) (e' := AI_return_invoke a)
      Hc Hc' HL ltac:(discriminate) ltac:(discriminate) H;
    rewrite HV; reflexivity
  end.
  - exfalso.
    have Hin : ro_es (lfill lh (vs ++ [::AI_return_invoke a])).
    { move: Hro. by rewrite /ro_es /= andbT. }
    have Hbad := ro_lfill_extract Hin.
    move: Hbad. by rewrite ro_es_cat /ro_es /= andbF.
  - have Ef : f1 = f2.
    { apply crt_frame_ext; last congruence. rewrite H3 H14.
      exact: crt_set_nth_default_irrelevant H0. }
    by rewrite Ef.

Qed.
End Host.
