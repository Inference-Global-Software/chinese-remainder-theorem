(* Determinism of WasmCert's simple reductions. *)
From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties.
From CRTWasm Require Import CRTExecutionContexts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Lemma crt_trap_not_value v : AI_trap <> v_to_e v.
Proof.
  move=> He. have H := v2e2v v. rewrite -He in H. discriminate H.
Qed.

Lemma crt_trap_not_ref v : AI_trap <> vref_to_e v.
Proof. destruct v; discriminate. Qed.

Lemma crt_lfill0_trap_present k (lh : lholed k) :
  k = 0 -> In AI_trap (lfill lh [:: AI_trap]).
Proof.
  destruct lh; move=> H; last discriminate H.
  simpl. apply in_or_app. right. by left.
Qed.

Ltac crt_simple_trap_absent :=
  match goal with
  | H : lfill ?lh [:: AI_trap] = ?src |- _ =>
    exfalso;
    let Hin := fresh "Htrap" in
    have Hin := crt_lfill0_trap_present lh erefl;
    rewrite H in Hin; simpl in Hin;
    intuition (try discriminate;
      match goal with
      | E : AI_trap = v_to_e ?v |- False => exact (crt_trap_not_value E)
      | E : v_to_e ?v = AI_trap |- False => symmetry in E; exact (crt_trap_not_value E)
      | E : AI_trap = vref_to_e ?v |- False => exact (crt_trap_not_ref E)
      | E : vref_to_e ?v = AI_trap |- False => symmetry in E; exact (crt_trap_not_ref E)
      end)
  end.

Lemma crt_lfill_escape_not_trap k (lh : lholed k) vs e :
  const_list vs -> ~ is_const e -> e <> AI_trap ->
  lfill lh (vs ++ [:: e]) <> [:: AI_trap].
Proof.
  move=> Hvs He Hne Hfill. destruct lh as [pre post|k pre n cont lh post]; simpl in Hfill.
  - rewrite -catA (catA (v_to_e_list pre) vs) in Hfill.
    have Hpre : const_list (v_to_e_list pre ++ vs).
    { apply const_list_concat; [apply v_to_e_const | exact Hvs]. }
    have [_ [Hsame _]] := crt_const_prefix_split
      (vs2 := [::]) (e2 := AI_trap) Hpre erefl He ltac:(discriminate) Hfill.
    exact (Hne Hsame).
  - have [_ [Hsame _]] := crt_const_prefix_split
      (vs2 := [::]) (e1 := AI_label n cont (lfill lh (vs ++ [:: e])))
      (e2 := AI_trap) (v_to_e_const pre) erefl
      ltac:(discriminate) ltac:(discriminate) Hfill.
    discriminate Hsame.
Qed.

Lemma crt_simple_deterministic es es1 es2 :
  reduce_simple es es1 -> reduce_simple es es2 -> es1 = es2.
Proof.
  move=> H1 H2.
  inversion H1; subst; inversion H2; subst; try reflexivity; try congruence; try lia.
  all: repeat match goal with
  | H : v_to_e ?v = v_to_e ?w |- _ => apply ve_inj in H; subst
  end; try reflexivity; try congruence.
  all: try crt_simple_trap_absent.
  all: try match goal with H : ?src = lfill ?lh [:: AI_trap] |- _ =>
    symmetry in H; crt_simple_trap_absent end.
  all: try match goal with
  | H : forall t, ?r <> VAL_ref_null t |- _ =>
    destruct r as [t'|f'|x']; simpl in *; try discriminate;
    exfalso; exact (H t' (Logic.eq_refl _))
  end.
  all: try (exfalso; match goal with H : ?x <> ?y |- _ => apply H; reflexivity end).
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
  - have [He _] := crt_lfill_escape_unique (lh := lh0) (lh' := lh)
      (e := AI_basic (BI_br (N.of_nat i0))) (e' := AI_basic (BI_br (N.of_nat i)))
      H5 H H7 ltac:(discriminate) ltac:(discriminate) H8.
    by rewrite He.
  - have [He _] := crt_lfill_escape_unique (lh := lh0) (lh' := lh)
      (e := AI_basic BI_return) (e' := AI_basic BI_return)
      H5 H H7 ltac:(discriminate) ltac:(discriminate) H8.
    symmetry. exact He.
Qed.

End Host.

Print Assumptions crt_simple_deterministic.

