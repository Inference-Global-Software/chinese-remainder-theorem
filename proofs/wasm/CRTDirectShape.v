(* Primitive reductions consume a fixed number of values before their active
   instruction; the only flat source with a trailing suffix is trap collapse. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties.
From CRTWasm Require Import CRTStorePure CRTResourceReads CRTExecutionContexts
  CRTSimpleDeterminism CRTDirectDeterminism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Host.
Context `{ho : host}.
Ltac crt_shape_split_last src :=
  lazymatch src with
  | [::?e] => constr:((([::] : seq administrative_instruction), e))
  | ?e :: ?es => let p := crt_shape_split_last es in
      lazymatch p with (?pre, ?op) => constr:(((e :: pre), op)) end
  | ?pre ++ [::?op] => constr:(((pre : seq administrative_instruction), op))
  end.
Lemma crt_shape_vref_const r : is_const (vref_to_e r) = true.
Proof. destruct r; reflexivity. Qed.
Ltac crt_shape_consts :=
  first [assumption | apply v_to_e_const |
    rewrite /const_list /= ?crt_shape_vref_const /is_const ?v2e2v; reflexivity].
Definition crt_flat_source es :=
  exists vs op, const_list vs /\ ~ is_const op /\ es = vs ++ [:: op].
Lemma crt_direct_source_shape hs s f es hs' s' f' es' :
  crt_direct_reduce hs s f es hs' s' f' es' ->
  crt_flat_source es \/
  (exists lh : lholed 0, es = lfill lh [::AI_trap] /\ es' = [::AI_trap]).
Proof.
  intros H. destruct H; subst;
    try match goal with H : reduce_simple _ _ |- _ => destruct H; subst end.
  all: try (left; match goal with |- crt_flat_source ?src =>
    let p := crt_shape_split_last src in
    lazymatch p with (?pre, ?op) =>
      exists pre, op; split; [crt_shape_consts | split; [discriminate | reflexivity]]
    end end).
  right. exists lh. split; reflexivity.
Qed.

Lemma crt_shape_flat_trap_op k (lh : lholed k) vs op :
  k = 0%nat -> const_list vs -> ~ is_const op ->
  lfill lh [::AI_trap] = vs ++ [::op] -> op = AI_trap.
Proof.
  destruct lh; intros Hk HC HN HE; [|discriminate].
  simpl in HE.
  destruct (crt_const_prefix_split (e1 := AI_trap) (e2 := op)
    (v_to_e_const l) HC ltac:(discriminate) HN HE) as [_ [Hop _]].
  symmetry; exact Hop.
Qed.

Definition crt_direct_arity (s : store_record) (f : frame)
    (op : administrative_instruction) : option nat :=
  match op with
  | AI_basic b =>
      match b with
      | BI_block tb _ | BI_loop tb _ =>
          match expand (f_inst f) tb with
          | Some (Tf params _) => Some (length params) | None => None end
      | BI_unop _ _ | BI_testop _ _ | BI_cvtop _ _ _ _
      | BI_vunop _ | BI_vtestop _ | BI_splat_vec _ | BI_extract_vec _ _ _
      | BI_ref_is_null | BI_drop | BI_local_set _ | BI_local_tee _
      | BI_global_set _ | BI_table_get _ | BI_load _ _ _ | BI_load_vec _ _
      | BI_memory_grow | BI_if _ _ _ | BI_br_if _ | BI_br_table _ _
      | BI_call_indirect _ _ | BI_return_call_indirect _ _ => Some 1%nat
      | BI_binop _ _ | BI_relop _ _ | BI_vbinop _ | BI_vshiftop _
      | BI_replace_vec _ _ | BI_table_set _ | BI_table_grow _
      | BI_load_vec_lane _ _ _ | BI_store _ _ _ | BI_store_vec _
      | BI_store_vec_lane _ _ _ => Some 2%nat
      | BI_vternop _ | BI_select _ | BI_table_fill _ | BI_table_copy _ _
      | BI_table_init _ _ | BI_memory_fill | BI_memory_copy | BI_memory_init _ => Some 3%nat
      | _ => Some 0%nat
      end
  | AI_invoke addr =>
      match lookup_N (s_funcs s) addr with
      | Some cl => let '(Tf params _) := cl_type cl in Some (length params)
      | None => None end
  | AI_label _ _ _ | AI_frame _ _ _ => Some 0%nat
  | _ => None
  end.

Lemma crt_direct_source_arity hs s f es hs' s' f' es' :
  crt_direct_reduce hs s f es hs' s' f' es' ->
  forall vs op, const_list vs -> ~ is_const op -> op <> AI_trap ->
  es = vs ++ [::op] -> crt_direct_arity s f op = Some (length vs).
Proof.
  move=> Hred. destruct Hred; move=> vs0 op Hconst Hn Hnot Hsrc;
    try match goal with H : reduce_simple _ _ |- _ => destruct H end; subst.
  all: try match goal with Hsrc : ?src = ?vs ++ [:: ?op] |- _ =>
    let p := crt_shape_split_last src in
    lazymatch p with (?pre, ?inst) =>
      change (pre ++ [::inst] = vs ++ [::op]) in Hsrc;
      apply app_inj_tail in Hsrc as [Hprefix Hop]; subst
    end end.
  all: cbn [crt_direct_arity]; try reflexivity; try congruence.
  - exfalso. apply Hnot. exact (crt_shape_flat_trap_op erefl Hconst Hn Hsrc).
  all: try match goal with H : expand _ _ = Some _ |- _ => rewrite H; cbn; congruence end.
  all: match goal with H : lookup_N (s_funcs _) _ = Some _ |- _ => rewrite H end.
  all: cbn [cl_type]; rewrite /v_to_e_list length_map; congruence.
Qed.
End Host.


