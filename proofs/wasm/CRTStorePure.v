(* Store preservation for the resource-free, native-only runtime used by CRT.
   This is a property of the real Wasm reduction relation.  It covers native
   calls as well as numeric, local, and control instructions. *)
From Coq Require Import NArith List Relations.Relation_Operators.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Record crt_resource_free_native_store (s : store_record) : Prop := {
  crt_empty_tables : s_tables s = [::];
  crt_empty_memories : s_mems s = [::];
  crt_empty_globals : s_globals s = [::];
  crt_empty_elements : s_elems s = [::];
  crt_empty_data : s_datas s = [::];
  crt_no_host_function : forall addr ft hf,
    lookup_N (s_funcs s) addr <> Some (FC_func_host ft hf)
}.

Lemma crt_lookup_N_nil (T : Type) n : @lookup_N T [::] n = None.
Proof. rewrite /lookup_N. by case: (N.to_nat n). Qed.

Definition crt_is_native (f : funcinst) : Prop :=
  match f with FC_func_native _ _ _ => True | FC_func_host _ _ => False end.

Lemma crt_resource_free_of_native_functions fs :
  List.Forall crt_is_native fs ->
  crt_resource_free_native_store (Build_store_record fs [::] [::] [::] [::] [::]).
Proof.
  move=> Hfs. constructor; try reflexivity.
  intros addr ft hf Hlook. rewrite /= /lookup_N in Hlook.
  rewrite List.Forall_forall in Hfs.
  have Hnative := Hfs (FC_func_host ft hf) (List.nth_error_In _ _ Hlook).
  exact Hnative.
Qed.

(* Each operation below must first resolve a resource in the store.  Empty
   resource vectors make a purported successful mutation contradictory. *)
Ltac crt_empty_update_contradiction Hpure Hupdate :=
  destruct Hpure as [Htables Hmems Hglobals Helems Hdata Hnative];
  unfold supdate_glob, supdate_glob_s, sglob_ind,
    stab_update, stab_grow, selem_drop,
    smem_store, smem_store_packed, smem_store_vec,
    smem_store_vec_lane, smem_grow, sdata_drop in Hupdate;
  rewrite ?Htables ?Hmems ?Hglobals ?Helems ?Hdata in Hupdate;
  rewrite ?crt_lookup_N_nil in Hupdate;
  repeat first [progress rewrite ?crt_lookup_N_nil in Hupdate |
    match type of Hupdate with
    | context [lookup_N ?xs ?idx] =>
        let E := fresh "Elookup" in destruct (lookup_N xs idx) eqn:E in Hupdate
    end];
  cbn [option_bind option_map] in Hupdate;
  rewrite ?crt_lookup_N_nil in Hupdate;
  first [discriminate Hupdate |
    match goal with E : lookup_N [::] _ = Some _ |- _ =>
      rewrite crt_lookup_N_nil in E; discriminate E
    end].

Theorem crt_reduce_preserves_resource_free_store
    hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  crt_resource_free_native_store s -> s' = s.
Proof.
  move=> Hred. induction Hred; intros Hpure; try reflexivity;
    try (apply IHHred; exact Hpure).
  - subst cl. exfalso. exact (crt_no_host_function Hpure H).
  - crt_empty_update_contradiction Hpure H.
  - crt_empty_update_contradiction Hpure H.
  - crt_empty_update_contradiction Hpure H.
  - crt_empty_update_contradiction Hpure H.
  - crt_empty_update_contradiction Hpure H.
  - crt_empty_update_contradiction Hpure H.
  - crt_empty_update_contradiction Hpure H.
  - crt_empty_update_contradiction Hpure H.
  - crt_empty_update_contradiction Hpure H.
  - crt_empty_update_contradiction Hpure H.
Qed.

Definition crt_cfg_store
    (c : host_state * store_record * frame * seq administrative_instruction) : store_record :=
  let '(_, s, _, _) := c in s.

Theorem crt_reduce_trans_preserves_resource_free_store
    hs s f es hs' s' f' es' :
  crt_resource_free_native_store s ->
  reduce_trans (hs, s, f, es) (hs', s', f', es') -> s' = s.
Proof.
  move=> Hpure Hred.
  have Hgeneral : forall c c', reduce_trans c c' ->
      crt_resource_free_native_store (crt_cfg_store c) ->
      crt_cfg_store c' = crt_cfg_store c.
  { intros c c' HR. induction HR; intros HP.
    - destruct x as [[[hs0 s0] f0] es0].
      destruct y as [[[hs1 s1] f1] es1].
      exact (crt_reduce_preserves_resource_free_store H HP).
    - reflexivity.
    - pose proof (IHHR1 HP) as HE.
      assert (HM : crt_resource_free_native_store (crt_cfg_store y)) by (rewrite HE; exact HP).
      rewrite (IHHR2 HM). exact HE. }
  exact (Hgeneral _ _ Hred Hpure).
Qed.

End Host.

Print Assumptions crt_reduce_preserves_resource_free_store.
Print Assumptions crt_reduce_trans_preserves_resource_free_store.
