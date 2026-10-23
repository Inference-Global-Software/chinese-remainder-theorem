(* Native calls backed by actual callee execution in the shared CRT runtime. *)
From Coq Require Import ZArith NArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem host.
From WasmVerifier Require Import Assertions Semantics MultiExit Activation Verifier.
From CRT Require Import CRTStatements.
From CRTGenerated Require Import main.
From CRTWasm Require Import CRTStorePure CRTModule CRTExecution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.

Lemma crt_stack_consts V args : stack_denote V (map T_const args) = Some args.
Proof. induction args; simpl; [reflexivity | now rewrite IHargs]. Qed.

Lemma crt_args_typed_length args params :
  args_typed args params -> length args = length params.
Proof.
  move: params. induction args as [|a args IH]; intros params H;
    destruct params as [|p params]; try contradiction; try reflexivity.
  destruct p; try contradiction. simpl in H. destruct H as [_ H].
  simpl. f_equal. exact (IH _ H).
Qed.

Lemma crt_results_typed_length rs results :
  results_typed rs results -> length rs = length results.
Proof.
  move: results. induction rs as [|r rs IH]; intros results H;
    destruct results as [|p results]; try contradiction; try reflexivity.
  destruct p; try contradiction. simpl in H. destruct H as [_ H].
  simpl. f_equal. exact (IH _ H).
Qed.

Section Host.
Context `{ho : host}.

Definition crt_entry_valuation args defaults : valuation :=
  {| val_log := [::];
     val_loc := loc_read (activation_frame crt_runtime args defaults);
     val_glob := glob_read crt_store (activation_frame crt_runtime args defaults);
     val_fun := fun _ _ => None |}.

Definition crt_entry_admissible fdef args : Prop :=
  forall defaults, default_vals (modfunc_locals fdef) = Some defaults ->
    assertion_denote (crt_entry_valuation args defaults)
      (AS_base [::] (HA_and (args_pinned args (N.of_nat 0))
         (func_pre_h main.main fdef))) ([::], aheap_empty).

Lemma crt_call_from_computes_at (i : nat) addr fdef params results args rs f H :
  lookup_N (mod_funcs main.main) (N.of_nat i) = Some fdef ->
  lookup_N (mod_types main.main) (modfunc_type fdef) = Some (Tf params results) ->
  lookup_N (inst_funcs (f_inst f)) (N.of_nat i) = Some addr ->
  lookup_N (s_funcs crt_store) addr =
    Some (FC_func_native (Tf params results) crt_inst fdef) ->
  crt_entry_admissible fdef args ->
  fun_computes_at crt_runtime i args rs ->
  sem_triple_at crt_store f (AS_base (map T_const args) H)
    [:: BI_call (N.of_nat i)] (AS_base (map T_const rs) H).
Proof.
  move=> Hfunc Htype Hcall Hnative Hentry Hcompute.
  rewrite /fun_computes_at Hfunc Htype in Hcompute.
  destruct Hcompute as [Hargs [Hresults [defaults [Hdefaults Hbody]]]].
  move=> hs V vs h [Hvs HH] Hr.
  rewrite crt_stack_consts in Hvs. inversion Hvs; subst vs.
  have Hreify : reifies_sto crt_store
      (activation_frame crt_runtime args defaults) aheap_empty
      (crt_entry_valuation args defaults).
  { apply reifies_sto_empty; reflexivity. }
  have Harity : length [seq VAL_num v | v <- args] = length params.
  { rewrite map_length. exact (crt_args_typed_length Hargs). }
  have Hlen : forall V' vs' h',
      assertion_denote V' (AS_base (map T_const rs) HA_true) (vs', h') ->
      length vs' = length results.
  { move=> V' vs' h' [Heq _]. rewrite crt_stack_consts in Heq.
    inversion Heq; subst vs'. exact (crt_results_typed_length Hresults). }
  destruct fdef as [idx locals body].
  have Hrun := sem_call_native_at
    (i := N.of_nat i) (addr := addr)
    (cl := FC_func_native (Tf params results) crt_inst (Build_module_func idx locals body))
    (inst := crt_inst) (ts1 := params) (ts2 := results) (ts := locals)
    (idx := idx) (defaults := defaults) (args := args)
    (f_caller := f) (s := crt_store)
    (V0 := crt_entry_valuation args defaults) (h0 := aheap_empty)
    hs Hcall Hbody Hnative erefl Harity Hdefaults (Hentry _ Hdefaults) Hreify Hlen.
  destruct Hrun as [s' [V' [rs' [h' [_ [Hred [Hrs _]]]]]]].
  rewrite crt_stack_consts in Hrs. inversion Hrs; subst rs'.
  have Hstore : s' = crt_store.
  { exact (crt_reduce_trans_preserves_resource_free_store crt_store_resource_free Hred). }
  subst s'. exists crt_store, f, V, rs, h. split; first reflexivity.
  have Hvalues : v_to_e_list [seq VAL_num v | v <- args] = vn_to_e args.
  { clear - args hfc memory ho. unfold v_to_e_list, vn_to_e.
    induction args; simpl; congruence. }
  split; first by rewrite Hvalues in Hred.
  split; last exact Hr. split; last exact HH. exact (crt_stack_consts V rs).
Qed.

Lemma crt_gcd_entry m n :
  crt_entry_admissible main.gcd_positive [:: main.Vi64 m; main.Vi64 n].
Proof.
  move=> defaults Hdefaults. vm_compute in Hdefaults.
  inversion Hdefaults; subst defaults.
  cbn [crt_entry_valuation activation_frame crt_runtime func_pre_h main.main
    main.gcd_positive args_pinned locals_typed assertion_denote hassert_denote
    stack_denote term_eq term_denote loc_read lookup_N val_loc f_locs
    modfunc_type modfunc_locals mod_types runtime_inst main.Vi64].
  repeat split; try reflexivity; try (eexists; split; reflexivity).
Qed.

Lemma crt_normalize_entry z d :
  crt_entry_admissible main.normalize [:: main.Vi64 z; main.Vi64 d].
Proof.
  move=> defaults Hdefaults. vm_compute in Hdefaults.
  inversion Hdefaults; subst defaults.
  cbn [crt_entry_valuation activation_frame crt_runtime func_pre_h main.main
    main.normalize args_pinned locals_typed assertion_denote hassert_denote
    stack_denote term_eq term_denote loc_read lookup_N val_loc f_locs
    modfunc_type modfunc_locals mod_types runtime_inst main.Vi64].
  repeat split; try reflexivity; try (eexists; split; reflexivity).
Qed.

Lemma crt_inverse_entry B A :
  crt_entry_admissible main.inverse_coprime [:: main.Vi64 B; main.Vi64 A].
Proof.
  move=> defaults Hdefaults. vm_compute in Hdefaults.
  inversion Hdefaults; subst defaults.
  cbn [crt_entry_valuation activation_frame crt_runtime func_pre_h main.main
    main.inverse_coprime args_pinned locals_typed assertion_denote hassert_denote
    stack_denote term_eq term_denote loc_read lookup_N val_loc f_locs
    modfunc_type modfunc_locals mod_types runtime_inst main.Vi64].
  repeat split; try reflexivity; try (eexists; split; reflexivity).
Qed.

Lemma crt_inverse_call_from_computes f H B A u :
  f_inst f = crt_inst ->
  fun_computes_at crt_runtime 2%nat [:: main.Vi64 B; main.Vi64 A] [:: main.Vi64 u] ->
  sem_triple_at crt_store f
    (AS_base [:: T_const (main.Vi64 B); T_const (main.Vi64 A)] H)
    [:: BI_call (N.of_nat 2)] (AS_base [:: T_const (main.Vi64 u)] H).
Proof.
  move=> Hinst Hcompute.
  apply: (crt_call_from_computes_at (i := 2%nat) (addr := N.of_nat 2)
    (fdef := main.inverse_coprime)
    (args := [:: main.Vi64 B; main.Vi64 A]) (rs := [:: main.Vi64 u])
    (params := [:: T_num T_i64; T_num T_i64])
    (results := [:: T_num T_i64])); try reflexivity.
  - by rewrite Hinst.
  - exact (crt_inverse_entry B A).
  - exact Hcompute.
Qed.

Lemma crt_gcd_call f H m n :
  f_inst f = crt_inst -> moduli m n ->
  sem_triple_at crt_store f
    (AS_base [:: T_const (main.Vi64 m); T_const (main.Vi64 n)] H)
    [:: BI_call (N.of_nat 0)]
    (AS_base [:: T_const (main.Vi64 (Z.gcd m n))] H).
Proof.
  move=> Hinst Hmod.
  apply: (crt_call_from_computes_at (i := 0%nat) (addr := N.of_nat 0)
    (fdef := main.gcd_positive)
    (args := [:: main.Vi64 m; main.Vi64 n]) (rs := [:: main.Vi64 (Z.gcd m n)])
    (params := [:: T_num T_i64; T_num T_i64])
    (results := [:: T_num T_i64])); try reflexivity.
  - by rewrite Hinst.
  - exact (crt_gcd_entry m n).
  - apply: fun_computes_at_of_computes; last exact (gcd_machine_computes Hmod).
    exists main.gcd_positive.
    eexists. split; reflexivity.
Qed.

Lemma crt_normalize_call f H z d :
  f_inst f = crt_inst -> word z -> 1 <= d <= M ->
  sem_triple_at crt_store f
    (AS_base [:: T_const (main.Vi64 z); T_const (main.Vi64 d)] H)
    [:: BI_call (N.of_nat 1)]
    (AS_base [:: T_const (main.Vi64 (z mod d))] H).
Proof.
  move=> Hinst Hz Hd.
  apply: (crt_call_from_computes_at (i := 1%nat) (addr := N.of_nat 1)
    (fdef := main.normalize)
    (args := [:: main.Vi64 z; main.Vi64 d]) (rs := [:: main.Vi64 (z mod d)])
    (params := [:: T_num T_i64; T_num T_i64])
    (results := [:: T_num T_i64])); try reflexivity.
  - by rewrite Hinst.
  - exact (crt_normalize_entry z d).
  - apply: fun_computes_at_of_computes; last exact (normalize_machine_computes Hz Hd).
    exists main.normalize.
    eexists. split; reflexivity.
Qed.

End Host.

Print Assumptions crt_call_from_computes_at.
Print Assumptions crt_gcd_call.
Print Assumptions crt_normalize_call.
