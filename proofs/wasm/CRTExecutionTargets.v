(* The exact integer execution targets, instantiated with ordinary WasmCert
   invocation.  The execution relations contain no mathematical postcondition. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem host.
From WasmVerifier Require Import Assertions Semantics Activation Verifier.
From CRT Require Import CRTStatements CRTLoops.
From CRTGenerated Require Import main.
From CRTWasm Require Import CRTAPIModel CRTContracts CRTModule CRTExecution
  CRTCalls CRTInverseExecution CRTPublicExecution CRTSolveExecution
  CRTExecutionDeterminism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.

Section Host.
Context `{ho : host}.

Definition crt_caller_frame : frame := Build_frame [::] crt_inst.

Definition crt_run (hs : host_state) (i : nat)
    (args : seq value_num) (result : Z) : Prop :=
  exists hs' s' f' (v : i64),
    reduce_trans
      (hs, crt_store, crt_caller_frame,
        vn_to_e args ++ [:: AI_basic (BI_call (N.of_nat i))])
      (hs', s', f', [:: AI_basic (BI_const_num (VAL_int64 v))]) /\
    result = Wasm_int.Int64.signed v.

Definition crt_gcd_exec hs m n :=
  crt_run hs 0%nat [:: main.Vi64 m; main.Vi64 n].
Definition crt_normalize_exec hs z d :=
  crt_run hs 1%nat [:: main.Vi64 z; main.Vi64 d].
Definition crt_inverse_exec hs B A :=
  crt_run hs 2%nat [:: main.Vi64 B; main.Vi64 A].
Definition crt_period_exec hs m n :=
  crt_run hs 3%nat [:: main.Vi64 m; main.Vi64 n].
Definition crt_solve_exec hs a m b n :=
  crt_run hs 4%nat [:: main.Vi64 a; main.Vi64 m; main.Vi64 b; main.Vi64 n].

Lemma crt_run_word hs i args result :
  crt_run hs i args result -> word result.
Proof.
  move=> [hs' [s' [f' [v [_ ->]]]]]. exact: crt_contract_signed_word.
Qed.

Lemma crt_run_of_call hs i args result : word result ->
  sem_triple_at crt_store crt_caller_frame
    (AS_base (map T_const args) HA_true)
    [:: BI_call (N.of_nat i)]
    (AS_base [:: T_const (main.Vi64 result)] HA_true) ->
  crt_run hs i args result.
Proof.
  move=> Hword Hcall.
  pose V : valuation :=
    {| val_log := [::]; val_loc := loc_read crt_caller_frame;
       val_glob := glob_read (@crt_store hfc memory) crt_caller_frame;
       val_fun := fun _ _ => None |}.
  have Hpre : assertion_denote V (AS_base (map T_const args) HA_true)
      (args, aheap_empty).
  { split; last exact I. exact: crt_stack_consts. }
  have Hreify : reifies_sto crt_store crt_caller_frame aheap_empty V.
  { apply reifies_sto_empty; reflexivity. }
  have [s' [f' [V' [rs [h' [_ [Hrun [Hpost _]]]]]]]] :=
    Hcall hs V args aheap_empty Hpre Hreify.
  destruct Hpost as [Hrs _]. simpl in Hrs. inversion Hrs; subst rs.
  exists hs, s', f', (Wasm_int.Int64.repr result). split.
  - exact Hrun.
  - symmetry. exact: crt_i64_signed_repr.
Qed.

Lemma crt_period_entry m n :
  crt_entry_admissible main.crt_period [:: main.Vi64 m; main.Vi64 n].
Proof.
  move=> defaults Hdefaults. vm_compute in Hdefaults.
  inversion Hdefaults; subst defaults.
  cbn [crt_entry_valuation activation_frame crt_runtime func_pre_h main.main
    main.crt_period args_pinned locals_typed assertion_denote hassert_denote
    stack_denote term_eq term_denote loc_read lookup_N val_loc f_locs
    modfunc_type modfunc_locals mod_types runtime_inst main.Vi64].
  repeat split; try reflexivity; try (eexists; split; reflexivity).
Qed.

Lemma crt_solve_entry a m b n :
  crt_entry_admissible main.crt_solve
    [:: main.Vi64 a; main.Vi64 m; main.Vi64 b; main.Vi64 n].
Proof.
  move=> defaults Hdefaults. vm_compute in Hdefaults.
  inversion Hdefaults; subst defaults.
  cbn [crt_entry_valuation activation_frame crt_runtime func_pre_h main.main
    main.crt_solve args_pinned locals_typed assertion_denote hassert_denote
    stack_denote term_eq term_denote loc_read lookup_N val_loc f_locs
    modfunc_type modfunc_locals mod_types runtime_inst main.Vi64].
  repeat split; try reflexivity; try (eexists; split; reflexivity).
Qed.

Lemma crt_gcd_exec_exists hs m n : moduli m n ->
  crt_gcd_exec hs m n (Z.gcd m n).
Proof.
  move=> Hmod. apply: crt_run_of_call.
  - have [Hlo [Hhi _]] := crt_gcd_Z_source_contract m n Hmod.
    apply: crt_modulus_word. destruct Hmod as [Hm Hn]. lia.
  - exact: crt_gcd_call.
Qed.

Lemma crt_normalize_exec_exists hs z d : word z -> 1 <= d <= M ->
  crt_normalize_exec hs z d (z mod d).
Proof.
  move=> Hz Hd. apply: crt_run_of_call.
  - have Hb := Z.mod_pos_bound z d ltac:(lia).
    unfold word, i64_min, i64_max. unfold M in Hd. lia.
  - exact: crt_normalize_call.
Qed.

Lemma crt_inverse_exec_exists hs B A : eea_inputs A B -> Z.gcd A B = 1 ->
  crt_inverse_exec hs B A (crt_inverse_Z B A).
Proof.
  move=> Hin Hcop. apply: crt_run_of_call.
  - have [Hu _] := crt_inverse_Z_correct B A ltac:(destruct Hin; lia) Hcop.
    destruct Hin as [_ HA]. unfold word, i64_min, i64_max. unfold M in HA. lia.
  - apply: crt_inverse_call_from_computes; first reflexivity.
    exact: inverse_machine_computes.
Qed.

Lemma crt_period_exec_exists hs m n : word m -> word n ->
  crt_period_exec hs m n (crt_period_Z m n).
Proof.
  move=> Hm Hn. apply: crt_run_of_call.
  - exact (proj2 (crt_period_Z_correct m n)).
  - apply: (crt_call_from_computes_at (i := 3%nat) (addr := N.of_nat 3)
      (fdef := main.crt_period)
      (args := [:: main.Vi64 m; main.Vi64 n])
      (rs := [:: main.Vi64 (crt_period_Z m n)])
      (params := [:: T_num T_i64; T_num T_i64])
      (results := [:: T_num T_i64])); try reflexivity.
    + exact: crt_period_entry.
    + exact: period_machine_computes.
Qed.

Lemma crt_solve_exec_exists hs a m b n :
  word a -> word m -> word b -> word n ->
  crt_solve_exec hs a m b n (crt_solve_Z a m b n).
Proof.
  move=> Ha Hm Hb Hn. apply: crt_run_of_call.
  - exact (proj2 (crt_solve_Z_correct a m b n)).
  - apply: (crt_call_from_computes_at (i := 4%nat) (addr := N.of_nat 4)
      (fdef := main.crt_solve)
      (args := [:: main.Vi64 a; main.Vi64 m; main.Vi64 b; main.Vi64 n])
      (rs := [:: main.Vi64 (crt_solve_Z a m b n)])
      (params := [:: T_num T_i64; T_num T_i64; T_num T_i64; T_num T_i64])
      (results := [:: T_num T_i64])); try reflexivity.
    + exact: crt_solve_entry.
    + exact: solve_machine_computes.
Qed.

Lemma call_normal_result_unique :
  forall hs i args hs1 s1 f1 hs2 s2 f2 (v1 v2 : i64),
    reduce_trans
      (hs, crt_store, crt_caller_frame,
        vn_to_e args ++ [:: AI_basic (BI_call (N.of_nat i))])
      (hs1, s1, f1, [:: AI_basic (BI_const_num (VAL_int64 v1))]) ->
    reduce_trans
      (hs, crt_store, crt_caller_frame,
        vn_to_e args ++ [:: AI_basic (BI_call (N.of_nat i))])
      (hs2, s2, f2, [:: AI_basic (BI_const_num (VAL_int64 v2))]) -> v1 = v2.
Proof.
  intros hs i args hs1 s1 f1 hs2 s2 f2 v1 v2 H1 H2.
  have HE := crt_reduce_trans_normal_unique
    (vs1 := [:: VAL_num (VAL_int64 v1)])
    (vs2 := [:: VAL_num (VAL_int64 v2)])
    crt_store_resource_free H1 H2.
  congruence.
Qed.

Lemma crt_run_result_unique hs i args r1 r2 :
  crt_run hs i args r1 -> crt_run hs i args r2 -> r1 = r2.
Proof.
  move=> [hs1 [s1 [f1 [v1 [Hrun1 ->]]]]] [hs2 [s2 [f2 [v2 [Hrun2 ->]]]]].
  by rewrite (call_normal_result_unique Hrun1 Hrun2).
Qed.

Lemma crt_run_total_correct hs i args result post :
  crt_run hs i args result -> post result ->
  total_correct (crt_run hs i args) post.
Proof.
  move=> Hrun Hpost. split; first by exists result.
  move=> r Hr. split; first exact: crt_run_word Hr.
  by rewrite (crt_run_result_unique Hr Hrun).
Qed.

Theorem gcd_execution_proved hs : T_gcd_execution (crt_gcd_exec hs).
Proof.
  move=> m n Hmod. apply: crt_run_total_correct;
    [exact: crt_gcd_exec_exists | reflexivity].
Qed.

Theorem normalize_execution_proved hs :
  T_normalize_execution (crt_normalize_exec hs).
Proof.
  move=> z d Hz Hd. apply: crt_run_total_correct;
    [exact: crt_normalize_exec_exists | reflexivity].
Qed.

Theorem inverse_execution_proved hs : T_inverse_execution (crt_inverse_exec hs).
Proof.
  move=> A B Hin Hcop. apply: crt_run_total_correct;
    first exact: crt_inverse_exec_exists.
  apply: crt_inverse_Z_correct; last exact Hcop. destruct Hin; lia.
Qed.

Theorem period_execution_proved hs : T_period_execution (crt_period_exec hs).
Proof.
  move=> m n Hm Hn. apply: crt_run_total_correct;
    first exact: crt_period_exec_exists.
  exact (proj1 (crt_period_Z_correct m n)).
Qed.

Theorem solve_execution_proved hs : T_solve_execution (crt_solve_exec hs).
Proof.
  move=> a m b n Ha Hm Hb Hn. apply: crt_run_total_correct;
    first exact: crt_solve_exec_exists.
  exact (proj1 (crt_solve_Z_correct a m b n)).
Qed.

End Host.

Print Assumptions gcd_execution_proved.
Print Assumptions normalize_execution_proved.
Print Assumptions inverse_execution_proved.
Print Assumptions period_execution_proved.
Print Assumptions solve_execution_proved.
