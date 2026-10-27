From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem host.
From WasmVerifier Require Import Assertions Semantics Activation Verifier.
From CRT Require Import CRTStatements CRTSystemStatements CRTSystemArithmetic.
From CRTWasm Require Import CRTContracts.
From CRTSystems Require Import SystemRuntime.
From CRTSystems Require Import FullWidthExecution SystemCalls FullWidthInverseExecution.
Module SM := CRTSystemGenerated.main.
Import FullWidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Section Host.
Context `{ho : host}.
Context (mem : meminst).
Definition system_caller_frame : frame := Build_frame [::] system_inst.
Lemma system_run_word hs i args result :
 system_run mem hs i args result -> word result.
Proof. move=> [hs' [s' [f' [v [_ ->]]]]]. exact: crt_contract_signed_word. Qed.
Lemma system_run_of_call hs i args result : word result ->
  sem_triple_at (system_store mem) system_caller_frame
    (AS_base (map T_const args) HA_true)
    [:: BI_call (i)]
    (AS_base [:: T_const (SM.Vi64 result)] HA_true) ->
  system_run mem hs i args result.
Proof.
  move=> Hword Hcall.
  pose V : valuation :=
    {| val_log := [::]; val_loc := loc_read system_caller_frame;
       val_glob := glob_read (@system_store hfc memory mem) system_caller_frame;
       val_fun := fun _ _ => None |}.
  have Hpre : assertion_denote V (AS_base (map T_const args) HA_true)
      (args, aheap_empty).
  { split; last exact I. exact: crt_stack_consts. }
  have Hreify : reifies_sto (system_store mem) system_caller_frame aheap_empty V.
  { apply reifies_sto_empty; reflexivity. }
  have [s' [f' [V' [rs [h' [_ [Hrun [Hpost _]]]]]]]] :=
    Hcall hs V args aheap_empty Hpre Hreify.
  destruct Hpost as [Hrs _]. simpl in Hrs. inversion Hrs; subst rs.
  exists hs, s', f', (Wasm_int.Int64.repr result). split.
  - exact Hrun.
  - symmetry. exact: crt_i64_signed_repr.
Qed.

Lemma system_run_total_correct hs i args result post :
 system_run mem hs i args result -> post result ->
 total_correct (system_run mem hs i args) post.
Proof.
 move=> Hrun Hpost. split; first by exists result.
 move=> r Hr. split; first exact: system_run_word Hr.
 by rewrite (system_run_unique Hr Hrun).
Qed.
Lemma system_gcd_exec_exists hs m n : moduli m n ->
 system_run mem hs 0%num [::SM.Vi64 m;SM.Vi64 n] (Z.gcd m n).
Proof.
 move=> Hmod. have [r [Hrun [Er Wr]]] := @FullWidthExecution.gcd_initial_run_correct m n Hmod.
 subst r. apply: system_run_of_call; first exact Wr.
 apply: crt_gcd_call; [reflexivity|exact Hmod].
Qed.
Lemma system_normalize_exec_exists hs z d : word z -> 1 <= d <= MAX ->
 system_run mem hs 1%num [::SM.Vi64 z;SM.Vi64 d] (z mod d).
Proof.
 move=> Hz Hd. have Hrange := Z.mod_pos_bound z d ltac:(lia).
 apply: system_run_of_call.
 - apply nonnegative_word. lia.
 - apply: crt_normalize_call; [reflexivity|exact Hz|exact Hd].
Qed.
Lemma system_inverse_exec_exists hs B A : eea_inputs A B -> Z.gcd A B = 1 ->
 system_run mem hs 2%num [::SM.Vi64 B;SM.Vi64 A] (FullWidth.inverse_model B A).
Proof.
 move=> Hin Hcop. have [Hrange _] := inverse_model_proved A B Hin Hcop.
 apply: system_run_of_call.
 - apply nonnegative_word. unfold eea_inputs in Hin; lia.
 - apply: crt_inverse_call_from_computes; [reflexivity|].
   exact: inverse_machine_computes.
Qed.
Lemma system_add_exec_exists hs x y d : 1 <= d <= MAX -> 0 <= x < d -> 0 <= y < d ->
 system_run mem hs 3%num [::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d] (FullWidth.add_mod x y d).
Proof.
 move=> Hd Hx Hy. have [_ [_ [_ [Wr _]]]] := add_mod_proved x y d Hd Hx Hy.
 apply: system_run_of_call; first exact Wr.
 apply: crt_add_call; [reflexivity|exact Hd|exact Hx|exact Hy].
Qed.
End Host.
Print Assumptions system_run_total_correct.
Print Assumptions system_inverse_exec_exists.
Print Assumptions system_add_exec_exists.
