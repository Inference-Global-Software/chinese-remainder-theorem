From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit
 NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTLoops CRTSystemStatements CRTSystemArithmetic.
From CRTWasm Require Import CRTAPIModel.
From CRTSystems Require Import ReadOnly SystemRuntime.
From CRTSystems Require Import FullWidthExecution SystemCalls FullWidthInversePrefix.
From CRTSystemGenerated Require Import main.
Module SM := CRTSystemGenerated.main.
Import FullWidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Section Host.
Context `{ho : host}.
Context (mem : meminst).
Ltac pinned_tac := solve [exact: pinned_bare | apply: pinned_left; pinned_tac | apply: pinned_right; pinned_tac].
Definition inverse_runtime_triple P es Q :=
  forall f, f_inst f = system_inst -> sem_triple_at (system_store mem) f P es Q.
Definition inverse_runtime_mx P es Qn Qr Qb :=
  forall f, f_inst f = system_inst -> sem_mx_at (system_store mem) f P es Qn Qr Qb.

Lemma inverse_runtime_triple_of_triple P es Q :
  sem_triple (triv_ctx SM.main) P es Q -> inverse_runtime_triple P es Q.
Proof.
  move=> H f Hinst. apply: sem_triple_at_of_triple; first exact H.
  by rewrite /frame_agrees Hinst /system_inst /triv_ctx.
Qed.

Lemma inverse_runtime_mx_of_mx P es Qn Qr Qb :
  sem_mx (triv_ctx SM.main) P es Qn Qr Qb -> inverse_runtime_mx P es Qn Qr Qb.
Proof.
  move=> H f Hinst. apply: sem_mx_at_of_mx; first exact H.
  by rewrite /frame_agrees Hinst /system_inst /triv_ctx.
Qed.

Lemma inverse_runtime_mx_after_triple P Q1 Qn Qr Qb es1 es2 :
  all ro_bi es1 ->
  inverse_runtime_triple P es1 Q1 -> inverse_runtime_mx Q1 es2 Qn Qr Qb ->
  inverse_runtime_mx P (es1 ++ es2) Qn Qr Qb.
Proof.
  move=> Hro1 H1 H2 f Hinst hs V vs h HP Hr.
  have [s1 [f1 [V1 [vs1 [h1 [Hrig1 [Hred1 [HQ1 Hr1]]]]]]]] :=
    H1 f Hinst hs V vs h HP Hr.
  have Hro : ro_es (vn_to_e vs ++ to_e_list es1).
  { rewrite ro_es_cat ro_es_basic Hro1 andbT.
    clear - vs hfc memory ho. induction vs; simpl; auto. }
  have Hstore : s1 = system_store mem :=
   proj1 (proj2 (ro_reduce_trans_preserved (system_store_readonly (mem:=mem)) Hro Hred1)).
  subst s1.
  have Hinst1 : f_inst f1 = system_inst.
  { by rewrite (reduce_trans_frame_inst Hred1) Hinst. }
  have [s2 [f2 [V2 [vs2 [h2 [Hrig2 [Hr2 Hd2]]]]]]] :=
    H2 f1 Hinst1 hs V1 vs1 h1 HQ1 Hr1.
  have Hsuffix := reduce_trans_suffix (to_e_list es2) Hred1.
  exists s2, f2, V2, vs2, h2.
  split; first by rewrite Hrig2 Hrig1. split; first exact Hr2.
  have Hcompose : forall X,
      reduce_trans (hs, (system_store mem), f1, vn_to_e vs1 ++ to_e_list es2) X ->
      reduce_trans (hs, (system_store mem), f, vn_to_e vs ++ to_e_list (es1 ++ es2)) X.
  { move=> X HX. apply: (rtt_trans (y := (hs, (system_store mem), f1, vn_to_e vs1 ++ to_e_list es2))).
    - rewrite to_e_list_cat catA. exact Hsuffix.
    - exact HX. }
  case: Hd2 => [[Hred2 HQ2]|[[i2 [lh2 [Hred2 HQ2]]]|[rest2 [Hred2 HQ2]]]].
  - left. by split; [apply: Hcompose |].
  - right; left. exists i2, lh2. by split; [apply: Hcompose |].
  - right; right. exists rest2. by split; [apply: Hcompose |].
Qed.

Lemma inverse_entry_entails A B :
  aentails (AS_base [::] (HA_and (args_pinned [:: SM.Vi64 B; SM.Vi64 A] 0%num)
    (func_pre_h SM.main SM.inverse_coprime))) (AS_base [::] (inverse_entry A B)).
Proof.
  move=> V [vs h] /= [Hs [[P0 [P1 _]] [[T0 [T1 _]] [T2 [T3 [T4 [T5 [T6 [T7 [T8 [T9 [T10 [T11 [T12 [T13 [T14 _]]]]]]]]]]]]]]]].
  split; first exact Hs.
  split; first exact P0.
  split; first exact P1.
  split; first by case: T2 => [w [Ew _]]; exists w.
  split; first by case: T3 => [w [Ew _]]; exists w.
  split; first by case: T4 => [w [Ew _]]; exists w.
  split; first by case: T5 => [w [Ew _]]; exists w.
  split; first by case: T6 => [w [Ew _]]; exists w.
  split; first by case: T7 => [w [Ew _]]; exists w.
  split; first by case: T8 => [w [Ew _]]; exists w.
  split; first by case: T9 => [w [Ew _]]; exists w.
  split; first by case: T10 => [w [Ew _]]; exists w.
  split; first by case: T11 => [w [Ew _]]; exists w.
  split; first by case: T12 => [w [Ew _]]; exists w.
  split; first by case: T13 => [w [Ew _]]; exists w.
  split; first by case: T14 => [w [Ew _]]; exists w.
  exact I.
Qed.
Lemma inverse_body_to_computation B A u :
  inverse_runtime_mx (AS_base [::] (inverse_entry A B)) (modfunc_body SM.inverse_coprime)
    (AS_base [:: T_const (SM.Vi64 u)] HA_true)
    (AS_base [:: T_const (SM.Vi64 u)] HA_true)
    (AS_base [:: T_const (SM.Vi64 u)] HA_true) ->
  system_computes mem 2%nat [:: SM.Vi64 B; SM.Vi64 A] [:: SM.Vi64 u].
Proof.
  move=> Hbody.
  change (args_typed [:: SM.Vi64 B; SM.Vi64 A] [:: T_num T_i64; T_num T_i64] /\
    results_typed [:: SM.Vi64 u] [:: T_num T_i64] /\
    exists defaults, default_vals (modfunc_locals SM.inverse_coprime) = Some defaults /\
      sem_mx_at (system_store mem) (activation_frame system_initial_runtime [:: SM.Vi64 B; SM.Vi64 A] defaults)
        (AS_base [::] (HA_and (args_pinned [:: SM.Vi64 B; SM.Vi64 A] 0%num)
          (func_pre_h SM.main SM.inverse_coprime)))
        (modfunc_body SM.inverse_coprime)
        (AS_base [:: T_const (SM.Vi64 u)] HA_true)
        (AS_base [:: T_const (SM.Vi64 u)] HA_true)
        (AS_base [:: T_const (SM.Vi64 u)] HA_true)).
  split; first by repeat split. split; first by repeat split.
  exists [:: VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0); VAL_num (SM.Vi64 0)].
  split; first by [].
  move=> hs V vs h HP Hr. apply: Hbody; [by [] | | exact Hr].
  exact: (inverse_entry_entails HP).
Qed.
Lemma inverse_reads_sem A B e :
  sem_triple (triv_ctx SM.main) (AS_base [::] (inverse_head A B e))
    [:: BI_local_get 6%num; BI_local_get 1%num]
    (AS_base [:: T_const (SM.Vi64 (t0 e)); T_const (SM.Vi64 A)] (inverse_head A B e)).
Proof.
  apply: (sem_seq (es1 := [:: BI_local_get 6%num])
    (Q := AS_base [:: T_const (SM.Vi64 (t0 e))] (inverse_head A B e))).
  - apply: get_pinned_frame. pinned_tac.
  - apply: get_pinned_frame. pinned_tac.
Qed.
Theorem inverse_machine_computes B A : eea_inputs A B -> Z.gcd A B = 1 ->
  system_computes mem 2%nat [:: SM.Vi64 B; SM.Vi64 A]
    [:: SM.Vi64 (FullWidth.inverse_model B A)].
Proof.
  move=> Hin Hcop.
  have Hinitial := eea_init_proved A B Hin.
  have [final [Hrun [Hfinal Hzero]]] := @FullWidthInversePrefix.eea_run_terminates A B (eea_init A B) Hin Hinitial.
  have Hout := eea_exit_proved A B final Hin Hfinal Hzero.
  have [Hu Hinv] := proj2 (proj2 Hout) Hcop.
  have HA : 1 <= A <= MAX by clear -Hin; destruct Hin as [[HB HBA] HA]; lia.
  have Wu : word (t0 final).
  { apply: (abs_word_small _ A); last exact (proj2 HA).
    destruct Hfinal as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT & _).
    exact HT. }
  have Eresult : t0 final mod A = FullWidth.inverse_model B A.
  { have [Hmrange Hminv] := inverse_model_proved A B Hin Hcop.
    have E1 := crt_inverse_Z_unique B A (t0 final mod A) ltac:(lia) Hcop Hu Hinv.
    have E2 := crt_inverse_Z_unique B A (FullWidth.inverse_model B A) ltac:(lia) Hcop Hmrange Hminv.
    congruence. }
  rewrite -Eresult.
  apply: inverse_body_to_computation.
  rewrite inverse_body_shape.
  change (inverse_runtime_mx (AS_base [::] (inverse_entry A B))
    ((inverse_prologue_code ++
      [:: BI_block (BT_valtype None) [:: BI_loop (BT_valtype None) inverse_loop_code]]) ++
      [:: BI_local_get 6%num; BI_local_get 1%num; BI_call 1%num; BI_return; BI_unreachable])
    (AS_base [:: T_const (SM.Vi64 (t0 final mod A))] HA_true)
    (AS_base [:: T_const (SM.Vi64 (t0 final mod A))] HA_true)
    (AS_base [:: T_const (SM.Vi64 (t0 final mod A))] HA_true)).
  apply: (inverse_runtime_mx_after_triple
    (es1 := inverse_prologue_code ++
      [:: BI_block (BT_valtype None) [:: BI_loop (BT_valtype None) inverse_loop_code]])
    (Q1 := AS_base [::] (inverse_head A B final))).
  - by vm_compute.
  - apply: inverse_runtime_triple_of_triple. exact: (inverse_prefix_sem Hin Hrun).
  - apply: (inverse_runtime_mx_after_triple
      (es1 := [:: BI_local_get 6%num; BI_local_get 1%num])
      (Q1 := AS_base [:: T_const (SM.Vi64 (t0 final)); T_const (SM.Vi64 A)] (inverse_head A B final))).
    + by [].
    + apply: inverse_runtime_triple_of_triple. exact: inverse_reads_sem.
    + apply: (inverse_runtime_mx_after_triple (es1 := [:: BI_call 1%num])
        (Q1 := AS_base [:: T_const (SM.Vi64 (t0 final mod A))] (inverse_head A B final))).
      * by [].
      * move=> f Hinst. exact: (crt_normalize_call Hinst Wu HA).
      * apply: inverse_runtime_mx_of_mx.
        apply: (sem_mx_conseq
          (P' := AS_base [:: T_const (SM.Vi64 (t0 final mod A))] HA_true)
          (Qn' := AS_base [:: T_const (SM.Vi64 (t0 final mod A))] HA_true)
          (Qr' := AS_base [:: T_const (SM.Vi64 (t0 final mod A))] HA_true)
          (Qb' := AS_base [:: T_const (SM.Vi64 (t0 final mod A))] HA_true)).
        -- move=> V [vs h] [Hs _]. by split.
        -- by [].
        -- by [].
        -- by [].
        -- exact: sem_mx_return_suffix.
Qed.
End Host.
Print Assumptions inverse_machine_computes.
