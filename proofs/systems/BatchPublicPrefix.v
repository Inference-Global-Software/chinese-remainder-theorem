(* Shared raw-ABI argument call and status dispatch for both public batch exports. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit MultiExitK NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTSystemStatements CRTFinite.
From CRTWasm Require Import CRTPublicExecution.
From CRTSystems Require Import SystemRuntime SystemMemory SystemControl SystemCalls FullWidthExecution MergePeriodExecution ArrayAccess BatchArithmetic BatchCount BatchClassState BatchPairLoop BatchClassModel BatchClassExecution.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition batch_classify_call_code := [::BI_local_get 0%num;BI_local_get 1%num;BI_local_get 2%num;BI_call 7%num].
Definition batch_dispatch_code := [::BI_local_set 3%num] ++ bc_status_test ++
 [::BI_if (BT_valtype None) [::BI_local_get 3%num;BI_return] [::]].
Section Host.
Context `{ho:host}.
Context (mem:meminst).
Lemma batch_call_classifier H rb mb count rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat ->
 pinned 0%num (SM.Vi32 (Z.of_N rb)) H -> pinned 1%num (SM.Vi32 (Z.of_N mb)) H ->
 pinned 2%num (SM.Vi32 (Z.of_nat count)) H ->
 system_triple mem (AS_base [::] H) batch_classify_call_code
 (AS_base [::T_const (SM.Vi64 (bc_classify count rs ms))] H).
Proof.
 move=> Hr Hm Hc P0 P1 P2.
 have Ec : bc_result (Z.of_nat count) rs ms=bc_classify count rs ms.
 { rewrite /bc_result Nat2Z.id. have E1 : (Z.of_nat count <? 0)=false by apply/Z.ltb_ge;lia.
   have E2 : (16 <? Z.of_nat count)=false by apply/Z.ltb_ge;lia. by rewrite E1 E2. }
 rewrite /batch_classify_call_code.
 apply: (system_triple_seq (es1:=[::BI_local_get 0%num;BI_local_get 1%num;BI_local_get 2%num])
 (Q1:=AS_base [::T_const (SM.Vi32 (Z.of_N rb));T_const (SM.Vi32 (Z.of_N mb));T_const (SM.Vi32 (Z.of_nat count))] H)); first reflexivity.
 - apply: system_triple_of_pure.
   apply: (sem_seq (es1:=[::BI_local_get 0%num]) (Q:=AS_base [::T_const (SM.Vi32 (Z.of_N rb))] H)); first exact: get_pinned_frame.
   apply: (sem_seq (es1:=[::BI_local_get 1%num])
   (Q:=AS_base [::T_const (SM.Vi32 (Z.of_N rb));T_const (SM.Vi32 (Z.of_N mb))] H)); exact: get_pinned_frame.
 - rewrite -Ec. move=> f Hi. apply: crt_batch_classify_call; try assumption. unfold batch_word32; lia.
Qed.
Lemma batch_dispatch H s result tail : word s ->
 loc_stable 3%num (SM.Vi64 s) H -> loc_present 3%num H ->
 (s<>0 -> result=s) ->
 (s=0 -> system_mxk mem (AS_base [::] H) tail crt_false_assert
 (AS_base [::T_const (SM.Vi64 result)] HA_true) (fun _ => crt_false_assert)) ->
 system_mxk mem (AS_base [::T_const (SM.Vi64 s)] H) (batch_dispatch_code ++ tail)
 crt_false_assert (AS_base [::T_const (SM.Vi64 result)] HA_true) (fun _ => crt_false_assert).
Proof.
 move=> Ws S3 P3 Herror Htail. rewrite /batch_dispatch_code -catA.
 pose HS := HA_and (bc_pin 3%num (SM.Vi64 s)) H.
 apply: (system_mxk_seq (es1:=[::BI_local_set 3%num]) (Q1:=AS_base [::] HS)); first reflexivity.
 - apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_local_set_const_frame.
 - apply: (system_mxk_seq (es1:=bc_status_test)
   (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool (negb (s =? 0))))] HS)); first reflexivity.
   + apply: system_mxk_lift. apply: system_triple_of_pure. apply: bc_status_sem; first exact Ws. rewrite /HS /bc_pin. bc_pinned.
   + destruct (Z.eq_dec s 0) as [Hz|Hnz].
     * have Eb : negb (s =? 0)=false by rewrite Hz;reflexivity. rewrite Eb.
       apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_local_get 3%num;BI_return] [::]])
       (Q1:=AS_base [::] HS)); first reflexivity.
       -- apply: (system_if_const (t2s:=[::])); first reflexivity.
          ++ move=> V vs h [Hs _]. by case: Hs => <-.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_nil_same.
       -- apply: (system_mxk_conseq (P':=AS_base [::] H) (Qn':=crt_false_assert)
          (Qr':=AS_base [::T_const (SM.Vi64 result)] HA_true) (Qb':=fun _ => crt_false_assert)); try by [].
          ++ move=> V [vs h] [Hs [_ HH]]. by split.
          ++ move=> k V vh HP. exact HP.
          ++ exact: Htail.
     * have Eb : negb (s =? 0)=true by apply Bool.negb_true_iff; apply Z.eqb_neq.
       rewrite Eb (Herror Hnz).
       apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_local_get 3%num;BI_return] [::]]) (Q1:=crt_false_assert)); first reflexivity.
       -- apply: system_mxk_of_pure_no_break. apply: crt_if_true_returns.
          apply: (sem_mx_seq (es1:=[::BI_local_get 3%num]) (Q1:=AS_base [::T_const (SM.Vi64 s)] HS)).
          ++ apply: sem_mx_lift. apply: get_pinned_frame. rewrite /HS /bc_pin. bc_pinned.
          ++ exact: p_stack_return.
       -- apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
Qed.
End Host.
