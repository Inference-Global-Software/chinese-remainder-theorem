(* Exact first classifier loop, including early invalid exit and checked cursor. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit MultiExitK NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTSystemStatements CRTFinite.
From CRTSystems Require Import SystemRuntime SystemMemory SystemControl SystemCalls FullWidthExecution BatchArithmetic BatchCount BatchValidation BatchClassState.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition bc_bad rs ms i := negb (FiniteSystem.validb
 (Wasm_int.Int64.signed (List.nth i rs (Wasm_int.Int64.repr 0)),
  Wasm_int.Int64.signed (List.nth i ms (Wasm_int.Int64.repr 0)))).
Fixpoint bc_validate fuel i rs ms : nat * Z :=
 match fuel with O => (i,0) | S k =>
 if bc_bad rs ms i then (i,-2) else bc_validate k (S i) rs ms end.
Definition bc_validation_stop := [::BI_const_num (SM.Vi64 (-2));BI_local_set 3%num;BI_br 2%num].
Definition bc_validation_step := validation_item 0%num 1%num 4%num 7%num ++
 [::BI_if (BT_valtype None) bc_validation_stop [::]] ++
 bc_inc_value 4%num ++ [::BI_local_set 4%num;BI_br 0%num].
Definition bc_validation_body := batch_loop_condition 4%num ++ [::BI_br_if 1%num] ++ bc_validation_step.
Lemma bc_validation_body_shape : classifier_validation_loop = bc_validation_body.
Proof. reflexivity. Qed.
Section Host.
Context `{ho:host}.
Context (mem:meminst).
Lemma bc_validation_item rb mb count i rs ms :
 array_region mem rb rs -> array_region mem mb ms -> ((i < count)%coq_nat /\ (count <= 16)%coq_nat) ->
 system_triple mem (AS_base [::] (BCHead rb mb count 0 i))
 (validation_item 0%num 1%num 4%num 7%num)
 (AS_base [::T_const (VAL_int32 (wasm_bool (bc_bad rs ms i)))] (BCHead rb mb count 0 i)).
Proof.
 move=> Hr Hm Hi. have Hrn : List.nth_error rs i = Some (List.nth i rs (Wasm_int.Int64.repr 0)).
 { apply List.nth_error_nth'. have Hlen := proj1 Hr. change (List.length rs = 16%nat) in Hlen. lia. }
 have Hmn : List.nth_error ms i = Some (List.nth i ms (Wasm_int.Int64.repr 0)).
 { apply List.nth_error_nth'. have Hlen := proj1 Hm. change (List.length ms = 16%nat) in Hlen. lia. }
 rewrite /bc_bad -validation_bad_model.
 apply: (validation_item_sem Hr Hrn Hm Hmn); bc_unfold; first [bc_pinned|bc_present|bc_stable].
Qed.
Lemma bc_validation_condition rb mb count i : ((i <= count)%coq_nat /\ (count <= 16)%coq_nat) ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (BCHead rb mb count 0 i))
 (batch_loop_condition 4%num)
 (AS_base [::T_const (VAL_int32 (wasm_bool (negb (Z.of_nat i <? Z.of_nat count))))] (BCHead rb mb count 0 i)).
Proof. move=> Hi. apply: batch_loop_condition_sem; try (unfold batch_word32; lia); bc_unfold; bc_pinned. Qed.
Lemma bc_validation_loop rb mb count fuel i rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count <= 16)%coq_nat ->
 (i + fuel = count)%coq_nat ->
 let result := bc_validate fuel i rs ms in
 let Q := AS_base [::] (BCHead rb mb count (snd result) (fst result)) in
 system_mxk mem (AS_base [::] (BCHead rb mb count 0 i))
 [::BI_loop (BT_valtype None) bc_validation_body] Q crt_false_assert
 (fun k => if k is O then Q else crt_false_assert).
Proof.
 move=> Hr Hm Hcount. move: i. induction fuel as [|fuel IH]; move=> i Hsum; cbn [bc_validate].
 - have Ei : i=count by lia. subst i.
   apply: (system_loop_unroll (Pback:=crt_false_assert) (t1s:=[::]) (t2s:=[::])); try reflexivity.
   + move=> V vs h [Hs _]. by case: Hs => <-.
   + move=> V vs h [_ HF]. by case: HF.
   + rewrite /bc_validation_body.
     apply: (system_mxk_seq (es1:=batch_loop_condition 4%num)
     (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (BCHead rb mb count 0 count))); first reflexivity.
     * apply: system_mxk_lift. apply: system_triple_of_pure.
       have H := bc_validation_condition (rb:=rb) (mb:=mb) (count:=count) (i:=count) ltac:(lia).
       by rewrite Z.ltb_irrefl in H.
     * apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=crt_false_assert)); first reflexivity.
       -- apply: system_mxk_of_pure. apply: (crt_br_if_true_sem (k:=1%nat)). by [].
       -- apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
   + apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
 - have Hi : (i < count)%coq_nat by lia.
   have Econd : (Z.of_nat i <? Z.of_nat count) = true by apply/Z.ltb_lt; lia.
   case Ebad: (bc_bad rs ms i).
   + apply: (system_loop_unroll (Pback:=crt_false_assert) (t1s:=[::]) (t2s:=[::])); try reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * move=> V vs h [_ HF]. by case: HF.
     * rewrite /bc_validation_body.
       apply: (system_mxk_seq (es1:=batch_loop_condition 4%num)
       (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BCHead rb mb count 0 i))); first reflexivity.
       -- apply: system_mxk_lift. apply: system_triple_of_pure.
          have H := bc_validation_condition (rb:=rb) (mb:=mb) (count:=count) (i:=i) ltac:(lia).
          by rewrite Econd in H.
       -- apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=AS_base [::] (BCHead rb mb count 0 i))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: crt_br_if_false_sem.
          ++ rewrite /bc_validation_step.
             apply: (system_mxk_seq (es1:=validation_item 0%num 1%num 4%num 7%num)
             (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (BCHead rb mb count 0 i))); first reflexivity.
             ** apply: system_mxk_lift. have H := bc_validation_item Hr Hm (count:=count) (i:=i) ltac:(lia). by rewrite Ebad in H.
             ** apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) bc_validation_stop [::]]) (Q1:=crt_false_assert)); first reflexivity.
                --- apply: (system_if_const (t2s:=[::])); first reflexivity.
                    +++ move=> V vs h [_ HF]. by case: HF.
                    +++ rewrite /bc_validation_stop.
                        apply: (system_mxk_seq (es1:=[::BI_const_num (SM.Vi64 (-2));BI_local_set 3%num])
                        (Q1:=AS_base [::] (BCHead rb mb count (-2) i))); first reflexivity.
                        *** apply: system_mxk_lift. apply: system_triple_of_pure.
                            apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 (-2))])
                            (Q:=AS_base [::T_const (SM.Vi64 (-2))] (BCHead rb mb count 0 i))).
                            ---- exact: sem_const_framed.
                            ---- exact: bc_set_head_status.
                        *** apply: system_mxk_of_pure. apply: (sem_mxk_br_k (k:=2%nat)). by [].
                --- apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
     * apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
   + apply: (system_loop_unroll (Pback:=AS_base [::] (BCHead rb mb count 0 (S i))) (t1s:=[::]) (t2s:=[::])); try reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * rewrite /bc_validation_body.
       apply: (system_mxk_seq (es1:=batch_loop_condition 4%num)
       (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BCHead rb mb count 0 i))); first reflexivity.
       -- apply: system_mxk_lift. apply: system_triple_of_pure.
          have H := bc_validation_condition (rb:=rb) (mb:=mb) (count:=count) (i:=i) ltac:(lia). by rewrite Econd in H.
       -- apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=AS_base [::] (BCHead rb mb count 0 i))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: crt_br_if_false_sem.
          ++ rewrite /bc_validation_step.
             apply: (system_mxk_seq (es1:=validation_item 0%num 1%num 4%num 7%num)
             (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BCHead rb mb count 0 i))); first reflexivity.
             ** apply: system_mxk_lift. have H := bc_validation_item Hr Hm (count:=count) (i:=i) ltac:(lia). by rewrite Ebad in H.
             ** apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) bc_validation_stop [::]]) (Q1:=AS_base [::] (BCHead rb mb count 0 i))); first reflexivity.
                --- apply: (system_if_const (t2s:=[::])); first reflexivity.
                    +++ move=> V vs h [Hs _]. by case: Hs => <-.
                    +++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_nil_same.
                --- rewrite -catA.
                    apply: (system_mxk_seq (es1:=bc_inc_value 4%num ++ [::BI_local_set 4%num])
                    (Q1:=AS_base [::] (BCHead rb mb count 0 (S i)))); first reflexivity.
                    +++ apply: system_mxk_lift. apply: system_triple_of_pure. apply: bc_inc_head. lia.
                    +++ apply: system_mxk_of_pure. apply: (sem_mxk_br_k (k:=0%nat)). by [].
     * apply: IH. lia.
Qed.
End Host.
