(* Full lexicographic compatibility scan over the emitted nested loops. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit MultiExitK NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTSystemStatements CRTFinite.
From CRTWasm Require Import CRTPublicExecution.
From CRTSystems Require Import SystemRuntime SystemMemory SystemControl SystemCalls FullWidthExecution ArrayAccess BatchArithmetic BatchCount BatchValidation BatchPair BatchClassState BatchValidateLoop BatchPairRow.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition bc_status_test := [::BI_local_get 3%num;BI_const_num (SM.Vi64 0);BI_relop T_i64 (Relop_i ROI_ne)].
Definition bc_outer_scan := bc_inc_value 4%num ++ [::BI_local_set 5%num;
 BI_block (BT_valtype None) [::BI_loop (BT_valtype None) bc_pair_body]] ++ bc_status_test.
Definition bc_outer_step := bc_outer_scan ++ [::BI_if (BT_valtype None) [::BI_br 2%num] [::]] ++
 bc_inc_value 4%num ++ [::BI_local_set 4%num;BI_br 0%num].
Definition bc_outer_body := batch_loop_condition 4%num ++ [::BI_br_if 1%num] ++ bc_outer_step.
Lemma bc_outer_body_shape : classifier_pair_outer = bc_outer_body.
Proof. reflexivity. Qed.
Fixpoint bc_pairs fuel i rs ms : nat * Z :=
 match fuel with O => (i,0) | S k =>
 if snd (bc_pair_row k i (S i) rs ms) =? 0 then bc_pairs k (S i) rs ms else (i,-1) end.
Lemma bc_pair_row_status fuel i j rs ms :
 snd (bc_pair_row fuel i j rs ms) = 0 \/ snd (bc_pair_row fuel i j rs ms) = -1.
Proof. move: j. induction fuel; move=> j; cbn [bc_pair_row]; first by left. case: bc_pair_bad; first by right. exact: IHfuel. Qed.
Section Host.
Context `{ho:host}.
Context (mem:meminst).
Lemma bc_status_sem H s : word s -> pinned 3%num (SM.Vi64 s) H ->
 sem_triple (triv_ctx SM.main) (AS_base [::] H) bc_status_test
 (AS_base [::T_const (VAL_int32 (wasm_bool (negb (s =? 0))))] H).
Proof.
 move=> Ws Hp. have Wz : word 0 by unfold word, i64_min, i64_max; lia.
 rewrite /bc_status_test -(crt_public_ne Ws Wz). apply: test_pin_const; try reflexivity. exact Hp.
Qed.
Lemma bc_start_row rb mb count i : (i<=16)%coq_nat ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (BCHead rb mb count 0 i))
 (bc_inc_value 4%num ++ [::BI_local_set 5%num])
 (AS_base [::] (BCRow rb mb count 0 i (S i))).
Proof.
 move=> Hi. apply: (sem_seq (Q:=AS_base [::T_const (SM.Vi32 (Z.of_nat (S i)))] (BCHead rb mb count 0 i))).
 - apply: bc_inc_value_sem; first exact Hi; bc_unfold; try bc_pinned; try bc_present; move=> z; bc_stable.
 - rewrite /BCRow /bc_pin. apply: sem_local_set_const_frame; bc_unfold; [bc_stable|bc_present].
Qed.
Lemma bc_row_block rb mb count fuel i j rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat ->
 (i<count)%coq_nat -> bc_all_valid count rs ms -> (j+fuel=count)%coq_nat ->
 system_triple mem (AS_base [::] (BCRow rb mb count 0 i j))
 [::BI_block (BT_valtype None) [::BI_loop (BT_valtype None) bc_pair_body]]
 (AS_base [::] (BCHead rb mb count (snd (bc_pair_row fuel i j rs ms)) i)).
Proof.
 move=> Hr Hm Hc Hi Hv Hsum.
 apply: (batch_triple_conseq (P':=AS_base [::] (BCRow rb mb count 0 i j))
 (Q':=AS_base [::] (BCRow rb mb count (snd (bc_pair_row fuel i j rs ms)) i (fst (bc_pair_row fuel i j rs ms))))).
 - by [].
 - move=> V [vs h] [Hs [_ HH]]. by split.
 - apply: system_triple_of_mxk. apply: (system_mxk_block (t1s:=[::]) (t2s:=[::])
   (Qb:=fun k => if k is O then AS_base [::] (BCRow rb mb count (snd (bc_pair_row fuel i j rs ms)) i (fst (bc_pair_row fuel i j rs ms))) else crt_false_assert)); try reflexivity.
   + move=> V vs h [Hs _]. by case: Hs => <-.
   + exact: bc_pair_row_loop.
Qed.
Lemma bc_outer_scan_sem rb mb count fuel i rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat ->
 bc_all_valid count rs ms -> (S i+fuel=count)%coq_nat ->
 let status := snd (bc_pair_row fuel i (S i) rs ms) in
 system_triple mem (AS_base [::] (BCHead rb mb count 0 i)) bc_outer_scan
 (AS_base [::T_const (VAL_int32 (wasm_bool (negb (status =? 0))))] (BCHead rb mb count status i)).
Proof.
 move=> Hr Hm Hc Hv Hsum status. rewrite /bc_outer_scan -catA.
 apply: (system_triple_seq (es1:=bc_inc_value 4%num ++ [::BI_local_set 5%num])
 (Q1:=AS_base [::] (BCRow rb mb count 0 i (S i)))); first reflexivity.
 - apply: system_triple_of_pure. apply: bc_start_row. lia.
 - apply: (system_triple_seq (es1:=[::BI_block (BT_valtype None) [::BI_loop (BT_valtype None) bc_pair_body]])
   (Q1:=AS_base [::] (BCHead rb mb count status i))); first reflexivity.
   + apply: bc_row_block; try assumption; lia.
   + apply: system_triple_of_pure. apply: bc_status_sem.
     * have [H|H] := bc_pair_row_status fuel i (S i) rs ms; rewrite /status H; unfold word, i64_min, i64_max; lia.
     * bc_unfold; bc_pinned.
Qed.
Lemma bc_pair_outer_loop rb mb count fuel i rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat ->
 bc_all_valid count rs ms -> (i+fuel=count)%coq_nat ->
 let result := bc_pairs fuel i rs ms in
 let Q := AS_base [::] (BCHead rb mb count (snd result) (fst result)) in
 system_mxk mem (AS_base [::] (BCHead rb mb count 0 i))
 [::BI_loop (BT_valtype None) bc_outer_body] Q crt_false_assert
 (fun k => if k is O then Q else crt_false_assert).
Proof.
 move=> Hr Hm Hcount Hv. move: i. induction fuel as [|fuel IH]; move=> i Hsum; cbn [bc_pairs].
 - have Ei : i=count by lia. subst i.
   apply: (system_loop_unroll (Pback:=crt_false_assert) (t1s:=[::]) (t2s:=[::])); try reflexivity.
   + move=> V vs h [Hs _]. by case: Hs => <-.
   + move=> V vs h [_ HF]. by case: HF.
   + rewrite /bc_outer_body.
     apply: (system_mxk_seq (es1:=batch_loop_condition 4%num)
     (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (BCHead rb mb count 0 count))); first reflexivity.
     * apply: system_mxk_lift. apply: system_triple_of_pure.
       have H := bc_validation_condition (rb:=rb) (mb:=mb) (count:=count) (i:=count) ltac:(lia).
       by rewrite Z.ltb_irrefl in H.
     * apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=crt_false_assert)); first reflexivity.
       -- apply: system_mxk_of_pure. apply: (crt_br_if_true_sem (k:=1%nat)). by [].
       -- apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
   + apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
 - have Hi : (i<count)%coq_nat by lia.
   have Econd : (Z.of_nat i <? Z.of_nat count) = true by apply/Z.ltb_lt; lia.
   have [Erow|Erow] := bc_pair_row_status fuel i (S i) rs ms; rewrite Erow; cbn.
   + apply: (system_loop_unroll (Pback:=AS_base [::] (BCHead rb mb count 0 (S i))) (t1s:=[::]) (t2s:=[::])); try reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * rewrite /bc_outer_body.
       apply: (system_mxk_seq (es1:=batch_loop_condition 4%num)
       (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BCHead rb mb count 0 i))); first reflexivity.
       -- apply: system_mxk_lift. apply: system_triple_of_pure.
          have H := bc_validation_condition (rb:=rb) (mb:=mb) (count:=count) (i:=i) ltac:(lia). by rewrite Econd in H.
       -- apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=AS_base [::] (BCHead rb mb count 0 i))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: crt_br_if_false_sem.
          ++ rewrite /bc_outer_step.
             apply: (system_mxk_seq (es1:=bc_outer_scan)
             (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BCHead rb mb count 0 i))); first reflexivity.
             ** apply: system_mxk_lift. have H := bc_outer_scan_sem Hr Hm Hcount Hv (fuel:=fuel) (i:=i) ltac:(lia). by rewrite Erow in H.
             ** apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_br 2%num] [::]]) (Q1:=AS_base [::] (BCHead rb mb count 0 i))); first reflexivity.
                --- apply: (system_if_const (t2s:=[::])); first reflexivity.
                    +++ move=> V vs h [Hs _]. by case: Hs => <-.
                    +++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_nil_same.
                --- idtac.
                    apply: (system_mxk_seq (es1:=bc_inc_value 4%num ++ [::BI_local_set 4%num])
                    (Q1:=AS_base [::] (BCHead rb mb count 0 (S i)))); first reflexivity.
                    +++ apply: system_mxk_lift. apply: system_triple_of_pure. apply: bc_inc_head. lia.
                    +++ apply: system_mxk_of_pure. apply: (sem_mxk_br_k (k:=0%nat)). by [].
     * apply: IH. lia.
   + apply: (system_loop_unroll (Pback:=crt_false_assert) (t1s:=[::]) (t2s:=[::])); try reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * move=> V vs h [_ HF]. by case: HF.
     * rewrite /bc_outer_body.
       apply: (system_mxk_seq (es1:=batch_loop_condition 4%num)
       (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BCHead rb mb count 0 i))); first reflexivity.
       -- apply: system_mxk_lift. apply: system_triple_of_pure.
          have H := bc_validation_condition (rb:=rb) (mb:=mb) (count:=count) (i:=i) ltac:(lia). by rewrite Econd in H.
       -- apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=AS_base [::] (BCHead rb mb count 0 i))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: crt_br_if_false_sem.
          ++ rewrite /bc_outer_step.
             apply: (system_mxk_seq (es1:=bc_outer_scan)
             (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (BCHead rb mb count (-1) i))); first reflexivity.
             ** apply: system_mxk_lift. have H := bc_outer_scan_sem Hr Hm Hcount Hv (fuel:=fuel) (i:=i) ltac:(lia). by rewrite Erow in H.
             ** apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_br 2%num] [::]]) (Q1:=crt_false_assert)); first reflexivity.
                --- apply: (system_if_const (t2s:=[::])); first reflexivity.
                    +++ move=> V vs h [_ HF]. by case: HF.
                    +++ apply: system_mxk_of_pure. apply: (sem_mxk_br_k (k:=2%nat)). by [].
                --- apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
     * apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
Qed.
End Host.
