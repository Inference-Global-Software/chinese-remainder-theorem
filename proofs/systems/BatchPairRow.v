(* Exact first classifier loop, including early invalid exit and checked cursor. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit MultiExitK NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTSystemStatements CRTFinite.
From CRTSystems Require Import SystemRuntime SystemMemory SystemControl SystemCalls FullWidthExecution BatchArithmetic BatchCount BatchValidation BatchClassState BatchPair BatchValidateLoop.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition bc_pair_bad rs ms i j := negb (FiniteSystem.compatb
 (Wasm_int.Int64.signed (List.nth i rs (Wasm_int.Int64.repr 0)), Wasm_int.Int64.signed (List.nth i ms (Wasm_int.Int64.repr 0)))
 (Wasm_int.Int64.signed (List.nth j rs (Wasm_int.Int64.repr 0)), Wasm_int.Int64.signed (List.nth j ms (Wasm_int.Int64.repr 0)))).
Fixpoint bc_pair_row fuel i j rs ms : nat * Z :=
 match fuel with O => (j,0) | S k =>
 if bc_pair_bad rs ms i j then (j,-1) else bc_pair_row k i (S j) rs ms end.
Definition bc_pair_stop := [::BI_const_num (SM.Vi64 (-1));BI_local_set 3%num;BI_br 2%num].
Definition bc_pair_step := pair_test_code ++ [::BI_if (BT_valtype None) bc_pair_stop [::]] ++
 bc_inc_value 5%num ++ [::BI_local_set 5%num;BI_br 0%num].
Definition bc_pair_body := batch_loop_condition 5%num ++ [::BI_br_if 1%num] ++ bc_pair_step.
Lemma bc_pair_body_shape : classifier_pair_inner = bc_pair_body.
Proof. reflexivity. Qed.
Definition bc_all_valid count rs ms := forall i, (i<count)%coq_nat -> bc_bad rs ms i = false.
Section Host.
Context `{ho:host}.
Context (mem:meminst).
Lemma bc_nth_error base xs i : array_region mem base xs -> (i<16)%coq_nat ->
 List.nth_error xs i = Some (List.nth i xs (Wasm_int.Int64.repr 0)).
Proof. move=> H Hi. apply List.nth_error_nth'. have Hlen := proj1 H. change (List.length xs = 16%nat) in Hlen. lia. Qed.
Lemma bc_pair_item rb mb count i j rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (i<count)%coq_nat -> (j<count)%coq_nat ->
 (count<=16)%coq_nat -> bc_all_valid count rs ms ->
 system_triple mem (AS_base [::] (BCRow rb mb count 0 i j)) pair_test_code
 (AS_base [::T_const (VAL_int32 (wasm_bool (bc_pair_bad rs ms i j)))] (BCRow rb mb count 0 i j)).
Proof.
 move=> Hr Hm Hi Hj Hc Hv.
 have Vi := Hv i Hi. have Vj := Hv j Hj.
 rewrite /bc_bad Bool.negb_false_iff in Vi. rewrite /bc_bad Bool.negb_false_iff in Vj.
 apply validb_spec in Vi. apply validb_spec in Vj.
 have Hd : FullWidth.domain
 (Wasm_int.Int64.signed (List.nth i rs (Wasm_int.Int64.repr 0))) (Wasm_int.Int64.signed (List.nth i ms (Wasm_int.Int64.repr 0)))
 (Wasm_int.Int64.signed (List.nth j rs (Wasm_int.Int64.repr 0))) (Wasm_int.Int64.signed (List.nth j ms (Wasm_int.Int64.repr 0))).
 { unfold FiniteSystem.valid_entry in Vi, Vj. unfold FullWidth.domain, FullWidth.moduli. cbn in Vi,Vj. tauto. }
 rewrite /bc_pair_bad -(pair_incompatible_model Hd).
 apply: (pair_test_sem Hr (bc_nth_error (i:=i) Hr ltac:(lia)) (bc_nth_error (i:=j) Hr ltac:(lia))
 Hm (bc_nth_error (i:=i) Hm ltac:(lia)) (bc_nth_error (i:=j) Hm ltac:(lia)));
 try exact Hd; bc_unfold; try bc_pinned; try bc_present; move=> z; bc_stable.
Qed.
Lemma bc_pair_condition rb mb count i j : ((j <= count)%coq_nat /\ (count <= 16)%coq_nat) ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (BCRow rb mb count 0 i j)) (batch_loop_condition 5%num)
 (AS_base [::T_const (VAL_int32 (wasm_bool (negb (Z.of_nat j <? Z.of_nat count))))] (BCRow rb mb count 0 i j)).
Proof. move=> Hj. apply: batch_loop_condition_sem; try (unfold batch_word32; lia); bc_unfold; bc_pinned. Qed.
Lemma bc_pair_row_loop rb mb count fuel i j rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count <= 16)%coq_nat ->
 (i<count)%coq_nat -> bc_all_valid count rs ms -> (j + fuel = count)%coq_nat ->
 let result := bc_pair_row fuel i j rs ms in
 let Q := AS_base [::] (BCRow rb mb count (snd result) i (fst result)) in
 system_mxk mem (AS_base [::] (BCRow rb mb count 0 i j))
 [::BI_loop (BT_valtype None) bc_pair_body] Q crt_false_assert
 (fun k => if k is O then Q else crt_false_assert).
Proof.
 move=> Hr Hm Hcount HiFixed Hv. move: j. induction fuel as [|fuel IH]; move=> j Hsum; cbn [bc_pair_row].
 - have Ei : j=count by lia. subst j.
   apply: (system_loop_unroll (Pback:=crt_false_assert) (t1s:=[::]) (t2s:=[::])); try reflexivity.
   + move=> V vs h [Hs _]. by case: Hs => <-.
   + move=> V vs h [_ HF]. by case: HF.
   + rewrite /bc_pair_body.
     apply: (system_mxk_seq (es1:=batch_loop_condition 5%num)
     (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (BCRow rb mb count 0 i count))); first reflexivity.
     * apply: system_mxk_lift. apply: system_triple_of_pure.
       have H := bc_pair_condition (rb:=rb) (mb:=mb) (count:=count) (i:=i) (j:=count) ltac:(lia).
       by rewrite Z.ltb_irrefl in H.
     * apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=crt_false_assert)); first reflexivity.
       -- apply: system_mxk_of_pure. apply: (crt_br_if_true_sem (k:=1%nat)). by [].
       -- apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
   + apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
 - have Hi : (j < count)%coq_nat by lia.
   have Econd : (Z.of_nat j <? Z.of_nat count) = true by apply/Z.ltb_lt; lia.
   case Ebad: (bc_pair_bad rs ms i j).
   + apply: (system_loop_unroll (Pback:=crt_false_assert) (t1s:=[::]) (t2s:=[::])); try reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * move=> V vs h [_ HF]. by case: HF.
     * rewrite /bc_pair_body.
       apply: (system_mxk_seq (es1:=batch_loop_condition 5%num)
       (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BCRow rb mb count 0 i j))); first reflexivity.
       -- apply: system_mxk_lift. apply: system_triple_of_pure.
          have H := bc_pair_condition (rb:=rb) (mb:=mb) (count:=count) (i:=i) (j:=j) ltac:(lia).
          by rewrite Econd in H.
       -- apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=AS_base [::] (BCRow rb mb count 0 i j))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: crt_br_if_false_sem.
          ++ rewrite /bc_pair_step.
             apply: (system_mxk_seq (es1:=pair_test_code)
             (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (BCRow rb mb count 0 i j))); first reflexivity.
             ** apply: system_mxk_lift. have H := bc_pair_item Hr Hm HiFixed Hi Hcount Hv. by rewrite Ebad in H.
             ** apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) bc_pair_stop [::]]) (Q1:=crt_false_assert)); first reflexivity.
                --- apply: (system_if_const (t2s:=[::])); first reflexivity.
                    +++ move=> V vs h [_ HF]. by case: HF.
                    +++ rewrite /bc_pair_stop.
                        apply: (system_mxk_seq (es1:=[::BI_const_num (SM.Vi64 (-1));BI_local_set 3%num])
                        (Q1:=AS_base [::] (BCRow rb mb count (-1) i j))); first reflexivity.
                        *** apply: system_mxk_lift. apply: system_triple_of_pure.
                            apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 (-1))])
                            (Q:=AS_base [::T_const (SM.Vi64 (-1))] (BCRow rb mb count 0 i j))).
                            ---- exact: sem_const_framed.
                            ---- exact: bc_set_row_status.
                        *** apply: system_mxk_of_pure. apply: (sem_mxk_br_k (k:=2%nat)). by [].
                --- apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
     * apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
   + apply: (system_loop_unroll (Pback:=AS_base [::] (BCRow rb mb count 0 i (S j))) (t1s:=[::]) (t2s:=[::])); try reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * rewrite /bc_pair_body.
       apply: (system_mxk_seq (es1:=batch_loop_condition 5%num)
       (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BCRow rb mb count 0 i j))); first reflexivity.
       -- apply: system_mxk_lift. apply: system_triple_of_pure.
          have H := bc_pair_condition (rb:=rb) (mb:=mb) (count:=count) (i:=i) (j:=j) ltac:(lia). by rewrite Econd in H.
       -- apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=AS_base [::] (BCRow rb mb count 0 i j))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: crt_br_if_false_sem.
          ++ rewrite /bc_pair_step.
             apply: (system_mxk_seq (es1:=pair_test_code)
             (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BCRow rb mb count 0 i j))); first reflexivity.
             ** apply: system_mxk_lift. have H := bc_pair_item Hr Hm HiFixed Hi Hcount Hv. by rewrite Ebad in H.
             ** apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) bc_pair_stop [::]]) (Q1:=AS_base [::] (BCRow rb mb count 0 i j))); first reflexivity.
                --- apply: (system_if_const (t2s:=[::])); first reflexivity.
                    +++ move=> V vs h [Hs _]. by case: Hs => <-.
                    +++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_nil_same.
                --- rewrite -catA.
                    apply: (system_mxk_seq (es1:=bc_inc_value 5%num ++ [::BI_local_set 5%num])
                    (Q1:=AS_base [::] (BCRow rb mb count 0 i (S j)))); first reflexivity.
                    +++ apply: system_mxk_lift. apply: system_triple_of_pure. apply: bc_inc_row. lia.
                    +++ apply: system_mxk_of_pure. apply: (sem_mxk_br_k (k:=0%nat)). by [].
     * apply: IH. lia.
Qed.
End Host.
