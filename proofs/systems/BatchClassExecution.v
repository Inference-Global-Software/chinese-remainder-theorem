(* The complete exact classifier, with invalid-before-incompatible precedence. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit MultiExitK NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTSystemStatements CRTFinite.
From CRTWasm Require Import CRTPublicExecution.
From CRTSystems Require Import SystemRuntime SystemMemory SystemControl SystemCalls FullWidthExecution FullWidthInverseExecution MergePeriodExecution ArrayAccess BatchArithmetic BatchCount BatchValidation BatchPair BatchClassState BatchValidateLoop BatchPairRow BatchPairLoop BatchClassModel.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition bc_init := [::BI_const_num (SM.Vi64 0);BI_local_set 3%num;BI_const_num (SM.Vi32 0);BI_local_set 4%num].
Definition bc_reset := [::BI_const_num (SM.Vi32 0);BI_local_set 4%num].
Definition bc_valid_block := [::BI_block (BT_valtype None) [::BI_loop (BT_valtype None) bc_validation_body]].
Definition bc_pairs_block := [::BI_block (BT_valtype None) [::BI_loop (BT_valtype None) bc_outer_body]].
Definition bc_after_validation := bc_status_test ++
 [::BI_if (BT_valtype None) [::BI_local_get 3%num;BI_return] [::]] ++
 bc_reset ++ bc_pairs_block ++ [::BI_local_get 3%num;BI_return;BI_unreachable].
Lemma bc_body_shape : modfunc_body SM.system_classify =
 batch_count_prefix ++ bc_init ++ bc_valid_block ++ bc_after_validation.
Proof. reflexivity. Qed.
Section Host.
Context `{ho:host}.
Context (mem:meminst).
Lemma bc_reset_sem rb mb count s :
 sem_triple (triv_ctx SM.main) (AS_base [::] (BCExit rb mb count s)) bc_reset
 (AS_base [::] (BCHead rb mb count s 0)).
Proof.
 rewrite /bc_reset. apply: (sem_seq (es1:=[::BI_const_num (SM.Vi32 0)])
 (Q:=AS_base [::T_const (SM.Vi32 0)] (BCExit rb mb count s))); first exact: sem_const_framed.
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi32 0)] (BCExit rb mb count s))
 (Q':=AS_base [::] (HA_and (bc_pin 4%num (SM.Vi32 0)) (BCExit rb mb count s)))); first by [].
 - bc_unfold. move=> V [vs h] [Hs HH]. split; first exact Hs. bc_heap HH.
 - rewrite /bc_pin. apply: sem_local_set_const_frame; bc_unfold; [bc_stable|bc_present].
Qed.
Lemma bc_init_sem rb mb count :
 sem_triple (triv_ctx SM.main) (AS_base [::] (BCBase rb mb count)) bc_init
 (AS_base [::] (BCHead rb mb count 0 0)).
Proof.
 change (sem_triple (triv_ctx SM.main) (AS_base [::] (BCBase rb mb count))
 ([::BI_const_num (SM.Vi64 0);BI_local_set 3%num] ++ bc_reset) (AS_base [::] (BCHead rb mb count 0 0))).
 apply: (sem_seq (Q:=AS_base [::] (BCExit rb mb count 0))); last exact: bc_reset_sem.
 apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 0)])
 (Q:=AS_base [::T_const (SM.Vi64 0)] (BCBase rb mb count))); first exact: sem_const_framed.
 rewrite /BCExit /bc_pin. apply: sem_local_set_const_frame; bc_unfold; [bc_stable|bc_present].
Qed.
Lemma bc_valid_block_sem rb mb count rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat ->
 system_triple mem (AS_base [::] (BCHead rb mb count 0 0)) bc_valid_block
 (AS_base [::] (BCExit rb mb count (if FiniteSystem.validate_loop (bc_entries count 0 rs ms) then 0 else -2))).
Proof.
 move=> Hr Hm Hc. rewrite -bc_validate_status.
 apply: (batch_triple_conseq (P':=AS_base [::] (BCHead rb mb count 0 0))
 (Q':=AS_base [::] (BCHead rb mb count (snd (bc_validate count 0 rs ms)) (fst (bc_validate count 0 rs ms))))); first by [].
 - exact: bc_head_exit.
 - apply: system_triple_of_mxk. rewrite /bc_valid_block.
   apply: (system_mxk_block (t1s:=[::]) (t2s:=[::])
   (Qb:=fun k => if k is O then AS_base [::] (BCHead rb mb count (snd (bc_validate count 0 rs ms)) (fst (bc_validate count 0 rs ms))) else crt_false_assert)); try reflexivity.
   + move=> V vs h [Hs _]. by case: Hs => <-.
   + apply: bc_validation_loop; try assumption; reflexivity.
Qed.
Lemma bc_pairs_block_sem rb mb count rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat -> bc_all_valid count rs ms ->
 system_triple mem (AS_base [::] (BCHead rb mb count 0 0)) bc_pairs_block
 (AS_base [::] (BCExit rb mb count (if FiniteSystem.pair_loop (bc_entries count 0 rs ms) then 0 else -1))).
Proof.
 move=> Hr Hm Hc Hv. rewrite -bc_pairs_model.
 apply: (batch_triple_conseq (P':=AS_base [::] (BCHead rb mb count 0 0))
 (Q':=AS_base [::] (BCHead rb mb count (snd (bc_pairs count 0 rs ms)) (fst (bc_pairs count 0 rs ms))))); first by [].
 - exact: bc_head_exit.
 - apply: system_triple_of_mxk. rewrite /bc_pairs_block.
   apply: (system_mxk_block (t1s:=[::]) (t2s:=[::])
   (Qb:=fun k => if k is O then AS_base [::] (BCHead rb mb count (snd (bc_pairs count 0 rs ms)) (fst (bc_pairs count 0 rs ms))) else crt_false_assert)); try reflexivity.
   + move=> V vs h [Hs _]. by case: Hs => <-.
   + apply: bc_pair_outer_loop; try assumption; reflexivity.
Qed.
Lemma bc_exit_return rb mb count s :
 system_mxk mem (AS_base [::] (BCExit rb mb count s))
 [::BI_local_get 3%num;BI_return;BI_unreachable] crt_false_assert
 (AS_base [::T_const (SM.Vi64 s)] HA_true) (fun _ => crt_false_assert).
Proof.
 apply: system_mxk_of_pure_no_break. apply: crt_pinned_return. bc_unfold; bc_pinned.
Qed.
Lemma bc_valid_body rb mb count rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat ->
 system_mxk mem (AS_base [::] (BCBase rb mb count)) (modfunc_body SM.system_classify)
 crt_false_assert (AS_base [::T_const (SM.Vi64 (bc_classify count rs ms))] HA_true) (fun _ => crt_false_assert).
Proof.
 move=> Hr Hm Hc. rewrite bc_body_shape.
 apply: (system_mxk_seq (es1:=batch_count_prefix) (Q1:=AS_base [::] (BCBase rb mb count))); first reflexivity.
 - apply: system_mxk_lift. apply: system_triple_of_pure. apply: (batch_count_valid (c:=Z.of_nat count)); first lia. bc_unfold; bc_pinned.
 - apply: (system_mxk_seq (es1:=bc_init) (Q1:=AS_base [::] (BCHead rb mb count 0 0))); first reflexivity.
   + apply: system_mxk_lift. apply: system_triple_of_pure. exact: bc_init_sem.
   + apply: (system_mxk_seq (es1:=bc_valid_block)
     (Q1:=AS_base [::] (BCExit rb mb count (if FiniteSystem.validate_loop (bc_entries count 0 rs ms) then 0 else -2)))); first reflexivity.
     * apply: system_mxk_lift. exact: bc_valid_block_sem.
     * rewrite /bc_classify /bc_after_validation.
       case Ev:(FiniteSystem.validate_loop (bc_entries count 0 rs ms)).
       -- apply: (system_mxk_seq (es1:=bc_status_test)
          (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BCExit rb mb count 0))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. apply: (bc_status_sem (s:=0)); first (unfold word,i64_min,i64_max;lia). bc_unfold; bc_pinned.
          ++ apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_local_get 3%num;BI_return] [::]])
             (Q1:=AS_base [::] (BCExit rb mb count 0))); first reflexivity.
             ** apply: (system_if_const (t2s:=[::])); first reflexivity.
                --- move=> V vs h [Hs _]. by case: Hs => <-.
                --- apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_nil_same.
             ** apply: (system_mxk_seq (es1:=bc_reset) (Q1:=AS_base [::] (BCHead rb mb count 0 0))); first reflexivity.
                --- apply: system_mxk_lift. apply: system_triple_of_pure. exact: bc_reset_sem.
                --- apply: (system_mxk_seq (es1:=bc_pairs_block)
                    (Q1:=AS_base [::] (BCExit rb mb count (if FiniteSystem.pair_loop (bc_entries count 0 rs ms) then 0 else -1)))); first reflexivity.
                    +++ apply: system_mxk_lift. apply: bc_pairs_block_sem; try assumption. by apply bc_entries_valid.
                    +++ exact: bc_exit_return.
       -- apply: (system_mxk_seq (es1:=bc_status_test)
          (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (BCExit rb mb count (-2)))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. apply: (bc_status_sem (s:=(-2))); first (unfold word,i64_min,i64_max;lia). bc_unfold; bc_pinned.
          ++ apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_local_get 3%num;BI_return] [::]]) (Q1:=crt_false_assert)); first reflexivity.
             ** apply: system_mxk_of_pure_no_break. apply: crt_if_true_returns.
                apply: (sem_mx_seq (es1:=[::BI_local_get 3%num])
                (Q1:=AS_base [::T_const (SM.Vi64 (-2))] (BCExit rb mb count (-2)))).
                --- apply: sem_mx_lift. apply: get_pinned_frame. bc_unfold; bc_pinned.
                --- exact: p_stack_return.
             ** apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
Qed.
Lemma bc_entry_entails rb mb count :
 aentails (AS_base [::] (HA_and (args_pinned [::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 (Z.of_nat count)] 0%num)
 (func_pre_h SM.main SM.system_classify))) (AS_base [::] (BCBase rb mb count)).
Proof.
 move=> V [vs h] /= [Hs [[P0 [P1 [P2 _]]] [[T0 [T1 [T2 _]]] [T3 [T4 [T5 [T6 [T7 [T8 [T9 [T10 [T11 [T12 [T13 _]]]]]]]]]]]]]].
 split; first exact Hs. unfold BCBase, bc_pin.
 split; first exact P0. split; first exact P1. split; first exact P2.
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
 by case: T13 => [w [Ew _]]; exists w.
Qed.
Definition bc_result c rs ms := if (c <? 0) || (16 <? c) then -2 else bc_classify (Z.to_nat c) rs ms.
Lemma bc_result_word c rs ms : word (bc_result c rs ms).
Proof.
 rewrite /bc_result /bc_classify. case: ((c <? 0) || (16 <? c));
 repeat match goal with |- context [if ?b then _ else _] => destruct b end;
 unfold word,i64_min,i64_max; lia.
Qed.
Lemma bc_valid_computes rb mb count rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat ->
 system_computes mem 7%nat [::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 (Z.of_nat count)]
 [::SM.Vi64 (bc_classify count rs ms)].
Proof.
 move=> Hr Hm Hc.
 have Hrun := bc_valid_body Hr Hm Hc.
 have Hbody : system_mx mem (AS_base [::] (BCBase rb mb count)) (modfunc_body SM.system_classify)
 (AS_base [::T_const (SM.Vi64 (bc_classify count rs ms))] HA_true)
 (AS_base [::T_const (SM.Vi64 (bc_classify count rs ms))] HA_true)
 (AS_base [::T_const (SM.Vi64 (bc_classify count rs ms))] HA_true).
 { apply: system_mx_of_mxk_no_break.
   apply: (system_mxk_conseq (P':=AS_base [::] (BCBase rb mb count)) (Qn':=crt_false_assert)
   (Qr':=AS_base [::T_const (SM.Vi64 (bc_classify count rs ms))] HA_true) (Qb':=fun _ => crt_false_assert)); try by [].
   - move=> V [vs h] [_ Hfalse]. by case: Hfalse.
   - move=> k V vh HP. exact HP.
   }
 rewrite /system_computes /=. split; first by repeat split. split; first by repeat split.
 exists [::VAL_num (SM.Vi64 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi64 0);
 VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);
 VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0)].
 split; first reflexivity.
 move=> hs V vs h HP Hreif. apply: Hbody; [reflexivity| |exact Hreif]. exact: (bc_entry_entails HP).
Qed.
Theorem batch_classify_machine_computes rb mb c rs ms :
 array_region mem rb rs -> array_region mem mb ms -> batch_word32 c ->
 system_computes mem 7%nat [::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 c]
 [::SM.Vi64 (bc_result c rs ms)].
Proof.
 move=> Hr Hm Wc. rewrite /bc_result. case Ebad:((c <? 0) || (16 <? c)).
 - have Hbad : c<0 \/ 16<c by apply Bool.orb_true_iff in Ebad; destruct Ebad as [H|H]; [left|right]; apply Z.ltb_lt.
   rewrite /system_computes /=. split; first by repeat split. split; first by repeat split.
   exists [::VAL_num (SM.Vi64 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi64 0);
   VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);
   VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0)].
   split; first reflexivity.
   apply: (sem_mx_at_of_mx (G:=triv_ctx SM.main)); last reflexivity.
   change (sem_mx (triv_ctx SM.main)
   (AS_base [::] (HA_and (args_pinned [::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 c] 0%num) (func_pre_h SM.main SM.system_classify)))
   (modfunc_body SM.system_classify) (AS_base [::T_const (SM.Vi64 (-2))] HA_true)
   (AS_base [::T_const (SM.Vi64 (-2))] HA_true) (AS_base [::T_const (SM.Vi64 (-2))] HA_true)). rewrite bc_body_shape.
   apply: (batch_count_invalid (c:=c)); try assumption. bc_pinned.
 - have Hc : 0<=c<=16 by apply Bool.orb_false_iff in Ebad; destruct Ebad as [Hlo Hhi]; apply Z.ltb_ge in Hlo; apply Z.ltb_ge in Hhi; lia.
   have Ec : Z.of_nat (Z.to_nat c)=c by apply Z2Nat.id; lia.
   rewrite -{1}Ec. apply: bc_valid_computes; try assumption; lia.
Qed.
Lemma bc_entry_admissible rb mb c :
 crt_entry_admissible mem SM.system_classify [::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 c].
Proof.
 move=> defaults Hd. vm_compute in Hd. inversion Hd; subst defaults.
 cbn [crt_entry_valuation activation_frame system_initial_runtime func_pre_h SM.main
 SM.system_classify args_pinned locals_typed assertion_denote hassert_denote stack_denote
 term_eq term_denote loc_read lookup_N val_loc f_locs modfunc_type modfunc_locals mod_types runtime_inst SM.Vi64 SM.Vi32].
 repeat split; try reflexivity; try (eexists; split; reflexivity).
Qed.
Lemma crt_batch_classify_call frame H rb mb c rs ms :
 f_inst frame = system_inst -> array_region mem rb rs -> array_region mem mb ms -> batch_word32 c ->
 sem_triple_at (system_store mem) frame
 (AS_base [::T_const (SM.Vi32 (Z.of_N rb));T_const (SM.Vi32 (Z.of_N mb));T_const (SM.Vi32 c)] H)
 [::BI_call 7%num] (AS_base [::T_const (SM.Vi64 (bc_result c rs ms))] H).
Proof.
 move=> Hi Hr Hm Wc.
 apply: (crt_call_from_computes_at (i:=7%nat) (addr:=7%num) (fdef:=SM.system_classify)
 (args:=[::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 c]) (rs:=[::SM.Vi64 (bc_result c rs ms)])
 (params:=[::T_num T_i32;T_num T_i32;T_num T_i32]) (results:=[::T_num T_i64])); try reflexivity.
 - by rewrite Hi.
 - exact: bc_entry_admissible.
 - exact: batch_classify_machine_computes.
Qed.
End Host.
Print Assumptions batch_classify_machine_computes.

