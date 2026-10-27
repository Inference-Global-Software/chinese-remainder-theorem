(* Exact native public solve export, including global error precedence. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit MultiExitK NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTSystemStatements CRTFinite.
From CRTWasm Require Import CRTPublicExecution.
From CRTSystems Require Import SystemRuntime SystemMemory SystemControl SystemCalls FullWidthExecution FullWidthInverseExecution MergePeriodExecution ArrayAccess BatchArithmetic BatchCount BatchClassState BatchValidateLoop BatchPairRow BatchClassModel BatchClassExecution BatchPublicPrefix BatchSolveFold.
Module SM := CRTSystemGenerated.main.
Import FullWidth FiniteSystem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition bs_init_code := [::BI_const_num (SM.Vi64 0);BI_local_set 4%num;BI_const_num (SM.Vi64 1);BI_local_set 5%num;BI_const_num (SM.Vi32 0);BI_local_set 6%num].
Definition bs_block_code := [::BI_block (BT_valtype None) [::BI_loop (BT_valtype None) bs_loop_code]].
Definition bs_tail_code := bs_init_code ++ bs_block_code ++ [::BI_local_get 4%num;BI_return;BI_unreachable].
Lemma bs_body_shape : modfunc_body SM.crt_system_solve = batch_count_prefix ++ batch_classify_call_code ++ batch_dispatch_code ++ bs_tail_code.
Proof. reflexivity. Qed.
Lemma bs_entries_bc fuel i rs ms : bs_entries fuel i rs ms = bc_entries fuel i rs ms.
Proof. reflexivity. Qed.
Section Host.
Context `{ho:host}.
Context (mem:meminst).
Ltac unfold_bs := unfold BSHead, BSExit, BSBase, bs_pin.
Ltac bs_pinned := bc_pinned.
Ltac bs_present := bc_present.
Ltac bs_stable := solve [exact: bs_stable_true | exact: loc_stable_defined_self | exact: loc_stable_pin_self | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other | apply: loc_stable_and; bs_stable].

Lemma bs_tail_sem rb mb count rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat -> bc_all_valid count rs ms ->
 system_mxk mem (AS_base [::] (BSBase rb mb count)) bs_tail_code crt_false_assert
 (AS_base [::T_const (SM.Vi64 (solve_value (solve_fold (bc_entries count 0 rs ms) 0 1)))] HA_true) (fun _ => crt_false_assert).
Proof.
 move=> Hr Hm Hc Hv. rewrite /bs_tail_code.
 apply: (system_mxk_seq (es1:=bs_init_code) (Q1:=AS_base [::] (BSHead rb mb count 0 0 1))); first reflexivity.
 - apply: system_mxk_lift. apply: system_triple_of_pure. exact: bs_initialize_sem.
 - apply: (system_mxk_seq (es1:=bs_block_code)
   (Q1:=AS_base [::] (BSExit rb mb count (solve_value (solve_fold (bc_entries count 0 rs ms) 0 1))))); first reflexivity.
   + apply: system_mxk_lift.
     have Wzero : word 0 by unfold word,i64_min,i64_max;lia.
     have Wone : word 1 by unfold word,i64_min,i64_max;lia.
     have H := bs_block_exec (rb:=rb) (mb:=mb) (count:=count) (i:=0%nat) Hr Hm Hc ltac:(lia) Wzero Wone.
     rewrite Nat.sub_0_r bs_entries_bc in H. exact H.
   + apply: system_mxk_of_pure_no_break. apply: crt_pinned_return. unfold_bs; bs_pinned.
Qed.
Lemma bs_valid_body rb mb count rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat ->
 system_mxk mem (AS_base [::] (BSBase rb mb count)) (modfunc_body SM.crt_system_solve)
 crt_false_assert (AS_base [::T_const (SM.Vi64 (solve_value (system_model (bc_entries count 0 rs ms))))] HA_true) (fun _ => crt_false_assert).
Proof.
 move=> Hr Hm Hc. rewrite bs_body_shape.
 apply: (system_mxk_seq (es1:=batch_count_prefix) (Q1:=AS_base [::] (BSBase rb mb count))); first reflexivity.
 - apply: system_mxk_lift. apply: system_triple_of_pure. apply: (batch_count_valid (c:=Z.of_nat count)); first lia. unfold_bs; bs_pinned.
 - apply: (system_mxk_seq (es1:=batch_classify_call_code)
   (Q1:=AS_base [::T_const (SM.Vi64 (bc_classify count rs ms))] (BSBase rb mb count))); first reflexivity.
   + apply: system_mxk_lift. apply: (batch_call_classifier Hr Hm Hc); unfold_bs; bs_pinned.
   + apply: batch_dispatch.
     * rewrite /bc_classify. repeat match goal with |- context [if ?b then _ else _] => destruct b end; unfold word,i64_min,i64_max;lia.
     * unfold_bs; bs_stable.
     * unfold_bs; bs_present.
     * rewrite /bc_classify /system_model. case: (validate_loop (bc_entries count 0 rs ms)); last by [].
       case: (pair_loop (bc_entries count 0 rs ms)); [by move=> H; exfalso; apply H|by []].
     * rewrite /bc_classify /system_model. case Ev:(validate_loop (bc_entries count 0 rs ms)); last discriminate.
       case Ep:(pair_loop (bc_entries count 0 rs ms)); last discriminate. move=> _.
       apply: bs_tail_sem; try assumption. by apply bc_entries_valid.
Qed.
Lemma bs_entry_entails rb mb count :
 aentails (AS_base [::] (HA_and (args_pinned [::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 (Z.of_nat count)] 0%num)
 (func_pre_h SM.main SM.crt_system_solve))) (AS_base [::] (BSBase rb mb count)).
Proof.
 move=> V [vs h] /= [Hs [[P0 [P1 [P2 _]]] [[T0 [T1 [T2 _]]] [T3 [T4 [T5 [T6 [T7 [T8 [T9 [T10 [T11 _]]]]]]]]]]]].
 split; first exact Hs. unfold BSBase, bs_pin.
 split; first exact P0. split; first exact P1. split; first exact P2.
 split; first by case: T3 => [w [Ew _]]; exists w.
 split; first by case: T4 => [w [Ew _]]; exists w.
 split; first by case: T5 => [w [Ew _]]; exists w.
 split; first by case: T6 => [w [Ew _]]; exists w.
 split; first by case: T7 => [w [Ew _]]; exists w.
 split; first by case: T8 => [w [Ew _]]; exists w.
 split; first by case: T9 => [w [Ew _]]; exists w.
 split; first by case: T10 => [w [Ew _]]; exists w.
 split; first by case: T11 => [w [Ew _]]; exists w. exact I.
Qed.
Definition bs_result c rs ms := if (c <? 0) || (16 <? c) then -2 else solve_value (system_model (bc_entries (Z.to_nat c) 0 rs ms)).
Lemma bs_valid_computes rb mb count rs ms :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat ->
 system_computes mem 8%nat [::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 (Z.of_nat count)]
 [::SM.Vi64 (solve_value (system_model (bc_entries count 0 rs ms)))].
Proof.
 move=> Hr Hm Hc.
 have Hrun := bs_valid_body Hr Hm Hc.
 have Hbody : system_mx mem (AS_base [::] (BSBase rb mb count)) (modfunc_body SM.crt_system_solve)
 (AS_base [::T_const (SM.Vi64 (solve_value (system_model (bc_entries count 0 rs ms))))] HA_true)
 (AS_base [::T_const (SM.Vi64 (solve_value (system_model (bc_entries count 0 rs ms))))] HA_true)
 (AS_base [::T_const (SM.Vi64 (solve_value (system_model (bc_entries count 0 rs ms))))] HA_true).
 { apply: system_mx_of_mxk_no_break.
   apply: (system_mxk_conseq (P':=AS_base [::] (BSBase rb mb count)) (Qn':=crt_false_assert)
   (Qr':=AS_base [::T_const (SM.Vi64 (solve_value (system_model (bc_entries count 0 rs ms))))] HA_true) (Qb':=fun _ => crt_false_assert)); try by [].
   - move=> V [vs h] [_ Hfalse]. by case: Hfalse.
   - move=> k V vh HP. exact HP.
   }
 rewrite /system_computes /=. split; first by repeat split. split; first by repeat split.
 exists [::VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0)].
 split; first reflexivity.
 move=> hs V vs h HP Hreif. apply: Hbody; [reflexivity| |exact Hreif]. exact: (bs_entry_entails HP).
Qed.
Theorem batch_solve_machine_computes rb mb c rs ms :
 array_region mem rb rs -> array_region mem mb ms -> batch_word32 c ->
 system_computes mem 8%nat [::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 c]
 [::SM.Vi64 (bs_result c rs ms)].
Proof.
 move=> Hr Hm Wc. rewrite /bs_result. case Ebad:((c <? 0) || (16 <? c)).
 - have Hbad : c<0 \/ 16<c by apply Bool.orb_true_iff in Ebad; destruct Ebad as [H|H]; [left|right]; apply Z.ltb_lt.
   rewrite /system_computes /=. split; first by repeat split. split; first by repeat split.
   exists [::VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0);VAL_num (SM.Vi32 0)].
   split; first reflexivity.
   apply: (sem_mx_at_of_mx (G:=triv_ctx SM.main)); last reflexivity.
   change (sem_mx (triv_ctx SM.main)
   (AS_base [::] (HA_and (args_pinned [::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 c] 0%num) (func_pre_h SM.main SM.crt_system_solve)))
   (modfunc_body SM.crt_system_solve) (AS_base [::T_const (SM.Vi64 (-2))] HA_true)
   (AS_base [::T_const (SM.Vi64 (-2))] HA_true) (AS_base [::T_const (SM.Vi64 (-2))] HA_true)). rewrite bs_body_shape.
   apply: (batch_count_invalid (c:=c)); try assumption. bs_pinned.
 - have Hc : 0<=c<=16 by apply Bool.orb_false_iff in Ebad; destruct Ebad as [Hlo Hhi]; apply Z.ltb_ge in Hlo; apply Z.ltb_ge in Hhi; lia.
   have Ec : Z.of_nat (Z.to_nat c)=c by apply Z2Nat.id; lia.
   rewrite -{1}Ec. apply: bs_valid_computes; try assumption; lia.
Qed.
Lemma bs_entry_admissible rb mb c :
 crt_entry_admissible mem SM.crt_system_solve [::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 c].
Proof.
 move=> defaults Hd. vm_compute in Hd. inversion Hd; subst defaults.
 cbn [crt_entry_valuation activation_frame system_initial_runtime func_pre_h SM.main
 SM.crt_system_solve args_pinned locals_typed assertion_denote hassert_denote stack_denote
 term_eq term_denote loc_read lookup_N val_loc f_locs modfunc_type modfunc_locals mod_types runtime_inst SM.Vi64 SM.Vi32].
 repeat split; try reflexivity; try (eexists; split; reflexivity).
Qed.
Lemma crt_batch_solve_call frame H rb mb c rs ms :
 f_inst frame = system_inst -> array_region mem rb rs -> array_region mem mb ms -> batch_word32 c ->
 sem_triple_at (system_store mem) frame
 (AS_base [::T_const (SM.Vi32 (Z.of_N rb));T_const (SM.Vi32 (Z.of_N mb));T_const (SM.Vi32 c)] H)
 [::BI_call 8%num] (AS_base [::T_const (SM.Vi64 (bs_result c rs ms))] H).
Proof.
 move=> Hi Hr Hm Wc.
 apply: (crt_call_from_computes_at (i:=8%nat) (addr:=8%num) (fdef:=SM.crt_system_solve)
 (args:=[::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 c]) (rs:=[::SM.Vi64 (bs_result c rs ms)])
 (params:=[::T_num T_i32;T_num T_i32;T_num T_i32]) (results:=[::T_num T_i64])); try reflexivity.
 - by rewrite Hi.
 - exact: bs_entry_admissible.
 - exact: batch_solve_machine_computes.
Qed.
End Host.
Print Assumptions batch_solve_machine_computes.
