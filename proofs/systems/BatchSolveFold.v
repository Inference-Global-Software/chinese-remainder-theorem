From Coq Require Import ZArith NArith Lia List Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit MultiExitK NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTMath CRTSystemStatements CRTSystemArithmetic CRTFinite.
From CRTWasm Require Import CRTPublicExecution CRTContracts CRTGeneralArithmetic.
From CRTSystems Require Import ReadOnly SystemRuntime SystemMemory SystemControl SystemCalls FullWidthExecution MergeSolvePure MergeSolveExecution MergePeriodExecution ScalarResultFacts.
From CRTSystems Require Import ArrayAccess BatchArithmetic BatchCount.
Module SM := CRTSystemGenerated.main.
Import FullWidth FiniteSystem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition bs_pin i c := term_eq (T_local i) (T_const c).
Definition BSBase rb mb count := HA_and (bs_pin 0%num (SM.Vi32 (Z.of_N rb)))
 (HA_and (bs_pin 1%num (SM.Vi32 (Z.of_N mb)))
 (HA_and (bs_pin 2%num (SM.Vi32 (Z.of_nat count)))
 (HA_and (HA_defined (T_local 3%num)) (HA_and (HA_defined (T_local 4%num))
 (HA_and (HA_defined (T_local 5%num)) (HA_and (HA_defined (T_local 6%num))
 (HA_and (HA_defined (T_local 7%num)) (HA_and (HA_defined (T_local 8%num))
 (HA_and (HA_defined (T_local 9%num)) (HA_and (HA_defined (T_local 10%num))
 (HA_and (HA_defined (T_local 11%num)) HA_true))))))))))).
Definition BSHead rb mb count i r p := HA_and (bs_pin 6%num (SM.Vi32 (Z.of_nat i)))
 (HA_and (bs_pin 4%num (SM.Vi64 r)) (HA_and (bs_pin 5%num (SM.Vi64 p)) (BSBase rb mb count))).
Definition BSNext rb mb count i r p next := HA_and (bs_pin 7%num (SM.Vi64 next)) (BSHead rb mb count i r p).
Definition BSExit rb mb count r := HA_and (bs_pin 4%num (SM.Vi64 r)) (BSBase rb mb count).
Definition bs_args_code := [::BI_local_get 4%num;BI_local_get 5%num] ++ array_access 0%num 6%num 8%num ++ array_access 1%num 6%num 8%num.
Definition bs_call_code := bs_args_code ++ [::BI_call 5%num;BI_local_set 7%num].
Definition bs_guard_code := [::BI_local_get 7%num;BI_const_num (SM.Vi64 0);BI_relop T_i64 (Relop_i (ROI_lt SX_S))].
Definition bs_period_code := bs_args_code ++ [::BI_call 6%num;BI_local_set 5%num].
Definition bs_increment_code := [::BI_local_get 6%num;BI_const_num (SM.Vi32 1)] ++ batch_checked_add_code 9%num 10%num 11%num ++ [::BI_local_set 6%num].
Definition bs_loop_code := batch_loop_condition 6%num ++ [::BI_br_if 1%num] ++ bs_call_code ++ bs_guard_code ++
 [::BI_if (BT_valtype None) [::BI_local_get 7%num;BI_local_set 4%num;BI_br 2%num] [::]] ++
 bs_period_code ++ [::BI_local_get 7%num;BI_local_set 4%num] ++ bs_increment_code ++ [::BI_br 0%num].
Lemma bs_loop_shape : List.nth 20 (modfunc_body SM.crt_system_solve) BI_unreachable = BI_block (BT_valtype None) [::BI_loop (BT_valtype None) bs_loop_code].
Proof. reflexivity. Qed.
Definition bs_entry rs ms i := (Wasm_int.Int64.signed (List.nth i rs (Wasm_int.Int64.repr 0)), Wasm_int.Int64.signed (List.nth i ms (Wasm_int.Int64.repr 0))).
Fixpoint bs_entries fuel i rs ms := match fuel with O=>[::] | S k=>bs_entry rs ms i :: bs_entries k (S i) rs ms end.
Lemma bs_entry_nth rs ms i a m : List.nth_error rs i = Some a -> List.nth_error ms i = Some m -> bs_entry rs ms i = (Wasm_int.Int64.signed a,Wasm_int.Int64.signed m).
Proof. move=> Ha Hm. rewrite /bs_entry (List.nth_error_nth _ _ _ Ha) (List.nth_error_nth _ _ _ Hm). reflexivity. Qed.
Lemma bs_merge_success a m b n r p : merge a m b n = Success r p -> 0<=r<p /\ 1<=p<=MAX.
Proof.
 move=> E. have H := scalar_model_proved a m b n. rewrite E in H. cbn in H.
 case: H => [_ [_ [Hp [_ [Hr _]]]]]. split; [exact Hr|lia].
Qed.
Lemma bs_fold_step C r p a m :
 solve_value (solve_fold ((a,m)::C) r p) =
 if solve_value (merge r p a m) <? 0 then solve_value (merge r p a m)
 else solve_value (solve_fold C (solve_value (merge r p a m)) (period_value (merge r p a m))).
Proof.
 cbn [solve_fold]. case E: (merge r p a m) => [|||next period]; try reflexivity.
 cbn [solve_value period_value]. have [Hnext _] := bs_merge_success E.
 have Ez : (next <? 0)=false by apply Z.ltb_ge; lia. by rewrite Ez.
Qed.
Section Host.
Context `{ho:host}.
Context (mem:meminst).
Ltac unfold_bs := rewrite /BSNext /BSHead /BSExit /BSBase /bs_pin.
Ltac bs_pinned := solve [exact: pinned_bare | apply: pinned_left; bs_pinned | apply: pinned_right; bs_pinned].
Ltac bs_present := solve [exact: loc_present_defined | exact: loc_present_pin | apply: loc_present_left; bs_present | apply: loc_present_right; bs_present].
Lemma bs_stable_true i c : loc_stable i c HA_true.
Proof. by []. Qed.
Ltac bs_stable := solve [exact: bs_stable_true | exact: loc_stable_defined_self | exact: loc_stable_pin_self | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other | apply: loc_stable_and; bs_stable].
Lemma bs_args_sem H rb mb rs ms i r p a m :
 array_region mem rb rs -> array_region mem mb ms -> List.nth_error rs i = Some a -> List.nth_error ms i = Some m ->
 pinned 0%num (SM.Vi32 (Z.of_N rb)) H -> pinned 1%num (SM.Vi32 (Z.of_N mb)) H ->
 pinned 6%num (SM.Vi32 (Z.of_nat i)) H -> pinned 4%num (SM.Vi64 r) H -> pinned 5%num (SM.Vi64 p) H ->
 loc_present 8%num H -> loc_stable 8%num (SM.Vi32 (Z.of_nat i)) H ->
 system_triple mem (AS_base [::] H) bs_args_code
 (AS_base [::T_const (SM.Vi64 r);T_const (SM.Vi64 p);T_const (VAL_int64 a);T_const (VAL_int64 m)] H).
Proof.
 move=> Hr Hm Ha Hn P0 P1 Pi Pr Pp Present Stable. rewrite /bs_args_code.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 r);T_const (SM.Vi64 p)] H)); first reflexivity.
 - apply: system_triple_of_pure. apply: (sem_seq (es1:=[::BI_local_get 4%num]) (Q:=AS_base [::T_const (SM.Vi64 r)] H)); exact: get_pinned_frame.
 - apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 r);T_const (SM.Vi64 p);T_const (VAL_int64 a)] H)); first reflexivity.
   + apply: (batch_frame_consts (vf:=[::SM.Vi64 r;SM.Vi64 p])). exact: (array_access_sem Hr Ha P0 Pi Present Stable).
   + apply: (batch_frame_consts (vf:=[::SM.Vi64 r;SM.Vi64 p;VAL_int64 a])). exact: (array_access_sem Hm Hn P1 Pi Present Stable).
Qed.
Lemma bs_call_sem rb mb count rs ms i r p a m :
 array_region mem rb rs -> array_region mem mb ms -> List.nth_error rs i = Some a -> List.nth_error ms i = Some m ->
 word r -> word p ->
 system_triple mem (AS_base [::] (BSHead rb mb count i r p)) bs_call_code
 (AS_base [::] (BSNext rb mb count i r p (solve_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m))))).
Proof.
 move=> Hr Hm Ha Hn Wr Wp. rewrite /bs_call_code.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 r);T_const (SM.Vi64 p);T_const (VAL_int64 a);T_const (VAL_int64 m)] (BSHead rb mb count i r p))); first reflexivity.
 - apply: (bs_args_sem Hr Hm Ha Hn); unfold_bs; first [bs_pinned|bs_present|bs_stable].
 - apply: (system_triple_seq (es1:=[::BI_call 5%num])
   (Q1:=AS_base [::T_const (SM.Vi64 (solve_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m))))] (BSHead rb mb count i r p))); first reflexivity.
   + rewrite -[VAL_int64 a]crt_contract_repr_signed -[VAL_int64 m]crt_contract_repr_signed.
     move=> f Hi. apply: crt_merge_solve_call; try assumption; exact: crt_contract_signed_word.
   + apply: system_triple_of_pure. apply: sem_local_set_const_frame; unfold_bs; [bs_stable|bs_present].
Qed.
Lemma bs_guard_sem rb mb count i r p next : word next ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (BSNext rb mb count i r p next)) bs_guard_code
 (AS_base [::T_const (VAL_int32 (wasm_bool (next <? 0)))] (BSNext rb mb count i r p next)).
Proof.
 move=> Wnext. have Wzero : word 0 by unfold word,i64_min,i64_max; lia.
 rewrite /bs_guard_code -(crt_public_lt Wnext Wzero). apply: test_pin_const; try reflexivity. unfold_bs. bs_pinned.
Qed.
Lemma bs_set_period rb mb count i r old p next :
 sem_triple (triv_ctx SM.main) (AS_base [::T_const (SM.Vi64 p)] (BSNext rb mb count i r old next))
 [::BI_local_set 5%num] (AS_base [::] (BSNext rb mb count i r p next)).
Proof.
 pose H := HA_and (bs_pin 7%num (SM.Vi64 next)) (HA_and (bs_pin 6%num (SM.Vi32 (Z.of_nat i))) (HA_and (bs_pin 4%num (SM.Vi64 r)) (BSBase rb mb count))).
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi64 p)] H)
 (Q':=AS_base [::] (HA_and (bs_pin 5%num (SM.Vi64 p)) H))).
 - move=> V [vs h] /= [Hs [Hnext [Hi [Hr [_ HB]]]]]. by split; [|split; [|split; [|split]]].
 - move=> V [vs h] /= [Hs [Hp [Hnext [Hi [Hr HB]]]]]. by split; [|split; [|split; [|split; [|split]]]].
 - unfold H. apply: sem_local_set_const_frame; unfold_bs; [bs_stable|bs_present].
Qed.
Lemma bs_set_residue rb mb count i old p next r :
 sem_triple (triv_ctx SM.main) (AS_base [::T_const (SM.Vi64 r)] (BSNext rb mb count i old p next))
 [::BI_local_set 4%num] (AS_base [::] (BSHead rb mb count i r p)).
Proof.
 pose H := HA_and (bs_pin 6%num (SM.Vi32 (Z.of_nat i))) (HA_and (bs_pin 5%num (SM.Vi64 p)) (BSBase rb mb count)).
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi64 r)] H)
 (Q':=AS_base [::] (HA_and (bs_pin 4%num (SM.Vi64 r)) H))).
 - move=> V [vs h] /= [Hs [_ [Hi [_ [Hp HB]]]]]. by split; [|split; [|split]].
 - move=> V [vs h] /= [Hs [Hr [Hi [Hp HB]]]]. by split; [|split; [|split; [|split]]].
 - unfold H. apply: sem_local_set_const_frame; unfold_bs; [bs_stable|bs_present].
Qed.
Lemma bs_set_index rb mb count i j r p :
 sem_triple (triv_ctx SM.main) (AS_base [::T_const (SM.Vi32 (Z.of_nat j))] (BSHead rb mb count i r p))
 [::BI_local_set 6%num] (AS_base [::] (BSHead rb mb count j r p)).
Proof.
 pose H := HA_and (bs_pin 4%num (SM.Vi64 r)) (HA_and (bs_pin 5%num (SM.Vi64 p)) (BSBase rb mb count)).
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi32 (Z.of_nat j))] H)
 (Q':=AS_base [::] (BSHead rb mb count j r p))).
 - move=> V [vs h] /= [Hs [_ HH]]. by split.
 - by [].
 - unfold H. apply: sem_local_set_const_frame; unfold_bs; [bs_stable|bs_present].
Qed.
Lemma bs_head_exit S rb mb count i r p :
 aentails (AS_base S (BSHead rb mb count i r p)) (AS_base S (BSExit rb mb count r)).
Proof. move=> V [vs h] /= [Hs [_ [Hr [_ HB]]]]. by split; [|split]. Qed.
Lemma bs_commit_residue rb mb count i r p next :
 sem_triple (triv_ctx SM.main) (AS_base [::] (BSNext rb mb count i r p next))
 [::BI_local_get 7%num;BI_local_set 4%num] (AS_base [::] (BSHead rb mb count i next p)).
Proof.
 apply: (sem_seq (es1:=[::BI_local_get 7%num]) (Q:=AS_base [::T_const (SM.Vi64 next)] (BSNext rb mb count i r p next))).
 - apply: get_pinned_frame. unfold_bs. bs_pinned.
 - exact: bs_set_residue.
Qed.
Lemma bs_period_sem rb mb count rs ms i r p a m next :
 array_region mem rb rs -> array_region mem mb ms -> List.nth_error rs i = Some a -> List.nth_error ms i = Some m ->
 word r -> word p ->
 system_triple mem (AS_base [::] (BSNext rb mb count i r p next)) bs_period_code
 (AS_base [::] (BSNext rb mb count i r (period_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m))) next)).
Proof.
 move=> Hr Hm Ha Hn Wr Wp. rewrite /bs_period_code.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 r);T_const (SM.Vi64 p);T_const (VAL_int64 a);T_const (VAL_int64 m)] (BSNext rb mb count i r p next))); first reflexivity.
 - apply: (bs_args_sem Hr Hm Ha Hn); unfold_bs; first [bs_pinned|bs_present|bs_stable].
 - apply: (system_triple_seq (es1:=[::BI_call 6%num])
   (Q1:=AS_base [::T_const (SM.Vi64 (period_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m))))] (BSNext rb mb count i r p next))); first reflexivity.
   + rewrite -[VAL_int64 a]crt_contract_repr_signed -[VAL_int64 m]crt_contract_repr_signed.
     move=> f Hi. apply: crt_merge_period_call; try assumption; exact: crt_contract_signed_word.
   + apply: system_triple_of_pure. exact: bs_set_period.
Qed.
Lemma bs_increment_sem rb mb count i r p : (i<16)%coq_nat ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (BSHead rb mb count i r p)) bs_increment_code
 (AS_base [::] (BSHead rb mb count (S i) r p)).
Proof.
 move=> Hi. have Wi : batch_word32 (Z.of_nat i) by unfold batch_word32; lia.
 have Wone : batch_word32 1 by unfold batch_word32; lia.
 have Wsum : batch_word32 (Z.of_nat i+1) by unfold batch_word32; lia.
 rewrite /bs_increment_code.
 apply: (sem_seq (Q:=AS_base [::T_const (SM.Vi32 (Z.of_nat i));T_const (SM.Vi32 1)] (BSHead rb mb count i r p))).
 - apply: (sem_seq (es1:=[::BI_local_get 6%num]) (Q:=AS_base [::T_const (SM.Vi32 (Z.of_nat i))] (BSHead rb mb count i r p))).
   + apply: get_pinned_frame. unfold_bs. bs_pinned.
   + exact: sem_const_framed.
 - apply: (sem_seq (Q:=AS_base [::T_const (SM.Vi32 (Z.of_nat i+1))] (BSHead rb mb count i r p))).
   + apply: (batch_checked_add_Z (ia:=9%num) (ib:=10%num) (ir:=11%num)); try discriminate; try assumption; unfold_bs; first [bs_stable|bs_present].
   + replace (Z.of_nat i+1) with (Z.of_nat (S i)) by lia. exact: bs_set_index.
Qed.
Lemma bs_prepare_sem rb mb count rs ms i r p a m :
 array_region mem rb rs -> array_region mem mb ms -> List.nth_error rs i = Some a -> List.nth_error ms i = Some m ->
 word r -> word p ->
 system_triple mem (AS_base [::] (BSHead rb mb count i r p)) (bs_call_code ++ bs_guard_code)
 (AS_base [::T_const (VAL_int32 (wasm_bool (solve_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)) <? 0)))]
 (BSNext rb mb count i r p (solve_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m))))).
Proof.
 move=> Hr Hm Ha Hn Wr Wp.
 apply: (system_triple_seq (Q1:=AS_base [::] (BSNext rb mb count i r p (solve_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)))))); first reflexivity.
 - exact: (bs_call_sem Hr Hm Ha Hn Wr Wp).
 - apply: system_triple_of_pure. apply: bs_guard_sem. exact: (proj1 (scalar_result_values_word r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m))).
Qed.
Lemma bs_update_sem rb mb count rs ms i r p a m next :
 array_region mem rb rs -> array_region mem mb ms -> List.nth_error rs i = Some a -> List.nth_error ms i = Some m ->
 word r -> word p -> (i<16)%coq_nat ->
 system_triple mem (AS_base [::] (BSNext rb mb count i r p next))
 (bs_period_code ++ [::BI_local_get 7%num;BI_local_set 4%num] ++ bs_increment_code)
 (AS_base [::] (BSHead rb mb count (S i) next (period_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m))))).
Proof.
 move=> Hr Hm Ha Hn Wr Wp Hi.
 apply: (system_triple_seq (Q1:=AS_base [::] (BSNext rb mb count i r (period_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m))) next))); first reflexivity.
 - exact: (bs_period_sem Hr Hm Ha Hn Wr Wp).
 - apply: (system_triple_seq (Q1:=AS_base [::] (BSHead rb mb count i next (period_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)))))); first reflexivity.
   + apply: system_triple_of_pure. exact: bs_commit_residue.
   + apply: system_triple_of_pure. exact: bs_increment_sem.
Qed.
Lemma bs_error_branch rb mb count i r p next Qn Qr Qb :
 aentails (AS_base [::] (BSExit rb mb count next)) (Qb 2%nat) ->
 system_mxk mem (AS_base [::] (BSNext rb mb count i r p next))
 [::BI_local_get 7%num;BI_local_set 4%num;BI_br 2%num] Qn Qr Qb.
Proof.
 move=> HQ. apply: (system_mxk_seq (es1:=[::BI_local_get 7%num;BI_local_set 4%num])
 (Q1:=AS_base [::] (BSHead rb mb count i next p))); first reflexivity.
 - apply: system_mxk_lift. apply: system_triple_of_pure. exact: bs_commit_residue.
 - apply: system_mxk_of_pure. apply: (sem_mxk_br_k (k:=2%nat)).
   move=> V st H. apply: HQ. exact: (bs_head_exit H).
Qed.
Lemma bs_loop_stopped rb mb count r p : (count<=16)%coq_nat ->
 system_mxk mem (AS_base [::] (BSHead rb mb count count r p))
 [::BI_loop (BT_valtype None) bs_loop_code]
 (AS_base [::] (BSExit rb mb count r)) crt_false_assert
 (fun k => if k is 0%nat then AS_base [::] (BSExit rb mb count r) else crt_false_assert).
Proof.
 move=> Hcount. apply: (system_loop_unroll (Pback:=crt_false_assert) (t1s:=[::]) (t2s:=[::])); try reflexivity.
 - move=> V vs h [Hs _]. by case: Hs => <-.
 - move=> V vs h [_ HF]. by case: HF.
 - rewrite /bs_loop_code.
   apply: (system_mxk_seq (es1:=batch_loop_condition 6%num)
   (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (BSHead rb mb count count r p))); first reflexivity.
   + apply: system_mxk_lift. apply: system_triple_of_pure.
     have Wc : batch_word32 (Z.of_nat count) by unfold batch_word32; lia.
     have H := batch_loop_condition_sem (G:=triv_ctx SM.main) (H:=BSHead rb mb count count r p) (idx:=6%num) Wc Wc ltac:(unfold_bs;bs_pinned) ltac:(unfold_bs;bs_pinned).
     by rewrite Z.ltb_irrefl in H.
   + apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=crt_false_assert)); first reflexivity.
     * apply: system_mxk_of_pure. apply: (crt_br_if_true_sem (k:=1%nat)). exact: bs_head_exit.
     * apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
 - apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
Qed.
Lemma bs_loop_exec fuel rb mb count rs ms i r p :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat -> (i+fuel=count)%coq_nat ->
 word r -> word p ->
 system_mxk mem (AS_base [::] (BSHead rb mb count i r p))
 [::BI_loop (BT_valtype None) bs_loop_code]
 (AS_base [::] (BSExit rb mb count (solve_value (solve_fold (bs_entries fuel i rs ms) r p)))) crt_false_assert
 (fun k => if k is 0%nat then AS_base [::] (BSExit rb mb count (solve_value (solve_fold (bs_entries fuel i rs ms) r p))) else crt_false_assert).
Proof.
 move: i r p. induction fuel as [|fuel IH]; move=> i r p Hr Hm Hcount Hfuel Wr Wp.
 - have Ei : i=count by lia. subst i. cbn [bs_entries solve_fold solve_value]. exact: bs_loop_stopped.
 - have Hi : (i<count)%coq_nat by lia. have Hi16 : (i<16)%coq_nat by lia.
   have Hrlen : List.length rs = 16%nat by have H:=proj1 Hr; rewrite length_is_size.
   have Hmlen : List.length ms = 16%nat by have H:=proj1 Hm; rewrite length_is_size.
   have [a Ha] : exists a, List.nth_error rs i=Some a.
   { destruct (List.nth_error rs i) as [a|] eqn:E; first by exists a. apply List.nth_error_None in E. lia. }
   have [m Hn] : exists m, List.nth_error ms i=Some m.
   { destruct (List.nth_error ms i) as [m|] eqn:E; first by exists m. apply List.nth_error_None in E. lia. }
   have Eentries : bs_entries (S fuel) i rs ms = (Wasm_int.Int64.signed a,Wasm_int.Int64.signed m)::bs_entries fuel (S i) rs ms.
   { cbn [bs_entries]. by rewrite (bs_entry_nth Ha Hn). }
   rewrite Eentries bs_fold_step.
   set next := solve_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)).
   set newp := period_value (merge r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)).
   have [Wnext Wnewp] := scalar_result_values_word r p (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m).
   have Wi : batch_word32 (Z.of_nat i) by unfold batch_word32; lia.
   have Wcount : batch_word32 (Z.of_nat count) by unfold batch_word32; lia.
   have Econd : negb (Z.of_nat i <? Z.of_nat count)=false by apply negb_false_iff; apply Z.ltb_lt; lia.
   have Hcond : sem_triple (triv_ctx SM.main) (AS_base [::] (BSHead rb mb count i r p))
    (batch_loop_condition 6%num) (AS_base [::T_const (VAL_int32 (wasm_bool false))] (BSHead rb mb count i r p)).
   { have H := batch_loop_condition_sem (G:=triv_ctx SM.main) (H:=BSHead rb mb count i r p) (idx:=6%num) Wi Wcount ltac:(unfold_bs;bs_pinned) ltac:(unfold_bs;bs_pinned). by rewrite Econd in H. }
   case Ebad : (next <? 0).
   + apply: (system_loop_unroll (Pback:=crt_false_assert) (t1s:=[::]) (t2s:=[::])); try reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * move=> V vs h [_ HF]. by case: HF.
     * rewrite /bs_loop_code.
       apply: (system_mxk_seq (es1:=batch_loop_condition 6%num)
       (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BSHead rb mb count i r p))); first reflexivity.
       -- apply: system_mxk_lift. exact: system_triple_of_pure.
       -- apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=AS_base [::] (BSHead rb mb count i r p))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: crt_br_if_false_sem.
          ++ apply: (system_mxk_seq (es1:=bs_call_code ++ bs_guard_code)
             (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (BSNext rb mb count i r p next))); first reflexivity.
             ** apply: system_mxk_lift. have H := bs_prepare_sem Hr Hm Ha Hn Wr Wp. rewrite -/next Ebad in H. exact: H.
             ** apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_local_get 7%num;BI_local_set 4%num;BI_br 2%num] [::]]) (Q1:=crt_false_assert)); first reflexivity.
                --- apply: (system_if_const (b:=true) (t2s:=[::])); first reflexivity.
                    +++ move=> V vs h [_ HF]. by case: HF.
                    +++ apply: bs_error_branch. by [].
                --- apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
     * apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
   + apply: (system_loop_unroll (Pback:=AS_base [::] (BSHead rb mb count (S i) next newp)) (t1s:=[::]) (t2s:=[::])); try reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * rewrite /bs_loop_code.
       apply: (system_mxk_seq (es1:=batch_loop_condition 6%num)
       (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BSHead rb mb count i r p))); first reflexivity.
       -- apply: system_mxk_lift. exact: system_triple_of_pure.
       -- apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=AS_base [::] (BSHead rb mb count i r p))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: crt_br_if_false_sem.
          ++ apply: (system_mxk_seq (es1:=bs_call_code ++ bs_guard_code)
             (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BSNext rb mb count i r p next))); first reflexivity.
             ** apply: system_mxk_lift. have H := bs_prepare_sem Hr Hm Ha Hn Wr Wp. rewrite -/next Ebad in H. exact: H.
             ** apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_local_get 7%num;BI_local_set 4%num;BI_br 2%num] [::]]) (Q1:=AS_base [::] (BSNext rb mb count i r p next))); first reflexivity.
                --- apply: system_mxk_lift. apply: system_triple_of_pure. apply: guard_if_false. exact: sem_nil_same.
                --- apply: (system_mxk_seq (es1:=bs_period_code ++ [::BI_local_get 7%num;BI_local_set 4%num] ++ bs_increment_code)
                    (Q1:=AS_base [::] (BSHead rb mb count (S i) next newp))); first reflexivity.
                    +++ apply: system_mxk_lift. exact: (bs_update_sem Hr Hm Ha Hn Wr Wp Hi16).
                    +++ apply: system_mxk_of_pure. apply: (sem_mxk_br_k (k:=0%nat)). by [].
     * apply: IH; try assumption. lia.
Qed.
Lemma bs_block_exec rb mb count rs ms i r p :
 array_region mem rb rs -> array_region mem mb ms -> (count<=16)%coq_nat -> (i<=count)%coq_nat ->
 word r -> word p ->
 system_triple mem (AS_base [::] (BSHead rb mb count i r p))
 [::BI_block (BT_valtype None) [::BI_loop (BT_valtype None) bs_loop_code]]
 (AS_base [::] (BSExit rb mb count (solve_value (solve_fold (bs_entries (Nat.sub count i) i rs ms) r p)))).
Proof.
 move=> Hr Hm Hcount Hi Wr Wp. apply: system_triple_of_mxk.
 apply: (system_mxk_block (t1s:=[::]) (t2s:=[::])
 (Qb:=fun k => if k is 0%nat then AS_base [::] (BSExit rb mb count (solve_value (solve_fold (bs_entries (Nat.sub count i) i rs ms) r p))) else crt_false_assert)); try reflexivity.
 - move=> V vs h [Hs _]. by case: Hs => <-.
 - apply: (bs_loop_exec (rs:=rs) (ms:=ms)); try assumption. lia.
Qed.
Lemma bs_initialize_sem rb mb count :
 sem_triple (triv_ctx SM.main) (AS_base [::] (BSBase rb mb count))
 [::BI_const_num (SM.Vi64 0);BI_local_set 4%num;BI_const_num (SM.Vi64 1);BI_local_set 5%num;BI_const_num (SM.Vi32 0);BI_local_set 6%num]
 (AS_base [::] (BSHead rb mb count 0%nat 0 1)).
Proof.
 apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 0)]) (Q:=AS_base [::T_const (SM.Vi64 0)] (BSBase rb mb count))); first exact: sem_const_framed.
 apply: (sem_seq (es1:=[::BI_local_set 4%num]) (Q:=AS_base [::] (BSExit rb mb count 0))).
 - apply: sem_local_set_const_frame; unfold_bs; [bs_stable|bs_present].
 - apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 1)]) (Q:=AS_base [::T_const (SM.Vi64 1)] (BSExit rb mb count 0))); first exact: sem_const_framed.
   apply: (sem_seq (es1:=[::BI_local_set 5%num]) (Q:=AS_base [::] (HA_and (bs_pin 4%num (SM.Vi64 0)) (HA_and (bs_pin 5%num (SM.Vi64 1)) (BSBase rb mb count))))).
   + apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi64 1)] (BSExit rb mb count 0))
     (Q':=AS_base [::] (HA_and (bs_pin 5%num (SM.Vi64 1)) (BSExit rb mb count 0)))); first by [].
     * move=> V [vs h] /= [Hs [Hp [Hr HB]]]. by split; [|split; [|split]].
     * apply: sem_local_set_const_frame; unfold_bs; [bs_stable|bs_present].
   + apply: (sem_seq (es1:=[::BI_const_num (SM.Vi32 0)]) (Q:=AS_base [::T_const (SM.Vi32 0)] (HA_and (bs_pin 4%num (SM.Vi64 0)) (HA_and (bs_pin 5%num (SM.Vi64 1)) (BSBase rb mb count))))); first exact: sem_const_framed.
     apply: sem_local_set_const_frame; unfold_bs; [bs_stable|bs_present].
Qed.
End Host.
