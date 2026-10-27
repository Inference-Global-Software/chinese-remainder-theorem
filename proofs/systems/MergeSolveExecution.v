(* Native full-width solve execution over arbitrary prepared memory. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit MultiExitK NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTMath CRTLoops CRTSystemStatements CRTSystemArithmetic CRTFinite.
From CRTWasm Require Import CRTContracts CRTPublicExecution CRTGeneralArithmetic CRTSolveExecution.
From CRTSystems Require Import ReadOnly SystemRuntime FullWidthExecution SystemCalls SystemControl
 FullWidthInverseExecution MulModExecution MergeValidation MergeSolvePure.
Module SM := CRTSystemGenerated.main.
Import FullWidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition merge_m_code := List.firstn 4 solver_reductions_code.
Definition merge_n_code := List.skipn 4 solver_reductions_code.
Definition merge_guard_code := [::BI_local_get 6%num;BI_const_num (SM.Vi64 MAX);
 BI_local_get 3%num;BI_binop T_i64 (Binop_i (BOI_div SX_S));BI_relop T_i64 (Relop_i (ROI_gt SX_S))].
Definition merge_product_code := [::BI_local_get 5%num;BI_local_get 4%num;
 BI_binop T_i64 (Binop_i (BOI_div SX_S));BI_local_get 7%num;BI_call 1%num;
 BI_local_get 9%num;BI_local_get 7%num;BI_call 4%num;BI_local_set 10%num].
Definition merge_finish_code := solver_B_code ++
 [::BI_local_get 8%num;BI_local_get 7%num;BI_call 2%num;BI_local_set 9%num] ++
 merge_product_code ++ solver_result_code ++ [::BI_return;BI_unreachable].
Definition merge_after_guard := merge_n_code ++
 [::BI_local_get 7%num;BI_const_num (SM.Vi64 1);BI_relop T_i64 (Relop_i ROI_eq);
 BI_if (BT_valtype None) [::BI_local_get 0%num;BI_return] [::]] ++ merge_finish_code.
Definition merge_after_compat := merge_m_code ++ merge_guard_code ++
 [::BI_if (BT_valtype None) [::BI_const_num (SM.Vi64 (-3));BI_return] [::]] ++ merge_after_guard.
Definition merge_after_gcd := solver_delta_code ++ solver_compatibility_test ++
 [::BI_if (BT_valtype None) [::BI_const_num (SM.Vi64 (-1));BI_return] [::]] ++ merge_after_compat.
Definition merge_after_validation := [::BI_local_get 1%num;BI_local_get 3%num;BI_call 0%num;BI_local_set 4%num] ++ merge_after_gcd.
Lemma merge_solve_body_shape : modfunc_body SM.crt_merge_solve = merge_validation ++
 [::BI_if (BT_valtype None) [::BI_const_num (SM.Vi64 (-2));BI_return] [::]] ++ merge_after_validation.
Proof. reflexivity. Qed.
Section Host.
Context `{ho : host}.
Context (mem : meminst).
Ltac pinned_tac := solve [exact: pinned_bare | apply: pinned_left; pinned_tac | apply: pinned_right; pinned_tac].
Ltac present_tac := solve [exact: loc_present_defined | exact: loc_present_pin | apply: loc_present_left; present_tac | apply: loc_present_right; present_tac].
Ltac stable_tac := solve [exact: solver_stable_true | exact: loc_stable_defined_self | exact: loc_stable_pin_self | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other | apply: loc_stable_and; stable_tac].
Ltac unfold_solve := rewrite /SolveT /SolveU /SolveB /SolveN /SolveM /SolveD /SolveG /SolveEntry.
Lemma merge_m_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (SolveD a m b n)) merge_m_code (AS_base [::] (SolveM a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
 rewrite /merge_m_code /solver_reductions_code /=.
 apply: (sem_seq (es1 := [:: BI_local_get 1%num])
  (Q := AS_base [:: T_const (SM.Vi64 m)] (SolveD a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 4%num])
  (Q := AS_base [:: T_const (SM.Vi64 m); T_const (SM.Vi64 (Z.gcd m n))] (SolveD a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))])
  (Q := AS_base [:: T_const (SM.Vi64 (m / Z.gcd m n))] (SolveD a m b n))).
 { apply: binop_consts; [by vm_compute | by [] | by [] | apply: crt_i64_div_positive_exact; lia]. }
 apply: sem_local_set_const_frame; unfold_solve; [stable_tac|present_tac].
Qed.
Lemma merge_n_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (SolveM a m b n)) merge_n_code (AS_base [::] (SolveN a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
 rewrite /merge_n_code /solver_reductions_code /=.
 apply: (sem_seq (es1 := [:: BI_local_get 3%num])
  (Q := AS_base [:: T_const (SM.Vi64 n)] (SolveM a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 4%num])
  (Q := AS_base [:: T_const (SM.Vi64 n); T_const (SM.Vi64 (Z.gcd m n))] (SolveM a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))])
  (Q := AS_base [:: T_const (SM.Vi64 (n / Z.gcd m n))] (SolveM a m b n))).
 { apply: binop_consts; [by vm_compute | by [] | by [] | apply: crt_i64_div_positive_exact; lia]. }
 apply: sem_local_set_const_frame; unfold_solve; [stable_tac | present_tac].
Qed.

Lemma merge_guard_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (SolveM a m b n)) merge_guard_code
 (AS_base [::T_const (VAL_int32 (wasm_bool (MAX/n <? m/Z.gcd m n)))] (SolveM a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] _] := Hd.
 have [_ [Hmq [Wmq _]]] := crt_period_intermediate_bounds (proj1 Hd).
 have Wmax : word MAX by unfold word,MAX,i64_min,i64_max; lia.
 have Hquot : 0 <= MAX/n <= MAX.
 { split; [apply Z.div_pos; unfold MAX,i64_max in *; lia|apply Z.div_le_upper_bound; unfold MAX,i64_max in *; nia]. }
 have Wquot := nonnegative_word (MAX/n) Hquot.
 rewrite /merge_guard_code.
 apply: (sem_seq (es1:=[::BI_local_get 6%num])
 (Q:=AS_base [::T_const (SM.Vi64 (m/Z.gcd m n))] (SolveM a m b n))).
 - apply: get_pinned_frame. unfold_solve. pinned_tac.
 - apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 MAX)])
   (Q:=AS_base [::T_const (SM.Vi64 (m/Z.gcd m n));T_const (SM.Vi64 MAX)] (SolveM a m b n))); first exact: sem_const_framed.
   apply: (sem_seq (es1:=[::BI_local_get 3%num])
   (Q:=AS_base [::T_const (SM.Vi64 (m/Z.gcd m n));T_const (SM.Vi64 MAX);T_const (SM.Vi64 n)] (SolveM a m b n))).
   + apply: get_pinned_frame. unfold_solve. pinned_tac.
   + apply: (sem_seq (es1:=[::BI_binop T_i64 (Binop_i (BOI_div SX_S))])
     (Q:=AS_base [::T_const (SM.Vi64 (m/Z.gcd m n));T_const (SM.Vi64 (MAX/n))] (SolveM a m b n))).
     * apply: (sem_frame_consts (vf:=[::SM.Vi64 (m/Z.gcd m n)])).
       apply: binop_consts; try reflexivity. apply: crt_i64_div_positive_exact; [unfold MAX,i64_max; lia|exact Hn].
     * rewrite -(crt_public_gt Wmq Wquot). apply: relop_consts; reflexivity.
Qed.
Lemma merge_inverse_domain a m b n : domain a m b n -> 1 < n / Z.gcd m n ->
 eea_inputs (n/Z.gcd m n) ((m/Z.gcd m n) mod (n/Z.gcd m n)) /\
 Z.gcd (n/Z.gcd m n) ((m/Z.gcd m n) mod (n/Z.gcd m n)) = 1.
Proof.
 move=> Hd Hnlarge. have [[Hm Hn] _] := Hd.
 have [Hg [Hgm [Hgn [Hmp [Hnp [Hcop _]]]]]] := reduction_proved m n ltac:(lia) ltac:(lia).
 have HnB : n/Z.gcd m n <= MAX.
 { have [_ [Hrange _]] := crt_period_intermediate_bounds (conj Hn Hm). rewrite Z.gcd_comm in Hrange. lia. }
 have Hcop' : Z.gcd (n/Z.gcd m n) ((m/Z.gcd m n) mod (n/Z.gcd m n)) = 1.
 { rewrite Z.gcd_comm Z.gcd_mod; last lia. by rewrite Z.gcd_comm. }
 have Hrange := Z.mod_pos_bound (m/Z.gcd m n) (n/Z.gcd m n) ltac:(lia).
 have Hnz : (m/Z.gcd m n) mod (n/Z.gcd m n) <> 0.
 { move=> Hz. rewrite Hz Z.gcd_0_r Z.abs_eq in Hcop'; lia. }
 split; last exact Hcop'. unfold eea_inputs. lia.
Qed.
Lemma merge_inverse_sem a m b n : domain a m b n -> 1 < n/Z.gcd m n ->
 let u := inverse_model ((m/Z.gcd m n) mod (n/Z.gcd m n)) (n/Z.gcd m n) in
 system_triple mem (AS_base [::] (SolveB a m b n))
 [::BI_local_get 8%num;BI_local_get 7%num;BI_call 2%num;BI_local_set 9%num]
 (AS_base [::] (SolveU a m b n u)).
Proof.
 move=> Hd Hlarge u. have [Hi Hcop] := merge_inverse_domain Hd Hlarge.
 apply: (system_triple_seq (es1:=[::BI_local_get 8%num;BI_local_get 7%num])
 (Q1:=AS_base [::T_const (SM.Vi64 ((m/Z.gcd m n) mod (n/Z.gcd m n)));T_const (SM.Vi64 (n/Z.gcd m n))] (SolveB a m b n))); first reflexivity.
 - apply: system_triple_of_pure.
   apply: (sem_seq (es1:=[::BI_local_get 8%num])
   (Q:=AS_base [::T_const (SM.Vi64 ((m/Z.gcd m n) mod (n/Z.gcd m n)))] (SolveB a m b n)));
   apply: get_pinned_frame; unfold_solve; pinned_tac.
 - apply: (system_triple_seq (es1:=[::BI_call 2%num])
   (Q1:=AS_base [::T_const (SM.Vi64 u)] (SolveB a m b n))); first reflexivity.
   + move=> frame Hinst. apply: crt_inverse_call_from_computes; first exact Hinst.
     exact: inverse_machine_computes.
   + apply: system_triple_of_pure. apply: sem_local_set_const_frame; unfold_solve; [stable_tac|present_tac].
Qed.
Lemma merge_product_sem a m b n u : domain a m b n -> compatible a m b n ->
 0 <= u < n/Z.gcd m n ->
 system_triple mem (AS_base [::] (SolveU a m b n u)) merge_product_code
 (AS_base [::] (SolveT a m b n u
 (FullWidth.mul_mod (((b-a)/Z.gcd m n) mod (n/Z.gcd m n)) u (n/Z.gcd m n)))).
Proof.
 move=> Hd Hc Hu.
 have [Hg [Hmq [Hnq [_ [_ [_ [Wd [_ Wq]]]]]]]] := reduction_machine_bounds_proved a m b n Hd.
 have Hnorm := Z.mod_pos_bound ((b-a)/Z.gcd m n) (n/Z.gcd m n) ltac:(lia).
 rewrite /merge_product_code.
 apply: (system_triple_seq (es1:=[::BI_local_get 5%num])
 (Q1:=AS_base [::T_const (SM.Vi64 (b-a))] (SolveU a m b n u))); first reflexivity.
 { apply: system_triple_of_pure. apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (system_triple_seq (es1:=[::BI_local_get 4%num])
 (Q1:=AS_base [::T_const (SM.Vi64 (b-a));T_const (SM.Vi64 (Z.gcd m n))] (SolveU a m b n u))); first reflexivity.
 { apply: system_triple_of_pure. apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (system_triple_seq (es1:=[::BI_binop T_i64 (Binop_i (BOI_div SX_S))])
 (Q1:=AS_base [::T_const (SM.Vi64 ((b-a)/Z.gcd m n))] (SolveU a m b n u))); first reflexivity.
 { apply: system_triple_of_pure. apply: binop_consts; try reflexivity. exact: solver_divisible_div. }
 apply: (system_triple_seq (es1:=[::BI_local_get 7%num])
 (Q1:=AS_base [::T_const (SM.Vi64 ((b-a)/Z.gcd m n));T_const (SM.Vi64 (n/Z.gcd m n))] (SolveU a m b n u))); first reflexivity.
 { apply: system_triple_of_pure. apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (system_triple_seq (es1:=[::BI_call 1%num])
 (Q1:=AS_base [::T_const (SM.Vi64 (((b-a)/Z.gcd m n) mod (n/Z.gcd m n)))] (SolveU a m b n u))); first reflexivity.
 { move=> frame Hi. exact: crt_normalize_call. }
 apply: (system_triple_seq (es1:=[::BI_local_get 9%num])
 (Q1:=AS_base [::T_const (SM.Vi64 (((b-a)/Z.gcd m n) mod (n/Z.gcd m n)));T_const (SM.Vi64 (u))] (SolveU a m b n u))); first reflexivity.
 { apply: system_triple_of_pure. apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (system_triple_seq (es1:=[::BI_local_get 7%num])
 (Q1:=AS_base [::T_const (SM.Vi64 (((b-a)/Z.gcd m n) mod (n/Z.gcd m n)));T_const (SM.Vi64 (u));T_const (SM.Vi64 (n/Z.gcd m n))] (SolveU a m b n u))); first reflexivity.
 { apply: system_triple_of_pure. apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (system_triple_seq (es1:=[::BI_call 4%num])
 (Q1:=AS_base [::T_const (SM.Vi64 (FullWidth.mul_mod (((b-a)/Z.gcd m n) mod (n/Z.gcd m n)) u (n/Z.gcd m n)))] (SolveU a m b n u))); first reflexivity.
 { move=> frame Hi. exact: crt_mul_call. }
 apply: system_triple_of_pure. apply: sem_local_set_const_frame; unfold_solve; [stable_tac|present_tac].
Qed.
Definition merge_solved a m b n :=
 if n/Z.gcd m n =? 1 then a else
 a + m * FullWidth.mul_mod (((b-a)/Z.gcd m n) mod (n/Z.gcd m n))
 (inverse_model ((m/Z.gcd m n) mod (n/Z.gcd m n)) (n/Z.gcd m n)) (n/Z.gcd m n).
Definition MergeRun P es r := system_mxk mem P es crt_false_assert
 (AS_base [::T_const (SM.Vi64 r)] HA_true) (fun _ => crt_false_assert).
Lemma merge_finish_sem a m b n : domain a m b n -> compatible a m b n ->
 Z.lcm m n <= MAX -> 1 < n/Z.gcd m n ->
 let u := inverse_model ((m/Z.gcd m n) mod (n/Z.gcd m n)) (n/Z.gcd m n) in
 let t := FullWidth.mul_mod (((b-a)/Z.gcd m n) mod (n/Z.gcd m n)) u (n/Z.gcd m n) in
 MergeRun (AS_base [::] (SolveN a m b n)) merge_finish_code (a+m*t).
Proof.
 move=> Hd Hc Hfit Hlarge u t.
 have [Hi Hcop] := merge_inverse_domain Hd Hlarge.
 have [Hu _] := inverse_model_proved _ _ Hi Hcop.
 have [Hg [Hmq [Hnq [_ [_ [_ [Wd [_ Wq]]]]]]]] := reduction_machine_bounds_proved a m b n Hd.
 have Hnorm := Z.mod_pos_bound ((b-a)/Z.gcd m n) (n/Z.gcd m n) ltac:(lia).
 have [_ [Ht Wt]] := mul_mod_proved _ _ _ Hnq Hnorm Hu.
 rewrite /MergeRun /merge_finish_code.
 apply: (system_mxk_seq (es1:=solver_B_code) (Q1:=AS_base [::] (SolveB a m b n))); first reflexivity.
 - apply: system_mxk_lift. apply: system_triple_of_pure. exact: solver_B_sem.
 - apply: (system_mxk_seq (es1:=[::BI_local_get 8%num;BI_local_get 7%num;BI_call 2%num;BI_local_set 9%num])
   (Q1:=AS_base [::] (SolveU a m b n u))); first reflexivity.
   + apply: system_mxk_lift. exact: merge_inverse_sem.
   + apply: (system_mxk_seq (es1:=merge_product_code)
     (Q1:=AS_base [::] (SolveT a m b n u t))); first reflexivity.
     * apply: system_mxk_lift. exact: merge_product_sem.
     * apply: (system_mxk_seq (es1:=solver_result_code)
       (Q1:=AS_base [::T_const (SM.Vi64 (a+m*t))] HA_true)); first reflexivity.
       -- apply: system_mxk_lift. apply: system_triple_of_pure.
          apply: (sem_conseq (P':=AS_base [::] (SolveT a m b n u t))
          (Q':=AS_base [::T_const (SM.Vi64 (a+m*t))] (SolveT a m b n u t))).
          ++ by [].
          ++ move=> V [vs h] [Hs _]. by split.
          ++ exact: solver_result_sem.
       -- apply: system_mxk_of_pure_no_break. exact: sem_mx_return_suffix.
Qed.
Lemma merge_after_guard_sem a m b n : domain a m b n -> compatible a m b n ->
 Z.lcm m n <= MAX ->
 MergeRun (AS_base [::] (SolveM a m b n)) merge_after_guard (merge_solved a m b n).
Proof.
 move=> Hd Hc Hfit.
 have [Hg [Hmq [Hnq _]]] := reduction_machine_bounds_proved a m b n Hd.
 have Wnq := crt_modulus_word Hnq.
 have Wone : word 1 by unfold word,i64_min,i64_max; lia.
 rewrite /MergeRun /merge_after_guard /merge_solved.
 apply: (system_mxk_seq (es1:=merge_n_code) (Q1:=AS_base [::] (SolveN a m b n))); first reflexivity.
 - apply: system_mxk_lift. apply: system_triple_of_pure. exact: merge_n_sem.
 - apply: (system_mxk_seq
   (es1:=[::BI_local_get 7%num;BI_const_num (SM.Vi64 1);BI_relop T_i64 (Relop_i ROI_eq)])
   (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool (n/Z.gcd m n =? 1)))] (SolveN a m b n))); first reflexivity.
   + apply: system_mxk_lift. apply: system_triple_of_pure.
     rewrite -(crt_public_eq Wnq Wone). apply: test_pin_const; try reflexivity. unfold_solve. pinned_tac.
   + case E: (n/Z.gcd m n =? 1).
     * apply: system_mxk_of_pure_no_break. apply: solver_return_local_suffix. unfold_solve. pinned_tac.
     * apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_local_get 0%num;BI_return] [::]])
       (Q1:=AS_base [::] (SolveN a m b n))); first reflexivity.
       -- apply: system_mxk_lift. apply: system_triple_of_pure. apply: guard_if_false. exact: sem_nil_same.
       -- apply: merge_finish_sem; try assumption. apply Z.eqb_neq in E. lia.
Qed.
Lemma merge_after_compat_sem a m b n : domain a m b n -> compatible a m b n ->
 MergeRun (AS_base [::] (SolveD a m b n)) merge_after_compat
 (if MAX/n <? m/Z.gcd m n then -3 else merge_solved a m b n).
Proof.
 move=> Hd Hc. rewrite /MergeRun /merge_after_compat.
 apply: (system_mxk_seq (es1:=merge_m_code) (Q1:=AS_base [::] (SolveM a m b n))); first reflexivity.
 - apply: system_mxk_lift. apply: system_triple_of_pure. exact: merge_m_sem.
 - apply: (system_mxk_seq (es1:=merge_guard_code)
   (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool (MAX/n <? m/Z.gcd m n)))] (SolveM a m b n))); first reflexivity.
   + apply: system_mxk_lift. apply: system_triple_of_pure. exact: merge_guard_sem.
   + case E: (MAX/n <? m/Z.gcd m n).
     * apply: system_mxk_of_pure_no_break. exact: solver_reject_suffix.
     * apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_const_num (SM.Vi64 (-3));BI_return] [::]])
       (Q1:=AS_base [::] (SolveM a m b n))); first reflexivity.
       -- apply: system_mxk_lift. apply: system_triple_of_pure. apply: guard_if_false. exact: sem_nil_same.
       -- apply: merge_after_guard_sem; try assumption.
          have Hguard := proj1 (lcm_guard_proved m n (proj1 Hd)). apply Z.ltb_ge in E. lia.
Qed.
Lemma merge_after_gcd_sem a m b n : domain a m b n ->
 MergeRun (AS_base [::] (SolveG a m b n)) merge_after_gcd
 (if Z.rem (b-a) (Z.gcd m n) =? 0 then
  if MAX/n <? m/Z.gcd m n then -3 else merge_solved a m b n else -1).
Proof.
 move=> Hd. rewrite /MergeRun /merge_after_gcd.
 apply: (system_mxk_seq (es1:=solver_delta_code) (Q1:=AS_base [::] (SolveD a m b n))); first reflexivity.
 - apply: system_mxk_lift. apply: system_triple_of_pure. exact: solver_delta_sem.
 - apply: (system_mxk_seq (es1:=solver_compatibility_test)
   (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool (negb (Z.rem (b-a) (Z.gcd m n) =? 0))))] (SolveD a m b n))); first reflexivity.
   + apply: system_mxk_lift. apply: system_triple_of_pure. exact: solver_compatibility_test_sem.
   + case E: (Z.rem (b-a) (Z.gcd m n) =? 0).
     * apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_const_num (SM.Vi64 (-1));BI_return] [::]])
       (Q1:=AS_base [::] (SolveD a m b n))); first reflexivity.
       -- apply: system_mxk_lift. apply: system_triple_of_pure. apply: guard_if_false. exact: sem_nil_same.
       -- apply: merge_after_compat_sem; first exact Hd.
          apply Z.eqb_eq in E. unfold compatible. apply Z.rem_divide; last exact E.
          have [Hg _] := crt_period_intermediate_bounds (proj1 Hd). lia.
     * apply: system_mxk_of_pure_no_break. exact: solver_reject_suffix.
Qed.
Lemma merge_valid_body_sem a m b n : domain a m b n ->
 MergeRun (AS_base [::] (SolveEntry a m b n)) merge_after_validation
 (if Z.rem (b-a) (Z.gcd m n) =? 0 then
  if MAX/n <? m/Z.gcd m n then -3 else merge_solved a m b n else -1).
Proof.
 move=> Hd. rewrite /MergeRun /merge_after_validation.
 apply: (system_mxk_seq (es1:=[::BI_local_get 1%num;BI_local_get 3%num])
 (Q1:=AS_base [::T_const (SM.Vi64 m);T_const (SM.Vi64 n)] (SolveEntry a m b n))); first reflexivity.
 - apply: system_mxk_lift. apply: system_triple_of_pure.
   apply: (sem_seq (es1:=[::BI_local_get 1%num])
   (Q:=AS_base [::T_const (SM.Vi64 m)] (SolveEntry a m b n)));
   apply: get_pinned_frame; unfold_solve; pinned_tac.
 - apply: (system_mxk_seq (es1:=[::BI_call 0%num])
   (Q1:=AS_base [::T_const (SM.Vi64 (Z.gcd m n))] (SolveEntry a m b n))); first reflexivity.
   + apply: system_mxk_lift. move=> frame Hi. apply: crt_gcd_call; [exact Hi|exact (proj1 Hd)].
   + apply: (system_mxk_seq (es1:=[::BI_local_set 4%num])
     (Q1:=AS_base [::] (SolveG a m b n))); first reflexivity.
     * apply: system_mxk_lift. apply: system_triple_of_pure. apply: sem_local_set_const_frame; unfold_solve; [stable_tac|present_tac].
     * exact: merge_after_gcd_sem.
Qed.
Definition merge_value a m b n :=
 if merge_bad a m b n then -2 else
 if Z.rem (b-a) (Z.gcd m n) =? 0 then
 if MAX/n <? m/Z.gcd m n then -3 else merge_solved a m b n else -1.
Lemma merge_body_sem a m b n : word a -> word m -> word b -> word n ->
 MergeRun (AS_base [::] (SolveEntry a m b n)) (modfunc_body SM.crt_merge_solve) (merge_value a m b n).
Proof.
 move=> Wa Wm Wb Wn. rewrite /MergeRun /merge_value merge_solve_body_shape.
 apply: (system_mxk_seq (es1:=merge_validation)
 (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool (merge_bad a m b n)))] (SolveEntry a m b n))); first reflexivity.
 - apply: system_mxk_lift. apply: system_triple_of_pure.
   apply: merge_validation_sem; try assumption; unfold_solve; pinned_tac.
 - case E: (merge_bad a m b n).
   + apply: system_mxk_of_pure_no_break. exact: solver_reject_suffix.
   + apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_const_num (SM.Vi64 (-2));BI_return] [::]])
     (Q1:=AS_base [::] (SolveEntry a m b n))); first reflexivity.
     * apply: system_mxk_lift. apply: system_triple_of_pure. apply: guard_if_false. exact: sem_nil_same.
     * apply: merge_valid_body_sem. exact (proj1 (merge_bad_false_domain Wa Wm Wb Wn) E).
Qed.
Lemma merge_value_model a m b n : word a -> word m -> word b -> word n ->
 merge_value a m b n = FiniteSystem.solve_value (FiniteSystem.merge a m b n).
Proof.
 move=> Wa Wm Wb Wn.
 have Hbad := merge_bad_model Wa Wm Wb Wn.
 rewrite /merge_value /FiniteSystem.merge.
 case E: (merge_bad a m b n).
 - rewrite E in Hbad. have Hv : (FiniteSystem.validb (a,m) && FiniteSystem.validb (b,n)) = false.
   { by case: (FiniteSystem.validb (a,m) && FiniteSystem.validb (b,n)) Hbad. }
   by rewrite Hv.
 - rewrite E in Hbad. have Hv : (FiniteSystem.validb (a,m) && FiniteSystem.validb (b,n)) = true.
   { by case: (FiniteSystem.validb (a,m) && FiniteSystem.validb (b,n)) Hbad. }
   rewrite Hv. have Hd := proj1 (merge_bad_false_domain Wa Wm Wb Wn) E.
   rewrite gcd_model_proved; last exact (proj1 Hd).
   have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
   have Er : (Z.rem (b-a) (Z.gcd m n) =? 0) = ((b-a) mod Z.gcd m n =? 0).
   { have Hiff : Z.rem (b-a) (Z.gcd m n) = 0 <-> (b-a) mod Z.gcd m n = 0.
     { exact (proj1 (signed_arithmetic_bridge_proved (b-a) (Z.gcd m n) (solver_delta_word Hd) Hg)). }
     case Er: (Z.rem (b-a) (Z.gcd m n) =? 0); case Em: ((b-a) mod Z.gcd m n =? 0); try reflexivity;
     [apply Z.eqb_eq in Er; apply Z.eqb_neq in Em|apply Z.eqb_neq in Er; apply Z.eqb_eq in Em]; tauto. }
   rewrite Er /merge_solved.
   by case: ((b-a) mod Z.gcd m n =? 0); case: (MAX/n <? m/Z.gcd m n).
Qed.
Lemma merge_solve_entry_entails a m b n :
 aentails (AS_base [::] (HA_and (args_pinned [:: SM.Vi64 a; SM.Vi64 m; SM.Vi64 b; SM.Vi64 n] 0%num)
   (func_pre_h SM.main SM.crt_merge_solve))) (AS_base [::] (SolveEntry a m b n)).
Proof.
 move=> V [vs h] /= [Hs [[P0 [P1 [P2 [P3 _]]]]
  [[T0 [T1 [T2 [T3 _]]]] [T4 [T5 [T6 [T7 [T8 [T9 [T10 [T11 [T12 [T13 _]]]]]]]]]]]]].
 split; first exact Hs.
 split; first exact P0. split; first exact P1. split; first exact P2. split; first exact P3.
 split; first by case: T4 => [w [Ew _]]; exists w.
 split; first by case: T5 => [w [Ew _]]; exists w.
 split; first by case: T6 => [w [Ew _]]; exists w.
 split; first by case: T7 => [w [Ew _]]; exists w.
 split; first by case: T8 => [w [Ew _]]; exists w.
 split; first by case: T9 => [w [Ew _]]; exists w.
 split; first by case: T10 => [w [Ew _]]; exists w.
 split; first by case: T11 => [w [Ew _]]; exists w.
 split; first by case: T12 => [w [Ew _]]; exists w.
 split; first by case: T13 => [w [Ew _]]; exists w. exact I.
Qed.

Theorem merge_solve_machine_computes a m b n : word a -> word m -> word b -> word n ->
 system_computes mem 5%nat [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n]
 [::SM.Vi64 (FiniteSystem.solve_value (FiniteSystem.merge a m b n))].
Proof.
 move=> Wa Wm Wb Wn. rewrite -(merge_value_model Wa Wm Wb Wn).
 have Hrun := merge_body_sem Wa Wm Wb Wn.
 have Hbody : system_mx mem (AS_base [::] (SolveEntry a m b n)) (modfunc_body SM.crt_merge_solve)
 (AS_base [::T_const (SM.Vi64 (merge_value a m b n))] HA_true)
 (AS_base [::T_const (SM.Vi64 (merge_value a m b n))] HA_true)
 (AS_base [::T_const (SM.Vi64 (merge_value a m b n))] HA_true).
 { apply: system_mx_of_mxk_no_break.
   apply: (system_mxk_conseq (P':=AS_base [::] (SolveEntry a m b n))
   (Qn':=crt_false_assert)
   (Qr':=AS_base [::T_const (SM.Vi64 (merge_value a m b n))] HA_true)
   (Qb':=fun _ => crt_false_assert)).
   - by [].
   - move=> V [vs h] [_ Hfalse]. by case: Hfalse.
   - by [].
   - move=> k V [vs h] HP. exact HP.
   - exact Hrun. }
 rewrite /system_computes /=.
 split; first by repeat split. split; first by repeat split.
 exists (List.repeat (VAL_num (SM.Vi64 0)) 10). split; first reflexivity.
 move=> hs V vs h HP Hr. apply: Hbody; [reflexivity| |exact Hr].
 exact: (merge_solve_entry_entails HP).
Qed.
Lemma crt_merge_solve_entry a m b n :
 crt_entry_admissible mem SM.crt_merge_solve [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n].
Proof.
 move=> defaults Hd. vm_compute in Hd. inversion Hd; subst defaults.
 cbn [crt_entry_valuation activation_frame system_initial_runtime func_pre_h SM.main
 SM.crt_merge_solve args_pinned locals_typed assertion_denote hassert_denote stack_denote
 term_eq term_denote loc_read lookup_N val_loc f_locs modfunc_type modfunc_locals mod_types runtime_inst SM.Vi64].
 repeat split; try reflexivity; try (eexists; split; reflexivity).
Qed.
Lemma crt_merge_solve_call frame H a m b n :
 f_inst frame = system_inst -> word a -> word m -> word b -> word n ->
 sem_triple_at (system_store mem) frame
 (AS_base [::T_const (SM.Vi64 a);T_const (SM.Vi64 m);T_const (SM.Vi64 b);T_const (SM.Vi64 n)] H)
 [::BI_call 5%num]
 (AS_base [::T_const (SM.Vi64 (FiniteSystem.solve_value (FiniteSystem.merge a m b n)))] H).
Proof.
 move=> Hi Wa Wm Wb Wn.
 apply: (crt_call_from_computes_at (i:=5%nat) (addr:=5%num) (fdef:=SM.crt_merge_solve)
 (args:=[::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n])
 (rs:=[::SM.Vi64 (FiniteSystem.solve_value (FiniteSystem.merge a m b n))])
 (params:=[::T_num T_i64;T_num T_i64;T_num T_i64;T_num T_i64]) (results:=[::T_num T_i64])); try reflexivity.
 - by rewrite Hi.
 - exact: crt_merge_solve_entry.
 - exact: merge_solve_machine_computes.
Qed.
End Host.
Print Assumptions merge_solve_machine_computes.
