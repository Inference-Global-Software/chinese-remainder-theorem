From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit
 NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTMath CRTSystemStatements CRTSystemArithmetic CRTFinite.
From CRTWasm Require Import CRTContracts CRTPublicExecution CRTGeneralArithmetic.
From CRTSystems Require Import ReadOnly SystemRuntime FullWidthExecution SystemCalls
 FullWidthInverseExecution SystemControl MergeValidation MergeSolvePure.
Module SM := CRTSystemGenerated.main.
Import FullWidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition ppin i z := term_eq (T_local i) (T_const (SM.Vi64 z)).
Definition PEntry a m b n := HA_and (ppin 0%num a) (HA_and (ppin 1%num m)
 (HA_and (ppin 2%num b) (HA_and (ppin 3%num n)
 (HA_and (HA_defined (T_local 4%num)) (HA_and (HA_defined (T_local 5%num))
 (HA_and (HA_defined (T_local 6%num)) (HA_and (HA_defined (T_local 7%num))
 (HA_defined (T_local 8%num))))))))).
Definition PG a m b n := HA_and (ppin 4%num (Z.gcd m n)) (PEntry a m b n).
Definition PQ a m b n := HA_and (ppin 5%num (m/Z.gcd m n)) (PG a m b n).
Definition p_reject z := [::BI_const_num (SM.Vi64 z);BI_return].
Definition p_gcd := [::BI_local_get 1%num;BI_local_get 3%num;BI_call 0%num;BI_local_set 4%num].
Definition p_diff := [::BI_local_get 2%num;BI_local_get 0%num] ++ crt_general_checked_sub_code 6%num 7%num 8%num.
Definition p_compat := p_diff ++ [::BI_local_get 4%num;BI_binop T_i64 (Binop_i (BOI_rem SX_S));
 BI_const_num (SM.Vi64 0);BI_relop T_i64 (Relop_i ROI_ne)].
Definition p_quot := [::BI_local_get 1%num;BI_local_get 4%num;BI_binop T_i64 (Binop_i (BOI_div SX_S));BI_local_set 5%num].
Definition p_overflow := [::BI_local_get 5%num;BI_const_num (SM.Vi64 MAX);BI_local_get 3%num;
 BI_binop T_i64 (Binop_i (BOI_div SX_S));BI_relop T_i64 (Relop_i (ROI_gt SX_S))].
Definition p_product := [::BI_local_get 5%num;BI_local_get 3%num] ++
 crt_general_checked_mul_code 6%num 7%num 8%num.
Definition p_tail := p_compat ++ [::BI_if (BT_valtype None) (p_reject (-1)) [::]] ++
 p_quot ++ p_overflow ++ [::BI_if (BT_valtype None) (p_reject (-3)) [::]] ++
 p_product ++ [::BI_return;BI_unreachable].
Lemma p_body_shape : modfunc_body SM.crt_merge_period =
 merge_validation ++ [::BI_if (BT_valtype None) (p_reject (-2)) [::]] ++ p_gcd ++ p_tail.
Proof. reflexivity. Qed.
Definition period_model_Z a m b n := if merge_bad a m b n then -2 else
 let g:=Z.gcd m n in if negb (Z.rem (b-a) g =? 0) then -1 else
 if MAX/n <? m/g then -3 else (m/g)*n.
Section Host.
Context `{ho:host}.
Context (mem:meminst).
Ltac pinned_tac := solve [exact: pinned_bare | apply: pinned_left; pinned_tac | apply: pinned_right; pinned_tac].
Ltac present_tac := solve [exact: loc_present_defined | exact: loc_present_pin | apply: loc_present_left; present_tac | apply: loc_present_right; present_tac].
Ltac stable_tac := solve [exact: loc_stable_defined_self | exact: loc_stable_pin_self | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other | apply: loc_stable_and; stable_tac].
Lemma period_checked_mul_Z G H x y :
  loc_stable 6%num (SM.Vi64 x) H -> loc_stable 7%num (SM.Vi64 y) H ->
  loc_stable 8%num (SM.Vi64 (x * y)) H ->
  loc_present 6%num H -> loc_present 7%num H -> loc_present 8%num H ->
  word x -> word y -> word (x * y) ->
  sem_triple G (AS_base [:: T_const (SM.Vi64 x); T_const (SM.Vi64 y)] H)
    (crt_general_checked_mul_code 6%num 7%num 8%num) (AS_base [:: T_const (SM.Vi64 (x * y))] H).
Proof.
  move=> SA SB SR PA PB PR Wx Wy Wxy.
  have E := crt_i64_mul_repr Wx Wy.
  have Range : Wasm_int.Int64.min_signed <=
    Wasm_int.Int64.signed (Wasm_int.Int64.repr x) *
    Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy)
      i64_min_signed_val i64_max_signed_val. exact Wxy. }
  have SR' : loc_stable 8%num (VAL_int64
    (Wasm_int.Int64.mul (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y))) H.
  { rewrite E. exact SR. }
  have P := crt_general_checked_mul_sem (ia := 6%num) (ib := 7%num) (ir := 8%num) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) SA SB SR' PA PB PR Range.
  rewrite E in P. exact: P.
Qed.
Lemma period_checked_sub_Z G H x y :
  loc_stable 6%num (SM.Vi64 x) H -> loc_stable 7%num (SM.Vi64 y) H ->
  loc_stable 8%num (SM.Vi64 (x - y)) H ->
  loc_present 6%num H -> loc_present 7%num H -> loc_present 8%num H ->
  word x -> word y -> word (x - y) ->
  sem_triple G (AS_base [:: T_const (SM.Vi64 x); T_const (SM.Vi64 y)] H)
    (crt_general_checked_sub_code 6%num 7%num 8%num) (AS_base [:: T_const (SM.Vi64 (x - y))] H).
Proof.
  move=> SA SB SR PA PB PR Wx Wy Wxy.
  have E := crt_i64_sub_repr Wx Wy.
  have Range : Wasm_int.Int64.min_signed <=
    Wasm_int.Int64.signed (Wasm_int.Int64.repr x) -
    Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy)
      i64_min_signed_val i64_max_signed_val. exact Wxy. }
  have SR' : loc_stable 8%num (VAL_int64
    (Wasm_int.Int64.sub (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y))) H.
  { rewrite E. exact SR. }
  have P := crt_general_checked_sub_sem (ia := 6%num) (ib := 7%num) (ir := 8%num) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) SA SB SR' PA PB PR Range.
  rewrite E in P. exact: P.
Qed.

Ltac unfold_period := rewrite /PQ /PG /PEntry /ppin.
Lemma p_diff_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (PG a m b n)) p_diff
 (AS_base [::T_const (SM.Vi64 (b-a))] (PG a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have Wa : word a by unfold word,MAX,i64_min,i64_max in *; lia.
 have Wb : word b by unfold word,MAX,i64_min,i64_max in *; lia.
 have Wd := solver_delta_word Hd.
 rewrite /p_diff.
 apply: (sem_seq (es1:=[::BI_local_get 2%num]) (Q:=AS_base [::T_const (SM.Vi64 b)] (PG a m b n))).
 { apply: get_pinned_frame. unfold_period. pinned_tac. }
 apply: (sem_seq (es1:=[::BI_local_get 0%num]) (Q:=AS_base [::T_const (SM.Vi64 b);T_const (SM.Vi64 a)] (PG a m b n))).
 { apply: get_pinned_frame. unfold_period. pinned_tac. }
 apply: period_checked_sub_Z; try assumption; unfold_period; first [stable_tac | present_tac].
Qed.
Lemma p_compat_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (PG a m b n)) p_compat
 (AS_base [::T_const (VAL_int32 (wasm_bool (negb (Z.rem (b-a) (Z.gcd m n) =? 0))))] (PG a m b n)).
Proof.
 move=> Hd. have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
 have Wd := solver_delta_word Hd. have Wr := crt_rem_word Wd Hg.
 have Wzero : word 0 by unfold word,i64_min,i64_max; lia.
 rewrite /p_compat.
 apply: (sem_seq (Q:=AS_base [::T_const (SM.Vi64 (b-a))] (PG a m b n))); first exact: p_diff_sem.
 apply: (sem_seq (es1:=[::BI_local_get 4%num]) (Q:=AS_base [::T_const (SM.Vi64 (b-a));T_const (SM.Vi64 (Z.gcd m n))] (PG a m b n))).
 { apply: get_pinned_frame. unfold_period. pinned_tac. }
 apply: (sem_seq (es1:=[::BI_binop T_i64 (Binop_i (BOI_rem SX_S))]) (Q:=AS_base [::T_const (SM.Vi64 (Z.rem (b-a) (Z.gcd m n)))] (PG a m b n))).
 { apply: binop_consts; try reflexivity. exact: crt_i64_rem_exact. }
 apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 0)]) (Q:=AS_base [::T_const (SM.Vi64 (Z.rem (b-a) (Z.gcd m n)));T_const (SM.Vi64 0)] (PG a m b n))); first exact: sem_const_framed.
 rewrite -(crt_public_ne Wr Wzero). apply: relop_consts; reflexivity.
Qed.
Lemma p_quot_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (PG a m b n)) p_quot (AS_base [::] (PQ a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
 rewrite /p_quot.
 apply: (sem_seq (es1 := [:: BI_local_get 1%num])
  (Q := AS_base [:: T_const (SM.Vi64 m)] (PG a m b n))).
 { apply: get_pinned_frame. unfold_period. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 4%num])
  (Q := AS_base [:: T_const (SM.Vi64 m); T_const (SM.Vi64 (Z.gcd m n))] (PG a m b n))).
 { apply: get_pinned_frame. unfold_period. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))])
  (Q := AS_base [:: T_const (SM.Vi64 (m / Z.gcd m n))] (PG a m b n))).
 { apply: binop_consts; [by vm_compute | by [] | by [] | apply: crt_i64_div_positive_exact; lia]. }
 apply: sem_local_set_const_frame; unfold_period; [stable_tac|present_tac].
Qed.
Lemma p_overflow_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (PQ a m b n)) p_overflow
 (AS_base [::T_const (VAL_int32 (wasm_bool (MAX/n <? m/Z.gcd m n)))] (PQ a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] _] := Hd.
 have [_ [Hmq [Wmq _]]] := crt_period_intermediate_bounds (proj1 Hd).
 have Wmax : word MAX by unfold word,MAX,i64_min,i64_max; lia.
 have Hquot : 0 <= MAX/n <= MAX.
 { split; [apply Z.div_pos; unfold MAX,i64_max in *; lia|apply Z.div_le_upper_bound; unfold MAX,i64_max in *; nia]. }
 have Wquot := nonnegative_word (MAX/n) Hquot.
 rewrite /p_overflow.
 apply: (sem_seq (es1:=[::BI_local_get 5%num])
 (Q:=AS_base [::T_const (SM.Vi64 (m/Z.gcd m n))] (PQ a m b n))).
 - apply: get_pinned_frame. unfold_period. pinned_tac.
 - apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 MAX)])
   (Q:=AS_base [::T_const (SM.Vi64 (m/Z.gcd m n));T_const (SM.Vi64 MAX)] (PQ a m b n))); first exact: sem_const_framed.
   apply: (sem_seq (es1:=[::BI_local_get 3%num])
   (Q:=AS_base [::T_const (SM.Vi64 (m/Z.gcd m n));T_const (SM.Vi64 MAX);T_const (SM.Vi64 n)] (PQ a m b n))).
   + apply: get_pinned_frame. unfold_period. pinned_tac.
   + apply: (sem_seq (es1:=[::BI_binop T_i64 (Binop_i (BOI_div SX_S))])
     (Q:=AS_base [::T_const (SM.Vi64 (m/Z.gcd m n));T_const (SM.Vi64 (MAX/n))] (PQ a m b n))).
     * apply: (sem_frame_consts (vf:=[::SM.Vi64 (m/Z.gcd m n)])).
       apply: binop_consts; try reflexivity. apply: crt_i64_div_positive_exact; [unfold MAX,i64_max; lia|exact Hn].
     * rewrite -(crt_public_gt Wmq Wquot). apply: relop_consts; reflexivity.
Qed.

Lemma p_product_sem a m b n : domain a m b n -> m/Z.gcd m n <= MAX/n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (PQ a m b n)) p_product
 (AS_base [::T_const (SM.Vi64 ((m/Z.gcd m n)*n))] (PQ a m b n)).
Proof.
 move=> Hd Hsafe. have [[Hm Hn] _] := Hd.
 have [_ [Hmq [Wmq Wn]]] := crt_period_intermediate_bounds (proj1 Hd).
 have Hbound : 0 <= (m/Z.gcd m n)*n <= MAX.
 { have Hdiv := Z.mul_div_le MAX n ltac:(lia). nia. }
 have Wprod := nonnegative_word _ Hbound.
 rewrite /p_product.
 apply: (sem_seq (es1:=[::BI_local_get 5%num]) (Q:=AS_base [::T_const (SM.Vi64 (m/Z.gcd m n))] (PQ a m b n))).
 { apply: get_pinned_frame. unfold_period. pinned_tac. }
 apply: (sem_seq (es1:=[::BI_local_get 3%num]) (Q:=AS_base [::T_const (SM.Vi64 (m/Z.gcd m n));T_const (SM.Vi64 n)] (PQ a m b n))).
 { apply: get_pinned_frame. unfold_period. pinned_tac. }
 apply: period_checked_mul_Z; try assumption; unfold_period; first [stable_tac | present_tac].
Qed.
Lemma p_const_return G H z tail Qn Qb :
 sem_mx G (AS_base [::] H) (BI_const_num (SM.Vi64 z)::BI_return::tail)
 Qn (AS_base [::T_const (SM.Vi64 z)] HA_true) Qb.
Proof.
 apply: (sem_mx_seq (es1:=[::BI_const_num (SM.Vi64 z)]) (Q1:=AS_base [::T_const (SM.Vi64 z)] HA_true)).
 - apply: sem_mx_lift. apply: (sem_conseq (P':=AS_base [::] HA_true) (Q':=AS_base [::T_const (SM.Vi64 z)] HA_true)).
   + move=> V [vs h] /= [Hs _]. by split.
   + by [].
   + exact: sem_const_framed.
 - exact: sem_mx_return_suffix.
Qed.
Lemma p_stack_return G H z tail Qn Qb :
 sem_mx G (AS_base [::T_const (SM.Vi64 z)] H) (BI_return::tail)
 Qn (AS_base [::T_const (SM.Vi64 z)] HA_true) Qb.
Proof.
 apply: (sem_mx_conseq (P':=AS_base [::T_const (SM.Vi64 z)] HA_true)
 (Qn':=Qn) (Qr':=AS_base [::T_const (SM.Vi64 z)] HA_true) (Qb':=Qb)); try by [].
 - move=> V [vs h] /= [Hs _]. by split.
 - exact: sem_mx_return_suffix.
Qed.
Lemma p_tail_sem a m b n Qn Qb : domain a m b n ->
 sem_mx (triv_ctx SM.main) (AS_base [::] (PG a m b n)) p_tail Qn
 (AS_base [::T_const (SM.Vi64 (if negb (Z.rem (b-a) (Z.gcd m n) =? 0) then -1
 else if MAX/n <? m/Z.gcd m n then -3 else (m/Z.gcd m n)*n))] HA_true) Qb.
Proof.
 move=> Hd. rewrite /p_tail.
 apply: (sem_mx_seq (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool (negb (Z.rem (b-a) (Z.gcd m n) =? 0))))] (PG a m b n))).
 { apply: sem_mx_lift. exact: p_compat_sem. }
 case Ec: (negb (Z.rem (b-a) (Z.gcd m n) =? 0)).
 - apply: (sem_mx_seq (Q1:=AS_base [::] HA_false)).
   + apply: crt_if_true_returns. exact: p_const_return.
   + apply: sem_mx_lift. exact: sem_false.
 - apply: (sem_mx_seq (Q1:=AS_base [::] (PG a m b n))).
   + apply: sem_mx_lift. apply: guard_if_false. exact: sem_nil_same.
   + apply: (sem_mx_seq (Q1:=AS_base [::] (PQ a m b n))).
     * apply: sem_mx_lift. exact: p_quot_sem.
     * apply: (sem_mx_seq (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool (MAX/n <? m/Z.gcd m n)))] (PQ a m b n))).
       -- apply: sem_mx_lift. exact: p_overflow_sem.
       -- case Eo: (MAX/n <? m/Z.gcd m n).
          ++ apply: (sem_mx_seq (Q1:=AS_base [::] HA_false)).
             ** apply: crt_if_true_returns. exact: p_const_return.
             ** apply: sem_mx_lift. exact: sem_false.
          ++ apply: (sem_mx_seq (Q1:=AS_base [::] (PQ a m b n))).
             ** apply: sem_mx_lift. apply: guard_if_false. exact: sem_nil_same.
             ** apply: (sem_mx_seq (Q1:=AS_base [::T_const (SM.Vi64 ((m/Z.gcd m n)*n))] (PQ a m b n))).
                --- apply: sem_mx_lift. apply: p_product_sem; first exact Hd. exact: (proj1 (Z.ltb_ge _ _) Eo).
                --- exact: p_stack_return.
Qed.
Lemma p_valid_prefix a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (PEntry a m b n))
 (merge_validation ++ [::BI_if (BT_valtype None) (p_reject (-2)) [::]])
 (AS_base [::] (PEntry a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have Wa : word a by unfold word,MAX,i64_min,i64_max in *; lia.
 have Wb : word b by unfold word,MAX,i64_min,i64_max in *; lia.
 have Wm := crt_modulus_word Hm. have Wn := crt_modulus_word Hn.
 have Hbfalse := proj2 (merge_bad_false_domain Wa Wm Wb Wn) Hd.
 apply: (sem_seq (Q:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (PEntry a m b n))).
 - rewrite -Hbfalse. apply: merge_validation_sem; try assumption; unfold_period; pinned_tac.
 - apply: guard_if_false. exact: sem_nil_same.
Qed.
Lemma p_gcd_sem a m b n : domain a m b n ->
 system_triple mem (AS_base [::] (PEntry a m b n)) p_gcd (AS_base [::] (PG a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] _] := Hd. rewrite /p_gcd.
 apply: (system_triple_seq (es1:=[::BI_local_get 1%num;BI_local_get 3%num])
 (Q1:=AS_base [::T_const (SM.Vi64 m);T_const (SM.Vi64 n)] (PEntry a m b n))); first reflexivity.
 - apply: system_triple_of_pure.
   apply: (sem_seq (es1:=[::BI_local_get 1%num]) (Q:=AS_base [::T_const (SM.Vi64 m)] (PEntry a m b n)));
   apply: get_pinned_frame; unfold_period; pinned_tac.
 - apply: (system_triple_seq (es1:=[::BI_call 0%num]) (Q1:=AS_base [::T_const (SM.Vi64 (Z.gcd m n))] (PEntry a m b n))); first reflexivity.
   + move=> f Hi. exact: crt_gcd_call.
   + apply: system_triple_of_pure. apply: sem_local_set_const_frame; unfold_period; [stable_tac|present_tac].
Qed.
Lemma p_body_sem a m b n Qn Qb : word a -> word m -> word b -> word n ->
 system_mx mem (AS_base [::] (PEntry a m b n)) (modfunc_body SM.crt_merge_period) Qn
 (AS_base [::T_const (SM.Vi64 (period_model_Z a m b n))] HA_true) Qb.
Proof.
 move=> Wa Wm Wb Wn. rewrite p_body_shape /period_model_Z.
 case Eb: (merge_bad a m b n).
 - apply: inverse_runtime_mx_of_mx.
   apply: (sem_mx_seq (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (PEntry a m b n))).
   + apply: sem_mx_lift. rewrite -Eb. apply: merge_validation_sem; try assumption; unfold_period; pinned_tac.
   + apply: (sem_mx_seq (Q1:=AS_base [::] HA_false)).
     * apply: crt_if_true_returns. exact: p_const_return.
     * apply: sem_mx_lift. exact: sem_false.
 - have Hd := proj1 (merge_bad_false_domain Wa Wm Wb Wn) Eb.
   apply: (inverse_runtime_mx_after_triple (es1:=merge_validation ++ [::BI_if (BT_valtype None) (p_reject (-2)) [::]]) (es2:=p_gcd ++ p_tail) (Q1:=AS_base [::] (PEntry a m b n))); first reflexivity.
   + apply: inverse_runtime_triple_of_triple. exact: p_valid_prefix.
   + apply: (inverse_runtime_mx_after_triple (Q1:=AS_base [::] (PG a m b n))); first reflexivity.
     * exact: p_gcd_sem.
     * apply: inverse_runtime_mx_of_mx. exact: p_tail_sem.
Qed.
Lemma p_entry_entails a m b n :
 aentails (AS_base [::] (HA_and (args_pinned [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n] 0%num)
 (func_pre_h SM.main SM.crt_merge_period))) (AS_base [::] (PEntry a m b n)).
Proof.
 move=> V [vs h] /= [Hs [[P0 [P1 [P2 [P3 _]]]] [[T0 [T1 [T2 [T3 _]]]] [T4 [T5 [T6 [T7 [T8 _]]]]]]]].
 split; first exact Hs.
 split; first exact P0. split; first exact P1. split; first exact P2. split; first exact P3.
 split; first by case: T4 => [w [Ew _]]; exists w.
 split; first by case: T5 => [w [Ew _]]; exists w.
 split; first by case: T6 => [w [Ew _]]; exists w.
 split; first by case: T7 => [w [Ew _]]; exists w.
 by case: T8 => [w [Ew _]]; exists w.
Qed.
Lemma p_body_to_computation a m b n r :
 system_mx mem (AS_base [::] (PEntry a m b n)) (modfunc_body SM.crt_merge_period)
 (AS_base [::T_const (SM.Vi64 r)] HA_true) (AS_base [::T_const (SM.Vi64 r)] HA_true)
 (AS_base [::T_const (SM.Vi64 r)] HA_true) ->
 system_computes mem 6%nat [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n] [::SM.Vi64 r].
Proof.
 move=> Hbody.
 change (args_typed [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n] [::T_num T_i64;T_num T_i64;T_num T_i64;T_num T_i64] /\
 results_typed [::SM.Vi64 r] [::T_num T_i64] /\
 exists defaults, default_vals (modfunc_locals SM.crt_merge_period) = Some defaults /\
 sem_mx_at (system_store mem) (activation_frame system_initial_runtime [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n] defaults)
 (AS_base [::] (HA_and (args_pinned [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n] 0%num) (func_pre_h SM.main SM.crt_merge_period)))
 (modfunc_body SM.crt_merge_period) (AS_base [::T_const (SM.Vi64 r)] HA_true)
 (AS_base [::T_const (SM.Vi64 r)] HA_true) (AS_base [::T_const (SM.Vi64 r)] HA_true)).
 split; first by repeat split. split; first by repeat split.
 exists [::VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0)].
 split; first reflexivity.
 move=> hs V vs h HP Hr. apply: Hbody; [reflexivity| |exact Hr]. exact: (p_entry_entails HP).
Qed.
Lemma period_model_Z_eq a m b n : word a -> word m -> word b -> word n ->
 period_model_Z a m b n = FiniteSystem.period_value (FiniteSystem.merge a m b n).
Proof.
 move=> Wa Wm Wb Wn. rewrite /period_model_Z /FiniteSystem.merge (merge_bad_model Wa Wm Wb Wn).
 case Hv: (FiniteSystem.validb (a,m) && FiniteSystem.validb (b,n)); last reflexivity.
 have Hb : merge_bad a m b n = false by rewrite (merge_bad_model Wa Wm Wb Wn) Hv.
 have Hd := proj1 (merge_bad_false_domain Wa Wm Wb Wn) Hb.
 have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
 rewrite (gcd_model_proved _ _ (proj1 Hd)).
 have Er : (Z.rem (b-a) (Z.gcd m n) =? 0) = ((b-a) mod (Z.gcd m n) =? 0).
 { apply Bool.eq_true_iff_eq. rewrite !Z.eqb_eq. exact: (Z.rem_mod_eq_0 (b-a) (Z.gcd m n) ltac:(lia)). }
 rewrite Er. case: ((b-a) mod (Z.gcd m n) =? 0); last reflexivity.
 case: (MAX/n <? m/Z.gcd m n); reflexivity.
Qed.
Theorem merge_period_machine_computes a m b n : word a -> word m -> word b -> word n ->
 system_computes mem 6%nat [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n]
 [::SM.Vi64 (FiniteSystem.period_value (FiniteSystem.merge a m b n))].
Proof.
 move=> Wa Wm Wb Wn. rewrite -(period_model_Z_eq Wa Wm Wb Wn).
 apply: p_body_to_computation. exact: p_body_sem.
Qed.

Lemma crt_merge_period_entry a m b n :
 crt_entry_admissible mem SM.crt_merge_period [::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n].
Proof.
 move=> defaults Hd. vm_compute in Hd. inversion Hd; subst defaults.
 cbn [crt_entry_valuation activation_frame system_initial_runtime func_pre_h SM.main
 SM.crt_merge_period args_pinned locals_typed assertion_denote hassert_denote stack_denote
 term_eq term_denote loc_read lookup_N val_loc f_locs modfunc_type modfunc_locals mod_types runtime_inst SM.Vi64].
 repeat split; try reflexivity; try (eexists; split; reflexivity).
Qed.
Lemma crt_merge_period_call frame H a m b n :
 f_inst frame = system_inst -> word a -> word m -> word b -> word n ->
 sem_triple_at (system_store mem) frame
 (AS_base [::T_const (SM.Vi64 a);T_const (SM.Vi64 m);T_const (SM.Vi64 b);T_const (SM.Vi64 n)] H)
 [::BI_call 6%num]
 (AS_base [::T_const (SM.Vi64 (FiniteSystem.period_value (FiniteSystem.merge a m b n)))] H).
Proof.
 move=> Hi Wa Wm Wb Wn.
 apply: (crt_call_from_computes_at (i:=6%nat) (addr:=6%num) (fdef:=SM.crt_merge_period)
 (args:=[::SM.Vi64 a;SM.Vi64 m;SM.Vi64 b;SM.Vi64 n])
 (rs:=[::SM.Vi64 (FiniteSystem.period_value (FiniteSystem.merge a m b n))])
 (params:=[::T_num T_i64;T_num T_i64;T_num T_i64;T_num T_i64]) (results:=[::T_num T_i64])); try reflexivity.
 - by rewrite Hi.
 - exact: crt_merge_period_entry.
 - exact: merge_period_machine_computes.
Qed.
End Host.
Print Assumptions merge_period_machine_computes.
