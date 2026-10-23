(* Execution refinement for the exact generated CRT solver. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit
 NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTMath CRTLoops.
From CRTGenerated Require Import main.
From CRTWasm Require Import CRTAPIModel CRTContracts CRTExecution CRTModule CRTCalls
 CRTPublicExecution CRTGeneralArithmetic CRTInverseExecution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Section Host.
Context `{ho : host}.
Ltac pinned_tac := solve [exact: pinned_bare | apply: pinned_left; pinned_tac | apply: pinned_right; pinned_tac].
Ltac present_tac := solve [exact: loc_present_defined | exact: loc_present_pin | apply: loc_present_left; present_tac | apply: loc_present_right; present_tac].
Lemma solver_stable_true i c : loc_stable i c HA_true.
Proof. by []. Qed.
Ltac stable_tac := solve [exact: solver_stable_true | exact: loc_stable_defined_self | exact: loc_stable_pin_self | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other | apply: loc_stable_and; stable_tac].
Lemma solver_checked_mul_Z G H x y :
  loc_stable 11%num (main.Vi64 x) H -> loc_stable 12%num (main.Vi64 y) H ->
  loc_stable 13%num (main.Vi64 (x * y)) H ->
  loc_present 11%num H -> loc_present 12%num H -> loc_present 13%num H ->
  word x -> word y -> word (x * y) ->
  sem_triple G (AS_base [:: T_const (main.Vi64 x); T_const (main.Vi64 y)] H)
    (crt_general_checked_mul_code 11%num 12%num 13%num) (AS_base [:: T_const (main.Vi64 (x * y))] H).
Proof.
  move=> SA SB SR PA PB PR Wx Wy Wxy.
  have E := crt_i64_mul_repr Wx Wy.
  have Range : Wasm_int.Int64.min_signed <=
    Wasm_int.Int64.signed (Wasm_int.Int64.repr x) *
    Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy)
      i64_min_signed_val i64_max_signed_val. exact Wxy. }
  have SR' : loc_stable 13%num (VAL_int64
    (Wasm_int.Int64.mul (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y))) H.
  { rewrite E. exact SR. }
  have P := crt_general_checked_mul_sem (ia := 11%num) (ib := 12%num) (ir := 13%num) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) SA SB SR' PA PB PR Range.
  rewrite E in P. exact: P.
Qed.
Lemma solver_checked_sub_Z G H x y :
  loc_stable 11%num (main.Vi64 x) H -> loc_stable 12%num (main.Vi64 y) H ->
  loc_stable 13%num (main.Vi64 (x - y)) H ->
  loc_present 11%num H -> loc_present 12%num H -> loc_present 13%num H ->
  word x -> word y -> word (x - y) ->
  sem_triple G (AS_base [:: T_const (main.Vi64 x); T_const (main.Vi64 y)] H)
    (crt_general_checked_sub_code 11%num 12%num 13%num) (AS_base [:: T_const (main.Vi64 (x - y))] H).
Proof.
  move=> SA SB SR PA PB PR Wx Wy Wxy.
  have E := crt_i64_sub_repr Wx Wy.
  have Range : Wasm_int.Int64.min_signed <=
    Wasm_int.Int64.signed (Wasm_int.Int64.repr x) -
    Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy)
      i64_min_signed_val i64_max_signed_val. exact Wxy. }
  have SR' : loc_stable 13%num (VAL_int64
    (Wasm_int.Int64.sub (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y))) H.
  { rewrite E. exact SR. }
  have P := crt_general_checked_sub_sem (ia := 11%num) (ib := 12%num) (ir := 13%num) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) SA SB SR' PA PB PR Range.
  rewrite E in P. exact: P.
Qed.

Lemma solver_checked_add_Z G H x y :
  loc_stable 11%num (main.Vi64 x) H -> loc_stable 12%num (main.Vi64 y) H ->
  loc_stable 13%num (main.Vi64 (x + y)) H ->
  loc_present 11%num H -> loc_present 12%num H -> loc_present 13%num H ->
  word x -> word y -> word (x + y) ->
  sem_triple G (AS_base [:: T_const (main.Vi64 x); T_const (main.Vi64 y)] H)
    (crt_general_checked_add_code 11%num 12%num 13%num) (AS_base [:: T_const (main.Vi64 (x + y))] H).
Proof.
  move=> SA SB SR PA PB PR Wx Wy Wxy.
  have E := crt_i64_add_repr Wx Wy.
  have Range : Wasm_int.Int64.min_signed <=
    Wasm_int.Int64.signed (Wasm_int.Int64.repr x) +
    Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy)
      i64_min_signed_val i64_max_signed_val. exact Wxy. }
  have SR' : loc_stable 13%num (VAL_int64
    (Wasm_int.Int64.add (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y))) H.
  { rewrite E. exact SR. }
  have P := crt_general_checked_add_sem (ia := 11%num) (ib := 12%num) (ir := 13%num) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) SA SB SR' PA PB PR Range.
  rewrite E in P. exact: P.
Qed.

Definition SolveEntry a m b n :=
 (HA_and (term_eq (T_local 0%num) (T_const (main.Vi64 a)))
 (HA_and (term_eq (T_local 1%num) (T_const (main.Vi64 m)))
 (HA_and (term_eq (T_local 2%num) (T_const (main.Vi64 b)))
 (HA_and (term_eq (T_local 3%num) (T_const (main.Vi64 n)))
 (HA_and (HA_defined (T_local 4%num))
 (HA_and (HA_defined (T_local 5%num))
 (HA_and (HA_defined (T_local 6%num))
 (HA_and (HA_defined (T_local 7%num))
 (HA_and (HA_defined (T_local 8%num))
 (HA_and (HA_defined (T_local 9%num))
 (HA_and (HA_defined (T_local 10%num))
 (HA_and (HA_defined (T_local 11%num))
 (HA_and (HA_defined (T_local 12%num))
 (HA_and (HA_defined (T_local 13%num))
 HA_true)))))))))))))).
Definition SolveG a m b n :=
 HA_and (term_eq (T_local 4%num) (T_const (main.Vi64 (Z.gcd m n)))) (SolveEntry a m b n).
Definition SolveD a m b n :=
 HA_and (term_eq (T_local 5%num) (T_const (main.Vi64 (b - a)))) (SolveG a m b n).
Definition SolveM a m b n :=
 HA_and (term_eq (T_local 6%num) (T_const (main.Vi64 (m / Z.gcd m n)))) (SolveD a m b n).
Definition SolveN a m b n :=
 HA_and (term_eq (T_local 7%num) (T_const (main.Vi64 (n / Z.gcd m n)))) (SolveM a m b n).
Definition SolveB a m b n :=
 HA_and (term_eq (T_local 8%num) (T_const (main.Vi64 ((m / Z.gcd m n) mod (n / Z.gcd m n))))) (SolveN a m b n).
Definition SolveU a m b n u :=
 HA_and (term_eq (T_local 9%num) (T_const (main.Vi64 (u)))) (SolveB a m b n).
Definition SolveT a m b n u t :=
 HA_and (term_eq (T_local 10%num) (T_const (main.Vi64 (t)))) (SolveU a m b n u).
Ltac unfold_solve := rewrite /SolveT /SolveU /SolveB /SolveN /SolveM /SolveD /SolveG /SolveEntry.

Definition solver_mul_code := crt_general_checked_mul_code 11%num 12%num 13%num.
Definition solver_sub_code := crt_general_checked_sub_code 11%num 12%num 13%num.
Definition solver_add_code := crt_general_checked_add_code 11%num 12%num 13%num.
Definition solver_moduli_validation := List.firstn 6 (modfunc_body main.crt_solve).
Definition solver_residue_validation := List.firstn 6 (List.skipn 7 (modfunc_body main.crt_solve)).
Definition solver_delta_code :=
 [:: BI_local_get 2%num; BI_local_get 0%num] ++ solver_sub_code ++ [:: BI_local_set 5%num].
Definition solver_compatibility_test :=
 [:: BI_local_get 5%num; BI_local_get 4%num; BI_binop T_i64 (Binop_i (BOI_rem SX_S));
 BI_const_num (main.Vi64 0); BI_relop T_i64 (Relop_i ROI_ne)].
Definition solver_reductions_code :=
 [:: BI_local_get 1%num; BI_local_get 4%num; BI_binop T_i64 (Binop_i (BOI_div SX_S)); BI_local_set 6%num;
 BI_local_get 3%num; BI_local_get 4%num; BI_binop T_i64 (Binop_i (BOI_div SX_S)); BI_local_set 7%num].
Definition solver_B_code :=
 [:: BI_local_get 6%num; BI_local_get 7%num; BI_binop T_i64 (Binop_i (BOI_rem SX_S)); BI_local_set 8%num].
Definition solver_product_code :=
 [:: BI_local_get 5%num; BI_local_get 4%num; BI_binop T_i64 (Binop_i (BOI_div SX_S)); BI_local_get 9%num] ++ solver_mul_code.
Definition solver_result_code :=
 [:: BI_local_get 0%num; BI_local_get 1%num; BI_local_get 10%num] ++ solver_mul_code ++ solver_add_code.
Definition solver_after_compatibility :=
 solver_reductions_code ++
 [:: BI_local_get 7%num; BI_const_num (main.Vi64 1); BI_relop T_i64 (Relop_i ROI_eq);
 BI_if (BT_valtype None) [:: BI_local_get 0%num; BI_return] [::]] ++
 solver_B_code ++ [:: BI_local_get 8%num; BI_local_get 7%num; BI_call 2%num; BI_local_set 9%num] ++
 solver_product_code ++ [:: BI_local_get 7%num; BI_call 1%num; BI_local_set 10%num] ++
 solver_result_code ++ [:: BI_return; BI_unreachable].
Definition solver_after_gcd := solver_delta_code ++ solver_compatibility_test ++
 [:: BI_if (BT_valtype None) [:: BI_const_num (main.Vi64 (-1)); BI_return] [::]] ++ solver_after_compatibility.
Definition solver_after_validation :=
 [:: BI_local_get 1%num; BI_local_get 3%num; BI_call 0%num; BI_local_set 4%num] ++ solver_after_gcd.
Lemma solver_body_shape : modfunc_body main.crt_solve =
 solver_moduli_validation ++ [:: BI_if (BT_valtype None) period_reject [::]] ++
 solver_residue_validation ++ [:: BI_if (BT_valtype None) period_reject [::]] ++ solver_after_validation.
Proof. by []. Qed.

Lemma solver_moduli_validation_sem a m b n : word m -> word n ->
  sem_triple (triv_ctx main.main) (AS_base [::] (SolveEntry a m b n))
    solver_moduli_validation
    (AS_base [:: T_const (VAL_int32 (wasm_bool (period_bad m n)))] (SolveEntry a m b n)).
Proof.
  move=> Hm Hn.
  have Hone : word 1 by unfold word, i64_min, i64_max; lia.
  have HM : word M by unfold word, i64_min, i64_max, M; lia.
  rewrite /solver_moduli_validation /main.crt_solve /period_bad /=.
  apply: (sem_seq
    (es1 := [:: BI_local_get 1%num; BI_const_num (main.Vi64 1);
      BI_relop T_i64 (Relop_i (ROI_lt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (m <? 1)))] (SolveEntry a m b n))).
  { rewrite -(crt_public_lt Hm Hone). apply: test_pin_const;
      [rewrite /SolveEntry; pinned_tac | by [] | by [] | by []]. }
  apply: (sem_seq
    (es1 := [:: BI_if (BT_valtype (Some (T_num T_i32))) [:: BI_const_num (main.Vi32 1)]
      [:: BI_local_get 1%num; BI_const_num (main.Vi64 M); BI_relop T_i64 (Relop_i (ROI_gt SX_S))]])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool ((m <? 1) || (M <? m))))] (SolveEntry a m b n))).
  { apply: crt_or_sem. rewrite -(crt_public_gt Hm HM). apply: test_pin_const;
      [rewrite /SolveEntry; pinned_tac | by [] | by [] | by []]. }
  apply: (sem_seq
    (es1 := [:: BI_if (BT_valtype (Some (T_num T_i32))) [:: BI_const_num (main.Vi32 1)]
      [:: BI_local_get 3%num; BI_const_num (main.Vi64 1); BI_relop T_i64 (Relop_i (ROI_lt SX_S))]])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool ((m <? 1) || (M <? m) || (n <? 1))))] (SolveEntry a m b n))).
  { apply: crt_or_sem. rewrite -(crt_public_lt Hn Hone). apply: test_pin_const;
      [rewrite /SolveEntry; pinned_tac | by [] | by [] | by []]. }
  apply: crt_or_sem. rewrite -(crt_public_gt Hn HM). apply: test_pin_const;
    [rewrite /SolveEntry; pinned_tac | by [] | by [] | by []].
Qed.


Lemma solver_delta_word a m b n : domain a m b n -> word (b - a).
Proof. move=> [[Hm Hn] [Ha Hb]]. unfold word, M, i64_min, i64_max in *; lia. Qed.

Lemma solver_delta_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx main.main) (AS_base [::] (SolveG a m b n)) solver_delta_code
  (AS_base [::] (SolveD a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have Wa : word a by unfold word, M, i64_min, i64_max in *; lia.
 have Wb : word b by unfold word, M, i64_min, i64_max in *; lia.
 have Wd := solver_delta_word Hd.
 rewrite /solver_delta_code.
 apply: (sem_seq (es1 := [:: BI_local_get 2%num])
  (Q := AS_base [:: T_const (main.Vi64 b)] (SolveG a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 0%num])
  (Q := AS_base [:: T_const (main.Vi64 b); T_const (main.Vi64 a)] (SolveG a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := solver_sub_code)
  (Q := AS_base [:: T_const (main.Vi64 (b-a))] (SolveG a m b n))).
 { apply: solver_checked_sub_Z; try assumption; unfold_solve; first [stable_tac | present_tac]. }
 apply: sem_local_set_const_frame; unfold_solve; [stable_tac | present_tac].
Qed.

Lemma solver_compatibility_test_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx main.main) (AS_base [::] (SolveD a m b n)) solver_compatibility_test
  (AS_base [:: T_const (VAL_int32 (wasm_bool (negb (Z.rem (b-a) (Z.gcd m n) =? 0))))] (SolveD a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
 have Wd := solver_delta_word Hd.
 have Wr := crt_rem_word Wd Hg.
 have Wzero : word 0 by unfold word, i64_min, i64_max; lia.
 rewrite /solver_compatibility_test.
 apply: (sem_seq (es1 := [:: BI_local_get 5%num])
  (Q := AS_base [:: T_const (main.Vi64 (b-a))] (SolveD a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 4%num])
  (Q := AS_base [:: T_const (main.Vi64 (b-a)); T_const (main.Vi64 (Z.gcd m n))] (SolveD a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_rem SX_S))])
  (Q := AS_base [:: T_const (main.Vi64 (Z.rem (b-a) (Z.gcd m n)))] (SolveD a m b n))).
 { apply: binop_consts; [by vm_compute | by [] | by [] | exact: crt_i64_rem_exact]. }
 apply: (sem_seq (es1 := [:: BI_const_num (main.Vi64 0)])
  (Q := AS_base [:: T_const (main.Vi64 (Z.rem (b-a) (Z.gcd m n))); T_const (main.Vi64 0)] (SolveD a m b n))).
 { exact: sem_const_framed. }
 rewrite -(crt_public_ne Wr Wzero). apply: relop_consts; by [].
Qed.

Lemma solver_reductions_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx main.main) (AS_base [::] (SolveD a m b n)) solver_reductions_code
  (AS_base [::] (SolveN a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
 rewrite /solver_reductions_code.
 apply: (sem_seq (es1 := [:: BI_local_get 1%num])
  (Q := AS_base [:: T_const (main.Vi64 m)] (SolveD a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 4%num])
  (Q := AS_base [:: T_const (main.Vi64 m); T_const (main.Vi64 (Z.gcd m n))] (SolveD a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))])
  (Q := AS_base [:: T_const (main.Vi64 (m / Z.gcd m n))] (SolveD a m b n))).
 { apply: binop_consts; [by vm_compute | by [] | by [] | apply: crt_i64_div_positive_exact; lia]. }
 apply: (sem_seq (es1 := [:: BI_local_set 6%num])
  (Q := AS_base [::] (SolveM a m b n))).
 { apply: sem_local_set_const_frame; unfold_solve; [stable_tac | present_tac]. }
 apply: (sem_seq (es1 := [:: BI_local_get 3%num])
  (Q := AS_base [:: T_const (main.Vi64 n)] (SolveM a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 4%num])
  (Q := AS_base [:: T_const (main.Vi64 n); T_const (main.Vi64 (Z.gcd m n))] (SolveM a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))])
  (Q := AS_base [:: T_const (main.Vi64 (n / Z.gcd m n))] (SolveM a m b n))).
 { apply: binop_consts; [by vm_compute | by [] | by [] | apply: crt_i64_div_positive_exact; lia]. }
 apply: sem_local_set_const_frame; unfold_solve; [stable_tac | present_tac].
Qed.

Lemma solver_B_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx main.main) (AS_base [::] (SolveN a m b n)) solver_B_code
  (AS_base [::] (SolveB a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have [Hg [Hmq [Wmq _]]] := crt_period_intermediate_bounds (proj1 Hd).
 have Hsw : moduli n m by split.
 have [_ [Hnq _]] := crt_period_intermediate_bounds Hsw.
 rewrite Z.gcd_comm in Hnq.
 have Hr : Z.rem (m / Z.gcd m n) (n / Z.gcd m n) =
   (m / Z.gcd m n) mod (n / Z.gcd m n) by apply: Z.rem_mod_nonneg; lia.
 rewrite /solver_B_code.
 apply: (sem_seq (es1 := [:: BI_local_get 6%num])
  (Q := AS_base [:: T_const (main.Vi64 (m / Z.gcd m n))] (SolveN a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 7%num])
  (Q := AS_base [:: T_const (main.Vi64 (m / Z.gcd m n)); T_const (main.Vi64 (n / Z.gcd m n))] (SolveN a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_rem SX_S))])
  (Q := AS_base [:: T_const (main.Vi64 ((m / Z.gcd m n) mod (n / Z.gcd m n)))] (SolveN a m b n))).
 { apply: binop_consts; [by vm_compute | by [] | by [] |]. rewrite -Hr. exact: crt_i64_rem_exact. }
 apply: sem_local_set_const_frame; unfold_solve; [stable_tac | present_tac].
Qed.

Lemma solver_divisible_div d g : word d -> 1 <= g <= M -> (g | d) -> word (d/g) ->
 app_binop (Binop_i (BOI_div SX_S)) (main.Vi64 d) (main.Vi64 g) = Some (main.Vi64 (d/g)).
Proof.
 move=> Wd Hg Hdiv Wq. have Wg := crt_modulus_word Hg.
 have Heq := exact_division g d ltac:(lia) Hdiv.
 have Hq : (d ÷ g) = d / g.
 { rewrite [d in (d ÷ g)]Heq Z.mul_comm Z.quot_mul; lia. }
 have Hnz : Wasm_int.Int64.signed (Wasm_int.Int64.repr g) <> 0.
 { rewrite (crt_i64_signed_repr Wg). lia. }
 have Hov : (Wasm_int.Int64.signed (Wasm_int.Int64.repr d) ÷
    Wasm_int.Int64.signed (Wasm_int.Int64.repr g)) <> Wasm_int.Int64.half_modulus.
 { rewrite (crt_i64_signed_repr Wd) (crt_i64_signed_repr Wg) Hq i64_half_modulus_val.
   unfold word, i64_min, i64_max in Wq. lia. }
 by rewrite (i64_div_s_some Hnz Hov) (crt_i64_signed_repr Wd) (crt_i64_signed_repr Wg) Hq.
Qed.

Lemma solver_product_sem a m b n u : domain a m b n -> compatible a m b n ->
 0 <= u < n / Z.gcd m n ->
 sem_triple (triv_ctx main.main) (AS_base [::] (SolveU a m b n u)) solver_product_code
  (AS_base [:: T_const (main.Vi64 (((b-a)/Z.gcd m n)*u))] (SolveU a m b n u)).
Proof.
 move=> Hd Hcompat Hu.
 have [Hg [Hmq [Hnq [Hdelta [Hquot [_ [_ [_ Hbounds]]]]]]]] := crt_bounds_proved a m b n Hd Hcompat.
 have [_ [Wp _]] := Hbounds u Hu.
 have Wd := solver_delta_word Hd.
 have Wq : word ((b-a)/Z.gcd m n).
 { apply Z.abs_le in Hquot. unfold word, M, i64_min, i64_max in *; lia. }
 have Wu : word u by unfold word, M, i64_min, i64_max in *; lia.
 rewrite /solver_product_code.
 apply: (sem_seq (es1 := [:: BI_local_get 5%num])
  (Q := AS_base [:: T_const (main.Vi64 (b-a))] (SolveU a m b n u))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 4%num])
  (Q := AS_base [:: T_const (main.Vi64 (b-a)); T_const (main.Vi64 (Z.gcd m n))] (SolveU a m b n u))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))])
  (Q := AS_base [:: T_const (main.Vi64 ((b-a)/Z.gcd m n))] (SolveU a m b n u))).
 { apply: binop_consts; [by vm_compute | by [] | by [] | exact: solver_divisible_div]. }
 apply: (sem_seq (es1 := [:: BI_local_get 9%num])
  (Q := AS_base [:: T_const (main.Vi64 ((b-a)/Z.gcd m n)); T_const (main.Vi64 u)] (SolveU a m b n u))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: solver_checked_mul_Z; try assumption; unfold_solve; first [stable_tac | present_tac].
Qed.

Lemma solver_result_sem a m b n u : domain a m b n -> compatible a m b n ->
 0 <= u < n / Z.gcd m n ->
 let t := (((b-a)/Z.gcd m n)*u) mod (n/Z.gcd m n) in
 sem_triple (triv_ctx main.main) (AS_base [::] (SolveT a m b n u t)) solver_result_code
  (AS_base [:: T_const (main.Vi64 (a+m*t))] (SolveT a m b n u t)).
Proof.
 move=> Hd Hcompat Hu t.
 have [Hg [Hmq [Hnq [Hdelta [Hquot [_ [_ [_ Hbounds]]]]]]]] := crt_bounds_proved a m b n Hd Hcompat.
 have [_ [Wp [Ht [Hmt [Wmt [Hx Wx]]]]]] := Hbounds u Hu.
 have [[Hm Hn] [Ha Hb]] := Hd.
 have Wa : word a by unfold word, M, i64_min, i64_max in *; lia.
 have Wm := crt_modulus_word Hm.
 have Wt : word t by unfold t; unfold word, M, i64_min, i64_max in *; lia.
 rewrite /solver_result_code.
 apply: (sem_seq (es1 := [:: BI_local_get 0%num])
  (Q := AS_base [:: T_const (main.Vi64 a)] (SolveT a m b n u t))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 1%num])
  (Q := AS_base [:: T_const (main.Vi64 a); T_const (main.Vi64 m)] (SolveT a m b n u t))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 10%num])
  (Q := AS_base [:: T_const (main.Vi64 a); T_const (main.Vi64 m); T_const (main.Vi64 t)] (SolveT a m b n u t))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := solver_mul_code)
  (Q := AS_base [:: T_const (main.Vi64 a); T_const (main.Vi64 (m*t))] (SolveT a m b n u t))).
 { apply: (sem_frame_consts (vf := [:: main.Vi64 a])).
   apply: solver_checked_mul_Z; try assumption; unfold_solve; first [stable_tac | present_tac]. }
 apply: solver_checked_add_Z; try assumption; unfold_solve; first [stable_tac | present_tac].
Qed.

Lemma solver_two_pin_test G H i j x y op :
 pinned i (main.Vi64 x) H -> pinned j (main.Vi64 y) H -> relop_type_agree T_i64 op ->
 sem_triple G (AS_base [::] H) [:: BI_local_get i; BI_local_get j; BI_relop T_i64 op]
  (AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop op (main.Vi64 x) (main.Vi64 y))))] H).
Proof.
 move=> Pi Pj Hty.
 apply: (sem_seq (es1 := [:: BI_local_get i]) (Q := AS_base [:: T_const (main.Vi64 x)] H)).
 { apply: get_pinned_frame. exact Pi. }
 apply: (sem_seq (es1 := [:: BI_local_get j])
  (Q := AS_base [:: T_const (main.Vi64 x); T_const (main.Vi64 y)] H)).
 { apply: get_pinned_frame. exact Pj. }
 apply: relop_consts; by [].
Qed.

Lemma solver_public_ge x y : word x -> word y ->
 app_relop (Relop_i (ROI_ge SX_S)) (main.Vi64 x) (main.Vi64 y) = (y <=? x).
Proof.
 move=> Wx Wy. rewrite /main.Vi64 crt_contract_ge.
 by rewrite (crt_contract_signed_repr Wx) (crt_contract_signed_repr Wy).
Qed.

Definition solver_residue_bad a m b n := ((a <? 0) || (m <=? a) || (b <? 0) || (n <=? b)).

Lemma solver_residue_validation_sem a m b n : word a -> word m -> word b -> word n ->
 sem_triple (triv_ctx main.main) (AS_base [::] (SolveEntry a m b n)) solver_residue_validation
  (AS_base [:: T_const (VAL_int32 (wasm_bool (solver_residue_bad a m b n)))] (SolveEntry a m b n)).
Proof.
 move=> Wa Wm Wb Wn.
 have Wzero : word 0 by unfold word, i64_min, i64_max; lia.
 rewrite /solver_residue_validation /main.crt_solve /solver_residue_bad /=.
 apply: (sem_seq (es1 := [:: BI_local_get 0%num; BI_const_num (main.Vi64 0); BI_relop T_i64 (Relop_i (ROI_lt SX_S))])
  (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (a <? 0)))] (SolveEntry a m b n))).
 { rewrite -(crt_public_lt Wa Wzero). apply: test_pin_const; [unfold_solve; pinned_tac | by [] | by [] | by []]. }
 apply: (sem_seq
  (es1 := [:: BI_if (BT_valtype (Some (T_num T_i32))) [:: BI_const_num (main.Vi32 1)]
   [:: BI_local_get 0%num; BI_local_get 1%num; BI_relop T_i64 (Relop_i (ROI_ge SX_S))]])
  (Q := AS_base [:: T_const (VAL_int32 (wasm_bool ((a <? 0) || (m <=? a))))] (SolveEntry a m b n))).
 { apply: crt_or_sem. rewrite -(solver_public_ge Wa Wm). apply: solver_two_pin_test;
   [unfold_solve; pinned_tac | unfold_solve; pinned_tac | by []]. }
 apply: (sem_seq
  (es1 := [:: BI_if (BT_valtype (Some (T_num T_i32))) [:: BI_const_num (main.Vi32 1)]
   [:: BI_local_get 2%num; BI_const_num (main.Vi64 0); BI_relop T_i64 (Relop_i (ROI_lt SX_S))]])
  (Q := AS_base [:: T_const (VAL_int32 (wasm_bool ((a <? 0) || (m <=? a) || (b <? 0))))] (SolveEntry a m b n))).
 { apply: crt_or_sem. rewrite -(crt_public_lt Wb Wzero). apply: test_pin_const;
   [unfold_solve; pinned_tac | by [] | by [] | by []]. }
 apply: crt_or_sem. rewrite -(solver_public_ge Wb Wn). apply: solver_two_pin_test;
   [unfold_solve; pinned_tac | unfold_solve; pinned_tac | by []].
Qed.

Lemma solver_residue_bad_spec a m b n : solver_residue_bad a m b n =
 negb ((0 <=? a) && (a <? m) && (0 <=? b) && (b <? n)).
Proof.
 have Hlt : forall x y, (x <? y) = negb (y <=? x).
 { move=> x y. case E: (x <? y); case F: (y <=? x); try reflexivity;
   [apply Z.ltb_lt in E; apply Z.leb_le in F | apply Z.ltb_ge in E; apply Z.leb_gt in F]; lia. }
 rewrite /solver_residue_bad !Hlt.
 by case: (0 <=? a); case: (m <=? a); case: (0 <=? b); case: (n <=? b).
Qed.

Lemma solver_valid_prefix_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx main.main) (AS_base [::] (SolveEntry a m b n))
  (solver_moduli_validation ++ [:: BI_if (BT_valtype None) period_reject [::]] ++
   solver_residue_validation ++ [:: BI_if (BT_valtype None) period_reject [::]])
  (AS_base [::] (SolveEntry a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have Wa : word a by unfold word, M, i64_min, i64_max in *; lia.
 have Wb : word b by unfold word, M, i64_min, i64_max in *; lia.
 have Wm := crt_modulus_word Hm. have Wn := crt_modulus_word Hn.
 have Emods : period_bad m n = false by rewrite period_bad_spec (proj2 (crt_moduli_b_spec m n) (proj1 Hd)).
 have Eres : solver_residue_bad a m b n = false.
 { rewrite /solver_residue_bad.
   have -> : (a <? 0) = false by apply/Z.ltb_ge; lia.
   have -> : (m <=? a) = false by apply/Z.leb_gt; lia.
   have -> : (b <? 0) = false by apply/Z.ltb_ge; lia.
   have -> : (n <=? b) = false by apply/Z.leb_gt; lia. by []. }
 apply: (sem_seq (Q := AS_base [:: T_const (VAL_int32 (wasm_bool false))] (SolveEntry a m b n))).
 { rewrite -Emods. exact: solver_moduli_validation_sem. }
 apply: (sem_seq (es1 := [:: BI_if (BT_valtype None) period_reject [::]]) (Q := AS_base [::] (SolveEntry a m b n))).
 { apply: guard_if_false. exact: sem_nil_same. }
 apply: (sem_seq (Q := AS_base [:: T_const (VAL_int32 (wasm_bool false))] (SolveEntry a m b n))).
 { rewrite -Eres. exact: solver_residue_validation_sem. }
 apply: guard_if_false. exact: sem_nil_same.
Qed.

Lemma solver_reject_suffix G H z tail Qn Qb :
 sem_mx G (AS_base [:: T_const (VAL_int32 (wasm_bool true))] H)
  ([:: BI_if (BT_valtype None) [:: BI_const_num (main.Vi64 z); BI_return] [::]] ++ tail)
  Qn (AS_base [:: T_const (main.Vi64 z)] HA_true) Qb.
Proof.
 apply: (sem_mx_seq (Q1 := AS_base [::] HA_false)).
 - apply: crt_if_true_returns.
   apply: (sem_mx_seq (es1 := [:: BI_const_num (main.Vi64 z)])
     (Q1 := AS_base [:: T_const (main.Vi64 z)] HA_true)).
   + apply: sem_mx_lift. apply: (sem_conseq (P' := AS_base [::] HA_true)
       (Q' := AS_base [:: T_const (main.Vi64 z)] HA_true)).
     * move=> V [vs h] /= [Hs _]. by split.
     * by [].
     * exact: sem_const_framed.
   + exact: sem_mx_return_suffix.
 - apply: sem_mx_lift. exact: sem_false.
Qed.

Lemma solver_invalid_body_sem a m b n Qn Qb : word a -> word m -> word b -> word n ->
 crt_domain_b a m b n = false ->
 sem_mx (triv_ctx main.main) (AS_base [::] (SolveEntry a m b n)) (modfunc_body main.crt_solve)
  Qn (AS_base [:: T_const (main.Vi64 (-2))] HA_true) Qb.
Proof.
 move=> Wa Wm Wb Wn Hbad. rewrite solver_body_shape.
 case Hmods: (crt_moduli_b m n).
 - have Emods : period_bad m n = false by rewrite period_bad_spec Hmods.
   have Eres : solver_residue_bad a m b n = true.
   { rewrite solver_residue_bad_spec. rewrite /crt_domain_b Hmods /= in Hbad. by rewrite Hbad. }
   apply: (sem_mx_seq (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool false))] (SolveEntry a m b n))).
   { apply: sem_mx_lift. rewrite -Emods. exact: solver_moduli_validation_sem. }
   apply: (sem_mx_seq (es1 := [:: BI_if (BT_valtype None) period_reject [::]]) (Q1 := AS_base [::] (SolveEntry a m b n))).
   { apply: sem_mx_lift. apply: guard_if_false. exact: sem_nil_same. }
   apply: (sem_mx_seq (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool true))] (SolveEntry a m b n))).
   { apply: sem_mx_lift. rewrite -Eres. exact: solver_residue_validation_sem. }
   exact: solver_reject_suffix.
 - have Emods : period_bad m n = true by rewrite period_bad_spec Hmods.
   apply: (sem_mx_seq (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool true))] (SolveEntry a m b n))).
   { apply: sem_mx_lift. rewrite -Emods. exact: solver_moduli_validation_sem. }
   exact: solver_reject_suffix.
Qed.

Lemma solver_result_return_sem a m b n u Qn Qb : domain a m b n -> compatible a m b n ->
 0 <= u < n / Z.gcd m n ->
 let t := (((b-a)/Z.gcd m n)*u) mod (n/Z.gcd m n) in
 sem_mx (triv_ctx main.main) (AS_base [::] (SolveT a m b n u t))
  (solver_result_code ++ [:: BI_return; BI_unreachable])
  Qn (AS_base [:: T_const (main.Vi64 (a+m*t))] HA_true) Qb.
Proof.
 move=> Hd Hc Hu t.
 apply: (sem_mx_seq (Q1 := AS_base [:: T_const (main.Vi64 (a+m*t))] HA_true)).
 - apply: sem_mx_lift. apply: (sem_conseq
    (P' := AS_base [::] (SolveT a m b n u t))
    (Q' := AS_base [:: T_const (main.Vi64 (a+m*t))] (SolveT a m b n u t))).
   + by [].
   + move=> V [vs h] /= [Hs _]. by split.
   + exact: solver_result_sem.
 - exact: sem_mx_return_suffix.
Qed.

Lemma solver_inverse_domain a m b n : domain a m b n -> compatible a m b n ->
 1 < n / Z.gcd m n ->
 eea_inputs (n / Z.gcd m n) ((m / Z.gcd m n) mod (n / Z.gcd m n)) /\
 Z.gcd (n / Z.gcd m n) ((m / Z.gcd m n) mod (n / Z.gcd m n)) = 1.
Proof.
 move=> Hd Hc Hnq. have [[Hm Hn] _] := Hd.
 have [_ [_ [HnB [_ [_ [_ [_ [Hrem _]]]]]]]] := crt_bounds_proved a m b n Hd Hc.
 have Hr := Hrem Hnq.
 split; first by unfold eea_inputs; lia.
 have [_ [_ [_ [_ [_ [Hcop _]]]]]] := reduction_proved m n ltac:(lia) ltac:(lia).
 rewrite Z.gcd_comm Z.gcd_mod; last lia. by rewrite Z.gcd_comm.
Qed.

Lemma solver_finish_sem a m b n Qn Qb : domain a m b n -> compatible a m b n ->
 1 < n / Z.gcd m n ->
 let u := crt_inverse_Z ((m / Z.gcd m n) mod (n / Z.gcd m n)) (n / Z.gcd m n) in
 let t := (((b-a)/Z.gcd m n)*u) mod (n/Z.gcd m n) in
 crt_runtime_mx (AS_base [::] (SolveN a m b n))
  (solver_B_code ++ [:: BI_local_get 8%num; BI_local_get 7%num; BI_call 2%num; BI_local_set 9%num] ++
   solver_product_code ++ [:: BI_local_get 7%num; BI_call 1%num; BI_local_set 10%num] ++
   solver_result_code ++ [:: BI_return; BI_unreachable])
  Qn (AS_base [:: T_const (main.Vi64 (a+m*t))] HA_true) Qb.
Proof.
 move=> Hd Hc Hnq u t.
 have [Hi Hcop] := solver_inverse_domain Hd Hc Hnq.
 have [Hu _] := crt_inverse_Z_correct ((m / Z.gcd m n) mod (n / Z.gcd m n))
   (n / Z.gcd m n) ltac:(lia) Hcop.
 have [_ [_ [HnB [_ [_ [_ [_ [_ Hbounds]]]]]]]] := crt_bounds_proved a m b n Hd Hc.
 have [_ [Wp _]] := Hbounds u Hu.
 apply: (crt_runtime_mx_after_triple (Q1 := AS_base [::] (SolveB a m b n))).
 { apply: crt_runtime_triple_of_triple. exact: solver_B_sem. }
 apply: (crt_runtime_mx_after_triple (es1 := [:: BI_local_get 8%num])
  (Q1 := AS_base [:: T_const (main.Vi64 ((m/Z.gcd m n) mod (n/Z.gcd m n)))] (SolveB a m b n))).
 { apply: crt_runtime_triple_of_triple. apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (crt_runtime_mx_after_triple (es1 := [:: BI_local_get 7%num])
  (Q1 := AS_base [:: T_const (main.Vi64 ((m/Z.gcd m n) mod (n/Z.gcd m n))); T_const (main.Vi64 (n/Z.gcd m n))] (SolveB a m b n))).
 { apply: crt_runtime_triple_of_triple. apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (crt_runtime_mx_after_triple (es1 := [:: BI_call 2%num])
  (Q1 := AS_base [:: T_const (main.Vi64 u)] (SolveB a m b n))).
 { move=> f Hinst. apply: crt_inverse_call_from_computes; first exact Hinst. exact: inverse_machine_computes. }
 apply: (crt_runtime_mx_after_triple (es1 := [:: BI_local_set 9%num])
  (Q1 := AS_base [::] (SolveU a m b n u))).
 { apply: crt_runtime_triple_of_triple. apply: sem_local_set_const_frame; unfold_solve; [stable_tac | present_tac]. }
 apply: (crt_runtime_mx_after_triple (es1 := solver_product_code)
  (Q1 := AS_base [:: T_const (main.Vi64 (((b-a)/Z.gcd m n)*u))] (SolveU a m b n u))).
 { apply: crt_runtime_triple_of_triple. exact: solver_product_sem. }
 apply: (crt_runtime_mx_after_triple (es1 := [:: BI_local_get 7%num])
  (Q1 := AS_base [:: T_const (main.Vi64 (((b-a)/Z.gcd m n)*u)); T_const (main.Vi64 (n/Z.gcd m n))] (SolveU a m b n u))).
 { apply: crt_runtime_triple_of_triple. apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (crt_runtime_mx_after_triple (es1 := [:: BI_call 1%num])
  (Q1 := AS_base [:: T_const (main.Vi64 t)] (SolveU a m b n u))).
 { move=> f Hinst. exact: crt_normalize_call. }
 apply: (crt_runtime_mx_after_triple (es1 := [:: BI_local_set 10%num])
  (Q1 := AS_base [::] (SolveT a m b n u t))).
 { apply: crt_runtime_triple_of_triple. apply: sem_local_set_const_frame; unfold_solve; [stable_tac | present_tac]. }
 apply: crt_runtime_mx_of_mx. exact: solver_result_return_sem.
Qed.

Definition solver_compatible_result a m b n :=
 if n / Z.gcd m n =? 1 then a else
 a + m * ((((b-a)/Z.gcd m n) *
   crt_inverse_Z ((m / Z.gcd m n) mod (n / Z.gcd m n)) (n / Z.gcd m n)) mod (n / Z.gcd m n)).

Lemma solver_return_local_suffix G H i c tail Qn Qb : pinned i c H ->
 sem_mx G (AS_base [:: T_const (VAL_int32 (wasm_bool true))] H)
  ([:: BI_if (BT_valtype None) [:: BI_local_get i; BI_return] [::]] ++ tail)
  Qn (AS_base [:: T_const c] HA_true) Qb.
Proof.
 move=> Hpin. apply: (sem_mx_seq (Q1 := AS_base [::] HA_false)).
 - apply: crt_if_true_returns. exact: crt_pinned_return.
 - apply: sem_mx_lift. exact: sem_false.
Qed.

Lemma solver_after_compatibility_sem a m b n Qn Qb : domain a m b n -> compatible a m b n ->
 crt_runtime_mx (AS_base [::] (SolveD a m b n)) solver_after_compatibility
  Qn (AS_base [:: T_const (main.Vi64 (solver_compatible_result a m b n))] HA_true) Qb.
Proof.
 move=> Hd Hc.
 have [_ [_ [Hnq _]]] := crt_bounds_proved a m b n Hd Hc.
 have Wnq := crt_modulus_word Hnq.
 have Wone : word 1 by unfold word, i64_min, i64_max; lia.
 rewrite /solver_after_compatibility.
 apply: (crt_runtime_mx_after_triple (Q1 := AS_base [::] (SolveN a m b n))).
 { apply: crt_runtime_triple_of_triple. exact: solver_reductions_sem. }
 apply: (crt_runtime_mx_after_triple
  (es1 := [:: BI_local_get 7%num; BI_const_num (main.Vi64 1); BI_relop T_i64 (Relop_i ROI_eq)])
  (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool (n / Z.gcd m n =? 1)))] (SolveN a m b n))).
 { apply: crt_runtime_triple_of_triple. rewrite -(crt_public_eq Wnq Wone). apply: test_pin_const;
   [unfold_solve; pinned_tac | by [] | by [] | by []]. }
 rewrite /solver_compatible_result. case Eone: (n / Z.gcd m n =? 1).
 - apply: crt_runtime_mx_of_mx. apply: solver_return_local_suffix. unfold_solve. pinned_tac.
 - apply: (crt_runtime_mx_after_triple
    (es1 := [:: BI_if (BT_valtype None) [:: BI_local_get 0%num; BI_return] [::]])
    (Q1 := AS_base [::] (SolveN a m b n))).
   + apply: crt_runtime_triple_of_triple. apply: guard_if_false. exact: sem_nil_same.
   + apply: solver_finish_sem; [exact Hd | exact Hc |]. apply Z.eqb_neq in Eone. lia.
Qed.

Lemma solver_after_gcd_sem a m b n Qn Qb : domain a m b n ->
 crt_runtime_mx (AS_base [::] (SolveG a m b n)) solver_after_gcd
  Qn (AS_base [:: T_const (main.Vi64
    (if Z.rem (b-a) (Z.gcd m n) =? 0 then solver_compatible_result a m b n else -1))] HA_true) Qb.
Proof.
 move=> Hd. rewrite /solver_after_gcd.
 apply: (crt_runtime_mx_after_triple (Q1 := AS_base [::] (SolveD a m b n))).
 { apply: crt_runtime_triple_of_triple. exact: solver_delta_sem. }
 apply: (crt_runtime_mx_after_triple
  (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool (negb (Z.rem (b-a) (Z.gcd m n) =? 0))))] (SolveD a m b n))).
 { apply: crt_runtime_triple_of_triple. exact: solver_compatibility_test_sem. }
 case Erem: (Z.rem (b-a) (Z.gcd m n) =? 0) => /=.
 - have Hc : compatible a m b n.
   { unfold compatible. apply Z.eqb_eq in Erem.
     have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
     exact (proj1 (Z.rem_divide (b-a) (Z.gcd m n) ltac:(lia)) Erem). }
   apply: (crt_runtime_mx_after_triple
    (es1 := [:: BI_if (BT_valtype None) [:: BI_const_num (main.Vi64 (-1)); BI_return] [::]])
    (Q1 := AS_base [::] (SolveD a m b n))).
   + apply: crt_runtime_triple_of_triple. apply: guard_if_false. exact: sem_nil_same.
   + exact: solver_after_compatibility_sem.
 - apply: crt_runtime_mx_of_mx. exact: solver_reject_suffix.
Qed.

Lemma solver_valid_body_sem a m b n Qn Qb : domain a m b n ->
 crt_runtime_mx (AS_base [::] (SolveEntry a m b n)) (modfunc_body main.crt_solve)
  Qn (AS_base [:: T_const (main.Vi64 (crt_solve_Z a m b n))] HA_true) Qb.
Proof.
 move=> Hd. rewrite /crt_solve_Z (proj2 (crt_domain_b_spec a m b n) Hd).
 rewrite solver_body_shape.
 apply: (crt_runtime_mx_after_triple
  (es1 := solver_moduli_validation ++ [:: BI_if (BT_valtype None) period_reject [::]] ++
   solver_residue_validation ++ [:: BI_if (BT_valtype None) period_reject [::]])
  (Q1 := AS_base [::] (SolveEntry a m b n))).
 { apply: crt_runtime_triple_of_triple. exact: solver_valid_prefix_sem. }
 rewrite /solver_after_validation.
 apply: (crt_runtime_mx_after_triple (es1 := [:: BI_local_get 1%num])
  (Q1 := AS_base [:: T_const (main.Vi64 m)] (SolveEntry a m b n))).
 { apply: crt_runtime_triple_of_triple. apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (crt_runtime_mx_after_triple (es1 := [:: BI_local_get 3%num])
  (Q1 := AS_base [:: T_const (main.Vi64 m); T_const (main.Vi64 n)] (SolveEntry a m b n))).
 { apply: crt_runtime_triple_of_triple. apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (crt_runtime_mx_after_triple (es1 := [:: BI_call 0%num])
  (Q1 := AS_base [:: T_const (main.Vi64 (Z.gcd m n))] (SolveEntry a m b n))).
 { move=> f Hinst. exact: (crt_gcd_call Hinst (proj1 Hd)). }
 apply: (crt_runtime_mx_after_triple (es1 := [:: BI_local_set 4%num])
  (Q1 := AS_base [::] (SolveG a m b n))).
 { apply: crt_runtime_triple_of_triple. apply: sem_local_set_const_frame; unfold_solve; [stable_tac | present_tac]. }
 exact: solver_after_gcd_sem.
Qed.

Lemma solver_entry_entails a m b n :
 aentails (AS_base [::] (HA_and (args_pinned [:: main.Vi64 a; main.Vi64 m; main.Vi64 b; main.Vi64 n] 0%num)
   (func_pre_h main.main main.crt_solve))) (AS_base [::] (SolveEntry a m b n)).
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

Lemma solver_body_to_computation a m b n r :
 crt_runtime_mx (AS_base [::] (SolveEntry a m b n)) (modfunc_body main.crt_solve)
  (AS_base [:: T_const (main.Vi64 r)] HA_true)
  (AS_base [:: T_const (main.Vi64 r)] HA_true)
  (AS_base [:: T_const (main.Vi64 r)] HA_true) ->
 fun_computes_at crt_runtime 4%nat [:: main.Vi64 a; main.Vi64 m; main.Vi64 b; main.Vi64 n] [:: main.Vi64 r].
Proof.
 move=> Hbody.
 change (args_typed [:: main.Vi64 a; main.Vi64 m; main.Vi64 b; main.Vi64 n]
   [:: T_num T_i64; T_num T_i64; T_num T_i64; T_num T_i64] /\
  results_typed [:: main.Vi64 r] [:: T_num T_i64] /\
  exists defaults, default_vals (modfunc_locals main.crt_solve) = Some defaults /\
   sem_mx_at crt_store (activation_frame crt_runtime [:: main.Vi64 a; main.Vi64 m; main.Vi64 b; main.Vi64 n] defaults)
    (AS_base [::] (HA_and (args_pinned [:: main.Vi64 a; main.Vi64 m; main.Vi64 b; main.Vi64 n] 0%num)
     (func_pre_h main.main main.crt_solve))) (modfunc_body main.crt_solve)
    (AS_base [:: T_const (main.Vi64 r)] HA_true)
    (AS_base [:: T_const (main.Vi64 r)] HA_true)
    (AS_base [:: T_const (main.Vi64 r)] HA_true)).
 split; first by repeat split. split; first by repeat split.
 exists (List.repeat (VAL_num (main.Vi64 0)) 10). split; first by [].
 move=> hs V vs h HP Hr. apply: Hbody; [by [] | | exact Hr]. exact: (solver_entry_entails HP).
Qed.

Theorem solve_machine_computes a m b n : word a -> word m -> word b -> word n ->
 fun_computes_at crt_runtime 4%nat [:: main.Vi64 a; main.Vi64 m; main.Vi64 b; main.Vi64 n]
  [:: main.Vi64 (crt_solve_Z a m b n)].
Proof.
 move=> Wa Wm Wb Wn. apply: solver_body_to_computation.
 case Hd: (crt_domain_b a m b n).
 - apply: solver_valid_body_sem. exact (proj1 (crt_domain_b_spec a m b n) Hd).
 - rewrite /crt_solve_Z Hd. apply: crt_runtime_mx_of_mx. exact: solver_invalid_body_sem.
Qed.

Theorem solve_machine_computes_i64 (a m b n : i64) :
 fun_computes_at crt_runtime 4%nat [:: VAL_int64 a; VAL_int64 m; VAL_int64 b; VAL_int64 n]
  [:: main.Vi64 (crt_solve_Z (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
    (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n))].
Proof.
 have H := solve_machine_computes (crt_contract_signed_word a) (crt_contract_signed_word m)
  (crt_contract_signed_word b) (crt_contract_signed_word n).
 change (fun_computes_at crt_runtime 4%nat
  [:: VAL_int64 (Wasm_int.Int64.repr (Wasm_int.Int64.signed a));
      VAL_int64 (Wasm_int.Int64.repr (Wasm_int.Int64.signed m));
      VAL_int64 (Wasm_int.Int64.repr (Wasm_int.Int64.signed b));
      VAL_int64 (Wasm_int.Int64.repr (Wasm_int.Int64.signed n))]
  [:: main.Vi64 (crt_solve_Z (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
    (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n))]) in H.
 by rewrite !Wasm_int.Int64.repr_signed in H.
Qed.

End Host.

Print Assumptions solve_machine_computes.
Print Assumptions solve_machine_computes_i64.
