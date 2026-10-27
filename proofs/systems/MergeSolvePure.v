(* Full-width pure segments shared with the exact emitted solve body. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTMath CRTLoops CRTSystemStatements CRTSystemArithmetic.
From CRTWasm Require Import CRTContracts CRTPublicExecution CRTGeneralArithmetic CRTSolveExecution.
From CRTSystems Require Import FullWidthExecution.
Module SM := CRTSystemGenerated.main.
Import FullWidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Lemma crt_period_intermediate_bounds m n : moduli m n ->
 1 <= Z.gcd m n <= MAX /\ 1 <= m / Z.gcd m n <= MAX /\
 word (m / Z.gcd m n) /\ word n.
Proof.
 move=> [Hm Hn]. have [Hg [Hgm [Hgn [Hq _]]]] := reduction_proved m n ltac:(lia) ltac:(lia).
 have Heq := exact_division _ _ Hg Hgm.
 have HBq : 1 <= m / Z.gcd m n <= MAX by nia.
 have HBg : 1 <= Z.gcd m n <= MAX by nia.
 split; first exact HBg. split; first exact HBq. split; exact: crt_modulus_word.
Qed.
Section Host.
Context `{ho : host}.
Ltac pinned_tac := solve [exact: pinned_bare | apply: pinned_left; pinned_tac | apply: pinned_right; pinned_tac].
Ltac present_tac := solve [exact: loc_present_defined | exact: loc_present_pin | apply: loc_present_left; present_tac | apply: loc_present_right; present_tac].
Lemma solver_stable_true i c : loc_stable i c HA_true.
Proof. by []. Qed.
Ltac stable_tac := solve [exact: solver_stable_true | exact: loc_stable_defined_self | exact: loc_stable_pin_self | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other | apply: loc_stable_and; stable_tac].
Lemma solver_checked_mul_Z G H x y :
  loc_stable 11%num (SM.Vi64 x) H -> loc_stable 12%num (SM.Vi64 y) H ->
  loc_stable 13%num (SM.Vi64 (x * y)) H ->
  loc_present 11%num H -> loc_present 12%num H -> loc_present 13%num H ->
  word x -> word y -> word (x * y) ->
  sem_triple G (AS_base [:: T_const (SM.Vi64 x); T_const (SM.Vi64 y)] H)
    (crt_general_checked_mul_code 11%num 12%num 13%num) (AS_base [:: T_const (SM.Vi64 (x * y))] H).
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
  loc_stable 11%num (SM.Vi64 x) H -> loc_stable 12%num (SM.Vi64 y) H ->
  loc_stable 13%num (SM.Vi64 (x - y)) H ->
  loc_present 11%num H -> loc_present 12%num H -> loc_present 13%num H ->
  word x -> word y -> word (x - y) ->
  sem_triple G (AS_base [:: T_const (SM.Vi64 x); T_const (SM.Vi64 y)] H)
    (crt_general_checked_sub_code 11%num 12%num 13%num) (AS_base [:: T_const (SM.Vi64 (x - y))] H).
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
  loc_stable 11%num (SM.Vi64 x) H -> loc_stable 12%num (SM.Vi64 y) H ->
  loc_stable 13%num (SM.Vi64 (x + y)) H ->
  loc_present 11%num H -> loc_present 12%num H -> loc_present 13%num H ->
  word x -> word y -> word (x + y) ->
  sem_triple G (AS_base [:: T_const (SM.Vi64 x); T_const (SM.Vi64 y)] H)
    (crt_general_checked_add_code 11%num 12%num 13%num) (AS_base [:: T_const (SM.Vi64 (x + y))] H).
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
 (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 a)))
 (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 m)))
 (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 b)))
 (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 n)))
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
 HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (Z.gcd m n)))) (SolveEntry a m b n).
Definition SolveD a m b n :=
 HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (b - a)))) (SolveG a m b n).
Definition SolveM a m b n :=
 HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (m / Z.gcd m n)))) (SolveD a m b n).
Definition SolveN a m b n :=
 HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (n / Z.gcd m n)))) (SolveM a m b n).
Definition SolveB a m b n :=
 HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 ((m / Z.gcd m n) mod (n / Z.gcd m n))))) (SolveN a m b n).
Definition SolveU a m b n u :=
 HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (u)))) (SolveB a m b n).
Definition SolveT a m b n u t :=
 HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (t)))) (SolveU a m b n u).
Ltac unfold_solve := rewrite /SolveT /SolveU /SolveB /SolveN /SolveM /SolveD /SolveG /SolveEntry.

Lemma solver_delta_word a m b n : domain a m b n -> word (b - a).
Proof. move=> [[Hm Hn] [Ha Hb]]. unfold word, MAX, i64_min, i64_max in *; lia. Qed.

Lemma solver_delta_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (SolveG a m b n)) solver_delta_code
  (AS_base [::] (SolveD a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have Wa : word a by unfold word, MAX, i64_min, i64_max in *; lia.
 have Wb : word b by unfold word, MAX, i64_min, i64_max in *; lia.
 have Wd := solver_delta_word Hd.
 rewrite /solver_delta_code.
 apply: (sem_seq (es1 := [:: BI_local_get 2%num])
  (Q := AS_base [:: T_const (SM.Vi64 b)] (SolveG a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 0%num])
  (Q := AS_base [:: T_const (SM.Vi64 b); T_const (SM.Vi64 a)] (SolveG a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := solver_sub_code)
  (Q := AS_base [:: T_const (SM.Vi64 (b-a))] (SolveG a m b n))).
 { apply: solver_checked_sub_Z; try assumption; unfold_solve; first [stable_tac | present_tac]. }
 apply: sem_local_set_const_frame; unfold_solve; [stable_tac | present_tac].
Qed.

Lemma solver_compatibility_test_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (SolveD a m b n)) solver_compatibility_test
  (AS_base [:: T_const (VAL_int32 (wasm_bool (negb (Z.rem (b-a) (Z.gcd m n) =? 0))))] (SolveD a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
 have Wd := solver_delta_word Hd.
 have Wr := crt_rem_word Wd Hg.
 have Wzero : word 0 by unfold word, i64_min, i64_max; lia.
 rewrite /solver_compatibility_test.
 apply: (sem_seq (es1 := [:: BI_local_get 5%num])
  (Q := AS_base [:: T_const (SM.Vi64 (b-a))] (SolveD a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 4%num])
  (Q := AS_base [:: T_const (SM.Vi64 (b-a)); T_const (SM.Vi64 (Z.gcd m n))] (SolveD a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_rem SX_S))])
  (Q := AS_base [:: T_const (SM.Vi64 (Z.rem (b-a) (Z.gcd m n)))] (SolveD a m b n))).
 { apply: binop_consts; [by vm_compute | by [] | by [] | exact: crt_i64_rem_exact]. }
 apply: (sem_seq (es1 := [:: BI_const_num (SM.Vi64 0)])
  (Q := AS_base [:: T_const (SM.Vi64 (Z.rem (b-a) (Z.gcd m n))); T_const (SM.Vi64 0)] (SolveD a m b n))).
 { exact: sem_const_framed. }
 rewrite -(crt_public_ne Wr Wzero). apply: relop_consts; by [].
Qed.

Lemma solver_reductions_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (SolveD a m b n)) solver_reductions_code
  (AS_base [::] (SolveN a m b n)).
Proof.
 move=> Hd. have [[Hm Hn] [Ha Hb]] := Hd.
 have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
 rewrite /solver_reductions_code.
 apply: (sem_seq (es1 := [:: BI_local_get 1%num])
  (Q := AS_base [:: T_const (SM.Vi64 m)] (SolveD a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 4%num])
  (Q := AS_base [:: T_const (SM.Vi64 m); T_const (SM.Vi64 (Z.gcd m n))] (SolveD a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))])
  (Q := AS_base [:: T_const (SM.Vi64 (m / Z.gcd m n))] (SolveD a m b n))).
 { apply: binop_consts; [by vm_compute | by [] | by [] | apply: crt_i64_div_positive_exact; lia]. }
 apply: (sem_seq (es1 := [:: BI_local_set 6%num])
  (Q := AS_base [::] (SolveM a m b n))).
 { apply: sem_local_set_const_frame; unfold_solve; [stable_tac | present_tac]. }
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

Lemma solver_B_sem a m b n : domain a m b n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (SolveN a m b n)) solver_B_code
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
  (Q := AS_base [:: T_const (SM.Vi64 (m / Z.gcd m n))] (SolveN a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 7%num])
  (Q := AS_base [:: T_const (SM.Vi64 (m / Z.gcd m n)); T_const (SM.Vi64 (n / Z.gcd m n))] (SolveN a m b n))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_rem SX_S))])
  (Q := AS_base [:: T_const (SM.Vi64 ((m / Z.gcd m n) mod (n / Z.gcd m n)))] (SolveN a m b n))).
 { apply: binop_consts; [by vm_compute | by [] | by [] |]. rewrite -Hr. exact: crt_i64_rem_exact. }
 apply: sem_local_set_const_frame; unfold_solve; [stable_tac | present_tac].
Qed.

Lemma solver_divisible_div d g : word d -> 1 <= g <= MAX -> (g | d) -> word (d/g) ->
 app_binop (Binop_i (BOI_div SX_S)) (SM.Vi64 d) (SM.Vi64 g) = Some (SM.Vi64 (d/g)).
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

Lemma solver_result_sem a m b n u t : domain a m b n -> compatible a m b n ->
 Z.lcm m n <= MAX -> 0 <= t < n / Z.gcd m n ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (SolveT a m b n u t)) solver_result_code
 (AS_base [::T_const (SM.Vi64 (a+m*t))] (SolveT a m b n u t)).
Proof.
 move=> Hd Hcompat Hfit Ht.
 have [_ [_ Hb]] := construct_bounds_proved a m b n Hd Hcompat Hfit.
 have [Wmt [Wx Hx]] := Hb t Ht.
 have [[Hm Hn] [Ha Hr]] := Hd.
 have Wa : word a by unfold word, MAX, i64_min, i64_max in *; lia.
 have Wm := crt_modulus_word Hm.
 have Hsw : moduli n m by split.
 have [_ [Hnq _]] := crt_period_intermediate_bounds Hsw.
 rewrite Z.gcd_comm in Hnq.
 have Wt : word t by apply nonnegative_word; lia.
 rewrite /solver_result_code.
 apply: (sem_seq (es1 := [:: BI_local_get 0%num])
  (Q := AS_base [:: T_const (SM.Vi64 a)] (SolveT a m b n u t))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 1%num])
  (Q := AS_base [:: T_const (SM.Vi64 a); T_const (SM.Vi64 m)] (SolveT a m b n u t))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := [:: BI_local_get 10%num])
  (Q := AS_base [:: T_const (SM.Vi64 a); T_const (SM.Vi64 m); T_const (SM.Vi64 t)] (SolveT a m b n u t))).
 { apply: get_pinned_frame. unfold_solve. pinned_tac. }
 apply: (sem_seq (es1 := solver_mul_code)
  (Q := AS_base [:: T_const (SM.Vi64 a); T_const (SM.Vi64 (m*t))] (SolveT a m b n u t))).
 { apply: (sem_frame_consts (vf := [:: SM.Vi64 a])).
   apply: solver_checked_mul_Z; try assumption; unfold_solve; first [stable_tac | present_tac]. }
 apply: solver_checked_add_Z; try assumption; unfold_solve; first [stable_tac | present_tac].
Qed.

End Host.
