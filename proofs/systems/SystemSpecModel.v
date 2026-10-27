(* Exact scalar interpretation; realization is supplied by actual execution. *)
From Coq Require Import ZArith NArith Lia List Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations host.
From WasmVerifier Require Import Assertions Semantics NumericDischarge Automation Activation Verifier.
From CRT Require Import CRTStatements CRTMath CRTSystemStatements CRTSystemArithmetic CRTFinite.
From CRTWasm Require Import CRTContracts.
From CRTSystems Require Import ScalarResultFacts.
From CRTSystemGenerated Require Import main.
Module SM := CRTSystemGenerated.main.
Import FullWidth FiniteSystem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition sp_moduli_b m n := (1 <=? m) && (m <=? MAX) && (1 <=? n) && (n <=? MAX).
Definition sp_inverse_b B A := (1 <=? B) && (B <? A) && (A <=? MAX) && (Z.gcd A B =? 1).
Definition sp_mod_b x y d := (1 <=? d) && (d <=? MAX) && (0 <=? x) && (x <? d) && (0 <=? y) && (y <? d).
Definition sp_solve a m b n := solve_value (merge a m b n).
Definition sp_period a m b n := period_value (merge a m b n).
Definition system_model_interp : fun_interp := fun i args =>
 match i,args with
 | O,[::VAL_int64 m;VAL_int64 n] =>
   if sp_moduli_b (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n)
   then Some [::SM.Vi64 (Z.gcd (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n))] else None
 | 1%nat,[::VAL_int64 z;VAL_int64 d] =>
   if (1 <=? Wasm_int.Int64.signed d) && (Wasm_int.Int64.signed d <=? MAX)
   then Some [::SM.Vi64 (Wasm_int.Int64.signed z mod Wasm_int.Int64.signed d)] else None
 | 2%nat,[::VAL_int64 B;VAL_int64 A] =>
   if sp_inverse_b (Wasm_int.Int64.signed B) (Wasm_int.Int64.signed A)
   then Some [::SM.Vi64 (inverse_model (Wasm_int.Int64.signed B) (Wasm_int.Int64.signed A))] else None
 | 3%nat,[::VAL_int64 x;VAL_int64 y;VAL_int64 d] =>
   if sp_mod_b (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed d)
   then Some [::SM.Vi64 (add_mod (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed d))] else None
 | 4%nat,[::VAL_int64 x;VAL_int64 y;VAL_int64 d] =>
   if sp_mod_b (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed d)
   then Some [::SM.Vi64 (mul_mod (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed d))] else None
 | 5%nat,[::VAL_int64 a;VAL_int64 m;VAL_int64 b;VAL_int64 n] =>
   Some [::SM.Vi64 (sp_solve (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n))]
 | 6%nat,[::VAL_int64 a;VAL_int64 m;VAL_int64 b;VAL_int64 n] =>
   Some [::SM.Vi64 (sp_period (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n))]
 | _,_ => None
 end.
Lemma sp_moduli_b_spec m n : sp_moduli_b m n = true <-> moduli m n.
Proof. rewrite /sp_moduli_b /moduli !andb_true_iff !Z.leb_le. tauto. Qed.
Lemma sp_inverse_b_spec B A : sp_inverse_b B A = true <-> eea_inputs A B /\ Z.gcd A B = 1.
Proof. rewrite /sp_inverse_b /eea_inputs !andb_true_iff !Z.leb_le !Z.ltb_lt !Z.eqb_eq. tauto || lia. Qed.
Lemma sp_mod_b_spec x y d : sp_mod_b x y d = true <-> 1 <= d <= MAX /\ 0 <= x < d /\ 0 <= y < d.
Proof. rewrite /sp_mod_b !andb_true_iff !Z.leb_le !Z.ltb_lt. tauto. Qed.
Lemma sp_gcd_contract m n : moduli m n ->
 let g := Z.gcd m n in 1 <= g /\ g <= m /\ g <= n /\ Z.rem m g = 0 /\ Z.rem n g = 0 /\
 forall d, 1 <= d <= MAX -> Z.rem m d = 0 -> Z.rem n d = 0 -> Z.rem g d = 0.
Proof.
 move=> [Hm Hn] /=. have Hg := CRTMath.gcd_positive m n ltac:(lia).
 have Hgm := Z.gcd_divide_l m n. have Hgn := Z.gcd_divide_r m n.
 split; first lia. split; first (apply Z.divide_pos_le; lia || assumption).
 split; first (apply Z.divide_pos_le; lia || assumption).
 split; first (apply Z.rem_divide; lia || assumption).
 split; first (apply Z.rem_divide; lia || assumption).
 move=> d Hd Hdm Hdn. apply Z.rem_divide; first lia.
 apply Z.gcd_greatest; apply Z.rem_divide; try lia; assumption.
Qed.
Lemma sp_inverse_contract B A : eea_inputs A B -> Z.gcd A B = 1 ->
 0 <= inverse_model B A < A /\ mul_mod B (inverse_model B A) A = 1.
Proof.
 move=> Hin Hcop. have [Hu Hcong] := inverse_model_proved A B Hin Hcop.
 split; first exact Hu. have [[HB HBA] HA] := Hin.
 have [Hm _] := mul_mod_proved B (inverse_model B A) A ltac:(lia) ltac:(lia) Hu.
 rewrite Hm. apply Znumtheory.Zdivide_mod_minus; lia || assumption.
Qed.
Lemma sp_result_words a m b n : word (sp_solve a m b n) /\ word (sp_period a m b n).
Proof. exact: scalar_result_values_word. Qed.
Lemma sp_success_contract a m b n : 0 <= sp_solve a m b n ->
 domain a m b n /\ 0 <= sp_solve a m b n < sp_period a m b n /\
 Z.rem (sp_solve a m b n) m = a /\ Z.rem (sp_solve a m b n) n = b.
Proof.
 rewrite /sp_solve /sp_period. have Hp := scalar_model_proved a m b n.
 case E: (merge a m b n) Hp => [| | |r p] /= Hp Hnonneg; try lia.
 have [Hv [_ [_ Hr]]] := Hp. have Hd := proj1 (valid_pair a m b n) Hv.
 have [[Hm Hn] [Ha Hb]] := Hd.
 have Hsol := Rep_solution _ _ _ Hr. have [_ [Hrange _]] := Hr.
 split; first exact Hd. split; first exact Hrange. rewrite !Z.rem_mod_nonneg; try lia.
 split; apply Znumtheory.Zdivide_mod_minus; try lia; apply Hsol; simpl; auto.
Qed.
Lemma sp_unique_contract a m b n y : domain a m b n -> 0 <= y < sp_period a m b n ->
 Z.rem y m = a -> Z.rem y n = b -> y = sp_solve a m b n.
Proof.
 move=> Hd. rewrite /sp_period /sp_solve. have Hp := scalar_model_proved a m b n.
 case E: (merge a m b n) Hp => [| | |r p] /= Hp Hy Hya Hyb; try lia.
 have [_ [_ [_ [HL [Hr Hequiv]]]]] := Hp.
 have [[Hm Hn] [Ha Hb]] := Hd.
 have Hsol : Sol [::(a,m);(b,n)] y.
 { move=> c d [Heq|[Heq|Hnil]]; try contradiction; inversion Heq; subst;
   apply Znumtheory.Zmod_divide_minus; try lia; rewrite -Z.rem_mod_nonneg; lia || assumption. }
 have [k Hk] := proj1 (Hequiv y) Hsol. have Hk0 : k=0 by nia. nia.
Qed.
