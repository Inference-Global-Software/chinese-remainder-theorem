From Coq Require Import ZArith NArith Lia List Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTMath CRTSystemStatements CRTSystemArithmetic.
From CRTWasm Require Import CRTPublicExecution CRTContracts CRTGeneralArithmetic.
From CRTSystems Require Import ReadOnly SystemRuntime SystemMemory SystemControl SystemCalls FullWidthExecution MergeSolvePure.
From CRTSystems Require Import ArrayAccess BatchArithmetic BatchCount BatchValidation.
Module SM := CRTSystemGenerated.main.
Import FullWidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition pair_gcd_code := array_access 1%num 4%num 7%num ++ array_access 1%num 5%num 7%num ++
 [::BI_call 0%num;BI_local_set 6%num].
Definition pair_diff_code := array_access 0%num 5%num 7%num ++ array_access 0%num 4%num 7%num ++
 crt_general_checked_sub_code 11%num 12%num 13%num.
Definition pair_test_code := pair_gcd_code ++ pair_diff_code ++
 [::BI_local_get 6%num;BI_binop T_i64 (Binop_i (BOI_rem SX_S));BI_const_num (SM.Vi64 0);BI_relop T_i64 (Relop_i ROI_ne)].
Definition classifier_pair_outer := match List.nth 16 (modfunc_body SM.system_classify) BI_unreachable with
 | BI_block _ [::BI_loop _ body] => body | _ => [::] end.
Definition classifier_pair_inner := match List.nth 21 classifier_pair_outer BI_unreachable with
 | BI_block _ [::BI_loop _ body] => body | _ => [::] end.
Lemma pair_test_shape : List.firstn 63 (List.skipn 5 classifier_pair_inner) = pair_test_code.
Proof. reflexivity. Qed.
Definition PairG H g := HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 g))) H.
Lemma pair_incompatible_model a m b n : domain a m b n ->
 negb (Z.rem (b-a) (Z.gcd m n) =? 0) = negb (FiniteSystem.compatb (a,m) (b,n)).
Proof.
 move=> [[Hm Hn] _]. unfold FiniteSystem.compatb; simpl.
 f_equal. apply Bool.eq_true_iff_eq. rewrite !Z.eqb_eq.
 apply Z.rem_mod_eq_0. have Hg := CRTMath.gcd_positive m n ltac:(lia). lia.
Qed.
Section Host.
Context `{ho:host}.
Context (mem:meminst).
Lemma pair_gcd_sem mb ms i j m n H :
 array_region mem mb ms -> List.nth_error ms i = Some m -> List.nth_error ms j = Some n ->
 pinned 1%num (SM.Vi32 (Z.of_N mb)) H -> pinned 4%num (SM.Vi32 (Z.of_nat i)) H -> pinned 5%num (SM.Vi32 (Z.of_nat j)) H ->
 loc_present 7%num H -> (forall z, loc_stable 7%num z H) ->
 loc_present 6%num H -> loc_stable 6%num (SM.Vi64 (Z.gcd (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n))) H ->
 moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) ->
 system_triple mem (AS_base [::] H) pair_gcd_code
 (AS_base [::] (PairG H (Z.gcd (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n)))).
Proof.
 move=> Hr Hmi Hnj Hp Hi Hj P7 S7 P6 S6 Hmod. rewrite /pair_gcd_code.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (VAL_int64 m)] H)); first reflexivity.
 - exact: (array_access_sem Hr Hmi Hp Hi P7 (S7 _)).
 - apply: (system_triple_seq (Q1:=AS_base [::T_const (VAL_int64 m);T_const (VAL_int64 n)] H)); first reflexivity.
   + apply: (batch_frame_consts (vf:=[::VAL_int64 m])). exact: (array_access_sem Hr Hnj Hp Hj P7 (S7 _)).
   + apply: (system_triple_seq (es1:=[::BI_call 0%num])
     (Q1:=AS_base [::T_const (SM.Vi64 (Z.gcd (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n)))] H)); first reflexivity.
     * rewrite -[VAL_int64 m]crt_contract_repr_signed -[VAL_int64 n]crt_contract_repr_signed.
       move=> f Hinst. exact: crt_gcd_call.
     * apply: system_triple_of_pure. exact: sem_local_set_const_frame.
Qed.
Lemma pair_diff_sem rb rs i j a b H :
 array_region mem rb rs -> List.nth_error rs i = Some a -> List.nth_error rs j = Some b ->
 pinned 0%num (SM.Vi32 (Z.of_N rb)) H -> pinned 4%num (SM.Vi32 (Z.of_nat i)) H -> pinned 5%num (SM.Vi32 (Z.of_nat j)) H ->
 loc_present 7%num H -> (forall z, loc_stable 7%num z H) ->
 loc_present 11%num H -> loc_present 12%num H -> loc_present 13%num H ->
 (forall z,loc_stable 11%num z H) -> (forall z,loc_stable 12%num z H) -> (forall z,loc_stable 13%num z H) ->
 word (Wasm_int.Int64.signed b - Wasm_int.Int64.signed a) ->
 system_triple mem (AS_base [::] H) pair_diff_code
 (AS_base [::T_const (SM.Vi64 (Wasm_int.Int64.signed b - Wasm_int.Int64.signed a))] H).
Proof.
 move=> Hr Hai Hbj Hp Hi Hj P7 S7 P11 P12 P13 S11 S12 S13 Wd. rewrite /pair_diff_code.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (VAL_int64 b)] H)); first reflexivity.
 - exact: (array_access_sem Hr Hbj Hp Hj P7 (S7 _)).
 - apply: (system_triple_seq (Q1:=AS_base [::T_const (VAL_int64 b);T_const (VAL_int64 a)] H)); first reflexivity.
   + apply: (batch_frame_consts (vf:=[::VAL_int64 b])). exact: (array_access_sem Hr Hai Hp Hi P7 (S7 _)).
   + apply: system_triple_of_pure.
     rewrite -[VAL_int64 a]crt_contract_repr_signed -[VAL_int64 b]crt_contract_repr_signed.
     apply: solver_checked_sub_Z; try assumption; try apply crt_contract_signed_word; auto.
Qed.
Lemma pair_test_sem rb mb rs ms i j a m b n H :
 array_region mem rb rs -> List.nth_error rs i = Some a -> List.nth_error rs j = Some b ->
 array_region mem mb ms -> List.nth_error ms i = Some m -> List.nth_error ms j = Some n ->
 pinned 0%num (SM.Vi32 (Z.of_N rb)) H -> pinned 1%num (SM.Vi32 (Z.of_N mb)) H ->
 pinned 4%num (SM.Vi32 (Z.of_nat i)) H -> pinned 5%num (SM.Vi32 (Z.of_nat j)) H ->
 loc_present 6%num H -> (forall z,loc_stable 6%num z H) ->
 loc_present 7%num H -> (forall z,loc_stable 7%num z H) ->
 loc_present 11%num H -> loc_present 12%num H -> loc_present 13%num H ->
 (forall z,loc_stable 11%num z H) -> (forall z,loc_stable 12%num z H) -> (forall z,loc_stable 13%num z H) ->
 domain (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n) ->
 system_triple mem (AS_base [::] H) pair_test_code
 (AS_base [::T_const (VAL_int32 (wasm_bool (negb (Z.rem (Wasm_int.Int64.signed b - Wasm_int.Int64.signed a)
 (Z.gcd (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n)) =? 0))))] H).
Proof.
 move=> Hrr Hai Hbj Hmr Hmi Hnj Pr Pm Pi Pj P6 S6 P7 S7 P11 P12 P13 S11 S12 S13 Hd.
 set g := Z.gcd (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n).
 set delta := Wasm_int.Int64.signed b - Wasm_int.Int64.signed a.
 have [Hg _] := crt_period_intermediate_bounds (proj1 Hd).
 have Wd := solver_delta_word Hd.
 have Wr := crt_rem_word Wd Hg.
 have Wzero : word 0 by unfold word,i64_min,i64_max; lia.
 apply: (batch_triple_conseq (P':=AS_base [::] H) (Q':=AS_base [::T_const (VAL_int32 (wasm_bool (negb (Z.rem delta g =? 0))))] (PairG H g))).
 - by move=> V vh.
 - move=> V [vs h] /= [Hs [_ HH]]. by split.
 - rewrite /pair_test_code.
   apply: (system_triple_seq (Q1:=AS_base [::] (PairG H g))); first reflexivity.
   + exact: (pair_gcd_sem Hmr Hmi Hnj Pm Pi Pj P7 S7 P6 (S6 _) (proj1 Hd)).
   + apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 delta)] (PairG H g))); first reflexivity.
     * apply: (pair_diff_sem Hrr Hai Hbj).
       -- apply: pinned_right. exact Pr.
       -- apply: pinned_right. exact Pi.
       -- apply: pinned_right. exact Pj.
       -- apply: loc_present_right. exact P7.
       -- move=> z. apply: loc_stable_and; first by apply: loc_stable_pin_other. exact: S7.
       -- apply: loc_present_right. exact P11.
       -- apply: loc_present_right. exact P12.
       -- apply: loc_present_right. exact P13.
       -- move=> z. apply: loc_stable_and; first by apply: loc_stable_pin_other. exact: S11.
       -- move=> z. apply: loc_stable_and; first by apply: loc_stable_pin_other. exact: S12.
       -- move=> z. apply: loc_stable_and; first by apply: loc_stable_pin_other. exact: S13.
       -- exact Wd.
     * apply: system_triple_of_pure.
       apply: (sem_seq (es1:=[::BI_local_get 6%num])
       (Q:=AS_base [::T_const (SM.Vi64 delta);T_const (SM.Vi64 g)] (PairG H g))).
       -- apply: get_pinned_frame. apply: pinned_left. exact: pinned_bare.
       -- apply: (sem_seq (es1:=[::BI_binop T_i64 (Binop_i (BOI_rem SX_S))])
          (Q:=AS_base [::T_const (SM.Vi64 (Z.rem delta g))] (PairG H g))).
          ++ apply: binop_consts; try reflexivity. exact: crt_i64_rem_exact.
          ++ apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 0)])
             (Q:=AS_base [::T_const (SM.Vi64 (Z.rem delta g));T_const (SM.Vi64 0)] (PairG H g))); first exact: sem_const_framed.
             rewrite -(crt_public_ne Wr Wzero). apply: relop_consts; reflexivity.
Qed.
End Host.
