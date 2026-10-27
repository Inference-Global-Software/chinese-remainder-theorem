From Coq Require Import ZArith NArith Lia List Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTSystemStatements.
From CRTWasm Require Import CRTPublicExecution CRTContracts.
From CRTSystems Require Import ReadOnly SystemRuntime SystemMemory SystemControl SystemCalls FullWidthExecution.
From CRTSystems Require Import ArrayAccess BatchArithmetic BatchCount.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition validation_low ptr idx tmp z := array_access ptr idx tmp ++
 [::BI_const_num (SM.Vi64 z);BI_relop T_i64 (Relop_i (ROI_lt SX_S))].
Definition validation_high rp mp idx tmp := array_access rp idx tmp ++ array_access mp idx tmp ++
 [::BI_relop T_i64 (Relop_i (ROI_ge SX_S))].
Definition validation_item rp mp idx tmp := validation_low mp idx tmp 1 ++
 [::BI_if (BT_valtype (Some (T_num T_i32))) [::BI_const_num (SM.Vi32 1)] (validation_low rp idx tmp 0);
 BI_if (BT_valtype (Some (T_num T_i32))) [::BI_const_num (SM.Vi32 1)] (validation_high rp mp idx tmp)].
Definition classifier_validation_loop :=
 match List.nth 9 (modfunc_body SM.system_classify) BI_unreachable with
 | BI_block _ [::BI_loop _ body] => body | _ => [::] end.
Lemma validation_item_shape : List.firstn 15 (List.skipn 5 classifier_validation_loop) = validation_item 0%num 1%num 4%num 7%num.
Proof. reflexivity. Qed.
Lemma validation_bad_model (r m:i64) :
 ((Wasm_int.Int64.signed m <? 1) || (Wasm_int.Int64.signed r <? 0) ||
 (Wasm_int.Int64.signed m <=? Wasm_int.Int64.signed r)) =
 negb (FiniteSystem.validb (Wasm_int.Int64.signed r,Wasm_int.Int64.signed m)).
Proof.
 have Hmax : (Wasm_int.Int64.signed m <=? FullWidth.MAX) = true.
 { apply/Z.leb_le. exact (proj2 (crt_contract_signed_word m)). }
 have Hlt : forall x y, (x <? y) = negb (y <=? x).
 { move=> x y. case E:(x <? y); case F:(y <=? x); try reflexivity;
   [apply Z.ltb_lt in E; apply Z.leb_le in F | apply Z.ltb_ge in E; apply Z.leb_gt in F]; lia. }
 rewrite /FiniteSystem.validb /= Hmax !Hlt.
 by case: (1 <=? Wasm_int.Int64.signed m); case: (0 <=? Wasm_int.Int64.signed r);
 case: (Wasm_int.Int64.signed m <=? Wasm_int.Int64.signed r).
Qed.
Section Host.
Context `{ho:host}.
Context (mem:meminst).
Lemma batch_or H b c es :
 system_triple mem (AS_base [::] H) es (AS_base [::T_const (VAL_int32 (wasm_bool c))] H) ->
 system_triple mem (AS_base [::T_const (VAL_int32 (wasm_bool b))] H)
 [::BI_if (BT_valtype (Some (T_num T_i32))) [::BI_const_num (SM.Vi32 1)] es]
 (AS_base [::T_const (VAL_int32 (wasm_bool (b || c)))] H).
Proof.
 move=> Hc. apply: system_triple_of_mxk.
 apply: (system_if_const (t2s:=[::T_num T_i32])); first reflexivity.
 - move=> V vs h [Hs _]. by case: Hs => <-.
 - case: b => /=; apply: system_mxk_lift.
   + apply: system_triple_of_pure. exact: sem_const_framed.
   + exact Hc.
Qed.
Lemma validation_low_sem base xs i x ptr idx tmp H z :
 array_region mem base xs -> List.nth_error xs i = Some x ->
 pinned ptr (SM.Vi32 (Z.of_N base)) H -> pinned idx (SM.Vi32 (Z.of_nat i)) H ->
 loc_present tmp H -> loc_stable tmp (SM.Vi32 (Z.of_nat i)) H -> word z ->
 system_triple mem (AS_base [::] H) (validation_low ptr idx tmp z)
 (AS_base [::T_const (VAL_int32 (wasm_bool (Wasm_int.Int64.signed x <? z)))] H).
Proof.
 move=> Hr Hnth Hp Hi Hpres Hstable Wz. rewrite /validation_low.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (VAL_int64 x)] H)); first reflexivity.
 - exact: (array_access_sem Hr Hnth Hp Hi Hpres Hstable).
 - apply: system_triple_of_pure.
   apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 z)])
   (Q:=AS_base [::T_const (VAL_int64 x);T_const (SM.Vi64 z)] H)); first exact: sem_const_framed.
   have Wx := crt_contract_signed_word x.
   rewrite -(crt_public_lt Wx Wz) crt_contract_repr_signed. apply: relop_consts; reflexivity.
Qed.
Lemma validation_high_sem rb mb rs ms i r m rp mp idx tmp H :
 array_region mem rb rs -> List.nth_error rs i = Some r ->
 array_region mem mb ms -> List.nth_error ms i = Some m ->
 pinned rp (SM.Vi32 (Z.of_N rb)) H -> pinned mp (SM.Vi32 (Z.of_N mb)) H ->
 pinned idx (SM.Vi32 (Z.of_nat i)) H -> loc_present tmp H -> loc_stable tmp (SM.Vi32 (Z.of_nat i)) H ->
 system_triple mem (AS_base [::] H) (validation_high rp mp idx tmp)
 (AS_base [::T_const (VAL_int32 (wasm_bool (Wasm_int.Int64.signed m <=? Wasm_int.Int64.signed r)))] H).
Proof.
 move=> Hr Hrn Hm Hmn Hp Hq Hi Hpres Hstable. rewrite /validation_high.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (VAL_int64 r)] H)); first reflexivity.
 - exact: (array_access_sem Hr Hrn Hp Hi Hpres Hstable).
 - apply: (system_triple_seq (Q1:=AS_base [::T_const (VAL_int64 r);T_const (VAL_int64 m)] H)); first reflexivity.
   + apply: (batch_frame_consts (vf:=[::VAL_int64 r])). exact: (array_access_sem Hm Hmn Hq Hi Hpres Hstable).
   + apply: system_triple_of_pure. rewrite -crt_contract_ge. apply: relop_consts; reflexivity.
Qed.
Lemma validation_item_sem rb mb rs ms i r m rp mp idx tmp H :
 array_region mem rb rs -> List.nth_error rs i = Some r ->
 array_region mem mb ms -> List.nth_error ms i = Some m ->
 pinned rp (SM.Vi32 (Z.of_N rb)) H -> pinned mp (SM.Vi32 (Z.of_N mb)) H ->
 pinned idx (SM.Vi32 (Z.of_nat i)) H -> loc_present tmp H -> loc_stable tmp (SM.Vi32 (Z.of_nat i)) H ->
 system_triple mem (AS_base [::] H) (validation_item rp mp idx tmp)
 (AS_base [::T_const (VAL_int32 (wasm_bool ((Wasm_int.Int64.signed m <? 1) ||
 (Wasm_int.Int64.signed r <? 0) || (Wasm_int.Int64.signed m <=? Wasm_int.Int64.signed r))))] H).
Proof.
 move=> Hr Hrn Hm Hmn Hp Hq Hi Hpres Hstable. rewrite /validation_item.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool (Wasm_int.Int64.signed m <? 1)))] H)); first reflexivity.
 - apply: (validation_low_sem Hm Hmn Hq Hi Hpres Hstable). unfold word,i64_min,i64_max; lia.
 - apply: (system_triple_seq (es1:=[::BI_if (BT_valtype (Some (T_num T_i32))) [::BI_const_num (SM.Vi32 1)] (validation_low rp idx tmp 0)])
   (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool ((Wasm_int.Int64.signed m <? 1) || (Wasm_int.Int64.signed r <? 0))))] H)); first reflexivity.
   + apply: batch_or. apply: (validation_low_sem Hr Hrn Hp Hi Hpres Hstable). unfold word,i64_min,i64_max; lia.
   + apply: batch_or. exact: (validation_high_sem Hr Hrn Hm Hmn Hp Hq Hi Hpres Hstable).
Qed.
End Host.
