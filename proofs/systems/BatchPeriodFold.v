From Coq Require Import ZArith NArith Lia List Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit MultiExitK NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTMath CRTSystemStatements CRTSystemArithmetic CRTFinite.
From CRTWasm Require Import CRTPublicExecution CRTContracts CRTGeneralArithmetic.
From CRTSystems Require Import ReadOnly SystemRuntime SystemMemory SystemControl SystemCalls FullWidthExecution MergeSolvePure.
From CRTSystems Require Import ArrayAccess BatchArithmetic BatchCount.
Module SM := CRTSystemGenerated.main.
Import FullWidth FiniteSystem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition bp_pin i c := term_eq (T_local i) (T_const c).
Definition BPBase rb mb count := (HA_and (bp_pin 0%num (SM.Vi32 (Z.of_N rb))) (HA_and (bp_pin 1%num (SM.Vi32 (Z.of_N mb))) (HA_and (bp_pin 2%num (SM.Vi32 (Z.of_nat count))) (HA_and (HA_defined (T_local 3%num)) (HA_and (HA_defined (T_local 4%num)) (HA_and (HA_defined (T_local 5%num)) (HA_and (HA_defined (T_local 6%num)) (HA_and (HA_defined (T_local 7%num)) (HA_and (HA_defined (T_local 8%num)) (HA_and (HA_defined (T_local 9%num)) (HA_and (HA_defined (T_local 10%num)) (HA_and (HA_defined (T_local 11%num)) (HA_and (HA_defined (T_local 12%num)) (HA_and (HA_defined (T_local 13%num)) (HA_and (HA_defined (T_local 14%num)) HA_true))))))))))))))).
Definition BPHead rb mb count i p := HA_and (bp_pin 5%num (SM.Vi32 (Z.of_nat i)))
 (HA_and (bp_pin 4%num (SM.Vi64 p)) (BPBase rb mb count)).
Definition BPG rb mb count i p m := HA_and (bp_pin 6%num (SM.Vi64 (Z.gcd p m))) (BPHead rb mb count i p).
Definition BPF rb mb count i p m := HA_and (bp_pin 7%num (SM.Vi64 (p/Z.gcd p m))) (BPG rb mb count i p m).
Definition BPExit rb mb count p := HA_and (bp_pin 4%num (SM.Vi64 p)) (BPBase rb mb count).
Definition bp_gcd_code := [::BI_local_get 4%num] ++ array_access 1%num 5%num 8%num ++ [::BI_call 0%num;BI_local_set 6%num].
Definition bp_factor_code := [::BI_local_get 4%num;BI_local_get 6%num;BI_binop T_i64 (Binop_i (BOI_div SX_S));BI_local_set 7%num].
Definition bp_guard_code := [::BI_local_get 7%num;BI_const_num (SM.Vi64 MAX)] ++ array_access 1%num 5%num 8%num ++
 [::BI_binop T_i64 (Binop_i (BOI_div SX_S));BI_relop T_i64 (Relop_i (ROI_gt SX_S))].
Definition bp_product_code := [::BI_local_get 7%num] ++ array_access 1%num 5%num 8%num ++ crt_general_checked_mul_code 12%num 13%num 14%num.
Definition bp_increment_code := [::BI_local_get 5%num;BI_const_num (SM.Vi32 1)] ++ batch_checked_add_code 9%num 10%num 11%num ++ [::BI_local_set 5%num].
Definition bp_loop_code := batch_loop_condition 5%num ++ [::BI_br_if 1%num] ++ bp_gcd_code ++ bp_factor_code ++ bp_guard_code ++
 [::BI_if (BT_valtype None) [::BI_const_num (SM.Vi64 (-3));BI_local_set 4%num;BI_br 2%num] [::]] ++
 bp_product_code ++ [::BI_local_set 4%num] ++ bp_increment_code ++ [::BI_br 0%num].
Lemma bp_loop_shape : List.nth 18 (modfunc_body SM.crt_system_period) BI_unreachable = BI_block (BT_valtype None) [::BI_loop (BT_valtype None) bp_loop_code].
Proof. reflexivity. Qed.
Definition bp_suffix (ms:seq i64) i fuel :=
 List.map (fun m:i64 => (0,Wasm_int.Int64.signed m)) (List.firstn fuel (List.skipn i ms)).
Lemma bp_suffix_zero ms i : bp_suffix ms i 0 = [::].
Proof. reflexivity. Qed.
Lemma bp_suffix_cons ms i fuel m : List.nth_error ms i = Some m ->
 bp_suffix ms i (S fuel) = (0,Wasm_int.Int64.signed m)::bp_suffix ms (S i) fuel.
Proof.
 move: ms. induction i as [|i IH]; move=> [|a ms] Hnth; try discriminate.
 - inversion Hnth; subst. reflexivity.
 - exact: IH Hnth.
Qed.
Lemma bp_period_fold_moduli C D p :
 List.map (@snd Z Z) C = List.map (@snd Z Z) D -> period_fold C p = period_fold D p.
Proof.
 move: D p. induction C as [|[a m] C IH]; move=> [|[b n] D] p E; try discriminate; first reflexivity.
 cbn in E. inversion E; subst n. cbn [period_fold].
 case: (MAX/m <? p/gcd_model p m); first reflexivity. apply: IH. assumption.
Qed.
Section Host.
Context `{ho:host}.
Context (mem:meminst).
Ltac unfold_bp := rewrite /BPF /BPG /BPHead /BPExit /BPBase /bp_pin.
Ltac bp_pinned := solve [exact: pinned_bare | apply: pinned_left; bp_pinned | apply: pinned_right; bp_pinned].
Ltac bp_present := solve [exact: loc_present_defined | exact: loc_present_pin | apply: loc_present_left; bp_present | apply: loc_present_right; bp_present].
Lemma bp_stable_true i c : loc_stable i c HA_true.
Proof. by []. Qed.
Ltac bp_stable := solve [exact: bp_stable_true | exact: loc_stable_defined_self | exact: loc_stable_pin_self | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other | apply: loc_stable_and; bp_stable].
Lemma bp_gcd_sem rb mb count ms i p m :
 array_region mem mb ms -> List.nth_error ms i = Some m -> moduli p (Wasm_int.Int64.signed m) ->
 system_triple mem (AS_base [::] (BPHead rb mb count i p)) bp_gcd_code
 (AS_base [::] (BPG rb mb count i p (Wasm_int.Int64.signed m))).
Proof.
 move=> Hr Hnth Hmod. rewrite /bp_gcd_code.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 p)] (BPHead rb mb count i p))); first reflexivity.
 - apply: system_triple_of_pure. apply: get_pinned_frame. unfold_bp. bp_pinned.
 - apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 p);T_const (VAL_int64 m)] (BPHead rb mb count i p))); first reflexivity.
   + apply: (batch_frame_consts (vf:=[::SM.Vi64 p])). apply: (array_access_sem Hr Hnth); unfold_bp; first [bp_pinned|bp_present|bp_stable].
   + apply: (system_triple_seq (es1:=[::BI_call 0%num]) (Q1:=AS_base [::T_const (SM.Vi64 (Z.gcd p (Wasm_int.Int64.signed m)))] (BPHead rb mb count i p))); first reflexivity.
     * rewrite -[VAL_int64 m]crt_contract_repr_signed. move=> f Hinst. exact: crt_gcd_call.
     * apply: system_triple_of_pure. apply: sem_local_set_const_frame; unfold_bp; [bp_stable|bp_present].
Qed.
Lemma bp_factor_sem rb mb count i p m : moduli p m ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (BPG rb mb count i p m)) bp_factor_code
 (AS_base [::] (BPF rb mb count i p m)).
Proof.
 move=> Hmod. have [Hp Hm] := Hmod. have [Hg _] := crt_period_intermediate_bounds Hmod.
 rewrite /bp_factor_code.
 apply: (sem_seq (es1:=[::BI_local_get 4%num]) (Q:=AS_base [::T_const (SM.Vi64 p)] (BPG rb mb count i p m))).
 - apply: get_pinned_frame. unfold_bp. bp_pinned.
 - apply: (sem_seq (es1:=[::BI_local_get 6%num]) (Q:=AS_base [::T_const (SM.Vi64 p);T_const (SM.Vi64 (Z.gcd p m))] (BPG rb mb count i p m))).
   + apply: get_pinned_frame. unfold_bp. bp_pinned.
   + apply: (sem_seq (es1:=[::BI_binop T_i64 (Binop_i (BOI_div SX_S))]) (Q:=AS_base [::T_const (SM.Vi64 (p/Z.gcd p m))] (BPG rb mb count i p m))).
     * apply: binop_consts; try reflexivity. apply: crt_i64_div_positive_exact; lia.
     * apply: sem_local_set_const_frame; unfold_bp; [bp_stable|bp_present].
Qed.
Lemma bp_guard_sem rb mb count ms i p m :
 array_region mem mb ms -> List.nth_error ms i = Some m -> moduli p (Wasm_int.Int64.signed m) ->
 system_triple mem (AS_base [::] (BPF rb mb count i p (Wasm_int.Int64.signed m))) bp_guard_code
 (AS_base [::T_const (VAL_int32 (wasm_bool (MAX/Wasm_int.Int64.signed m <? p/Z.gcd p (Wasm_int.Int64.signed m))))] (BPF rb mb count i p (Wasm_int.Int64.signed m))).
Proof.
 move=> Hr Hnth Hmod. have [Hp Hm] := Hmod.
 have [_ [Hfactor [Wfactor Wm]]] := crt_period_intermediate_bounds Hmod.
 have Hquot : 0 <= MAX/Wasm_int.Int64.signed m <= MAX.
 { split; [apply Z.div_pos; unfold MAX,i64_max in *; lia|apply Z.div_le_upper_bound; unfold MAX,i64_max in *; nia]. }
 have Wquot := nonnegative_word _ Hquot.
 rewrite /bp_guard_code.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 (p/Z.gcd p (Wasm_int.Int64.signed m)));T_const (SM.Vi64 MAX)] (BPF rb mb count i p (Wasm_int.Int64.signed m)))); first reflexivity.
 - apply: system_triple_of_pure. apply: (sem_seq (es1:=[::BI_local_get 7%num])
   (Q:=AS_base [::T_const (SM.Vi64 (p/Z.gcd p (Wasm_int.Int64.signed m)))] (BPF rb mb count i p (Wasm_int.Int64.signed m)))).
   + apply: get_pinned_frame. unfold_bp. bp_pinned.
   + exact: sem_const_framed.
 - apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 (p/Z.gcd p (Wasm_int.Int64.signed m)));T_const (SM.Vi64 MAX);T_const (VAL_int64 m)] (BPF rb mb count i p (Wasm_int.Int64.signed m)))); first reflexivity.
   + apply: (batch_frame_consts (vf:=[::SM.Vi64 (p/Z.gcd p (Wasm_int.Int64.signed m));SM.Vi64 MAX])). apply: (array_access_sem Hr Hnth); unfold_bp; first [bp_pinned|bp_present|bp_stable].
   + rewrite -[VAL_int64 m]crt_contract_repr_signed. apply: system_triple_of_pure.
     apply: (sem_seq (es1:=[::BI_binop T_i64 (Binop_i (BOI_div SX_S))])
     (Q:=AS_base [::T_const (SM.Vi64 (p/Z.gcd p (Wasm_int.Int64.signed m)));T_const (SM.Vi64 (MAX/Wasm_int.Int64.signed m))] (BPF rb mb count i p (Wasm_int.Int64.signed m)))).
     * apply: (sem_frame_consts (vf:=[::SM.Vi64 (p/Z.gcd p (Wasm_int.Int64.signed m))])).
       apply: binop_consts; try reflexivity. apply: crt_i64_div_positive_exact; [unfold MAX,i64_max; lia|exact Hm].
     * rewrite -(crt_public_gt Wfactor Wquot). apply: relop_consts; reflexivity.
Qed.
Lemma bp_checked_mul_Z G H x y :
  loc_stable 12%num (SM.Vi64 x) H -> loc_stable 13%num (SM.Vi64 y) H ->
  loc_stable 14%num (SM.Vi64 (x * y)) H ->
  loc_present 12%num H -> loc_present 13%num H -> loc_present 14%num H ->
  word x -> word y -> word (x * y) ->
  sem_triple G (AS_base [:: T_const (SM.Vi64 x); T_const (SM.Vi64 y)] H)
    (crt_general_checked_mul_code 12%num 13%num 14%num) (AS_base [:: T_const (SM.Vi64 (x * y))] H).
Proof.
  move=> SA SB SR PA PB PR Wx Wy Wxy.
  have E := crt_i64_mul_repr Wx Wy.
  have Range : Wasm_int.Int64.min_signed <=
    Wasm_int.Int64.signed (Wasm_int.Int64.repr x) *
    Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy)
      i64_min_signed_val i64_max_signed_val. exact Wxy. }
  have SR' : loc_stable 14%num (VAL_int64
    (Wasm_int.Int64.mul (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y))) H.
  { rewrite E. exact SR. }
  have P := crt_general_checked_mul_sem (ia := 12%num) (ib := 13%num) (ir := 14%num) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) SA SB SR' PA PB PR Range.
  rewrite E in P. exact: P.
Qed.
Lemma bp_product_sem rb mb count ms i p m :
 array_region mem mb ms -> List.nth_error ms i = Some m -> moduli p (Wasm_int.Int64.signed m) ->
 p/Z.gcd p (Wasm_int.Int64.signed m) <= MAX/Wasm_int.Int64.signed m ->
 system_triple mem (AS_base [::] (BPF rb mb count i p (Wasm_int.Int64.signed m))) bp_product_code
 (AS_base [::T_const (SM.Vi64 ((p/Z.gcd p (Wasm_int.Int64.signed m))*Wasm_int.Int64.signed m))] (BPF rb mb count i p (Wasm_int.Int64.signed m))).
Proof.
 move=> Hr Hnth Hmod Hsafe. have [Hp Hm] := Hmod.
 have [_ [Hfactor [Wfactor Wm]]] := crt_period_intermediate_bounds Hmod.
 have Hbound : 0 <= (p/Z.gcd p (Wasm_int.Int64.signed m))*Wasm_int.Int64.signed m <= MAX.
 { have Hdiv := Z.mul_div_le MAX (Wasm_int.Int64.signed m) ltac:(lia). nia. }
 have Wprod := nonnegative_word _ Hbound.
 rewrite /bp_product_code.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 (p/Z.gcd p (Wasm_int.Int64.signed m)))] (BPF rb mb count i p (Wasm_int.Int64.signed m)))); first reflexivity.
 - apply: system_triple_of_pure. apply: get_pinned_frame. unfold_bp. bp_pinned.
 - apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 (p/Z.gcd p (Wasm_int.Int64.signed m)));T_const (VAL_int64 m)] (BPF rb mb count i p (Wasm_int.Int64.signed m)))); first reflexivity.
   + apply: (batch_frame_consts (vf:=[::SM.Vi64 (p/Z.gcd p (Wasm_int.Int64.signed m))])). apply: (array_access_sem Hr Hnth); unfold_bp; first [bp_pinned|bp_present|bp_stable].
   + rewrite -[VAL_int64 m]crt_contract_repr_signed. apply: system_triple_of_pure.
     apply: bp_checked_mul_Z; try assumption; unfold_bp; first [bp_stable|bp_present].
Qed.
Lemma bp_set_period G rb mb count i old p :
 sem_triple G (AS_base [::T_const (SM.Vi64 p)] (BPHead rb mb count i old))
 [::BI_local_set 4%num] (AS_base [::] (BPHead rb mb count i p)).
Proof.
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi64 p)]
 (HA_and (bp_pin 5%num (SM.Vi32 (Z.of_nat i))) (BPBase rb mb count)))
 (Q':=AS_base [::] (HA_and (bp_pin 4%num (SM.Vi64 p))
 (HA_and (bp_pin 5%num (SM.Vi32 (Z.of_nat i))) (BPBase rb mb count))))).
 - move=> V [vs h] /= [Hs [Hi [_ HB]]]. by split; [|split].
 - move=> V [vs h] /= [Hs [Hp [Hi HB]]]. by split; [|split; [|split]].
 - apply: sem_local_set_const_frame; unfold_bp; [bp_stable|bp_present].
Qed.
Lemma bp_set_index G rb mb count i j p :
 sem_triple G (AS_base [::T_const (SM.Vi32 (Z.of_nat j))] (BPHead rb mb count i p))
 [::BI_local_set 5%num] (AS_base [::] (BPHead rb mb count j p)).
Proof.
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi32 (Z.of_nat j))] (BPExit rb mb count p))
 (Q':=AS_base [::] (BPHead rb mb count j p))); try by [].
 - move=> V [vs h] /= [Hs [_ Hrest]]. by split.
 - apply: sem_local_set_const_frame; unfold_bp; [bp_stable|bp_present].
Qed.
Lemma bp_increment_sem rb mb count i p : (i<16)%coq_nat ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (BPHead rb mb count i p)) bp_increment_code
 (AS_base [::] (BPHead rb mb count (S i) p)).
Proof.
 move=> Hi. have Wi : batch_word32 (Z.of_nat i) by unfold batch_word32; lia.
 have Wone : batch_word32 1 by unfold batch_word32; lia.
 have Wsum : batch_word32 (Z.of_nat i+1) by unfold batch_word32; lia.
 rewrite /bp_increment_code.
 apply: (sem_seq (Q:=AS_base [::T_const (SM.Vi32 (Z.of_nat i));T_const (SM.Vi32 1)] (BPHead rb mb count i p))).
 - apply: (sem_seq (es1:=[::BI_local_get 5%num]) (Q:=AS_base [::T_const (SM.Vi32 (Z.of_nat i))] (BPHead rb mb count i p))).
   + apply: get_pinned_frame. unfold_bp. bp_pinned.
   + exact: sem_const_framed.
 - apply: (sem_seq (Q:=AS_base [::T_const (SM.Vi32 (Z.of_nat i+1))] (BPHead rb mb count i p))).
   + apply: (batch_checked_add_Z (ia:=9%num) (ib:=10%num) (ir:=11%num)); try discriminate; try assumption; unfold_bp; first [bp_stable|bp_present].
   + replace (Z.of_nat i+1) with (Z.of_nat (S i)) by lia. exact: bp_set_index.
Qed.
Lemma bp_initialize_sem G rb mb count :
 sem_triple G (AS_base [::] (BPBase rb mb count))
 [::BI_const_num (SM.Vi64 1);BI_local_set 4%num;BI_const_num (SM.Vi32 0);BI_local_set 5%num]
 (AS_base [::] (BPHead rb mb count 0%nat 1)).
Proof.
 apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 1)]) (Q:=AS_base [::T_const (SM.Vi64 1)] (BPBase rb mb count))); first exact: sem_const_framed.
 apply: (sem_seq (es1:=[::BI_local_set 4%num]) (Q:=AS_base [::] (BPExit rb mb count 1))).
 - apply: sem_local_set_const_frame; unfold_bp; [bp_stable|bp_present].
 - apply: (sem_seq (es1:=[::BI_const_num (SM.Vi32 0)]) (Q:=AS_base [::T_const (SM.Vi32 0)] (BPExit rb mb count 1))); first exact: sem_const_framed.
   apply: sem_local_set_const_frame; unfold_bp; [bp_stable|bp_present].
Qed.
Lemma bp_drop_factor S rb mb count i p m :
 aentails (AS_base S (BPF rb mb count i p m)) (AS_base S (BPHead rb mb count i p)).
Proof. move=> V [vs h] /= [Hs [_ [_ HH]]]. by split. Qed.
Lemma bp_drop_index S rb mb count i p :
 aentails (AS_base S (BPHead rb mb count i p)) (AS_base S (BPExit rb mb count p)).
Proof. move=> V [vs h] /= [Hs [_ HH]]. by split. Qed.
Lemma bp_update_sem rb mb count ms i p m :
 array_region mem mb ms -> List.nth_error ms i = Some m -> moduli p (Wasm_int.Int64.signed m) ->
 (i<16)%coq_nat -> p/Z.gcd p (Wasm_int.Int64.signed m) <= MAX/Wasm_int.Int64.signed m ->
 system_triple mem (AS_base [::] (BPF rb mb count i p (Wasm_int.Int64.signed m)))
 (bp_product_code ++ [::BI_local_set 4%num] ++ bp_increment_code)
 (AS_base [::] (BPHead rb mb count (S i) ((p/Z.gcd p (Wasm_int.Int64.signed m))*Wasm_int.Int64.signed m))).
Proof.
 move=> Hr Hnth Hmod Hi Hsafe.
 apply: (system_triple_seq (Q1:=AS_base [::T_const (SM.Vi64 ((p/Z.gcd p (Wasm_int.Int64.signed m))*Wasm_int.Int64.signed m))] (BPF rb mb count i p (Wasm_int.Int64.signed m)))); first reflexivity.
 - exact: (bp_product_sem Hr Hnth Hmod Hsafe).
 - apply: (system_triple_seq (Q1:=AS_base [::] (BPHead rb mb count i ((p/Z.gcd p (Wasm_int.Int64.signed m))*Wasm_int.Int64.signed m)))); first reflexivity.
   + apply: system_triple_of_pure. apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi64 ((p/Z.gcd p (Wasm_int.Int64.signed m))*Wasm_int.Int64.signed m))] (BPHead rb mb count i p)) (Q':=AS_base [::] (BPHead rb mb count i ((p/Z.gcd p (Wasm_int.Int64.signed m))*Wasm_int.Int64.signed m)))); [exact: bp_drop_factor|by []|exact: bp_set_period].
   + apply: system_triple_of_pure. exact: bp_increment_sem.
Qed.
Lemma bp_loop_stopped rb mb count p : (count<=16)%coq_nat ->
 system_mxk mem (AS_base [::] (BPHead rb mb count count p))
 [::BI_loop (BT_valtype None) bp_loop_code]
 (AS_base [::] (BPExit rb mb count p)) crt_false_assert
 (fun k => if k is 0%nat then AS_base [::] (BPExit rb mb count p) else crt_false_assert).
Proof.
 move=> Hcount.
 apply: (system_loop_unroll (Pback:=crt_false_assert) (t1s:=[::]) (t2s:=[::])); try reflexivity.
 - move=> V vs h [Hs _]. by case: Hs => <-.
 - move=> V vs h [_ HF]. by case: HF.
 - rewrite /bp_loop_code.
   apply: (system_mxk_seq (es1:=batch_loop_condition 5%num)
   (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (BPHead rb mb count count p))); first reflexivity.
   + apply: system_mxk_lift. apply: system_triple_of_pure.
     have Wc : batch_word32 (Z.of_nat count) by unfold batch_word32; lia.
     have H := batch_loop_condition_sem (G:=triv_ctx SM.main) (H:=BPHead rb mb count count p) (idx:=5%num) Wc Wc ltac:(unfold_bp; bp_pinned) ltac:(unfold_bp; bp_pinned).
     by rewrite Z.ltb_irrefl in H.
   + apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=crt_false_assert)); first reflexivity.
     * apply: system_mxk_of_pure. apply: (crt_br_if_true_sem (k:=1%nat)). exact: bp_drop_index.
     * apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
 - apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
Qed.
Lemma bp_prepare_sem rb mb count ms i p m :
 array_region mem mb ms -> List.nth_error ms i = Some m -> moduli p (Wasm_int.Int64.signed m) ->
 system_triple mem (AS_base [::] (BPHead rb mb count i p))
 (bp_gcd_code ++ bp_factor_code ++ bp_guard_code)
 (AS_base [::T_const (VAL_int32 (wasm_bool (MAX/Wasm_int.Int64.signed m <? p/Z.gcd p (Wasm_int.Int64.signed m))))] (BPF rb mb count i p (Wasm_int.Int64.signed m))).
Proof.
 move=> Hr Hnth Hmod.
 apply: (system_triple_seq (Q1:=AS_base [::] (BPG rb mb count i p (Wasm_int.Int64.signed m)))); first reflexivity.
 - exact: (bp_gcd_sem Hr Hnth Hmod).
 - apply: (system_triple_seq (Q1:=AS_base [::] (BPF rb mb count i p (Wasm_int.Int64.signed m)))); first reflexivity.
   + apply: system_triple_of_pure. exact: bp_factor_sem.
   + exact: (bp_guard_sem Hr Hnth Hmod).
Qed.
Lemma bp_overflow_branch rb mb count i p m Qn Qr Qb :
 aentails (AS_base [::] (BPExit rb mb count (-3))) (Qb 2%nat) ->
 system_mxk mem (AS_base [::] (BPF rb mb count i p m))
 [::BI_const_num (SM.Vi64 (-3));BI_local_set 4%num;BI_br 2%num] Qn Qr Qb.
Proof.
 move=> HQ.
 apply: (system_mxk_conseq (P':=AS_base [::] (BPHead rb mb count i p)) (Qn':=Qn) (Qr':=Qr) (Qb':=Qb)).
 - exact: bp_drop_factor.
 - by [].
 - by [].
 - by move=> k.
 - apply: (system_mxk_seq (es1:=[::BI_const_num (SM.Vi64 (-3))])
   (Q1:=AS_base [::T_const (SM.Vi64 (-3))] (BPHead rb mb count i p))); first reflexivity.
   + apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_const_framed.
   + apply: (system_mxk_seq (es1:=[::BI_local_set 4%num])
     (Q1:=AS_base [::] (BPHead rb mb count i (-3)))); first reflexivity.
     * apply: system_mxk_lift. apply: system_triple_of_pure. exact: bp_set_period.
     * apply: system_mxk_of_pure. apply: (sem_mxk_br_k (k:=2%nat)).
       move=> V st H. apply: HQ. exact: (bp_drop_index H).
Qed.
Lemma bp_loop_exec fuel rb mb count ms i p :
 array_region mem mb ms -> (count<=16)%coq_nat -> (i+fuel=count)%coq_nat ->
 (forall j m, (j<count)%coq_nat -> List.nth_error ms j = Some m -> 1<=Wasm_int.Int64.signed m<=MAX) ->
 1<=p<=MAX ->
 system_mxk mem (AS_base [::] (BPHead rb mb count i p))
 [::BI_loop (BT_valtype None) bp_loop_code]
 (AS_base [::] (BPExit rb mb count (period_fold (bp_suffix ms i fuel) p))) crt_false_assert
 (fun k => if k is 0%nat then AS_base [::] (BPExit rb mb count (period_fold (bp_suffix ms i fuel) p)) else crt_false_assert).
Proof.
 move: i p. induction fuel as [|fuel IH]; move=> i p Hr Hcount Hfuel Hvalid Hp.
 - have Ei : i=count by lia. subst i. rewrite bp_suffix_zero. exact: bp_loop_stopped.
 - have Hi : (i<count)%coq_nat by lia.
   have Hi16 : (i<16)%coq_nat by lia.
   have Hlen : List.length ms = 16%nat.
   { have H := proj1 Hr. by rewrite length_is_size. }
   have [m Hnth] : exists m, List.nth_error ms i = Some m.
   { destruct (List.nth_error ms i) as [m|] eqn:E; first by exists m.
     apply List.nth_error_None in E. lia. }
   have Hm := Hvalid i m Hi Hnth.
   have Hmod : moduli p (Wasm_int.Int64.signed m) := conj Hp Hm.
   rewrite (bp_suffix_cons fuel Hnth). cbn [period_fold]. rewrite (gcd_model_proved p (Wasm_int.Int64.signed m) Hmod).
   have Wi : batch_word32 (Z.of_nat i) by unfold batch_word32; lia.
   have Wcount : batch_word32 (Z.of_nat count) by unfold batch_word32; lia.
   have Econd : negb (Z.of_nat i <? Z.of_nat count) = false by apply negb_false_iff; apply Z.ltb_lt; lia.
   have Hcond : sem_triple (triv_ctx SM.main) (AS_base [::] (BPHead rb mb count i p))
     (batch_loop_condition 5%num)
     (AS_base [::T_const (VAL_int32 (wasm_bool false))] (BPHead rb mb count i p)).
   { have H := batch_loop_condition_sem (G:=triv_ctx SM.main) (H:=BPHead rb mb count i p) (idx:=5%num) Wi Wcount ltac:(unfold_bp;bp_pinned) ltac:(unfold_bp;bp_pinned). by rewrite Econd in H. }
   case Eover : (MAX/Wasm_int.Int64.signed m <? p/Z.gcd p (Wasm_int.Int64.signed m)).
   + apply: (system_loop_unroll (Pback:=crt_false_assert) (t1s:=[::]) (t2s:=[::])); try reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * move=> V vs h [_ HF]. by case: HF.
     * rewrite /bp_loop_code.
       apply: (system_mxk_seq (es1:=batch_loop_condition 5%num)
       (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BPHead rb mb count i p))); first reflexivity.
       -- apply: system_mxk_lift. exact: system_triple_of_pure.
       -- apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=AS_base [::] (BPHead rb mb count i p))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: crt_br_if_false_sem.
          ++ apply: (system_mxk_seq (es1:=bp_gcd_code ++ bp_factor_code ++ bp_guard_code)
             (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (BPF rb mb count i p (Wasm_int.Int64.signed m)))); first reflexivity.
             ** apply: system_mxk_lift. have H := bp_prepare_sem Hr Hnth Hmod. by rewrite Eover in H.
             ** apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_const_num (SM.Vi64 (-3));BI_local_set 4%num;BI_br 2%num] [::]]) (Q1:=crt_false_assert)); first reflexivity.
                --- apply: (system_if_const (b:=true) (t2s:=[::])); first reflexivity.
                    +++ move=> V vs h [_ HF]. by case: HF.
                    +++ apply: bp_overflow_branch. by [].
                --- apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
     * apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
   + have Hsafe : p/Z.gcd p (Wasm_int.Int64.signed m) <= MAX/Wasm_int.Int64.signed m by apply Z.ltb_ge.
     have Hnew : 1 <= (p/Z.gcd p (Wasm_int.Int64.signed m))*Wasm_int.Int64.signed m <= MAX.
     { have [_ [Hfactor _]] := crt_period_intermediate_bounds Hmod.
       have Hdiv := Z.mul_div_le MAX (Wasm_int.Int64.signed m) ltac:(lia). nia. }
     apply: (system_loop_unroll
       (Pback:=AS_base [::] (BPHead rb mb count (S i) ((p/Z.gcd p (Wasm_int.Int64.signed m))*Wasm_int.Int64.signed m)))
       (t1s:=[::]) (t2s:=[::])); try reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * rewrite /bp_loop_code.
       apply: (system_mxk_seq (es1:=batch_loop_condition 5%num)
       (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BPHead rb mb count i p))); first reflexivity.
       -- apply: system_mxk_lift. exact: system_triple_of_pure.
       -- apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=AS_base [::] (BPHead rb mb count i p))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: crt_br_if_false_sem.
          ++ apply: (system_mxk_seq (es1:=bp_gcd_code ++ bp_factor_code ++ bp_guard_code)
             (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (BPF rb mb count i p (Wasm_int.Int64.signed m)))); first reflexivity.
             ** apply: system_mxk_lift. have H := bp_prepare_sem Hr Hnth Hmod. by rewrite Eover in H.
             ** apply: (system_mxk_seq (es1:=[::BI_if (BT_valtype None) [::BI_const_num (SM.Vi64 (-3));BI_local_set 4%num;BI_br 2%num] [::]]) (Q1:=AS_base [::] (BPF rb mb count i p (Wasm_int.Int64.signed m)))); first reflexivity.
                --- apply: system_mxk_lift. apply: system_triple_of_pure. apply: guard_if_false. exact: sem_nil_same.
                --- apply: (system_mxk_seq (es1:=bp_product_code ++ [::BI_local_set 4%num] ++ bp_increment_code)
                    (Q1:=AS_base [::] (BPHead rb mb count (S i) ((p/Z.gcd p (Wasm_int.Int64.signed m))*Wasm_int.Int64.signed m)))); first reflexivity.
                    +++ apply: system_mxk_lift. exact: (bp_update_sem Hr Hnth Hmod Hi16 Hsafe).
                    +++ apply: system_mxk_of_pure. apply: (sem_mxk_br_k (k:=0%nat)). by [].
     * apply: IH; try assumption. lia.
Qed.
Lemma bp_block_exec rb mb count ms i p :
 array_region mem mb ms -> (count<=16)%coq_nat -> (i<=count)%coq_nat ->
 (forall j m, (j<count)%coq_nat -> List.nth_error ms j = Some m -> 1<=Wasm_int.Int64.signed m<=MAX) ->
 1<=p<=MAX ->
 system_triple mem (AS_base [::] (BPHead rb mb count i p))
 [::BI_block (BT_valtype None) [::BI_loop (BT_valtype None) bp_loop_code]]
 (AS_base [::] (BPExit rb mb count (period_fold (bp_suffix ms i (Nat.sub count i)) p))).
Proof.
 move=> Hr Hcount Hi Hvalid Hp. apply: system_triple_of_mxk.
 apply: (system_mxk_block (t1s:=[::]) (t2s:=[::])
 (Qb:=fun k => if k is 0%nat then AS_base [::] (BPExit rb mb count (period_fold (bp_suffix ms i (Nat.sub count i)) p)) else crt_false_assert)); try reflexivity.
 - move=> V vs h [Hs _]. by case: Hs => <-.
 - apply: (bp_loop_exec (ms:=ms)); try assumption. lia.
Qed.
End Host.
