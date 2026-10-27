(* Finite execution of the exact repeated-doubling Wasm loop. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit
 MultiExitK NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTSystemStatements CRTSystemArithmetic.
From CRTWasm Require Import CRTContracts.
From CRTSystems Require Import ReadOnly SystemRuntime FullWidthExecution SystemCalls SystemControl MulLoopState FullWidthInverseExecution.
Module SM := CRTSystemGenerated.main.
Import FullWidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition mpin i z := term_eq (T_local i) (T_const (SM.Vi64 z)).
Definition MulHead d a f r := HA_and (mpin 2%num d)
 (HA_and (mpin 3%num a) (HA_and (mpin 4%num f) (mpin 5%num r))).
Definition MulState d e := MulHead d (acc e) (factor e) (remaining e).
Definition mul_condition := [:: BI_local_get 5%num; BI_const_num (SM.Vi64 0);
 BI_relop T_i64 (Relop_i (ROI_gt SX_S)); BI_testop T_i32 TO_eqz].
Definition mul_odd := [:: BI_local_get 5%num; BI_const_num (SM.Vi64 2);
 BI_binop T_i64 (Binop_i (BOI_rem SX_S)); BI_const_num (SM.Vi64 1);
 BI_relop T_i64 (Relop_i ROI_eq)].
Definition mul_add := [::BI_local_get 3%num;BI_local_get 4%num;BI_local_get 2%num;
 BI_call 3%num;BI_local_set 3%num].
Definition mul_half := [:: BI_local_get 5%num;BI_const_num (SM.Vi64 2);
 BI_binop T_i64 (Binop_i (BOI_div SX_S));BI_local_set 5%num].
Definition mul_double := [::BI_local_get 4%num;BI_local_get 4%num;BI_local_get 2%num;
 BI_call 3%num;BI_local_set 4%num].
Definition mul_update := mul_odd ++ [::BI_if (BT_valtype None) mul_add [::]] ++ mul_half ++ mul_double.
Definition mul_loop_code := mul_condition ++ [::BI_br_if 1%num] ++ mul_update ++ [::BI_br 0%num].
Definition mul_prologue := [::BI_const_num (SM.Vi64 0);BI_local_set 3%num;
 BI_local_get 0%num;BI_local_set 4%num;BI_local_get 1%num;BI_local_set 5%num].
Lemma mul_body_shape : modfunc_body SM.mul_mod = mul_prologue ++
 [::BI_block (BT_valtype None) [::BI_loop (BT_valtype None) mul_loop_code]] ++
 [::BI_local_get 3%num;BI_return;BI_unreachable].
Proof. reflexivity. Qed.
Section Host.
Context `{ho : host}.
Context (mem : meminst).
Ltac pinned_tac := solve [exact: pinned_bare | apply: pinned_left; pinned_tac | apply: pinned_right; pinned_tac].
Ltac present_tac := solve [exact: loc_present_defined | exact: loc_present_pin | apply: loc_present_left; present_tac | apply: loc_present_right; present_tac].
Ltac stable_tac := solve [exact: loc_stable_defined_self | exact: loc_stable_pin_self | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other | apply: loc_stable_and; stable_tac].

Ltac crt_heap_from HH :=
  lazymatch type of HH with
  | hassert_denote ?V ?H ?h =>
    lazymatch goal with
    | |- hassert_denote V (HA_and ?P ?Q) h =>
        split; crt_heap_from HH
    | |- hassert_denote V (HA_defined (T_local ?i)) h =>
        let Hp := fresh "Hp" in
        assert (Hp : loc_present i H) by present_tac;
        exact (Hp V h HH)
    | |- hassert_denote V (term_eq (T_local ?i) (T_const ?c)) h =>
        let Hp := fresh "Hp" in
        assert (Hp : pinned i c H) by pinned_tac;
        exists c; split; first exact (Hp V h HH); reflexivity
    end
  end.

Lemma mul_set_a d a f r v :
 sem_triple (triv_ctx SM.main)
 (AS_base [::T_const (SM.Vi64 v)] (MulHead d a f r)) [::BI_local_set 3%num]
 (AS_base [::] (MulHead d v f r)).
Proof.
 pose H := HA_and (mpin 2%num d) (HA_and (HA_defined (T_local 3%num)) (HA_and (mpin 4%num f) (mpin 5%num r))).
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi64 v)] H)
 (Q':=AS_base [::] (HA_and (mpin 3%num v) H))).
 - rewrite /MulHead /H /mpin. move=> V [vs h] [Hs HH]. split; first exact Hs. crt_heap_from HH.
 - rewrite /MulHead /H /mpin. move=> V [vs h] [Hs HH]. split; first exact Hs. crt_heap_from HH.
 - rewrite /H /mpin. apply: sem_local_set_const_frame; [stable_tac|present_tac].
Qed.
Lemma mul_set_f d a f r v :
 sem_triple (triv_ctx SM.main)
 (AS_base [::T_const (SM.Vi64 v)] (MulHead d a f r)) [::BI_local_set 4%num]
 (AS_base [::] (MulHead d a v r)).
Proof.
 pose H := HA_and (mpin 2%num d) (HA_and (mpin 3%num a) (HA_and (HA_defined (T_local 4%num)) (mpin 5%num r))).
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi64 v)] H)
 (Q':=AS_base [::] (HA_and (mpin 4%num v) H))).
 - rewrite /MulHead /H /mpin. move=> V [vs h] [Hs HH]. split; first exact Hs. crt_heap_from HH.
 - rewrite /MulHead /H /mpin. move=> V [vs h] [Hs HH]. split; first exact Hs. crt_heap_from HH.
 - rewrite /H /mpin. apply: sem_local_set_const_frame; [stable_tac|present_tac].
Qed.
Lemma mul_set_r d a f r v :
 sem_triple (triv_ctx SM.main)
 (AS_base [::T_const (SM.Vi64 v)] (MulHead d a f r)) [::BI_local_set 5%num]
 (AS_base [::] (MulHead d a f v)).
Proof.
 pose H := HA_and (mpin 2%num d) (HA_and (mpin 3%num a) (HA_and (mpin 4%num f) (HA_defined (T_local 5%num)))).
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi64 v)] H)
 (Q':=AS_base [::] (HA_and (mpin 5%num v) H))).
 - rewrite /MulHead /H /mpin. move=> V [vs h] [Hs HH]. split; first exact Hs. crt_heap_from HH.
 - rewrite /MulHead /H /mpin. move=> V [vs h] [Hs HH]. split; first exact Hs. crt_heap_from HH.
 - rewrite /H /mpin. apply: sem_local_set_const_frame; [stable_tac|present_tac].
Qed.
Definition MulEntry x y d := HA_and (mpin 0%num x) (HA_and (mpin 1%num y)
 (HA_and (mpin 2%num d) (HA_and (HA_defined (T_local 3%num))
 (HA_and (HA_defined (T_local 4%num)) (HA_defined (T_local 5%num)))))).
Lemma mul_prologue_sem x y d :
 sem_triple (triv_ctx SM.main) (AS_base [::] (MulEntry x y d)) mul_prologue
 (AS_base [::] (MulHead d 0 x y)).
Proof.
 rewrite /mul_prologue.
 apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 0)])
 (Q:=AS_base [::T_const (SM.Vi64 0)] (MulEntry x y d))); first exact: sem_const_framed.
 apply: (sem_seq (es1:=[::BI_local_set 3%num])
 (Q:=AS_base [::] (HA_and (mpin 3%num 0) (MulEntry x y d)))).
 - rewrite /MulEntry /mpin. apply: sem_local_set_const_frame; [stable_tac|present_tac].
 - apply: (sem_seq (es1:=[::BI_local_get 0%num])
   (Q:=AS_base [::T_const (SM.Vi64 x)] (HA_and (mpin 3%num 0) (MulEntry x y d)))).
   + apply: get_pinned_frame. rewrite /MulEntry /mpin. pinned_tac.
   + apply: (sem_seq (es1:=[::BI_local_set 4%num])
     (Q:=AS_base [::] (HA_and (mpin 4%num x) (HA_and (mpin 3%num 0) (MulEntry x y d))))).
     * rewrite /MulEntry /mpin. apply: sem_local_set_const_frame; [stable_tac|present_tac].
     * apply: (sem_seq (es1:=[::BI_local_get 1%num])
       (Q:=AS_base [::T_const (SM.Vi64 y)] (HA_and (mpin 4%num x) (HA_and (mpin 3%num 0) (MulEntry x y d))))).
       -- apply: get_pinned_frame. rewrite /MulEntry /mpin. pinned_tac.
       -- apply: (sem_conseq
          (P':=AS_base [::T_const (SM.Vi64 y)] (HA_and (mpin 4%num x) (HA_and (mpin 3%num 0) (MulEntry x y d))))
          (Q':=AS_base [::] (HA_and (mpin 5%num y) (HA_and (mpin 4%num x) (HA_and (mpin 3%num 0) (MulEntry x y d)))))).
          ++ by [].
          ++ rewrite /MulHead /MulEntry /mpin. move=> V [vs h] [Hs HH]. split; first exact Hs. crt_heap_from HH.
          ++ rewrite /MulEntry /mpin. apply: sem_local_set_const_frame; [stable_tac|present_tac].
Qed.
Lemma mul_condition_sem d a f r : word r ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (MulHead d a f r)) mul_condition
 (AS_base [::T_const (VAL_int32 (wasm_bool (negb (0 <? r))))] (MulHead d a f r)).
Proof.
 move=> Wr. rewrite /mul_condition.
 apply: (sem_seq (es1:=[::BI_local_get 5%num;BI_const_num (SM.Vi64 0);
 BI_relop T_i64 (Relop_i (ROI_gt SX_S))])
 (Q:=AS_base [::T_const (VAL_int32 (wasm_bool (0 <? r)))] (MulHead d a f r))).
 - rewrite -(crt_i64_gt_zero Wr). apply: test_pin_const; try reflexivity.
   rewrite /MulHead /mpin. pinned_tac.
 - exact: crt_eqz_bool_sem.
Qed.
Lemma mul_odd_sem d a f r : 0 <= r <= MAX ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (MulHead d a f r)) mul_odd
 (AS_base [::T_const (VAL_int32 (wasm_bool (r mod 2 =? 1)))] (MulHead d a f r)).
Proof.
 move=> Hr. have Wr : word r by apply nonnegative_word.
 have Htwo : 1 <= 2 <= MAX by unfold MAX,i64_max; lia.
 have Erem := crt_i64_rem_exact Wr Htwo.
 rewrite (Z.rem_mod_nonneg r 2 ltac:(lia) ltac:(lia)) in Erem.
 rewrite /mul_odd.
 apply: (sem_seq (es1:=[::BI_local_get 5%num;BI_const_num (SM.Vi64 2)])
 (Q:=AS_base [::T_const (SM.Vi64 r);T_const (SM.Vi64 2)] (MulHead d a f r))).
 - apply: (sem_seq (es1:=[::BI_local_get 5%num])
   (Q:=AS_base [::T_const (SM.Vi64 r)] (MulHead d a f r))).
   + apply: get_pinned_frame. rewrite /MulHead /mpin. pinned_tac.
   + exact: sem_const_framed.
 - apply: (sem_seq (es1:=[::BI_binop T_i64 (Binop_i (BOI_rem SX_S))])
   (Q:=AS_base [::T_const (SM.Vi64 (r mod 2))] (MulHead d a f r))).
   + apply: binop_consts; try reflexivity. exact Erem.
   + apply: (sem_seq (es1:=[::BI_const_num (SM.Vi64 1)])
     (Q:=AS_base [::T_const (SM.Vi64 (r mod 2));T_const (SM.Vi64 1)] (MulHead d a f r))).
     * exact: sem_const_framed.
     * have Wrem : word (r mod 2).
       { apply nonnegative_word. have := Z.mod_pos_bound r 2 ltac:(lia). unfold MAX,i64_max; lia. }
       have Wone : word 1 by unfold word,i64_min,i64_max; lia.
       have E : app_relop (Relop_i ROI_eq) (SM.Vi64 (r mod 2)) (SM.Vi64 1) = (r mod 2 =? 1).
       { rewrite /SM.Vi64 crt_contract_eq (crt_i64_signed_repr Wrem) (crt_i64_signed_repr Wone). reflexivity. }
       rewrite -E. apply: relop_consts; reflexivity.
Qed.
Lemma mul_add_sem d a f r : 1 <= d <= MAX -> 0 <= a < d -> 0 <= f < d ->
 system_triple mem (AS_base [::] (MulHead d a f r)) mul_add
 (AS_base [::] (MulHead d (add_mod a f d) f r)).
Proof.
 move=> Hd Ha Hf. rewrite /mul_add.
 apply: (system_triple_seq (es1:=[::BI_local_get 3%num;BI_local_get 4%num;BI_local_get 2%num])
 (Q1:=AS_base [::T_const (SM.Vi64 a);T_const (SM.Vi64 f);T_const (SM.Vi64 d)] (MulHead d a f r))); first reflexivity.
 - apply: system_triple_of_pure.
   apply: (sem_seq (es1:=[::BI_local_get 3%num])
   (Q:=AS_base [::T_const (SM.Vi64 a)] (MulHead d a f r))).
   + apply: get_pinned_frame. rewrite /MulHead /mpin. pinned_tac.
   + apply: (sem_seq (es1:=[::BI_local_get 4%num])
     (Q:=AS_base [::T_const (SM.Vi64 a);T_const (SM.Vi64 f)] (MulHead d a f r)));
     apply: get_pinned_frame; rewrite /MulHead /mpin; pinned_tac.
 - apply: (system_triple_seq (es1:=[::BI_call 3%num])
   (Q1:=AS_base [::T_const (SM.Vi64 (add_mod a f d))] (MulHead d a f r))); first reflexivity.
   + move=> frame Hi. exact: crt_add_call.
   + apply: system_triple_of_pure. exact: mul_set_a.
Qed.
Lemma mul_double_sem d a f r : 1 <= d <= MAX -> 0 <= a < d -> 0 <= f < d ->
 system_triple mem (AS_base [::] (MulHead d a f r)) mul_double
 (AS_base [::] (MulHead d a (add_mod f f d) r)).
Proof.
 move=> Hd Ha Hf. rewrite /mul_double.
 apply: (system_triple_seq (es1:=[::BI_local_get 4%num;BI_local_get 4%num;BI_local_get 2%num])
 (Q1:=AS_base [::T_const (SM.Vi64 f);T_const (SM.Vi64 f);T_const (SM.Vi64 d)] (MulHead d a f r))); first reflexivity.
 - apply: system_triple_of_pure.
   apply: (sem_seq (es1:=[::BI_local_get 4%num])
   (Q:=AS_base [::T_const (SM.Vi64 f)] (MulHead d a f r))).
   + apply: get_pinned_frame. rewrite /MulHead /mpin. pinned_tac.
   + apply: (sem_seq (es1:=[::BI_local_get 4%num])
     (Q:=AS_base [::T_const (SM.Vi64 f);T_const (SM.Vi64 f)] (MulHead d a f r)));
     apply: get_pinned_frame; rewrite /MulHead /mpin; pinned_tac.
 - apply: (system_triple_seq (es1:=[::BI_call 3%num])
   (Q1:=AS_base [::T_const (SM.Vi64 (add_mod f f d))] (MulHead d a f r))); first reflexivity.
   + move=> frame Hi. exact: crt_add_call.
   + apply: system_triple_of_pure. exact: mul_set_f.
Qed.
Lemma mul_half_sem d a f r : 0 <= r <= MAX ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (MulHead d a f r)) mul_half
 (AS_base [::] (MulHead d a f (r/2))).
Proof.
 move=> Hr. rewrite /mul_half.
 apply: (sem_seq (es1:=[::BI_local_get 5%num;BI_const_num (SM.Vi64 2)])
 (Q:=AS_base [::T_const (SM.Vi64 r);T_const (SM.Vi64 2)] (MulHead d a f r))).
 - apply: (sem_seq (es1:=[::BI_local_get 5%num])
   (Q:=AS_base [::T_const (SM.Vi64 r)] (MulHead d a f r))).
   + apply: get_pinned_frame. rewrite /MulHead /mpin. pinned_tac.
   + exact: sem_const_framed.
 - apply: (sem_seq (es1:=[::BI_binop T_i64 (Binop_i (BOI_div SX_S))])
   (Q:=AS_base [::T_const (SM.Vi64 (r/2))] (MulHead d a f r))).
   + apply: binop_consts; try reflexivity. apply: crt_i64_div_positive_exact; first exact Hr.
     unfold MAX,i64_max; lia.
   + exact: mul_set_r.
Qed.
Lemma mul_update_sem d e : 1 <= d <= MAX -> mul_state_safe d e ->
 system_triple mem (AS_base [::] (MulState d e)) mul_update
 (AS_base [::] (MulState d (mul_step d e))).
Proof.
 move=> Hd. destruct e as [a f r]. move=> [Ha [Hf Hr]].
 rewrite /MulState /mul_step /= /mul_update.
 pose anew := if r mod 2 =? 1 then add_mod a f d else a.
 have Hnew : 0 <= anew < d.
 { rewrite /anew. case: (r mod 2 =? 1); last exact Ha.
   exact (proj1 (proj2 (add_mod_proved a f d Hd Ha Hf))). }
 apply: (system_triple_seq (es1:=mul_odd)
 (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool (r mod 2 =? 1)))] (MulHead d a f r))); first reflexivity.
 - apply: system_triple_of_pure. exact: mul_odd_sem.
 - apply: (system_triple_seq (es1:=[::BI_if (BT_valtype None) mul_add [::]])
   (Q1:=AS_base [::] (MulHead d anew f r))); first reflexivity.
   + apply: system_triple_of_mxk. apply: (system_if_const (t2s:=[::])); first reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * rewrite /anew. case: (r mod 2 =? 1).
       -- apply: system_mxk_lift. exact: mul_add_sem.
       -- apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_nil_same.
   + apply: (system_triple_seq (es1:=mul_half)
     (Q1:=AS_base [::] (MulHead d anew f (r/2)))); first reflexivity.
     * apply: system_triple_of_pure. exact: mul_half_sem.
     * exact: mul_double_sem.
Qed.

Lemma mul_loop_stopped d e : remaining e = 0 ->
 system_mxk mem (AS_base [::] (MulState d e))
 [::BI_loop (BT_valtype None) mul_loop_code]
 (AS_base [::] (MulState d e)) crt_false_assert
 (fun k => if k is 0%nat then AS_base [::] (MulState d e) else crt_false_assert).
Proof.
 move=> Hz.
 apply: (system_loop_unroll (Pback:=crt_false_assert) (t1s:=[::]) (t2s:=[::])); try reflexivity.
 - move=> V vs h [Hs _]. by case: Hs => <-.
 - move=> V vs h [_ HF]. by case: HF.
 - rewrite /mul_loop_code.
   apply: (system_mxk_seq (es1:=mul_condition)
   (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool true))] (MulState d e))); first reflexivity.
   + apply: system_mxk_lift. apply: system_triple_of_pure.
     have Wr : word (remaining e) by rewrite Hz; unfold word,i64_min,i64_max; lia.
     have H := mul_condition_sem (d:=d) (a:=acc e) (f:=factor e) Wr.
     rewrite Hz in H. rewrite /MulState Hz. exact H.
   + apply: (system_mxk_seq (es1:=[::BI_br_if 1%num]) (Q1:=crt_false_assert)); first reflexivity.
     * apply: system_mxk_of_pure. apply: (crt_br_if_true_sem (k:=1%nat)). by [].
     * apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
 - apply: system_mxk_lift. apply: system_triple_of_pure. exact: sem_false.
Qed.

Lemma mul_loop_exec fuel d e : 1 <= d <= MAX -> mul_state_safe d e ->
 0 <= remaining e < 2 ^ Z.of_nat fuel ->
 system_mxk mem (AS_base [::] (MulState d e))
 [::BI_loop (BT_valtype None) mul_loop_code]
 (AS_base [::] (MulState d (mul_state_loop fuel d e))) crt_false_assert
 (fun k => if k is 0%nat then AS_base [::] (MulState d (mul_state_loop fuel d e)) else crt_false_assert).
Proof.
 move: e. induction fuel as [|fuel IH]; move=> e Hd He Hfuel.
 - cbn [mul_state_loop]. apply: mul_loop_stopped. cbn in Hfuel. lia.
 - cbn [mul_state_loop]. case E: (0 <? remaining e).
   + have Hpos : 0 < remaining e by apply/Z.ltb_lt.
     have Hnext := mul_step_safe d e Hd He.
     have Hless : 0 <= remaining (mul_step d e) < 2 ^ Z.of_nat fuel.
     { cbn [mul_step]. rewrite Nat2Z.inj_succ Z.pow_succ_r in Hfuel; try lia.
       split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
     have Wr : word (remaining e) by apply nonnegative_word; exact (proj2 (proj2 He)).
     apply: (system_loop_unroll (Pback:=AS_base [::] (MulState d (mul_step d e)))
     (t1s:=[::]) (t2s:=[::])); try reflexivity.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * move=> V vs h [Hs _]. by case: Hs => <-.
     * rewrite /mul_loop_code.
       apply: (system_mxk_seq (es1:=mul_condition)
       (Q1:=AS_base [::T_const (VAL_int32 (wasm_bool false))] (MulState d e))); first reflexivity.
       -- apply: system_mxk_lift. apply: system_triple_of_pure.
          have H := mul_condition_sem (d:=d) (a:=acc e) (f:=factor e) Wr.
          by rewrite E in H.
       -- apply: (system_mxk_seq (es1:=[::BI_br_if 1%num])
          (Q1:=AS_base [::] (MulState d e))); first reflexivity.
          ++ apply: system_mxk_lift. apply: system_triple_of_pure. exact: crt_br_if_false_sem.
          ++ apply: (system_mxk_seq (es1:=mul_update)
             (Q1:=AS_base [::] (MulState d (mul_step d e)))); first reflexivity.
             ** apply: system_mxk_lift. exact: mul_update_sem.
             ** apply: system_mxk_of_pure. apply: (sem_mxk_br_k (k:=0%nat)). by [].
     * exact: IH.
   + apply: mul_loop_stopped. apply Z.ltb_ge in E. unfold mul_state_safe in He. lia.
Qed.
Lemma mul_block_exec fuel d e : 1 <= d <= MAX -> mul_state_safe d e ->
 0 <= remaining e < 2 ^ Z.of_nat fuel ->
 system_triple mem (AS_base [::] (MulState d e))
 [::BI_block (BT_valtype None) [::BI_loop (BT_valtype None) mul_loop_code]]
 (AS_base [::] (MulState d (mul_state_loop fuel d e))).
Proof.
 move=> Hd He Hfuel. apply: system_triple_of_mxk.
 apply: (system_mxk_block (t1s:=[::]) (t2s:=[::])
 (Qb:=fun k => if k is 0%nat then AS_base [::] (MulState d (mul_state_loop fuel d e)) else crt_false_assert)); try reflexivity.
 - move=> V vs h [Hs _]. by case: Hs => <-.
 - exact: mul_loop_exec.
Qed.
Lemma mul_entry_entails x y d :
 aentails (AS_base [::] (HA_and (args_pinned [::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d] 0%num)
 (func_pre_h SM.main SM.mul_mod))) (AS_base [::] (MulEntry x y d)).
Proof.
 move=> V [vs h] /= [Hs [[P0 [P1 [P2 _]]] [[T0 [T1 [T2 _]]] [T3 [T4 [T5 _]]]]]].
 split; first exact Hs. repeat split; try assumption.
 - by case: T3 => [w [Ew _]]; exists w.
 - by case: T4 => [w [Ew _]]; exists w.
 - by case: T5 => [w [Ew _]]; exists w.
Qed.
Lemma mul_body_to_computation x y d result :
 inverse_runtime_mx mem (AS_base [::] (MulEntry x y d)) (modfunc_body SM.mul_mod)
 (AS_base [::T_const (SM.Vi64 result)] HA_true)
 (AS_base [::T_const (SM.Vi64 result)] HA_true)
 (AS_base [::T_const (SM.Vi64 result)] HA_true) ->
 system_computes mem 4%nat [::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d] [::SM.Vi64 result].
Proof.
 move=> Hbody. rewrite /system_computes /=.
 split; first by repeat split. split; first by repeat split.
 exists [::VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0);VAL_num (SM.Vi64 0)].
 split; first reflexivity.
 move=> hs V vs h HP Hr. apply: Hbody; [reflexivity| |exact Hr]. exact: mul_entry_entails HP.
Qed.
Theorem mul_mod_machine_computes x y d :
 1 <= d <= MAX -> 0 <= x < d -> 0 <= y < d ->
 system_computes mem 4%nat [::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d]
 [::SM.Vi64 (FullWidth.mul_mod x y d)].
Proof.
 move=> Hd Hx Hy.
 pose init := {|acc:=0;factor:=x;remaining:=y|}.
 pose last := mul_state_loop 64 d init.
 have Hsafe : mul_state_safe d init by apply mul_state_initial_safe.
 have Hfuel : 0 <= remaining init < 2 ^ Z.of_nat 64 by exact (mul_state_initial_fuel y d Hd Hy).
 have E : FullWidth.mul_mod x y d = acc last by rewrite /last mul_state_loop_acc.
 rewrite E. apply: mul_body_to_computation. rewrite mul_body_shape.
 apply: (inverse_runtime_mx_after_triple (es1:=mul_prologue)
 (Q1:=AS_base [::] (MulState d init))); first reflexivity.
 - apply: inverse_runtime_triple_of_triple. exact: mul_prologue_sem.
 - apply: (inverse_runtime_mx_after_triple
   (es1:=[::BI_block (BT_valtype None) [::BI_loop (BT_valtype None) mul_loop_code]])
   (Q1:=AS_base [::] (MulState d last))); first reflexivity.
   + exact: mul_block_exec.
   + apply: inverse_runtime_mx_of_mx. apply: crt_pinned_return.
     rewrite /MulState /MulHead /mpin. pinned_tac.
Qed.
Lemma crt_mul_entry x y d :
 crt_entry_admissible mem SM.mul_mod [::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d].
Proof.
 move=> defaults Hd. vm_compute in Hd. inversion Hd; subst defaults.
 cbn [crt_entry_valuation activation_frame system_initial_runtime func_pre_h SM.main
 SM.mul_mod args_pinned locals_typed assertion_denote hassert_denote stack_denote
 term_eq term_denote loc_read lookup_N val_loc f_locs modfunc_type modfunc_locals mod_types runtime_inst SM.Vi64].
 repeat split; try reflexivity; try (eexists; split; reflexivity).
Qed.
Lemma crt_mul_call frame H x y d :
 f_inst frame = system_inst -> 1 <= d <= MAX -> 0 <= x < d -> 0 <= y < d ->
 sem_triple_at (system_store mem) frame
 (AS_base [::T_const (SM.Vi64 x);T_const (SM.Vi64 y);T_const (SM.Vi64 d)] H)
 [::BI_call 4%num] (AS_base [::T_const (SM.Vi64 (FullWidth.mul_mod x y d))] H).
Proof.
 move=> Hi Hd Hx Hy.
 apply: (crt_call_from_computes_at (i:=4%nat) (addr:=4%num) (fdef:=SM.mul_mod)
 (args:=[::SM.Vi64 x;SM.Vi64 y;SM.Vi64 d]) (rs:=[::SM.Vi64 (FullWidth.mul_mod x y d)])
 (params:=[::T_num T_i64;T_num T_i64;T_num T_i64]) (results:=[::T_num T_i64])); try reflexivity.
 - by rewrite Hi.
 - exact: crt_mul_entry.
 - exact: mul_mod_machine_computes.
Qed.
End Host.
Print Assumptions mul_mod_machine_computes.
