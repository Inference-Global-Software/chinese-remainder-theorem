(* Proof-only state-returning form of the actual repeated-doubling recurrence. *)
From Coq Require Import ZArith Lia.
From CRT Require Import CRTStatements CRTSystemStatements CRTSystemArithmetic.
Import FullWidth.
Open Scope Z_scope.
Fixpoint mul_state_loop (fuel : nat) (d : Z) (e : mul_state) : mul_state :=
 match fuel with O => e | S k =>
 if 0 <? remaining e then mul_state_loop k d (mul_step d e) else e end.
Lemma mul_state_loop_acc : forall fuel d e,
 acc (mul_state_loop fuel d e) = mul_loop fuel d e.
Proof.
 induction fuel; intros; cbn; [reflexivity|].
 destruct (0 <? remaining e); [apply IHfuel|reflexivity].
Qed.
Definition mul_state_safe d e :=
 0 <= acc e < d /\ 0 <= factor e < d /\ 0 <= remaining e <= MAX.
Lemma mul_step_safe : forall d e, 1 <= d <= MAX -> mul_state_safe d e ->
 mul_state_safe d (mul_step d e).
Proof.
 intros d [a f r] Hd [Ha [Hf Hr]].
 pose proof (add_mod_proved a f d Hd Ha Hf) as (_ & Hnewa & _).
 pose proof (add_mod_proved f f d Hd Hf Hf) as (_ & Hnewf & _).
 unfold mul_state_safe, mul_step in *; cbn in *.
 assert (Hhalf : 0 <= r/2 <= r).
 { split; [apply Z.div_pos|apply Z.div_le_upper_bound]; lia. }
 destruct (r mod 2 =? 1); repeat split; lia.
Qed.
Lemma mul_state_loop_safe : forall fuel d e,
 1 <= d <= MAX -> mul_state_safe d e -> mul_state_safe d (mul_state_loop fuel d e).
Proof.
 induction fuel; intros d e Hd He; cbn; [exact He|].
 destruct (0 <? remaining e); [apply IHfuel; [exact Hd|apply mul_step_safe; assumption]|exact He].
Qed.
Lemma mul_state_loop_finished : forall fuel d e,
 0 <= remaining e < 2 ^ Z.of_nat fuel -> remaining (mul_state_loop fuel d e) = 0.
Proof.
 induction fuel; intros d e Hr; cbn [mul_state_loop].
 - cbn in Hr. lia.
 - destruct (0 <? remaining e) eqn:E.
   + apply IHfuel. cbn [mul_step].
     rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hr by lia.
     split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
   + apply Z.ltb_ge in E. lia.
Qed.
Lemma mul_state_initial_safe : forall x y d,
 1 <= d <= MAX -> 0 <= x < d -> 0 <= y < d ->
 mul_state_safe d {|acc:=0;factor:=x;remaining:=y|}.
Proof. unfold mul_state_safe; cbn; intros; repeat split; lia. Qed.
Lemma mul_state_initial_fuel : forall y d,
 1 <= d <= MAX -> 0 <= y < d -> 0 <= y < 2 ^ Z.of_nat 64.
Proof. unfold MAX, i64_max; cbn; intros; lia. Qed.
Print Assumptions mul_state_loop_acc.
Print Assumptions mul_state_loop_finished.
