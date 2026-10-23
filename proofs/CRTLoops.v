(* Kernel-checked facts about the mathematical loop recurrences.  The run
   relations below do not describe generated WebAssembly execution. *)
From Coq Require Import ZArith Lia Wf_nat.
From CRT Require Import CRTStatements.
Open Scope Z_scope.

Lemma abs_word_small : forall z K,
  Z.abs z <= K -> K <= M -> word z.
Proof.
  intros z K Hz HK. apply Z.abs_le in Hz.
  unfold word, i64_min, i64_max, M in *. lia.
Qed.

Theorem normalize_proved : T_normalize.
Proof.
  unfold T_normalize. intros z d Hz Hd.
  pose proof (Z.rem_bound_abs z d ltac:(lia)) as Hbound.
  rewrite (Z.abs_eq d) in Hbound by lia.
  pose proof (Z.quot_rem z d ltac:(lia)) as Hdiv.
  pose proof (Z.abs_spec (Z.rem z d)) as Habs.
  destruct (Z.rem z d <? 0) eqn:Htest.
  - apply Z.ltb_lt in Htest.
    assert (Hr : -d < Z.rem z d < 0) by lia.
    assert (Heq : Z.rem z d + d = z mod d).
    { apply (Z.mod_unique_pos z d (Z.quot z d - 1)); nia. }
    repeat split; try assumption; try lia;
      unfold word, i64_min, i64_max, M in *; lia.
  - apply Z.ltb_ge in Htest.
    assert (Hr : 0 <= Z.rem z d < d) by lia.
    assert (Heq : Z.rem z d = z mod d).
    { apply (Z.mod_unique_pos z d (Z.quot z d)); assumption. }
    repeat split; try assumption; try lia;
      unfold word, i64_min, i64_max, M in *; lia.
Qed.

Lemma gcd_rotate_mod : forall a b, b <> 0 ->
  Z.gcd b (a mod b) = Z.gcd a b.
Proof.
  intros a b Hb. rewrite Z.gcd_comm, Z.gcd_mod by assumption.
  apply Z.gcd_comm.
Qed.

Theorem gcd_init_proved : T_gcd_init.
Proof. unfold T_gcd_init, moduli, gcd_inv. intros; intuition lia. Qed.

Theorem gcd_step_proved : T_gcd_step.
Proof.
  unfold T_gcd_step, gcd_inv. intros m n a b (Ha & Hb & Hg) Hpos.
  pose proof (Z.mod_pos_bound a b Hpos) as Hr.
  repeat split; try lia.
  - rewrite gcd_rotate_mod by lia. exact Hg.
Qed.

Theorem gcd_exit_proved : T_gcd_exit.
Proof.
  unfold T_gcd_exit, gcd_inv. intros m n a (Ha & Hb & Hg).
  rewrite Z.gcd_0_r, Z.abs_eq in Hg by lia. exact Hg.
Qed.

Lemma abs_opposite_update : forall x y q,
  x * y <= 0 -> 0 <= q ->
  Z.abs (x - q * y) = Z.abs x + q * Z.abs y.
Proof.
  intros x y q Hsign Hq.
  destruct (Z.abs_spec x) as [[Hx Hax] | [Hx Hax]];
    destruct (Z.abs_spec y) as [[Hy Hay] | [Hy Hay]];
    rewrite Hax, Hay;
    destruct (Z.abs_spec (x - q * y)) as [[Hnew Habs] | [Hnew Habs]];
    rewrite Habs; nia.
Qed.

(* The weighted identities bound both the intermediate product and the new
   coefficient, including the iteration whose new remainder is zero. *)
Lemma coefficient_step : forall a b c q x y K,
  0 < b -> 0 <= c -> 1 <= q -> a = q * b + c ->
  x * y <= 0 -> a * Z.abs y + b * Z.abs x = K ->
  Z.abs (x - q * y) = Z.abs x + q * Z.abs y /\
  y * (x - q * y) <= 0 /\
  b * Z.abs (x - q * y) + c * Z.abs y = K /\
  Z.abs (q * y) <= K /\ Z.abs (x - q * y) <= K.
Proof.
  intros a b c q x y K Hb Hc Hq Ha Hsign Hweight.
  pose proof (Z.abs_nonneg x) as Hx.
  pose proof (Z.abs_nonneg y) as Hy.
  pose proof (Z.square_nonneg y) as Hsq.
  assert (Habs : Z.abs (x - q * y) = Z.abs x + q * Z.abs y).
  { apply abs_opposite_update; lia. }
  assert (Hweight' : b * Z.abs (x - q * y) + c * Z.abs y = K).
  { rewrite Habs, Ha in *. nia. }
  assert (Hprod : Z.abs (q * y) <= K).
  { rewrite Z.abs_mul, (Z.abs_eq q) by lia. rewrite Ha in Hweight. nia. }
  repeat split; try assumption; try nia.
Qed.

Theorem eea_init_proved : T_eea_init.
Proof.
  unfold T_eea_init, eea_inputs, eea_inv, eea_init.
  intros A B H. cbn. repeat split; try reflexivity; nia.
Qed.

Theorem eea_step_proved : T_eea_step.
Proof.
  unfold T_eea_step. intros A B [a b x y u v] Hin Hinv Hguard.
  unfold eea_inputs in Hin. unfold eea_inv in Hinv. cbn in Hinv, Hguard.
  destruct Hinv as (Hb & Hba & Ha & Hg & Hbez0 & Hbez1 & Hdet &
    Hs & Ht & Hws & Hwt & Hx & Hy & Hu & Hv).
  pose proof (Z.mod_pos_bound a b Hguard) as Hmod.
  pose proof (Z.div_mod a b ltac:(lia)) as Hdiv.
  pose proof (Z.div_pos a b ltac:(lia) Hguard) as Hqnonneg.
  assert (Hq : 1 <= a / b).
  { pose proof (Z.div_str_pos a b ltac:(lia)); lia. }
  assert (Hdiv' : a = (a / b) * b + a mod b) by (rewrite Z.mul_comm; exact Hdiv).
  pose proof (coefficient_step a b (a mod b) (a / b) x y B
    Hguard ltac:(lia) Hq Hdiv' Hs Hws) as (Hsabs & Hsnew & Hwsnew & Hsp & Hsn).
  pose proof (coefficient_step a b (a mod b) (a / b) u v A
    Hguard ltac:(lia) Hq Hdiv' Ht Hwt) as (Htabs & Htnew & Hwtnew & Htp & Htn).
  unfold eea_step, eea_inv. cbn.
  split.
  - split. exact (proj1 Hmod).
    split. exact (proj2 Hmod).
    split. { clear - Hba Ha. lia. }
    split. { rewrite gcd_rotate_mod by lia. exact Hg. }
    split. exact Hbez1.
    split.
    { replace (A * (x - a / b * y) + B * (u - a / b * v))
        with ((A * x + B * u) - (a / b) * (A * y + B * v)) by ring.
      rewrite <- Hbez0, <- Hbez1. clear - Hdiv'. lia. }
    split.
    { replace (y * (u - a / b * v) - (x - a / b * y) * v)
        with (-(x * v - y * u)) by ring.
      rewrite Z.abs_opp. exact Hdet. }
    repeat split; assumption.
  - split. exact Hmod.
    apply Z2Nat.inj_lt; clear - Hmod Hguard; lia.
Qed.

Theorem eea_step_bounds_proved : T_eea_step_bounds.
Proof.
  unfold T_eea_step_bounds. intros A B [a b x y u v] Hin Hinv Hguard.
  unfold eea_inputs in Hin. unfold eea_inv in Hinv. cbn in *.
  destruct Hinv as (Hb & Hba & Ha & Hg & Hbez0 & Hbez1 & Hdet &
    Hs & Ht & Hws & Hwt & Hx & Hy & Hu & Hv).
  pose proof (Z.mod_pos_bound a b Hguard) as Hmod.
  pose proof (Z.div_mod a b ltac:(lia)) as Hdiv.
  assert (Hq : 1 <= a / b).
  { pose proof (Z.div_str_pos a b ltac:(lia)); lia. }
  assert (HqA : a / b <= A).
  { apply Z.div_le_upper_bound; clear - Hguard Hba Ha; nia. }
  assert (Hqr : 0 <= a / b * b <= A).
  { clear - Hmod Hdiv Ha Hq Hguard. nia. }
  assert (Hdiv' : a = (a / b) * b + a mod b) by (rewrite Z.mul_comm; exact Hdiv).
  pose proof (coefficient_step a b (a mod b) (a / b) x y B
    Hguard ltac:(lia) Hq Hdiv' Hs Hws) as (Hsabs & Hsnew & Hwsnew & Hsp & Hsn).
  pose proof (coefficient_step a b (a mod b) (a / b) u v A
    Hguard ltac:(lia) Hq Hdiv' Ht Hwt) as (Htabs & Htnew & Hwtnew & Htp & Htn).
  assert (Wsp : word (a / b * y)) by (eapply abs_word_small; [exact Hsp | clear - Hin; lia]).
  assert (Wsn : word (x - a / b * y)) by (eapply abs_word_small; [exact Hsn | clear - Hin; lia]).
  assert (Wtp : word (a / b * v)) by (eapply abs_word_small; [exact Htp | clear - Hin; lia]).
  assert (Wtn : word (u - a / b * v)) by (eapply abs_word_small; [exact Htn | clear - Hin; lia]).
  repeat first [assumption | split].
Qed.

Theorem eea_exit_proved : T_eea_exit.
Proof.
  unfold T_eea_exit. intros A B e Hin Hinv Hzero.
  unfold eea_inputs in Hin. unfold eea_inv in Hinv.
  destruct Hinv as (Hb & Hba & Ha & Hg & Hbez0 & Hrest).
  clear Hrest.
  rewrite Hzero, Z.gcd_0_r, Z.abs_eq in Hg by lia.
  split. exact Hg.
  split. lia.
  intros Hcoprime. split.
  - apply Z.mod_pos_bound. lia.
  - unfold congruent. exists (-s0 e - B * (t0 e / A)).
    pose proof (Z.div_mod (t0 e) A ltac:(lia)) as Hdiv.
    pose proof (f_equal (fun z => B * z) Hdiv) as HBdiv.
    clear - Hbez0 Hg Hcoprime HBdiv. cbn in HBdiv. nia.
Qed.

(* Finite runs of the mathematical Euclidean recurrence.  These constructors
   contain no machine semantics and make no claim about a Wasm instance. *)
Inductive gcd_run : Z -> Z -> Z -> Prop :=
| gcd_run_done : forall a, gcd_run a 0 a
| gcd_run_next : forall a b result,
    0 < b -> gcd_run b (a mod b) result -> gcd_run a b result.

Theorem gcd_run_terminates : forall m n a b,
  gcd_inv m n a b ->
  exists result, gcd_run a b result /\ result = Z.gcd m n /\ word result.
Proof.
  intros m n a b.
  remember (Z.to_nat b) as k eqn:Hk.
  revert a b Hk.
  induction k as [k IH] using lt_wf_ind.
  intros a b Hk Hinv.
  destruct (Z.eq_dec b 0) as [Hzero | Hnonzero].
  - subst b. exists a. split. constructor.
    split. apply (gcd_exit_proved m n a Hinv).
    destruct Hinv as (Ha & _). unfold word, i64_min, i64_max, M in *. lia.
  - assert (Hpos : 0 < b) by (destruct Hinv as (_ & Hb & _); lia).
    destruct (gcd_step_proved m n a b Hinv Hpos) as (Hnext & Hmod & Hless).
    destruct (IH (Z.to_nat (a mod b)) ltac:(lia) b (a mod b) eq_refl Hnext)
      as (result & Hrun & Hresult & Hword).
    exists result. repeat first [assumption | split].
    apply gcd_run_next; assumption.
Qed.

Theorem gcd_initial_run_correct : forall m n, moduli m n ->
  exists result, gcd_run m n result /\ result = Z.gcd m n /\ word result.
Proof.
  intros m n Hin. apply gcd_run_terminates. apply gcd_init_proved. exact Hin.
Qed.

Inductive eea_run : eea_state -> eea_state -> Prop :=
| eea_run_done : forall e, r1 e = 0 -> eea_run e e
| eea_run_next : forall e final,
    0 < r1 e -> eea_run (eea_step e) final -> eea_run e final.

Theorem eea_run_terminates : forall A B e,
  eea_inputs A B -> eea_inv A B e ->
  exists final, eea_run e final /\ eea_inv A B final /\ r1 final = 0.
Proof.
  intros A B e Hin.
  remember (Z.to_nat (r1 e)) as k eqn:Hk.
  revert e Hk.
  induction k as [k IH] using lt_wf_ind.
  intros e Hk Hinv.
  destruct (Z.eq_dec (r1 e) 0) as [Hzero | Hnonzero].
  - exists e. repeat first [assumption | split]. apply eea_run_done. exact Hzero.
  - assert (Hpos : 0 < r1 e) by (destruct Hinv as (Hb & _); lia).
    destruct (eea_step_proved A B e Hin Hinv Hpos) as (Hnext & Hmod & Hless).
    destruct (IH (Z.to_nat (r1 (eea_step e))) ltac:(lia)
      (eea_step e) eq_refl Hnext) as (final & Hrun & Hfinal & Hzero).
    exists final. repeat first [assumption | split].
    apply eea_run_next; assumption.
Qed.

Theorem eea_initial_run_correct : forall A B,
  eea_inputs A B ->
  exists final, eea_run (eea_init A B) final /\ r1 final = 0 /\
    r0 final = Z.gcd A B /\
    A * s0 final + B * t0 final = Z.gcd A B /\
    (Z.gcd A B = 1 ->
       0 <= t0 final mod A < A /\ congruent A (B * (t0 final mod A)) 1).
Proof.
  intros A B Hin.
  destruct (eea_run_terminates A B (eea_init A B) Hin (eea_init_proved A B Hin))
    as (final & Hrun & Hinv & Hzero).
  exists final. split. exact Hrun. split. exact Hzero.
  exact (eea_exit_proved A B final Hin Hinv Hzero).
Qed.

Print Assumptions normalize_proved.
Print Assumptions gcd_init_proved.
Print Assumptions gcd_step_proved.
Print Assumptions gcd_exit_proved.
Print Assumptions eea_init_proved.
Print Assumptions eea_step_proved.
Print Assumptions eea_step_bounds_proved.
Print Assumptions eea_exit_proved.
Print Assumptions gcd_run_terminates.
Print Assumptions gcd_initial_run_correct.
Print Assumptions eea_run_terminates.
Print Assumptions eea_initial_run_correct.
