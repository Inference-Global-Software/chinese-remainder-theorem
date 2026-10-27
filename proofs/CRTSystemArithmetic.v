(* Full-width versions retain the legacy EEA invariant without changing it. *)
From Coq Require Import ZArith Lia Wf_nat List Bool.
From CRT Require Import CRTStatements CRTSystemStatements CRTMath.
Import FullWidth.
Open Scope Z_scope.
Lemma abs_word_small : forall z K,
  Z.abs z <= K -> K <= MAX -> word z.
Proof.
  intros z K Hz HK. apply Z.abs_le in Hz.
  unfold word, MAX, i64_min, i64_max in *. lia.
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
      unfold word, MAX, i64_min, i64_max in *; lia.
  - apply Z.ltb_ge in Htest.
    assert (Hr : 0 <= Z.rem z d < d) by lia.
    assert (Heq : Z.rem z d = z mod d).
    { apply (Z.mod_unique_pos z d (Z.quot z d)); assumption. }
    repeat split; try assumption; try lia;
      unfold word, MAX, i64_min, i64_max in *; lia.
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
    destruct Hinv as (Ha & _). unfold word, MAX, i64_min, i64_max in *. lia.
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

Theorem construct_proved : T_construct.
Proof.
  unfold T_construct. intros a m b n Hdom Hcompat. cbn zeta.
  destruct Hdom as [[Hm Hn] [Ha Hb]].
  destruct (reduction_proved m n ltac:(lia) ltac:(lia)) as
    [Hg [Hgm [Hgn [Hm1 [Hn1 [Hcop [Hl Hp]]]]]]].
  pose proof (exact_division _ _ Hg Hgm) as Hmeq.
  pose proof (exact_division _ _ Hg Hgn) as Hneq.
  pose proof (exact_division _ _ Hg Hcompat) as Hdeq.
  destruct (period_properties m n ltac:(lia) ltac:(lia)) as [_ [_ [_ Hperiod]]].
  split.
  - intros Hone. unfold canonical, solution, congruent.
    rewrite Hperiod, Hone. split; [nia |]. split.
    + exists 0. ring.
    + exists (-((b - a) / Z.gcd m n)). nia.
  - intros Hlarge u Hu [v Hv].
    pose proof (Z.mod_pos_bound ((b - a) / Z.gcd m n * u)
      (n / Z.gcd m n) Hn1) as Ht.
    unfold canonical, solution, congruent. split.
    + rewrite Hperiod. nia.
    + split.
      * exists (((b - a) / Z.gcd m n * u) mod (n / Z.gcd m n)). ring.
      * exists (((b - a) / Z.gcd m n) * v -
          (m / Z.gcd m n) * (((b - a) / Z.gcd m n * u) / (n / Z.gcd m n))).
        set (g := Z.gcd m n) in *.
        set (m1 := m / g) in *.
        set (n1 := n / g) in *.
        set (d := (b - a) / g) in *.
        pose proof (Z.div_mod (d * u) n1 ltac:(lia)) as Hmod.
        assert (He : d * u - (d * u) mod n1 = n1 * (d * u / n1)) by lia.
        replace (a + m * ((d * u) mod n1) - b)
          with (m * ((d * u) mod n1) - (b - a)) by ring.
        rewrite Hmeq, Hdeq, Hneq.
        replace (g * m1 * ((d * u) mod n1) - g * d)
          with (g * (d * (m1 * u - 1) - m1 * (d * u - (d * u) mod n1))) by ring.
        rewrite Hv, He. ring.
Qed.


Lemma nonnegative_word : forall z, 0 <= z <= MAX -> word z.
Proof. unfold word, MAX, i64_min, i64_max; lia. Qed.

Theorem add_mod_proved : T_add_mod.
Proof.
  unfold T_add_mod, add_mod. intros x y d Hd Hx Hy.
  destruct (d-y <=? x) eqn:Hcase.
  - apply Z.leb_le in Hcase.
    assert (Heq : x-(d-y) = (x+y) mod d).
    { apply (Z.mod_unique_pos (x+y) d 1); lia. }
    repeat split; try lia; try assumption; apply nonnegative_word; lia.
  - apply Z.leb_gt in Hcase.
    rewrite Z.mod_small by lia.
    repeat split; try lia; apply nonnegative_word; lia.
Qed.

Lemma add_mod_congruent : forall x y d,
  1 <= d <= MAX -> 0 <= x < d -> 0 <= y < d ->
  congruent d (add_mod x y d) (x+y).
Proof.
  intros x y d Hd Hx Hy. rewrite (proj1 (add_mod_proved x y d Hd Hx Hy)).
  unfold congruent. exists (-((x+y)/d)). pose proof (Z.div_mod (x+y) d ltac:(lia)). nia.
Qed.

Theorem mul_step_proved : T_mul_step.
Proof.
  unfold T_mul_step. intros product d [a f r] Hd (Ha & Hf & Hr & Hinv) Hpos.
  cbn in *. unfold mul_step; cbn.
  pose proof (add_mod_proved a f d Hd Ha Hf) as (Hae & Har & _ & Haw & _).
  pose proof (add_mod_proved f f d Hd Hf Hf) as (Hfe & Hfr & _ & Hfw & _).
  destruct (add_mod_congruent a f d Hd Ha Hf) as [ka Hka].
  destruct (add_mod_congruent f f d Hd Hf Hf) as [kf Hkf].
  destruct Hinv as [ki Hki].
  pose proof (Z.div_mod r 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound r 2 ltac:(lia)) as Hmod.
  assert (Hhalf : 0 <= r/2 < r).
  { split; [apply Z.div_pos; lia | apply Z.div_lt; lia]. }
  destruct (r mod 2 =? 1) eqn:Hbit.
  - apply Z.eqb_eq in Hbit.
    assert (Hnew : congruent d (add_mod a f d + add_mod f f d * (r/2)) product).
    { unfold congruent. exists (ki + ka + kf * (r/2)). nia. }
    assert (Hrw : r <= MAX -> word (r/2)) by (intros; apply nonnegative_word; lia).
    unfold mul_inv; cbn. repeat first [assumption | split]; lia.
  - apply Z.eqb_neq in Hbit. assert (r mod 2 = 0) by lia.
    assert (Hnew : congruent d (a + add_mod f f d * (r/2)) product).
    { unfold congruent. exists (ki + kf * (r/2)). nia. }
    assert (Haw' : word a) by (apply nonnegative_word; lia).
    assert (Hrw : r <= MAX -> word (r/2)) by (intros; apply nonnegative_word; lia).
    unfold mul_inv; cbn. repeat first [assumption | split]; lia.
Qed.

Lemma congruent_residue : forall d r z,
  0 < d -> 0 <= r < d -> congruent d r z -> r = z mod d.
Proof.
  intros d r z Hd Hr [k Hk]. apply (Z.mod_unique_pos z d (-k)); nia.
Qed.

Lemma mul_loop_correct : forall fuel product d e,
  1 <= d <= MAX -> mul_inv product d e ->
  remaining e < 2 ^ Z.of_nat fuel ->
  mul_loop fuel d e = product mod d.
Proof.
  induction fuel as [|fuel IH]; intros product d e Hd Hinv Hfuel.
  - cbn in Hfuel |- *. destruct Hinv as (Ha & Hf & Hr & Hc).
    assert (remaining e = 0) by lia.
    apply congruent_residue; try lia. rewrite H, Z.mul_0_r, Z.add_0_r in Hc. exact Hc.
  - cbn [mul_loop]. destruct (0 <? remaining e) eqn:Htest.
    + apply Z.ltb_lt in Htest.
      apply IH; try assumption.
      * exact (proj1 (mul_step_proved product d e Hd Hinv Htest)).
      * cbn [mul_step]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hfuel by lia.
        apply Z.div_lt_upper_bound; lia.
    + apply Z.ltb_ge in Htest. destruct Hinv as (Ha & Hf & Hr & Hc).
      assert (remaining e = 0) by lia.
      apply congruent_residue; try lia. rewrite H, Z.mul_0_r, Z.add_0_r in Hc. exact Hc.
Qed.

Theorem mul_mod_proved : T_mul_mod.
Proof.
  unfold T_mul_mod. intros x y d Hd Hx Hy.
  assert (Hinv : mul_inv (x*y) d {|acc:=0;factor:=x;remaining:=y|}).
  { unfold mul_inv; cbn. repeat split; try lia. unfold congruent. exists 0; ring. }
  assert (Heq : mul_mod x y d = (x*y) mod d).
  { unfold mul_mod. apply mul_loop_correct; try assumption.
    cbn. unfold MAX, i64_max in Hd. lia. }
  pose proof (Z.mod_pos_bound (x*y) d ltac:(lia)) as Hr.
  rewrite Heq. split; [reflexivity|]. split; [exact Hr|]. apply nonnegative_word; lia.
Qed.

Lemma gcd_loop_correct : forall fuel m n a b,
  gcd_inv m n a b -> (Z.to_nat b < fuel)%nat ->
  gcd_loop fuel a b = Z.gcd m n.
Proof.
  induction fuel as [|fuel IH]; intros m n a b Hinv Hfuel; [lia|].
  cbn [gcd_loop]. destruct (0 <? b) eqn:Htest.
  - apply Z.ltb_lt in Htest.
    destruct (gcd_step_proved m n a b Hinv Htest) as (Hnext & _ & Hless).
    apply IH with (m:=m) (n:=n); assumption || lia.
  - apply Z.ltb_ge in Htest. assert (b=0) by (destruct Hinv as (_ & Hb & _); lia).
    subst. apply gcd_exit_proved; assumption.
Qed.
Theorem gcd_model_proved : T_gcd_model.
Proof.
  intros a b Hd. unfold gcd_model. apply gcd_loop_correct; [apply gcd_init_proved|]; assumption || lia.
Qed.
Lemma eea_loop_correct : forall fuel A B e,
  eea_inputs A B -> eea_inv A B e -> (Z.to_nat (r1 e) < fuel)%nat ->
  eea_inv A B (eea_loop fuel e) /\ r1 (eea_loop fuel e) = 0.
Proof.
  induction fuel as [|fuel IH]; intros A B e Hin Hinv Hfuel; [lia|].
  cbn [eea_loop]. destruct (0 <? r1 e) eqn:Htest.
  - apply Z.ltb_lt in Htest.
    destruct (eea_step_proved A B e Hin Hinv Htest) as (Hnext & _ & Hless).
    apply IH; assumption || lia.
  - apply Z.ltb_ge in Htest. split; [assumption|]. destruct Hinv as (Hr & _); lia.
Qed.
Theorem inverse_model_proved : T_inverse_model.
Proof.
  intros A B Hin Hcop. unfold inverse_model.
  destruct (eea_loop_correct (S (Z.to_nat B)) A B (eea_init A B) Hin
    (eea_init_proved A B Hin) ltac:(cbn;lia)) as (Hinv & Hzero).
  exact (proj2 (proj2 (eea_exit_proved A B _ Hin Hinv Hzero)) Hcop).
Qed.

Theorem lcm_guard_proved : T_lcm_guard.
Proof.
  intros m n Hdom. destruct Hdom as (Hm & Hn).
  destruct (reduction_proved m n ltac:(lia) ltac:(lia)) as
    (Hg & Hgm & Hgn & Hm1 & Hn1 & Hcop & Hl & Hp).
  rewrite <- Hl. unfold period. split.
  - pose proof (Z.div_mod MAX n ltac:(lia)).
    pose proof (Z.mod_pos_bound MAX n ltac:(lia)). split; nia.
  - intros Hguard. apply nonnegative_word. split; [nia|].
    pose proof (Z.div_mod MAX n ltac:(lia)).
    pose proof (Z.mod_pos_bound MAX n ltac:(lia)). nia.
Qed.

Theorem construct_bounds_proved : T_construct_bounds.
Proof.
  intros a m b n ((Hm & Hn) & Ha & Hb) Hcompat HL.
  destruct (reduction_proved m n ltac:(lia) ltac:(lia)) as
    (Hg & Hgm & Hgn & Hm1 & Hn1 & Hcop & Hl & Hp).
  pose proof (exact_division _ _ Hg Hcompat) as Hdelta.
  destruct (period_properties m n ltac:(lia) ltac:(lia)) as (_ & _ & _ & Hperiod).
  assert (Hdw : word (b-a)).
  { unfold word, MAX, i64_min, i64_max in *; lia. }
  split; [assumption|]. split.
  - apply abs_word_small with (K:=MAX).
    + apply Z.abs_le. unfold MAX, i64_max in *. nia.
    + lia.
  - intros t Ht. assert (Hr : 0 <= a+m*t < Z.lcm m n).
    { rewrite <- Hl, Hperiod. nia. }
    repeat split; try lia; apply nonnegative_word; nia.
Qed.

Import FullWidthMachineTargets.
Theorem index_arithmetic_proved : T_index_arithmetic.
Proof.
  intros count i Hcount Hi. unfold word, i64_min, i64_max; lia.
Qed.
Theorem mul_machine_arithmetic_proved : T_mul_machine_arithmetic.
Proof.
  intros d e product Hd Hinv Hrmax Hr.
  pose proof (mul_step_proved product d e Hd Hinv Hr) as (_ & Hnext & _).
  destruct Hinv as (Ha & Hf & Hnonneg & _).
  pose proof (Z.mod_pos_bound (remaining e) 2 ltac:(lia)) as Hbit.
  assert (Hhalf : 0 <= remaining e / 2 < remaining e).
  { split; [apply Z.div_pos; lia|apply Z.div_lt; lia]. }
  repeat split; try (apply nonnegative_word; lia).
  apply Z2Nat.inj_lt; lia.
Qed.
Theorem reduction_machine_bounds_proved : T_reduction_machine_bounds.
Proof.
  intros a m b n ((Hm & Hn) & Ha & Hb). cbn zeta.
  pose proof (gcd_positive m n ltac:(lia)) as Hg.
  pose proof (Z.gcd_divide_l m n) as Hgm.
  pose proof (Z.gcd_divide_r m n) as Hgn.
  pose proof (Z.divide_pos_le (Z.gcd m n) m ltac:(lia) Hgm) as Hgmle.
  pose proof (Z.divide_pos_le (Z.gcd m n) n ltac:(lia) Hgn) as Hgnle.
  pose proof (exact_division _ _ Hg Hgm) as Hmeq.
  pose proof (exact_division _ _ Hg Hgn) as Hneq.
  assert (Hm1 : 1 <= m/Z.gcd m n <= MAX).
  { assert (0 < m/Z.gcd m n) by (apply Z.div_str_pos; lia). nia. }
  assert (Hn1 : 1 <= n/Z.gcd m n <= MAX).
  { assert (0 < n/Z.gcd m n) by (apply Z.div_str_pos; lia). nia. }
  assert (Hd : -MAX < b-a < MAX) by lia.
  pose proof (Z.mod_pos_bound (b-a) (Z.gcd m n) Hg) as Hrem.
  pose proof (Z.div_mod (b-a) (Z.gcd m n) ltac:(lia)) as Hdiv.
  assert (Hquot : -MAX <= (b-a)/Z.gcd m n <= MAX) by nia.
  repeat split; try lia; unfold word, MAX, i64_min, i64_max in *; lia.
Qed.

Import SignedArithmeticTargets.
Theorem signed_arithmetic_bridge_proved : T_signed_arithmetic_bridge.
Proof.
  intros z d Hz Hd. split.
  - rewrite Z.rem_divide, Z.mod_divide by lia. reflexivity.
  - split.
    + intros Hdiv.
      assert (Hr : Z.rem z d = 0) by (apply Z.rem_divide; lia || assumption).
      pose proof (Z.quot_rem z d ltac:(lia)).
      pose proof (exact_division d z ltac:(lia) Hdiv). nia.
    + intros Hnonneg. split.
      * apply Z.rem_mod_nonneg; lia.
      * apply Z.quot_div_nonneg; lia.
Qed.
