(* Abstract generalized CRT and the arithmetic envelope of its construction. *)
From Coq Require Import ZArith Lia.
From CRT Require Import CRTStatements.
Open Scope Z_scope.

Lemma exact_division : forall d z, 0 < d -> (d | z) -> z = d * (z / d).
Proof.
  intros d z Hd Hdiv. apply Z.div_exact; [lia |].
  apply Z.mod_divide; [lia | exact Hdiv].
Qed.

Lemma gcd_positive : forall m n, 0 < m -> 0 < Z.gcd m n.
Proof.
  intros m n Hm. pose proof (Z.gcd_nonneg m n).
  assert (Z.gcd m n <> 0) by (intro Hz; apply Z.gcd_eq_0_l in Hz; lia).
  lia.
Qed.

Lemma congruent_normalization : forall d x a, 0 < d ->
  (congruent d x a <-> congruent d x (a mod d)).
Proof.
  intros d x a Hd. unfold congruent.
  pose proof (Z.div_mod a d ltac:(lia)) as Ha.
  split; intros [k Hk].
  - exists (k + a / d). nia.
  - exists (k - a / d). nia.
Qed.

Theorem normalization_proved : T_normalization.
Proof.
  unfold T_normalization, solution. intros a m b n x Hm Hn.
  rewrite (congruent_normalization m x a Hm),
    (congruent_normalization n x b Hn). reflexivity.
Qed.

Theorem reduction_proved : T_reduction.
Proof.
  unfold T_reduction. intros m n Hm Hn. cbn zeta.
  pose proof (gcd_positive m n Hm) as Hg.
  pose proof (Z.gcd_divide_l m n) as Hgm.
  pose proof (Z.gcd_divide_r m n) as Hgn.
  pose proof (Z.divide_pos_le _ _ Hm Hgm) as Hgmle.
  pose proof (Z.divide_pos_le _ _ Hn Hgn) as Hgnle.
  assert (Hm1 : 0 < m / Z.gcd m n) by (apply Z.div_str_pos; lia).
  assert (Hn1 : 0 < n / Z.gcd m n) by (apply Z.div_str_pos; lia).
  assert (Hl : period m n = Z.lcm m n).
  { unfold period, Z.lcm. rewrite Z.gcd_div_swap.
    symmetry. apply Z.abs_eq. nia. }
  repeat split; try assumption.
  - apply Z.gcd_div_gcd; [lia | reflexivity].
  - unfold period. nia.
Qed.

Lemma period_properties : forall m n, 0 < m -> 0 < n ->
  0 < period m n /\ (m | period m n) /\ (n | period m n) /\
  period m n = m * (n / Z.gcd m n).
Proof.
  intros m n Hm Hn.
  destruct (reduction_proved m n Hm Hn) as
    [Hg [Hgm [Hgn [Hm1 [Hn1 [Hcop [Hl Hp]]]]]]].
  split; [exact Hp |]. split.
  - rewrite Hl. apply Z.divide_lcm_l.
  - split.
    + rewrite Hl. apply Z.divide_lcm_r.
    + unfold period. apply Z.gcd_div_swap.
Qed.

Theorem generalized_crt_proved : T_generalized_CRT.
Proof.
  unfold T_generalized_CRT. intros a m b n Hm Hn.
  unfold compatible, solution, congruent. split.
  - intros [x [Hmx Hnx]].
    replace (b - a) with ((x - a) - (x - b)) by ring.
    apply Z.divide_sub_r.
    + eapply Z.divide_trans; [apply Z.gcd_divide_l | exact Hmx].
    + eapply Z.divide_trans; [apply Z.gcd_divide_r | exact Hnx].
  - intros [k Hk].
    destruct (Z.gcd_bezout m n (Z.gcd m n) eq_refl) as [u [v Huv]].
    exists (a + m * (k * u)). split.
    + exists (k * u). ring.
    + exists (-k * v).
      replace (a + m * (k * u) - b)
        with (k * (u * m + v * n) - (b - a) - k * v * n) by ring.
      rewrite Huv. nia.
Qed.

Lemma solution_difference : forall a m b n x y,
  0 < m -> 0 < n -> solution a m b n x ->
  (solution a m b n y <-> (period m n | y - x)).
Proof.
  intros a m b n x y Hm Hn [Hmx Hnx].
  destruct (reduction_proved m n Hm Hn) as
    [Hg [Hgm [Hgn [Hm1 [Hn1 [Hcop [Hl Hp]]]]]]].
  unfold solution, congruent in *. rewrite Hl, Z.lcm_divide_iff.
  split; intros [Hy1 Hy2]; split.
  - replace (y - x) with ((y - a) - (x - a)) by ring.
    apply Z.divide_sub_r; assumption.
  - replace (y - x) with ((y - b) - (x - b)) by ring.
    apply Z.divide_sub_r; assumption.
  - replace (y - a) with ((y - x) + (x - a)) by ring.
    apply Z.divide_add_r; assumption.
  - replace (y - b) with ((y - x) + (x - b)) by ring.
    apply Z.divide_add_r; assumption.
Qed.

Theorem all_solutions_proved : T_all_solutions.
Proof.
  unfold T_all_solutions. intros a m b n x Hm Hn Hx y.
  rewrite (solution_difference a m b n x y Hm Hn Hx).
  split; intros [k Hk]; exists k; lia.
Qed.

Theorem canonical_unique_proved : T_canonical_unique.
Proof.
  unfold T_canonical_unique. intros a m b n Hm Hn Hcompat.
  destruct (proj2 (generalized_crt_proved a m b n Hm Hn) Hcompat) as [x Hx].
  destruct (period_properties m n Hm Hn) as [Hp _].
  pose proof (Z.mod_pos_bound x (period m n) Hp) as Hrange.
  assert (Hcanon : canonical a m b n (x mod period m n)).
  { split; [exact Hrange |].
    apply (proj2 (solution_difference a m b n x _ Hm Hn Hx)).
    exists (-(x / period m n)).
    pose proof (Z.div_mod x (period m n) ltac:(lia)). nia. }
  exists (x mod period m n). split; [exact Hcanon |].
  intros y [Hy HySol]. destruct Hcanon as [_ Hmod].
  destruct (proj1 (all_solutions_proved a m b n _ Hm Hn Hmod y) HySol)
    as [k Hk].
  assert (k = 0) by nia. nia.
Qed.

Theorem incompatible_proved : T_incompatible.
Proof.
  unfold T_incompatible. intros a m b n Hm Hn Hnot x Hx.
  apply Hnot. apply (proj1 (generalized_crt_proved a m b n Hm Hn)).
  exists x. exact Hx.
Qed.

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

(* Keeping the common envelope in named facts makes the numerical safety
   argument independent of the particular inverse candidate. *)
Theorem crt_bounds_proved : T_crt_bounds.
Proof.
  unfold T_crt_bounds. intros a m b n Hdom Hcompat. cbn zeta.
  destruct Hdom as [[Hm Hn] [Ha Hb]].
  destruct (reduction_proved m n ltac:(lia) ltac:(lia)) as
    [Hg [Hgm [Hgn [Hm1 [Hn1 [Hcop [Hl Hp]]]]]]].
  pose proof (exact_division _ _ Hg Hgm) as Hmeq.
  pose proof (exact_division _ _ Hg Hgn) as Hneq.
  pose proof (exact_division _ _ Hg Hcompat) as Hdeq.
  pose proof (Z.divide_pos_le (Z.gcd m n) m ltac:(lia) Hgm) as Hgmle.
  destruct (period_properties m n ltac:(lia) ltac:(lia)) as [_ [_ [_ Hperiod]]].
  set (g := Z.gcd m n) in *.
  set (m1 := m / g) in *.
  set (n1 := n / g) in *.
  set (d := (b - a) / g) in *.
  assert (HM : 1 <= M) by (unfold M; lia).
  assert (HgB : 1 <= g <= M) by lia.
  assert (HmB : 1 <= m1 <= M) by nia.
  assert (HnB : 1 <= n1 <= M) by nia.
  assert (Hdelta : Z.abs (b - a) <= M - 1) by (apply Z.abs_le; lia).
  assert (Hd : Z.abs d <= M - 1).
  { assert (He : Z.abs (b - a) = g * Z.abs d).
    { rewrite Hdeq, Z.abs_mul, (Z.abs_eq g ltac:(lia)). reflexivity. }
    pose proof (Z.abs_nonneg d). nia. }
  assert (HL : 1 <= period m n <= M * M).
  { rewrite Hperiod. nia. }
  assert (HLword : word (period m n)).
  { unfold word, i64_min, i64_max. unfold M in HL. lia. }
  assert (Hrem : 1 < n1 -> 1 <= m1 mod n1 < n1).
  { intros Hlarge. pose proof (Z.mod_pos_bound m1 n1 Hn1) as Hr.
    assert (Hcopmod : Z.gcd (m1 mod n1) n1 = 1).
    { rewrite Z.gcd_mod by lia. rewrite Z.gcd_comm. exact Hcop. }
    assert (m1 mod n1 <> 0).
    { intro Hz. rewrite Hz, Z.gcd_0_l, Z.abs_eq in Hcopmod by lia. lia. }
    lia. }
  do 8 (split; [assumption |]).
  intros u Hu. cbn zeta.
  pose proof (Z.mod_pos_bound (d * u) n1 Hn1) as Ht.
  assert (HuB : 0 <= u <= M - 1) by lia.
  assert (Hproduct : Z.abs (d * u) <= (M - 1) * (M - 1)).
  { rewrite Z.abs_mul, (Z.abs_eq u ltac:(lia)).
    pose proof (Z.abs_nonneg d). nia. }
  assert (Hproductword : word (d * u)).
  { apply Z.abs_le in Hproduct.
    unfold word, i64_min, i64_max. unfold M in Hproduct. lia. }
  assert (Hmt : 0 <= m * ((d * u) mod n1) <= M * (M - 1)).
  { clear - Hm Ht HnB. nia. }
  assert (Hmtword : word (m * ((d * u) mod n1))).
  { unfold word, i64_min, i64_max. unfold M in Hmt. lia. }
  assert (Hx : 0 <= a + m * ((d * u) mod n1) < period m n).
  { rewrite Hperiod. clear - Hm Ha Ht. nia. }
  assert (Hxword : word (a + m * ((d * u) mod n1))).
  { unfold word, i64_min, i64_max. unfold M in HL. lia. }
  do 6 (split; [assumption |]). exact Hxword.
Qed.

Print Assumptions normalization_proved.
Print Assumptions reduction_proved.
Print Assumptions generalized_crt_proved.
Print Assumptions canonical_unique_proved.
Print Assumptions all_solutions_proved.
Print Assumptions incompatible_proved.
Print Assumptions construct_proved.
Print Assumptions crt_bounds_proved.
