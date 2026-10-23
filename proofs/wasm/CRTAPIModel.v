(* Concrete mathematical results for the generated public API.  These lemmas
   specify the interpretation used by a Wasm proof; they do not assert that
   any Wasm function realizes that interpretation. *)
From Coq Require Import ZArith Lia Bool.
From CRT Require Import CRTStatements CRTMath.
Open Scope Z_scope.

Definition crt_moduli_b (m n : Z) : bool :=
  (1 <=? m) && (m <=? M) && (1 <=? n) && (n <=? M).

Definition crt_domain_b (a m b n : Z) : bool :=
  crt_moduli_b m n && (0 <=? a) && (a <? m) && (0 <=? b) && (b <? n).

Lemma crt_moduli_b_spec m n : crt_moduli_b m n = true <-> moduli m n.
Proof.
  unfold crt_moduli_b, moduli. rewrite !andb_true_iff, !Z.leb_le. tauto.
Qed.

Lemma crt_domain_b_spec a m b n : crt_domain_b a m b n = true <-> domain a m b n.
Proof.
  unfold crt_domain_b, domain.
  rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt, crt_moduli_b_spec. tauto.
Qed.

Definition crt_inverse_Z (B A : Z) : Z :=
  let '(_, v, _) := Znumtheory.extgcd A B in v mod A.

Lemma crt_inverse_Z_correct B A : 0 < A -> Z.gcd A B = 1 ->
  0 <= crt_inverse_Z B A < A /\ congruent A (B * crt_inverse_Z B A) 1.
Proof.
  intros HA Hcop. unfold crt_inverse_Z.
  destruct (Znumtheory.extgcd A B) as [[u v] g] eqn:He.
  pose proof (Znumtheory.extgcd_correct A B He) as [Hbez Hg].
  split; [apply Z.mod_pos_bound; exact HA |].
  unfold congruent. exists (-u - B * (v / A)).
  pose proof (Z.div_mod v A ltac:(lia)). rewrite Hg, Hcop in Hbez. nia.
Qed.

Lemma crt_inverse_Z_unique B A u : 0 < A -> Z.gcd A B = 1 ->
  0 <= u < A -> congruent A (B * u) 1 -> u = crt_inverse_Z B A.
Proof.
  intros HA Hcop Hu Hinv.
  destruct (crt_inverse_Z_correct B A HA Hcop) as [Hv Hiv].
  assert (HD : (A | B * (u - crt_inverse_Z B A))).
  { replace (B * (u - crt_inverse_Z B A))
      with ((B * u - 1) - (B * crt_inverse_Z B A - 1)) by ring.
    apply Z.divide_sub_r; assumption. }
  destruct (Z.gauss A B (u - crt_inverse_Z B A) HD Hcop) as [k Hk].
  assert (k = 0) by nia. nia.
Qed.

Definition crt_period_Z (m n : Z) : Z :=
  if crt_moduli_b m n then period m n else -2.

Definition crt_solve_Z (a m b n : Z) : Z :=
  if crt_domain_b a m b n then
    let g := Z.gcd m n in
    if Z.rem (b - a) g =? 0 then
      let m1 := m / g in
      let n1 := n / g in
      if n1 =? 1 then a
      else a + m * (((b - a) / g * crt_inverse_Z (m1 mod n1) n1) mod n1)
    else -1
  else -2.

Lemma crt_period_bounds m n : moduli m n ->
  1 <= period m n <= M * M /\ word (period m n).
Proof.
  intros [Hm Hn].
  destruct (reduction_proved m n ltac:(lia) ltac:(lia)) as
    [Hg [Hgm [Hgn [Hm1 [Hn1 [Hcop [Hl Hp]]]]]]].
  pose proof (exact_division _ _ Hg Hgm) as Hmeq.
  assert (HB : 1 <= period m n <= M * M).
  { unfold period. assert (m / Z.gcd m n <= M) by nia. nia. }
  split; [exact HB |]. unfold word, i64_min, i64_max. unfold M in HB. lia.
Qed.

Theorem crt_period_Z_correct m n :
  period_post m n (crt_period_Z m n) /\ word (crt_period_Z m n).
Proof.
  unfold crt_period_Z. destruct (crt_moduli_b m n) eqn:Hdomain.
  - apply crt_moduli_b_spec in Hdomain.
    destruct (crt_period_bounds m n Hdomain) as [HB HW].
    split; [|exact HW]. right. split; [exact Hdomain |].
    destruct Hdomain as [Hm Hn].
    destruct (reduction_proved m n ltac:(lia) ltac:(lia)) as
      [_ [_ [_ [_ [_ [_ [Hl _]]]]]]]. exact Hl.
  - split.
    + left. split; [|reflexivity].
      intro H. apply crt_moduli_b_spec in H. congruence.
    + unfold word, i64_min, i64_max. lia.
Qed.

Lemma crt_solve_Z_canonical a m b n :
  domain a m b n -> compatible a m b n ->
  canonical a m b n (crt_solve_Z a m b n).
Proof.
  intros Hdomain Hcompat.
  pose proof Hdomain as [[Hm Hn] [Ha Hb]].
  unfold crt_solve_Z. rewrite (proj2 (crt_domain_b_spec a m b n) Hdomain).
  pose proof (gcd_positive m n ltac:(lia)) as Hg.
  assert (Hr : Z.rem (b - a) (Z.gcd m n) = 0).
  { apply Z.rem_divide; [lia | exact Hcompat]. }
  rewrite Hr, Z.eqb_refl.
  destruct (Z.eqb_spec (n / Z.gcd m n) 1) as [Hone|Hmany].
  - exact (proj1 (construct_proved a m b n Hdomain Hcompat) Hone).
  - destruct (reduction_proved m n ltac:(lia) ltac:(lia)) as
      [_ [_ [_ [Hm1 [Hn1 [Hcop _]]]]]].
    set (m1 := m / Z.gcd m n) in *.
    set (n1 := n / Z.gcd m n) in *.
    assert (HcopB : Z.gcd n1 (m1 mod n1) = 1).
    { rewrite Z.gcd_comm, Z.gcd_mod by lia. rewrite Z.gcd_comm. exact Hcop. }
    destruct (crt_inverse_Z_correct (m1 mod n1) n1 Hn1 HcopB) as [Hu Hinv].
    apply (proj2 (construct_proved a m b n Hdomain Hcompat) ltac:(lia)
      (crt_inverse_Z (m1 mod n1) n1) Hu).
    unfold congruent in *. destruct Hinv as [k Hk].
    exists (k + (m1 / n1) * crt_inverse_Z (m1 mod n1) n1).
    pose proof (Z.div_mod m1 n1 ltac:(lia)). nia.
Qed.

Theorem crt_solve_Z_correct a m b n :
  solve_post a m b n (crt_solve_Z a m b n) /\ word (crt_solve_Z a m b n).
Proof.
  destruct (crt_domain_b a m b n) eqn:Hd.
  - apply crt_domain_b_spec in Hd.
    pose proof Hd as [[Hm Hn] [Ha Hb]].
    pose proof (gcd_positive m n ltac:(lia)) as Hg.
    destruct (Z.eqb_spec (Z.rem (b - a) (Z.gcd m n)) 0) as [Hr|Hr].
    + assert (Hcompat : compatible a m b n).
      { apply Z.rem_divide; [lia | exact Hr]. }
      pose proof (crt_solve_Z_canonical a m b n Hd Hcompat) as Hcanon.
      split.
      * right. right. exact (conj Hd (conj Hcompat Hcanon)).
      * destruct Hcanon as [HX _].
        destruct (crt_period_bounds m n (proj1 Hd)) as [HL _].
        unfold word, i64_min, i64_max. unfold M in HL. lia.
    + assert (Hnot : ~ compatible a m b n).
      { intro HC. apply Hr. apply Z.rem_divide; [lia | exact HC]. }
      assert (HE : crt_solve_Z a m b n = -1).
      { unfold crt_solve_Z. rewrite (proj2 (crt_domain_b_spec a m b n) Hd).
        destruct (Z.eqb_spec (Z.rem (b - a) (Z.gcd m n)) 0); congruence. }
      rewrite HE. split.
      * right. left. exact (conj Hd (conj Hnot eq_refl)).
      * unfold word, i64_min, i64_max. lia.
  - assert (Hnot : ~ domain a m b n).
    { intro H. apply crt_domain_b_spec in H. congruence. }
    assert (HE : crt_solve_Z a m b n = -2) by (unfold crt_solve_Z; rewrite Hd; reflexivity).
    rewrite HE. split.
    + left. exact (conj Hnot eq_refl).
    + unfold word, i64_min, i64_max. lia.
Qed.

Theorem crt_solve_Z_unique a m b n x :
  domain a m b n -> canonical a m b n x -> x = crt_solve_Z a m b n.
Proof.
  intros Hdomain Hx. pose proof Hdomain as [[Hm Hn] _].
  assert (Hcompat : compatible a m b n).
  { apply (proj1 (generalized_crt_proved a m b n ltac:(lia) ltac:(lia))).
    exists x. exact (proj2 Hx). }
  destruct (canonical_unique_proved a m b n ltac:(lia) ltac:(lia) Hcompat)
    as [y [Hy Hunique]].
  transitivity y; [exact (Hunique x Hx) |]. symmetry. apply Hunique.
  exact (crt_solve_Z_canonical a m b n Hdomain Hcompat).
Qed.

Lemma crt_canonical_remainders a m b n x :
  domain a m b n -> canonical a m b n x ->
  Z.rem x m = a /\ Z.rem x n = b.
Proof.
  intros [[Hm Hn] [Ha Hb]] [Hx [Hxma Hxnb]].
  rewrite !Z.rem_mod_nonneg by lia. split.
  - apply Znumtheory.Zdivide_mod_minus; assumption.
  - apply Znumtheory.Zdivide_mod_minus; assumption.
Qed.

Lemma crt_remainders_solution a m b n x :
  0 < m -> 0 < n -> 0 <= x ->
  Z.rem x m = a -> Z.rem x n = b -> solution a m b n x.
Proof.
  intros Hm Hn Hx Ha Hb.
  rewrite Z.rem_mod_nonneg in Ha, Hb by lia.
  split; unfold congruent.
  - apply (Znumtheory.Zmod_divide_minus x m a Hm Ha).
  - apply (Znumtheory.Zmod_divide_minus x n b Hn Hb).
Qed.

Theorem crt_solve_Z_domain_contract a m b n :
  (~ domain a m b n -> crt_solve_Z a m b n = -2) /\
  (domain a m b n -> -1 <= crt_solve_Z a m b n).
Proof.
  destruct (crt_solve_Z_correct a m b n) as [Hpost _].
  unfold solve_post in Hpost.
  destruct Hpost as [[Hbad Hr]|[[Hd [Hbad Hr]]|[Hd [HC [Hx HS]]]]]; split; intros; try contradiction; lia.
Qed.

Theorem crt_solve_Z_compatibility_contract a m b n :
  domain a m b n ->
  (Z.rem (b - a) (Z.gcd m n) = 0 -> 0 <= crt_solve_Z a m b n) /\
  (Z.rem (b - a) (Z.gcd m n) <> 0 -> crt_solve_Z a m b n = -1).
Proof.
  intros Hd. pose proof Hd as [[Hm Hn] _].
  pose proof (gcd_positive m n ltac:(lia)) as Hg.
  destruct (crt_solve_Z_correct a m b n) as [Hpost _].
  unfold solve_post in Hpost. destruct Hpost as [[Hbad Hr]|[[_ [Hbad Hr]]|[_ [HC [Hx HS]]]]].
  - contradiction.
  - split; [|intros; exact Hr]. intros Hrem. exfalso. apply Hbad.
    apply Z.rem_divide; [lia | exact Hrem].
  - split; [intros; lia |]. intros Hrem. exfalso. apply Hrem.
    apply Z.rem_divide; [lia | exact HC].
Qed.

Theorem crt_solve_Z_solution_contract a m b n :
  domain a m b n -> 0 <= crt_solve_Z a m b n ->
  crt_solve_Z a m b n < crt_period_Z m n /\
  Z.rem (crt_solve_Z a m b n) m = a /\
  Z.rem (crt_solve_Z a m b n) n = b.
Proof.
  intros Hd Hnonneg.
  destruct (crt_solve_Z_correct a m b n) as [Hpost _].
  unfold solve_post in Hpost. destruct Hpost as [[Hbad Hr]|[[_ [_ Hr]]|[_ [_ Hcanon]]]].
  - contradiction.
  - lia.
  - split.
    + unfold crt_period_Z. rewrite (proj2 (crt_moduli_b_spec m n) (proj1 Hd)).
      exact (proj2 (proj1 Hcanon)).
    + exact (crt_canonical_remainders a m b n _ Hd Hcanon).
Qed.

Theorem crt_solve_Z_impossibility_contract a m b n y :
  domain a m b n -> crt_solve_Z a m b n = -1 -> 0 <= y ->
  Z.rem y m <> a \/ Z.rem y n <> b.
Proof.
  intros Hd Hreject Hy. pose proof Hd as [[Hm Hn] _].
  destruct (Z.eq_dec (Z.rem y m) a) as [Ha|Ha]; [|left; exact Ha].
  right. intro Hb.
  pose proof (crt_remainders_solution a m b n y ltac:(lia) ltac:(lia) Hy Ha Hb) as HS.
  assert (HC : compatible a m b n).
  { apply (proj1 (generalized_crt_proved a m b n ltac:(lia) ltac:(lia))). exists y. exact HS. }
  pose proof (crt_solve_Z_canonical a m b n Hd HC) as [[Hnonneg _] _]. lia.
Qed.

Theorem crt_solve_Z_existence_contract a m b n :
  domain a m b n -> Z.rem (b - a) (Z.gcd m n) = 0 ->
  exists x, word x /\ 0 <= x < crt_period_Z m n /\
    Z.rem x m = a /\ Z.rem x n = b /\ x = crt_solve_Z a m b n /\
    forall y, 0 <= y < crt_period_Z m n ->
      Z.rem y m = a -> Z.rem y n = b -> y = x.
Proof.
  intros Hd Hrem. pose proof Hd as [[Hm Hn] _].
  pose proof (gcd_positive m n ltac:(lia)) as Hg.
  assert (HC : compatible a m b n) by (apply Z.rem_divide; [lia | exact Hrem]).
  pose proof (crt_solve_Z_canonical a m b n Hd HC) as Hcanon.
  pose proof (crt_canonical_remainders a m b n _ Hd Hcanon) as [Hra Hrb].
  assert (HL : crt_period_Z m n = period m n).
  { unfold crt_period_Z. rewrite (proj2 (crt_moduli_b_spec m n) (proj1 Hd)). reflexivity. }
  exists (crt_solve_Z a m b n).
  split; [exact (proj2 (crt_solve_Z_correct a m b n)) |].
  split; [rewrite HL; exact (proj1 Hcanon) |].
  split; [exact Hra |]. split; [exact Hrb |]. split; [reflexivity |].
  intros y Hy Hya Hyb. apply crt_solve_Z_unique; [exact Hd |].
  split; [rewrite <- HL; exact Hy |].
  apply crt_remainders_solution; try assumption; lia.
Qed.

Theorem crt_gcd_Z_source_contract m n : moduli m n ->
  let g := Z.gcd m n in
  1 <= g /\ g <= m /\ g <= n /\ Z.rem m g = 0 /\ Z.rem n g = 0 /\
  forall d, 1 <= d <= M -> Z.rem m d = 0 -> Z.rem n d = 0 -> Z.rem g d = 0.
Proof.
  intros [Hm Hn]. cbn zeta.
  pose proof (gcd_positive m n ltac:(lia)) as Hg.
  pose proof (Z.gcd_divide_l m n) as Hgm.
  pose proof (Z.gcd_divide_r m n) as Hgn.
  split; [lia |]. split; [apply Z.divide_pos_le; [lia | exact Hgm] |].
  split; [apply Z.divide_pos_le; [lia | exact Hgn] |].
  split; [apply Z.rem_divide; [lia | exact Hgm] |].
  split; [apply Z.rem_divide; [lia | exact Hgn] |].
  intros d Hd Hdm Hdn. apply Z.rem_divide; [lia |].
  apply Z.gcd_greatest; apply Z.rem_divide; try lia; assumption.
Qed.

Theorem crt_inverse_Z_source_contract B A : eea_inputs A B -> Z.gcd A B = 1 ->
  let u := crt_inverse_Z B A in
  0 <= u < A /\ Z.rem (B * u) A = 1 /\ word (B * u).
Proof.
  intros [[HB HBA] HA] Hcop. cbn zeta.
  destruct (crt_inverse_Z_correct B A ltac:(lia) Hcop) as [Hu Hcong].
  split; [exact Hu |]. split.
  - rewrite Z.rem_mod_nonneg by nia.
    apply Znumtheory.Zdivide_mod_minus; [lia | exact Hcong].
  - assert (Hprod : 0 <= B * crt_inverse_Z B A <= M * M) by nia.
    unfold word, i64_min, i64_max. unfold M in Hprod. lia.
Qed.

Print Assumptions crt_period_Z_correct.
Print Assumptions crt_solve_Z_correct.
Print Assumptions crt_solve_Z_unique.
Print Assumptions crt_solve_Z_domain_contract.
Print Assumptions crt_solve_Z_compatibility_contract.
Print Assumptions crt_solve_Z_solution_contract.
Print Assumptions crt_solve_Z_impossibility_contract.
Print Assumptions crt_solve_Z_existence_contract.
Print Assumptions crt_gcd_Z_source_contract.
Print Assumptions crt_inverse_Z_source_contract.
