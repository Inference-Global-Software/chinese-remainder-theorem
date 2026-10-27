(* Finite-list generalized CRT. Mathcomp supplies the proved distributive law;
   all bridges below are proved through divisibility universal properties. *)
From Coq Require Import ZArith Lia List Bool Permutation.
From mathcomp Require Import ssrnat div order.
From CRT Require Import CRTStatements CRTSystemStatements CRTMath CRTSystemArithmetic.
Import ListNotations FullWidth.
Open Scope Z_scope.

Lemma nat_dvd_bridge : forall a b : nat,
  (Z.of_nat a | Z.of_nat b) <-> dvdn a b = true.
Proof.
  intros a b. rewrite <- (Bool.reflect_iff _ _ (@dvdnP a b)).
  rewrite mulnE. split.
  - intros [k Hk]. exists (Z.to_nat (Z.abs k)).
    apply Nat2Z.inj. rewrite Nat2Z.inj_mul, Z2Nat.id by apply Z.abs_nonneg.
    pose proof (f_equal Z.abs Hk) as Habs.
    rewrite Z.abs_mul in Habs.
    rewrite (Z.abs_eq (Z.of_nat a)), (Z.abs_eq (Z.of_nat b)) in Habs by lia. exact Habs.
  - intros [k Hk]. exists (Z.of_nat k). rewrite Hk, Nat2Z.inj_mul. reflexivity.
Qed.

Lemma nat_gcd_bridge : forall a b,
  Z.gcd (Z.of_nat a) (Z.of_nat b) = Z.of_nat (gcdn a b).
Proof.
  intros a b. apply Z.divide_antisym_nonneg; try apply Z.gcd_nonneg; try lia.
  - set (g := Z.gcd (Z.of_nat a) (Z.of_nat b)).
    assert (Hg : 0 <= g) by apply Z.gcd_nonneg.
    replace g with (Z.of_nat (Z.to_nat g)) by (rewrite Z2Nat.id; lia).
    apply nat_dvd_bridge. rewrite dvdn_gcd. apply andb_true_iff. split;
      apply nat_dvd_bridge; rewrite Z2Nat.id by lia;
      unfold g; [apply Z.gcd_divide_l | apply Z.gcd_divide_r].
  - apply Z.gcd_greatest; apply nat_dvd_bridge;
      [apply dvdn_gcdl | apply dvdn_gcdr].
Qed.

Lemma nat_lcm_bridge : forall a b,
  Z.lcm (Z.of_nat a) (Z.of_nat b) = Z.of_nat (lcmn a b).
Proof.
  intros a b. apply Z.divide_antisym_nonneg; try apply Z.lcm_nonneg; try lia.
  - apply Z.lcm_least; apply nat_dvd_bridge;
      [apply dvdn_lcml | apply dvdn_lcmr].
  - set (l := Z.lcm (Z.of_nat a) (Z.of_nat b)).
    assert (Hl : 0 <= l) by apply Z.lcm_nonneg.
    replace l with (Z.of_nat (Z.to_nat l)) by (rewrite Z2Nat.id; lia).
    apply nat_dvd_bridge. rewrite dvdn_lcm. apply andb_true_iff. split;
      apply nat_dvd_bridge; rewrite Z2Nat.id by lia;
      unfold l; [apply Z.divide_lcm_l | apply Z.divide_lcm_r].
Qed.

Lemma gcd_lcm_distributive : forall a b c,
  0 <= a -> 0 <= b -> 0 <= c ->
  Z.gcd a (Z.lcm b c) = Z.lcm (Z.gcd a b) (Z.gcd a c).
Proof.
  intros a b c Ha Hb Hc.
  replace a with (Z.of_nat (Z.to_nat a)) by (rewrite Z2Nat.id; lia).
  replace b with (Z.of_nat (Z.to_nat b)) by (rewrite Z2Nat.id; lia).
  replace c with (Z.of_nat (Z.to_nat c)) by (rewrite Z2Nat.id; lia).
  rewrite !nat_lcm_bridge, !nat_gcd_bridge, nat_lcm_bridge.
  rewrite (gcdnC (Z.to_nat a) (lcmn (Z.to_nat b) (Z.to_nat c))).
  rewrite Order.NatDvd.meetUl, (gcdnC (Z.to_nat b) (Z.to_nat a)),
    (gcdnC (Z.to_nat c) (Z.to_nat a)). reflexivity.
Qed.
Print Assumptions gcd_lcm_distributive.

Import FiniteSystem.
Lemma positive_tail : forall c C, positive (c::C) -> positive C.
Proof. intros c C H; inversion H; assumption. Qed.
Lemma valid_positive : forall C, valid C -> positive C.
Proof.
  intros C H. induction H; constructor; unfold valid_entry in *; cbn in *; tauto || lia.
Qed.
Lemma L_positive : forall C, positive C -> 0 < L C.
Proof.
  intros C H. induction H as [|[a m] C Hm HC IH]; cbn; [lia|].
  cbn in Hm. destruct (reduction_proved m (L C) Hm IH) as
    (_ & _ & _ & _ & _ & _ & Hl & Hp). rewrite <- Hl. exact Hp.
Qed.
Lemma L_universal : forall C d, (L C | d) <->
  forall a m, In (a,m) C -> (m | d).
Proof.
  induction C as [|[a m] C IH]; intros d; cbn.
  - split; intros; [contradiction|apply Z.divide_1_l].
  - rewrite Z.lcm_divide_iff, IH. split.
    + intros (Hm & HC) b n [Heq|Hin]; [inversion Heq; subst; assumption|eauto].
    + intros H. split; [apply (H a m); auto|]. intros b n Hin. apply (H b n); auto.
Qed.
Theorem period_subsystem_proved : T_period_subsystem.
Proof.
  intros A B Hinc. apply L_universal. intros a m Hin.
  apply (proj1 (L_universal B (L B)) (Z.divide_refl _) a m). apply Hinc; assumption.
Qed.
Lemma L_app : forall A B, L (A++B) = Z.lcm (L A) (L B).
Proof.
  induction A as [|[a m] A IH]; intros B; cbn.
  - rewrite Z.lcm_1_l. symmetry. apply Z.abs_eq. destruct B as [|[a m] B]; cbn; [lia|apply Z.lcm_nonneg].
  - rewrite IH, Z.lcm_assoc. reflexivity.
Qed.
Lemma Sol_nil : forall x, Sol [] x.
Proof. intros x a m H; contradiction. Qed.
Lemma Sol_cons : forall a m C x,
  Sol ((a,m)::C) x <-> congruent m x a /\ Sol C x.
Proof.
  intros a m C x. unfold Sol. split.
  - intros H. split; [apply H; left; reflexivity|]. intros; apply H; right; assumption.
  - intros (H & HC) b n [Heq|Hin]; [inversion Heq; subst; assumption|eauto].
Qed.
Lemma Sol_app : forall A B x, Sol (A++B) x <-> Sol A x /\ Sol B x.
Proof.
  intros A B x. unfold Sol. setoid_rewrite in_app_iff. firstorder.
Qed.
Lemma finite_difference : forall C r, Sol C r ->
  forall x, Sol C x <-> congruent (L C) x r.
Proof.
  intros C r Hr x. unfold congruent. rewrite L_universal. split.
  - intros Hx a m Hin. replace (x-r) with ((x-a)-(r-a)) by ring.
    apply Z.divide_sub_r; [apply Hx|apply Hr]; assumption.
  - intros H a m Hin. unfold congruent.
    replace (x-a) with ((x-r)+(r-a)) by ring.
    apply Z.divide_add_r; [apply (H a m)|apply Hr]; assumption.
Qed.
Lemma Pairwise_necessary : forall C x, positive C -> Sol C x -> Pairwise C.
Proof.
  intros C x Hpos Hsol a m b n Ham Hbn.
  apply Forall_forall with (x:=(a,m)) in Hpos as Hm; [cbn in Hm|assumption].
  apply Forall_forall with (x:=(b,n)) in Hpos as Hn; [cbn in Hn|assumption].
  apply (proj1 (generalized_crt_proved a m b n Hm Hn)). exists x; split; apply Hsol; assumption.
Qed.
Lemma Pairwise_tail : forall c C, Pairwise (c::C) -> Pairwise C.
Proof. intros c C H a m b n Ham Hbn. apply H; right; assumption. Qed.
Lemma gcd_L_divides : forall C n d,
  positive C -> 0 < n ->
  (forall a m, In (a,m) C -> (Z.gcd m n | d)) -> (Z.gcd (L C) n | d).
Proof.
  intros C n d Hpos Hn. induction Hpos as [|[a m] C Hm HC IH]; intros H.
  - change (Z.gcd 1 n | d). rewrite Z.gcd_1_l. apply Z.divide_1_l.
  - cbn in Hm |- *. rewrite Z.gcd_comm, gcd_lcm_distributive by
      (try lia; pose proof (L_positive C HC); lia).
    apply Z.lcm_least.
    + rewrite Z.gcd_comm. apply (H a m); left; reflexivity.
    + rewrite Z.gcd_comm. apply IH. intros b p Hin. apply (H b p); right; assumption.
Qed.
Theorem finite_existence_proved : T_finite_existence.
Proof.
  intros C Hpos. split.
  - intros [x Hx]. eapply Pairwise_necessary; eauto.
  - induction Hpos as [|[a m] C Hm HC IH]; intros Hpair.
    + exists 0. apply Sol_nil.
    + cbn in Hm. destruct (IH (Pairwise_tail _ _ Hpair)) as [r Hr].
      assert (Hcomp : compatible r (L C) a m).
      { unfold compatible. apply gcd_L_divides; try assumption.
        intros b n Hin.
        pose proof (Hpair b n a m (or_intror Hin) (or_introl eq_refl)) as Hba.
        pose proof (Hr b n Hin) as Hbr.
        unfold compatible, congruent in *.
        replace (a-r) with ((a-b)-(r-b)) by ring.
        apply Z.divide_sub_r; [exact Hba|].
        eapply Z.divide_trans; [apply Z.gcd_divide_l|exact Hbr]. }
      destruct (proj2 (generalized_crt_proved r (L C) a m (L_positive C HC) Hm) Hcomp)
        as [x [Hxr Hxa]].
      exists x. apply Sol_cons. split; [assumption|].
      apply (proj2 (finite_difference C r Hr x)); assumption.
Qed.
Lemma representation_from_solution : forall C x,
  positive C -> Sol C x -> Rep C (x mod L C) (L C).
Proof.
  intros C x HC Hx. pose proof (L_positive C HC) as HL.
  assert (Hr : Sol C (x mod L C)).
  { apply (proj2 (finite_difference C x Hx _)). unfold congruent.
    exists (-(x / L C)). pose proof (Z.div_mod x (L C) ltac:(lia)); nia. }
  split; [reflexivity|]. split; [apply Z.mod_pos_bound; assumption|].
  apply finite_difference; assumption.
Qed.
Lemma Rep_solution : forall C r p, Rep C r p -> Sol C r.
Proof.
  intros C r p (_ & _ & Hrep). apply Hrep. unfold congruent. rewrite Z.sub_diag. apply Z.divide_0_r.
Qed.
Lemma Rep_unique : forall C r p s q,
  Rep C r p -> Rep C s q -> r=s /\ p=q.
Proof.
  intros C r p s q (Hp & Hr & HC) Hsrep.
  pose proof (Rep_solution _ _ _ Hsrep) as Hs.
  destruct Hsrep as (Hq & Hsr & _). subst q p.
  destruct (proj1 (HC s) Hs) as [k Hk]. assert (k=0) by nia. split; [nia|reflexivity].
Qed.
Theorem finite_canonical_proved : T_finite_canonical.
Proof.
  intros C HC Hpair. destruct (proj2 (finite_existence_proved C HC) Hpair) as [x Hx].
  exists (x mod L C). pose proof (representation_from_solution C x HC Hx) as Hrep.
  split; [assumption|]. intros s Hs. exact (proj1 (Rep_unique _ _ _ _ _ Hs Hrep)).
Qed.
Theorem finite_all_solutions_proved : T_finite_all_solutions.
Proof.
  intros C r p (_ & _ & Hrep) x. rewrite Hrep. unfold congruent.
  split; intros [k Hk]; exists k; lia.
Qed.
Theorem composition_proved : T_composition.
Proof.
  intros A B r p s q HA HB (Hp & Hr & HArep) (Hq & Hs & HBrep).
  assert (Hsol : forall x, Sol (A++B) x <-> solution r p s q x).
  { intros x. rewrite Sol_app, HArep, HBrep. reflexivity. }
  split; [assumption|]. split.
  - rewrite Hp, Hq. apply L_app.
  - rewrite <- (generalized_crt_proved r p s q ltac:(lia) ltac:(lia)). split; intros [x Hx]; exists x; apply Hsol; assumption.
Qed.

Lemma validb_spec : forall c, validb c = true <-> valid_entry c.
Proof.
  intros [a m]. unfold validb, valid_entry; cbn.
  rewrite !andb_true_iff, !Z.leb_le, Z.ltb_lt. tauto.
Qed.
Lemma validate_loop_spec : forall C, validate_loop C = true <-> valid C.
Proof.
  induction C as [|c C IH]; cbn [validate_loop].
  - split; intros; constructor.
  - destruct (validb c) eqn:Hc.
    + rewrite IH. split; intros H; [constructor|inversion H];
        try assumption. apply validb_spec; assumption.
    + split; [discriminate|]. intros H. inversion H; subst.
      apply validb_spec in H2. congruence.
Qed.
Lemma compatible_sym : forall a m b n, compatible a m b n -> compatible b n a m.
Proof.
  intros a m b n H. unfold compatible in *. rewrite Z.gcd_comm.
  replace (a-b) with (-(b-a)) by ring. apply Z.divide_opp_r; assumption.
Qed.
Lemma compatible_refl : forall a m, compatible a m a m.
Proof. intros a m. unfold compatible. rewrite Z.sub_diag. apply Z.divide_0_r. Qed.
Lemma Pairwise_cons : forall a m C,
  Pairwise ((a,m)::C) <-> Pairwise C /\
  (forall b n, In (b,n) C -> compatible a m b n).
Proof.
  intros a m C. split.
  - intros H. split; [apply Pairwise_tail with (c:=(a,m)); assumption|].
    intros b n Hin. apply H; [left; reflexivity|right; assumption].
  - intros (HC & Hrow) b n d p [Heq|Hb] [Heq'|Hd].
    + inversion Heq; inversion Heq'; subst. apply compatible_refl.
    + inversion Heq; subst. apply Hrow; assumption.
    + inversion Heq'; subst. apply compatible_sym. apply Hrow; assumption.
    + apply HC; assumption.
Qed.
Lemma compatb_spec : forall a m b n, 0 < m ->
  compatb (a,m) (b,n) = true <-> compatible a m b n.
Proof.
  intros a m b n Hm. unfold compatb, compatible; cbn.
  rewrite Z.eqb_eq, Z.mod_divide; [reflexivity|pose proof (gcd_positive m n Hm); lia].
Qed.
Lemma pair_row_spec : forall a m C, 0 < m ->
  pair_row (a,m) C = true <-> forall b n, In (b,n) C -> compatible a m b n.
Proof.
  intros a m C Hm. induction C as [|[b n] C IH]; cbn [pair_row].
  - split; [intros _ b n H; contradiction|reflexivity].
  - destruct (compatb (a,m) (b,n)) eqn:Hb.
    + apply compatb_spec in Hb; [|assumption]. rewrite IH. split.
      * intros H d p [Heq|Hin]; [inversion Heq; subst; assumption|apply H; assumption].
      * intros H d p Hin. apply H; right; assumption.
    + split; [discriminate|]. intros H.
      assert (compatb (a,m) (b,n) = true) by (apply compatb_spec; [assumption|apply H; left; reflexivity]).
      congruence.
Qed.
Lemma pair_loop_spec : forall C, positive C ->
  pair_loop C = true <-> Pairwise C.
Proof.
  intros C Hpos. induction Hpos as [|[a m] C Hm HC IH]; cbn [pair_loop].
  - split; [intros _ a m b n H; contradiction|reflexivity].
  - cbn in Hm. rewrite Pairwise_cons. destruct (pair_row (a,m) C) eqn:Hr.
    + pose proof (proj1 (pair_row_spec a m C Hm) Hr) as Hrow. rewrite IH. tauto.
    + split; [discriminate|]. intros (_ & Hr').
      assert (pair_row (a,m) C = true) by (apply pair_row_spec; assumption). congruence.
Qed.
Lemma valid_pair : forall a m b n,
  valid [(a,m);(b,n)] <-> domain a m b n.
Proof.
  intros. unfold valid, domain, moduli, valid_entry.
  repeat rewrite Forall_cons_iff. cbn. split; intuition.
Qed.
Lemma positive_pair : forall a m b n, 0 < m -> 0 < n -> positive [(a,m);(b,n)].
Proof. intros. repeat constructor; assumption. Qed.
Lemma pair_Pairwise : forall a m b n,
  Pairwise [(a,m);(b,n)] <-> compatible a m b n.
Proof.
  intros. rewrite Pairwise_cons, Pairwise_cons. split.
  - intros (_ & H). apply H; left; reflexivity.
  - intros H. split.
    + split; unfold Pairwise; intros; contradiction.
    + intros c d [Heq|Hnil]; [inversion Heq; subst; assumption|contradiction].
Qed.
Lemma L_pair : forall a m b n, 0 < n -> L [(a,m);(b,n)] = Z.lcm m n.
Proof. intros. cbn [L]. rewrite Z.lcm_1_r, Z.abs_eq by lia. reflexivity. Qed.
Lemma canonical_Rep_pair : forall a m b n r,
  0 < m -> 0 < n -> canonical a m b n r -> Rep [(a,m);(b,n)] r (Z.lcm m n).
Proof.
  intros a m b n r Hm Hn (Hr & Hsol).
  destruct (reduction_proved m n Hm Hn) as (_ & _ & _ & _ & _ & _ & Hl & _).
  assert (Hs : Sol [(a,m);(b,n)] r).
  { rewrite !Sol_cons. destruct Hsol. repeat split; try assumption. apply Sol_nil. }
  split; [symmetry; apply L_pair; assumption|]. split; [rewrite <- Hl; assumption|].
  rewrite <- (L_pair a m b n Hn). apply finite_difference; assumption.
Qed.
Lemma merge_contract : forall a m b n, domain a m b n ->
  match merge a m b n with
  | Invalid => False
  | Inconsistent => ~ compatible a m b n
  | Overflow => compatible a m b n /\ MAX < Z.lcm m n
  | Success r p => compatible a m b n /\ p = Z.lcm m n /\ p <= MAX /\ canonical a m b n r
  end.
Proof.
  intros a m b n Hd. destruct Hd as ((Hm & Hn) & Ha & Hb).
  assert (Hd : domain a m b n) by (unfold domain, moduli; tauto).
  assert (Hv1 : validb (a,m)=true) by (apply validb_spec; unfold valid_entry; cbn; tauto).
  assert (Hv2 : validb (b,n)=true) by (apply validb_spec; unfold valid_entry; cbn; tauto).
  unfold merge. rewrite Hv1, Hv2. cbn [andb]. rewrite gcd_model_proved by (unfold moduli; tauto).
  destruct (reduction_proved m n ltac:(lia) ltac:(lia)) as
    (Hg & Hgm & Hgn & Hm1 & Hn1 & Hcop & Hl & Hp).
  destruct ((b-a) mod Z.gcd m n =? 0) eqn:Htest.
  - apply Z.eqb_eq in Htest.
    assert (Hcompat : compatible a m b n) by (unfold compatible; apply Z.mod_divide; lia || assumption).
    destruct (MAX/n <? m/Z.gcd m n) eqn:Hguard.
    + apply Z.ltb_lt in Hguard. split; [assumption|].
      apply (proj1 (proj1 (lcm_guard_proved m n ltac:(unfold moduli; tauto)))); lia.
    + apply Z.ltb_ge in Hguard.
      assert (HL : Z.lcm m n <= MAX).
      { pose proof (proj1 (lcm_guard_proved m n ltac:(unfold moduli; tauto))). lia. }
      change (period m n = Z.lcm m n) in Hl.
      split; [assumption|]. split; [exact Hl|]. split; [change (period m n <= MAX); rewrite Hl; assumption|].
      destruct (n/Z.gcd m n =? 1) eqn:Hone.
      * apply Z.eqb_eq in Hone. exact (proj1 (construct_proved a m b n Hd Hcompat) Hone).
      * apply Z.eqb_neq in Hone.
        assert (Hlarge : 1 < n/Z.gcd m n) by lia.
        set (n1:=n/Z.gcd m n) in *.
        set (m1:=m/Z.gcd m n) in *.
        assert (HB : 1 <= m1 mod n1 < n1).
        { pose proof (Z.mod_pos_bound m1 n1 Hn1).
          assert (Hc : Z.gcd (m1 mod n1) n1 = 1).
          { rewrite Z.gcd_mod by lia. rewrite Z.gcd_comm. assumption. }
          assert (m1 mod n1 <> 0).
          { intros Hzero. rewrite Hzero, Z.gcd_0_l, Z.abs_eq in Hc by lia; lia. } lia. }
        assert (Hnmax : n1 <= MAX).
        { pose proof (exact_division _ _ Hg Hgn); fold n1 in H; nia. }
        assert (Hc : Z.gcd n1 (m1 mod n1) = 1).
        { rewrite Z.gcd_comm, Z.gcd_mod by lia. rewrite Z.gcd_comm; assumption. }
        pose proof (inverse_model_proved n1 (m1 mod n1) ltac:(unfold eea_inputs; lia) Hc)
          as (Hu & Hinv).
        assert (Hinv' : congruent n1 (m1 * inverse_model (m1 mod n1) n1) 1).
        { destruct Hinv as [k Hk]. unfold congruent.
          exists (k + (m1/n1) * inverse_model (m1 mod n1) n1).
          pose proof (Z.div_mod m1 n1 ltac:(lia)); nia. }
        rewrite (proj1 (mul_mod_proved (((b-a)/Z.gcd m n) mod n1)
          (inverse_model (m1 mod n1) n1) n1 ltac:(lia)
          (Z.mod_pos_bound _ _ Hn1) Hu)).
        rewrite Z.mul_mod_idemp_l by lia.
        exact (proj2 (construct_proved a m b n Hd Hcompat) Hlarge _ Hu Hinv').
  - apply Z.eqb_neq in Htest. intros Hcomp. apply Htest.
    apply Z.mod_divide; [lia|exact Hcomp].
Qed.
Theorem scalar_model_proved : T_scalar_model.
Proof.
  intros a m b n. destruct (validb (a,m) && validb (b,n)) eqn:Hv.
  - apply andb_true_iff in Hv as [Ha Hb]. apply validb_spec in Ha; apply validb_spec in Hb.
    assert (Hd : domain a m b n) by (unfold domain, moduli, valid_entry in *; cbn in *; tauto).
    pose proof (merge_contract a m b n Hd) as Hc.
    destruct Hd as ((Hm & Hn) & _).
    destruct (merge a m b n) as [ | | | r p]; cbn [result_post] in *; [contradiction| | |].
    + split; [apply valid_pair; unfold domain, moduli; unfold valid_entry in *; cbn in *; tauto|].
      rewrite pair_Pairwise. assumption.
    + destruct Hc as (Hcomp & HL). repeat split.
      * apply valid_pair; unfold domain, moduli; unfold valid_entry in *; cbn in *; tauto.
      * apply pair_Pairwise; assumption.
      * rewrite L_pair by lia; assumption.
    + destruct Hc as (Hcomp & Hp & Hmax & Hcan). subst p.
      split; [apply valid_pair; unfold domain, moduli; unfold valid_entry in *; cbn in *; tauto|].
      split; [apply pair_Pairwise; assumption|]. split; [assumption|].
      apply canonical_Rep_pair; lia || assumption.
  - unfold merge. rewrite Hv. cbn [result_post]. intros Hvalid.
    apply valid_pair in Hvalid as ((Hm & Hn) & Ha & Hb).
    assert (validb (a,m)=true) by (apply validb_spec; unfold valid_entry; cbn; tauto).
    assert (validb (b,n)=true) by (apply validb_spec; unfold valid_entry; cbn; tauto).
    rewrite H, H0 in Hv. discriminate.
Qed.

Lemma result_post_transfer_valid : forall A B q,
  valid A -> valid B -> L A = L B -> (forall x, Sol A x <-> Sol B x) ->
  result_post A q -> result_post B q.
Proof.
  intros A B q HA HB HL HS Hpost.
  assert (HP : Pairwise A <-> Pairwise B).
  { rewrite <- (finite_existence_proved A (valid_positive A HA)),
      <- (finite_existence_proved B (valid_positive B HB)).
    split; intros [x Hx]; exists x; apply HS; assumption. }
  destruct q as [ | | | r p]; cbn [result_post] in *.
  - contradiction.
  - tauto.
  - rewrite <- HL; tauto.
  - destruct Hpost as (_ & Hpair & Hmax & Hp & Hr & Hrep).
    split; [assumption|]. split; [apply HP; assumption|]. split; [assumption|].
    split; [rewrite <- HL; assumption|]. split; [assumption|].
    intros x. rewrite <- HS. apply Hrep.
Qed.
Theorem merge_composition_proved : T_merge_composition.
Proof.
  intros A B r p s q HA HB HrepA HrepB Hp Hq.
  pose proof (composition_proved A B r p s q (valid_positive _ HA)
    (valid_positive _ HB) HrepA HrepB) as (HS & HL & HC).
  destruct HrepA as (HpA & Hr & _); destruct HrepB as (HqB & Hs & _).
  eapply result_post_transfer_valid with (A:=[(r,p);(s,q)]).
  - apply valid_pair. unfold domain, moduli. intuition lia.
  - apply Forall_app; split; assumption.
  - rewrite L_pair by lia. symmetry; assumption.
  - intros x. rewrite !Sol_cons, HS. unfold solution. pose proof (Sol_nil x). tauto.
  - apply scalar_model_proved.
Qed.
Lemma Rep_singleton : forall a m, valid_entry (a,m) -> Rep [(a,m)] a m.
Proof.
  intros a m H. unfold valid_entry in H; cbn in H.
  split; [cbn [L]; rewrite Z.lcm_1_r, Z.abs_eq by lia; reflexivity|].
  split; [tauto|]. intros x. rewrite Sol_cons. split; [tauto|].
  intros Hx. split; [assumption|apply Sol_nil].
Qed.
Lemma Rep_empty : Rep [] 0 1.
Proof.
  split; [reflexivity|]. split; [lia|]. intros x. split;
    [intros _; unfold congruent; apply Z.divide_1_l|intros _; apply Sol_nil].
Qed.
Lemma pairwise_incl : forall A B, incl A B -> Pairwise B -> Pairwise A.
Proof. intros A B Hi HP a m b n Ha Hb. apply HP; apply Hi; assumption. Qed.
Lemma valid_incl : forall A B, incl A B -> valid B -> valid A.
Proof.
  intros A B Hi Hv. apply Forall_forall. intros c Hc.
  apply Forall_forall with (x:=c) in Hv; [assumption|apply Hi; assumption].
Qed.
Lemma overflow_monotone : forall A B,
  positive B -> incl A B -> MAX < L A -> MAX < L B.
Proof.
  intros A B HB Hi Hmax. pose proof (period_subsystem_proved A B Hi) as Hd.
  pose proof (Z.divide_pos_le (L A) (L B) (L_positive B HB) Hd). lia.
Qed.
Lemma solve_fold_correct : forall C A r p,
  valid (A++C) -> Pairwise (A++C) -> Rep A r p -> p <= MAX ->
  result_post (A++C) (solve_fold C r p).
Proof.
  induction C as [|[a m] C IH]; intros A r p HV HP HR Hmax.
  - rewrite app_nil_r in *. cbn [solve_fold result_post]. tauto.
  - assert (Hi : incl (A++[(a,m)]) (A++(a,m)::C)).
    { intros c Hc. apply in_app_iff in Hc as [Hc|[Heq|Hnil]];
        apply in_app_iff; [left; assumption|right; left; assumption|contradiction]. }
    assert (Hprefix : valid (A++[(a,m)])) by (eapply valid_incl; eauto).
    assert (Hprepair : Pairwise (A++[(a,m)])) by (eapply pairwise_incl; eauto).
    assert (HA : valid A).
    { apply Forall_app in Hprefix; tauto. }
    assert (Hentry : valid_entry (a,m)).
    { apply Forall_app in Hprefix as [_ Hsingle]. inversion Hsingle; assumption. }
    assert (Hm : m <= MAX) by (unfold valid_entry in Hentry; cbn in Hentry; lia).
    pose proof (merge_composition_proved A [(a,m)] r p a m HA
      ltac:(constructor; [assumption|constructor]) HR (Rep_singleton a m Hentry)
      Hmax Hm) as HM.
    cbn [solve_fold]. destruct (merge r p a m) as [ | | | r' p'] eqn:Hmerge;
      cbn [result_post] in HM |- *.
    + contradiction.
    + tauto.
    + destruct HM as (_ & _ & Ho). split; [assumption|]. split; [assumption|].
      eapply overflow_monotone; [apply valid_positive; exact HV|exact Hi|exact Ho].
    + destruct HM as (_ & _ & Hfit & Hrep).
      specialize (IH (A++[(a,m)]) r' p').
      rewrite <- app_assoc in IH. cbn [app] in IH. apply IH; assumption.
Qed.
Theorem finite_model_proved : T_finite_model.
Proof.
  intros C. unfold system_model. destruct (validate_loop C) eqn:Hv.
  - apply validate_loop_spec in Hv. destruct (pair_loop C) eqn:Hp.
    + apply solve_fold_correct with (A:=[]); cbn; try assumption.
      * apply (proj1 (pair_loop_spec C (valid_positive C Hv))); assumption.
      * apply Rep_empty.
      * unfold MAX, i64_max; lia.
    + cbn [result_post]. split; [assumption|]. intro Hpair.
      apply (proj2 (pair_loop_spec C (valid_positive C Hv))) in Hpair. congruence.
  - cbn [result_post]. intro Hvalid. apply validate_loop_spec in Hvalid. congruence.
Qed.
Lemma result_post_unique : forall C q1 q2,
  result_post C q1 -> result_post C q2 -> q1=q2.
Proof.
  intros C q1 q2 H1 H2.
  destruct q1 as [ | | | r p]; destruct q2 as [ | | | s q];
    cbn [result_post] in *; try reflexivity; try tauto.
  - destruct H2 as (_ & _ & Hmax & Hp & _). tauto || lia.
  - destruct H1 as (_ & _ & Hmax & Hp & _). tauto || lia.
  - destruct H1 as (_ & _ & _ & HR); destruct H2 as (_ & _ & _ & HS).
    destruct (Rep_unique C r p s q HR HS). subst. reflexivity.
Qed.
Lemma L_permutation : forall A B, Permutation A B -> L A = L B.
Proof.
  intros A B HP. apply Z.divide_antisym_nonneg.
  - destruct A as [|[a m] A]; cbn; [lia|apply Z.lcm_nonneg].
  - destruct B as [|[b n] B]; cbn; [lia|apply Z.lcm_nonneg].
  - apply period_subsystem_proved. intros c Hc. eapply Permutation_in; eauto.
  - apply period_subsystem_proved. intros c Hc. eapply Permutation_in; [apply Permutation_sym; exact HP|exact Hc].
Qed.
Lemma result_post_permutation : forall A B q,
  Permutation A B -> result_post A q -> result_post B q.
Proof.
  intros A B q HP Hpost.
  assert (HV : valid A <-> valid B).
  { split; intros H.
    - apply valid_incl with (B:=A); [|assumption].
      intros c Hc. eapply Permutation_in; [apply Permutation_sym; exact HP|exact Hc].
    - apply valid_incl with (B:=B); [|assumption].
      intros c Hc. eapply Permutation_in; eauto. }
  assert (HS : forall x, Sol A x <-> Sol B x).
  { intros x. unfold Sol. split; intros H a m Hin; apply H.
    - eapply Permutation_in; [apply Permutation_sym; exact HP|exact Hin].
    - eapply Permutation_in; [exact HP|exact Hin]. }
  destruct q as [ | | | r p]; cbn [result_post] in Hpost |- *.
  - tauto.
  - eapply (result_post_transfer_valid A B Inconsistent); [exact (proj1 Hpost)|apply HV; exact (proj1 Hpost)|apply L_permutation; exact HP|exact HS|exact Hpost].
  - eapply (result_post_transfer_valid A B Overflow); [exact (proj1 Hpost)|apply HV; exact (proj1 Hpost)|apply L_permutation; exact HP|exact HS|exact Hpost].
  - eapply (result_post_transfer_valid A B (Success r p)); [exact (proj1 Hpost)|apply HV; exact (proj1 Hpost)|apply L_permutation; exact HP|exact HS|exact Hpost].
Qed.
Theorem permutation_proved : T_permutation.
Proof.
  intros A B HP. apply result_post_unique with (C:=B).
  - eapply result_post_permutation; [exact HP|apply finite_model_proved].
  - apply finite_model_proved.
Qed.
Theorem empty_proved : T_empty.
Proof. reflexivity. Qed.
Theorem singleton_proved : T_singleton.
Proof.
  intros a m HV. apply result_post_unique with (C:=[(a,m)]); [apply finite_model_proved|].
  cbn [result_post]. split; [constructor; [assumption|constructor]|].
  split.
  - apply (proj1 (finite_existence_proved [(a,m)] (valid_positive [(a,m)] ltac:(constructor; [exact HV|constructor])))).
    exists a. apply Rep_solution with (p:=m). apply Rep_singleton; assumption.
  - split; [unfold valid_entry in HV; cbn in HV; lia|apply Rep_singleton; assumption].
Qed.

Lemma duplicate_post : forall C c q, In c C -> result_post C q -> result_post (c::C) q.
Proof.
  intros C [a m] q Hin HQ.
  assert (HV : valid ((a,m)::C) <-> valid C).
  { split; [intros H; inversion H; assumption|]. intros H. constructor; [|assumption].
    apply Forall_forall with (x:=(a,m)) in H; assumption. }
  assert (HL : L C = L ((a,m)::C)).
  { apply Z.divide_antisym_nonneg.
    - destruct C as [|[b n] C]; cbn; [lia|apply Z.lcm_nonneg].
    - cbn [L]. apply Z.lcm_nonneg.
    - apply period_subsystem_proved. intros d Hd; right; assumption.
    - apply period_subsystem_proved. intros d [Heq|Hd]; [subst; assumption|assumption]. }
  assert (HS : forall x, Sol C x <-> Sol ((a,m)::C) x).
  { intros x. rewrite Sol_cons. split; [intros H; split; [apply H; assumption|assumption]|tauto]. }
  destruct q as [ | | | r p]; cbn [result_post] in HQ |- *.
  - tauto.
  - eapply (result_post_transfer_valid C ((a,m)::C) Inconsistent); try eassumption; apply HV; tauto.
  - eapply (result_post_transfer_valid C ((a,m)::C) Overflow); try eassumption; apply HV; tauto.
  - eapply (result_post_transfer_valid C ((a,m)::C) (Success r p)); try eassumption; apply HV; tauto.
Qed.
Theorem duplicate_proved : T_duplicate.
Proof.
  intros C c Hin. apply result_post_unique with (C:=c::C); [apply finite_model_proved|].
  apply duplicate_post; [assumption|apply finite_model_proved].
Qed.

Lemma merge_period_equation : forall a m b n,
  domain a m b n -> compatible a m b n ->
  period_value (merge a m b n) =
    if MAX/n <? m/gcd_model m n then -3 else (m/gcd_model m n)*n.
Proof.
  intros a m b n HD HC. destruct HD as ((Hm & Hn) & Ha & Hb).
  assert (HV1 : validb (a,m)=true) by (apply validb_spec; unfold valid_entry; cbn; tauto).
  assert (HV2 : validb (b,n)=true) by (apply validb_spec; unfold valid_entry; cbn; tauto).
  unfold merge. rewrite HV1, HV2. cbn [andb].
  rewrite gcd_model_proved by (unfold moduli; tauto).
  assert (Ht : (b-a) mod Z.gcd m n =? 0 = true).
  { apply Z.eqb_eq. apply Z.mod_divide; [pose proof (gcd_positive m n ltac:(lia)); lia|assumption]. }
  rewrite Ht. destruct (MAX/n <? m/Z.gcd m n); reflexivity.
Qed.
Lemma period_fold_matches : forall C A r p,
  valid (A++C) -> Pairwise (A++C) -> Rep A r p -> p <= MAX ->
  period_fold C p = period_value (solve_fold C r p).
Proof.
  induction C as [|[a m] C IH]; intros A r p HV HP HR Hmax; [reflexivity|].
  assert (HA : valid A) by (apply Forall_app in HV; tauto).
  assert (HC : valid ((a,m)::C)) by (apply Forall_app in HV; tauto).
  inversion HC as [|c cs Hentry Htail]; subst.
  assert (HD : domain r p a m).
  { destruct HR as (_ & Hr & _). unfold valid_entry in Hentry; cbn in Hentry.
    unfold domain, moduli; intuition lia. }
  assert (Hcomp : compatible r p a m).
  { destruct (proj2 (finite_existence_proved _ (valid_positive _ HV)) HP) as [x Hx].
    destruct (proj1 (Sol_app A ((a,m)::C) x) Hx) as [HxA HxC].
    destruct (proj1 (Sol_cons a m C x) HxC) as [Hxa _].
    destruct HR as (_ & Hr & Hrep).
    apply (proj1 (generalized_crt_proved r p a m ltac:(lia) ltac:(unfold domain, moduli in HD; lia))).
    exists x. split; [exact (proj1 (Hrep x) HxA)|exact Hxa]. }
  pose proof (merge_contract r p a m HD) as HM.
  pose proof (merge_period_equation r p a m HD Hcomp) as HE.
  pose proof (merge_composition_proved A [(a,m)] r p a m HA
    ltac:(constructor; [exact Hentry|constructor]) HR (Rep_singleton a m Hentry)
    Hmax ltac:(unfold valid_entry in Hentry; cbn in Hentry; lia)) as Hpost.
  cbn [period_fold solve_fold].
  destruct (merge r p a m) as [ | | | r' p'] eqn:Hmerge; cbn [period_value result_post] in HM, HE, Hpost |- *.
  - contradiction.
  - contradiction.
  - destruct (MAX/m <? p/gcd_model p m); [reflexivity|].
    rewrite gcd_model_proved in HE by (unfold domain in HD; tauto).
    destruct HD as ((Hp & Hm) & _).
    pose proof (proj1 (period_properties p m ltac:(lia) ltac:(lia))). unfold period in H; lia.
  - destruct Hpost as (_ & _ & Hfit & Hrep).
    destruct (MAX/m <? p/gcd_model p m) eqn:Hg.
    + destruct Hrep as (_ & Hr & _); lia.
    + rewrite <- HE. specialize (IH (A++[(a,m)]) r' p').
      rewrite <- app_assoc in IH. cbn [app] in IH. apply IH; assumption.
Qed.
Theorem period_model_proved : T_period_model.
Proof.
  intros C. unfold period_model, system_model. destruct (validate_loop C) eqn:HV; [|reflexivity].
  destruct (pair_loop C) eqn:HP; [|reflexivity].
  apply validate_loop_spec in HV.
  apply period_fold_matches with (A:=[]) (r:=0); cbn; try assumption.
  - apply (proj1 (pair_loop_spec C (valid_positive C HV))); assumption.
  - apply Rep_empty.
  - unfold MAX, i64_max; lia.
Qed.

Import FiniteSystemTargets.
Theorem overflow_exact_proved : T_overflow_exact.
Proof.
  intros C. split.
  - intros H. pose proof (finite_model_proved C). rewrite H in H0. exact H0.
  - intros H. apply result_post_unique with (C:=C); [apply finite_model_proved|exact H].
Qed.
Theorem summary_commutative_proved : T_summary_commutative.
Proof.
  intros A B r p s q HA HB HR HS Hp Hq.
  apply result_post_unique with (C:=A++B).
  - apply merge_composition_proved; assumption.
  - apply result_post_permutation with (A:=B++A); [apply Permutation_app_comm|].
    apply merge_composition_proved; assumption.
Qed.
Theorem summary_associative_proved : T_summary_associative.
Proof.
  intros A B C r p s q t u abv abp bcv bcp HA HB HC HR HS HT Hp Hq Hu HAB HBC.
  pose proof (merge_composition_proved A B r p s q HA HB HR HS Hp Hq) as HPAB.
  pose proof (merge_composition_proved B C s q t u HB HC HS HT Hq Hu) as HPBC.
  rewrite HAB in HPAB. rewrite HBC in HPBC.
  destruct HPAB as (HVAB & _ & HfitAB & HrepAB).
  destruct HPBC as (HVBC & _ & HfitBC & HrepBC).
  apply result_post_unique with (C:=(A++B)++C).
  - apply merge_composition_proved; assumption.
  - rewrite <- app_assoc. apply merge_composition_proved; assumption.
Qed.
Theorem scan_models_proved : T_scan_models.
Proof.
  split; [apply validate_loop_spec|]. split; [apply pair_loop_spec|]. intros; cbn; lia.
Qed.
Theorem cursor_bounds_proved : T_cursor_bounds.
Proof. unfold T_cursor_bounds. intros; lia. Qed.
Theorem batch_classification_proved : T_batch_classification.
Proof.
  intros C count HC. unfold batch_model. split.
  - intros Hbad. destruct ((0 <=? count) && (count <=? 16)) eqn:Ht; [|reflexivity].
    apply andb_true_iff in Ht as [H0 H16]. apply Z.leb_le in H0; apply Z.leb_le in H16; lia.
  - intros Hvalid. assert ((0 <=? count) && (count <=? 16) = true).
    { apply andb_true_iff; split; apply Z.leb_le; lia. }
    rewrite H. apply finite_model_proved.
Qed.

Lemma validation_inv_step : forall done c todo,
  validation_inv done (c::todo) -> valid_entry c -> validation_inv (done++[c]) todo.
Proof.
  intros done c todo Hdone Hc. unfold validation_inv in *. apply Forall_app. split;
    [assumption|constructor; [assumption|constructor]].
Qed.
Lemma validation_inv_exit : forall done, validation_inv done [] -> valid done.
Proof. intros; assumption. Qed.
Lemma pair_scan_row_step : forall done c checked d pending tail,
  pair_scan_inv done c checked (d::pending) tail ->
  compatible (fst c) (snd c) (fst d) (snd d) ->
  pair_scan_inv done c (checked++[d]) pending tail.
Proof.
  intros done c checked d pending tail (HP & HD & HC) Hcd.
  split; [assumption|]. split.
  - intros a b Ha Hb. apply HD; [assumption|].
    cbn in Hb |- *. destruct Hb as [Heq|Hb]; [left; assumption|right].
    apply in_app_iff in Hb as [Hb|Hb].
    + apply in_app_iff in Hb as [Hb|[Heq|Hnil]].
      * apply in_app_iff; left; assumption.
      * apply in_app_iff; right; left; assumption.
      * contradiction.
    + apply in_app_iff; right; right; assumption.
  - intros a Ha. apply in_app_iff in Ha as [Ha|[Heq|Hnil]].
    + apply HC; assumption.
    + subst; assumption.
    + contradiction.
Qed.

Import IndexedLoopTargets.
Lemma active_cursor_step : forall (C : list constraint) (count i : nat),
  Nat.lt i count /\ Nat.le count (length C) ->
  active_cursor C count i = nth i C (0,1) :: active_cursor C count (S i).
Proof.
  intros C count i. revert C count.
  induction i as [|i IH]; intros C count Hbounds; destruct C as [|c C]; cbn in Hbounds; [lia| |lia|].
  - destruct count; [lia|]. unfold active_cursor; cbn. rewrite Nat.sub_0_r. reflexivity.
  - destruct count; [lia|]. unfold active_cursor in *. cbn.
    apply IH. cbn in Hbounds; lia.
Qed.
Lemma firstn_cursor_step : forall (C : list constraint) (i : nat),
  Nat.lt i (length C) -> firstn (S i) C = firstn i C ++ [nth i C (0,1)].
Proof.
  intros C i. revert C. induction i as [|i IH]; intros C Hi;
    destruct C as [|c C]; cbn in *; try lia; try reflexivity.
  rewrite IH by lia. reflexivity.
Qed.
Theorem indexed_list_bridge_proved : T_indexed_list_bridge.
Proof.
  intros C count i Hbounds. split; [apply active_cursor_step; assumption|].
  split; [apply firstn_cursor_step; lia|lia].
Qed.
