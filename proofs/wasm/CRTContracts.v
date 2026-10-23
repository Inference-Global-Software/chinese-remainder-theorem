(* Denotational obligations for the exact compiler-generated hassert payloads.
   Every bridge to ValidSpec below requires actual Wasm execution explicitly.
   No generated proof-placeholder theorem is used. *)
From Coq Require Import ZArith NArith Lia List Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations host.
From WasmVerifier Require Import Assertions Semantics NumericDischarge Automation Activation Verifier.
From CRT Require Import CRTStatements.
From CRTWasm Require Import CRTAPIModel.
From CRTGenerated Require Import crt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Close Scope Z_scope.

Lemma crt_contract_signed_word (x : i64) : word (Wasm_int.Int64.signed x).
Proof.
  have Hx := Wasm_int.Int64.signed_range x.
  unfold word, i64_min, i64_max.
  rewrite i64_min_signed_val i64_max_signed_val in Hx. lia.
Qed.

Lemma crt_contract_repr_signed (x : i64) :
  crt.Vi64 (Wasm_int.Int64.signed x) = VAL_int64 x.
Proof.
  change (VAL_int64 (Wasm_int.Int64.repr (Wasm_int.Int64.signed x)) = VAL_int64 x).
  by rewrite Wasm_int.Int64.repr_signed.
Qed.

Lemma crt_contract_signed_repr z : word z ->
  Wasm_int.Int64.signed (Wasm_int.Int64.repr z) = z.
Proof.
  move=> Hz. apply: Wasm_int.Int64.signed_repr.
  rewrite i64_min_signed_val i64_max_signed_val. exact Hz.
Qed.

Lemma crt_contract_signed_one :
  Wasm_int.Int64.signed (Wasm_int.int_of_Z i64m 1) = 1%Z.
Proof. apply crt_contract_signed_repr. unfold word, i64_min, i64_max. lia. Qed.

Lemma crt_contract_signed_M :
  Wasm_int.Int64.signed (Wasm_int.int_of_Z i64m 2147483647) = M.
Proof. apply crt_contract_signed_repr. unfold word, M, i64_min, i64_max. lia. Qed.

Lemma crt_contract_lt (x y : i64) :
  app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 x) (VAL_int64 y) =
  Z.ltb (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y).
Proof.
  rewrite i64_lt_s_app /Wasm_int.Int64.lt.
  case: Coqlib.zlt => Hxy; symmetry;
    [apply/Z.ltb_lt | apply/Z.ltb_ge]; lia.
Qed.

Lemma crt_contract_le (x y : i64) :
  app_relop (Relop_i (ROI_le SX_S)) (VAL_int64 x) (VAL_int64 y) =
  Z.leb (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y).
Proof.
  change (negb (Wasm_int.Int64.lt y x) =
    Z.leb (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y)).
  rewrite /Wasm_int.Int64.lt. case: Coqlib.zlt => Hxy; simpl; symmetry;
    [apply/Z.leb_gt | apply/Z.leb_le]; lia.
Qed.

Lemma crt_contract_gt (x y : i64) :
  app_relop (Relop_i (ROI_gt SX_S)) (VAL_int64 x) (VAL_int64 y) =
  Z.ltb (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed x).
Proof. exact: crt_contract_lt. Qed.

Lemma crt_contract_ge (x y : i64) :
  app_relop (Relop_i (ROI_ge SX_S)) (VAL_int64 x) (VAL_int64 y) =
  Z.leb (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed x).
Proof. exact: crt_contract_le. Qed.

Lemma crt_contract_eq (x y : i64) :
  app_relop (Relop_i ROI_eq) (VAL_int64 x) (VAL_int64 y) =
  Z.eqb (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y).
Proof.
  rewrite i64_eq_app. case: (Wasm_int.Int64.eq_eqP x y) => Hxy.
  - subst y. by rewrite Z.eqb_refl.
  - symmetry. apply/Z.eqb_neq. move=> Heq. apply Hxy.
    by rewrite -[x]Wasm_int.Int64.repr_signed -[y]Wasm_int.Int64.repr_signed Heq.
Qed.

Lemma crt_contract_ne (x y : i64) :
  app_relop (Relop_i ROI_ne) (VAL_int64 x) (VAL_int64 y) =
  negb (Z.eqb (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y)).
Proof. rewrite i64_ne_app -crt_contract_eq i64_eq_app. reflexivity. Qed.

Lemma crt_leaf_i64_or_kfalse (V : valuation) (h : aheap) (i : N) :
  (exists c : i64, val_loc V i = Some (VAL_int64 c)) \/
  hassert_denote V (kfalse (HA_has_type (T_local i) T_i64)) h.
Proof.
  case E: (val_loc V i) => [[c32|c|f32v|f64v]|].
  - right. rewrite /= E. by move=> [v [[<-] Hty]].
  - by left; exists c.
  - right. rewrite /= E. by move=> [v [[<-] Hty]].
  - right. rewrite /= E. by move=> [v [[<-] Hty]].
  - right. rewrite /= E. by move=> [v []].
Qed.

Lemma crt_contract_guard_false (V : valuation) (h : aheap)
    (nt : number_type) (op : relop) (a b : term) (va vb : value_num) :
  term_denote V a = Some va -> term_denote V b = Some vb ->
  app_relop op va vb = false ->
  hassert_denote V
    (kfalse (HA_not (term_eq (T_relop nt op a b) (T_const (crt.Vi32 0))))) h.
Proof.
  move=> Ha Hb Hop. exists (crt.Vi32 0). split; last by [].
  by rewrite /= Ha Hb Hop.
Qed.

Ltac crt_false_antecedent :=
  first [assumption |
    apply: hdenote_kfalse_Hand_introl; crt_false_antecedent |
    apply: hdenote_kfalse_Hand_intror; crt_false_antecedent].

Definition crt_helper_gcd_total (FI : fun_interp) : Prop :=
  forall m n : i64,
    moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) ->
    exists rs, FI 0 [:: VAL_int64 m; VAL_int64 n] = Some rs.

Definition crt_helper_normalize_total (FI : fun_interp) : Prop :=
  forall z d : i64,
    (1 <= Wasm_int.Int64.signed d <= M)%Z ->
    exists rs, FI 1 [:: VAL_int64 z; VAL_int64 d] = Some rs.

Lemma crt_helper_normalize_total_payload (FI : fun_interp) :
  crt_helper_normalize_total FI ->
  forall (V : valuation) (h : aheap), val_fun V = FI ->
  hassert_denote V (ktrue crt.crt__HelperContracts_hspec3) h.
Proof.
  move=> Htotal V h Hpin. rewrite /crt.crt__HelperContracts_hspec3.
  case: (crt_leaf_i64_or_kfalse V h 0%num) => [[z Hz]|Hbad].
  2: { apply: hdenote_ktrue_Himpl_introl. crt_false_antecedent. }
  case: (crt_leaf_i64_or_kfalse V h 1%num) => [[d Hd]|Hbad].
  2: { apply: hdenote_ktrue_Himpl_introl. crt_false_antecedent. }
  case Hlo: (app_relop (Relop_i (ROI_le SX_S)) (crt.Vi64 1) (VAL_int64 d)).
  2: { have Hbad := @crt_contract_guard_false V h T_i64 (Relop_i (ROI_le SX_S))
         (T_const (crt.Vi64 1)) (T_local 1%num) (crt.Vi64 1) (VAL_int64 d) erefl Hd Hlo.
       apply: hdenote_ktrue_Himpl_introl. crt_false_antecedent. }
  case Hhi: (app_relop (Relop_i (ROI_le SX_S)) (VAL_int64 d) (crt.Vi64 2147483647)).
  2: { have Hbad := @crt_contract_guard_false V h T_i64 (Relop_i (ROI_le SX_S))
         (T_local 1%num) (T_const (crt.Vi64 2147483647)) (VAL_int64 d) (crt.Vi64 2147483647) Hd erefl Hhi.
       apply: hdenote_ktrue_Himpl_introl. crt_false_antecedent. }
  have Hdmod : (1 <= Wasm_int.Int64.signed d <= M)%Z.
  { rewrite !crt_contract_le in Hlo Hhi.
    rewrite crt_contract_signed_one in Hlo.
    rewrite crt_contract_signed_M in Hhi.
    move/Z.leb_le: Hlo => Hlo. move/Z.leb_le: Hhi => Hhi. lia. }
  have [rs Hrs] := Htotal z d Hdmod.
  apply: hdenote_ktrue_Himpl_intror. by rewrite /= Hz Hd Hpin Hrs.
Qed.

Lemma crt_helper_gcd_total_payload (FI : fun_interp) :
  crt_helper_gcd_total FI ->
  forall (V : valuation) (h : aheap), val_fun V = FI ->
  hassert_denote V (ktrue crt.crt__HelperContracts_hspec1) h.
Proof.
  move=> Htotal V h Hpin. rewrite /crt.crt__HelperContracts_hspec1.
  case: (crt_leaf_i64_or_kfalse V h 0%num) => [[m Hm]|Hbad].
  2: { apply: hdenote_ktrue_Himpl_introl. crt_false_antecedent. }
  case: (crt_leaf_i64_or_kfalse V h 1%num) => [[n Hn]|Hbad].
  2: { apply: hdenote_ktrue_Himpl_introl. crt_false_antecedent. }
  case Hmlo: (app_relop (Relop_i (ROI_le SX_S)) (crt.Vi64 1) (VAL_int64 m)).
  2: { have Hbad := @crt_contract_guard_false V h T_i64 (Relop_i (ROI_le SX_S))
         (T_const (crt.Vi64 1)) (T_local 0%num) (crt.Vi64 1) (VAL_int64 m) erefl Hm Hmlo.
       apply: hdenote_ktrue_Himpl_introl. crt_false_antecedent. }
  case Hmhi: (app_relop (Relop_i (ROI_le SX_S)) (VAL_int64 m) (crt.Vi64 2147483647)).
  2: { have Hbad := @crt_contract_guard_false V h T_i64 (Relop_i (ROI_le SX_S))
         (T_local 0%num) (T_const (crt.Vi64 2147483647)) (VAL_int64 m) (crt.Vi64 2147483647) Hm erefl Hmhi.
       apply: hdenote_ktrue_Himpl_introl. crt_false_antecedent. }
  case Hnlo: (app_relop (Relop_i (ROI_le SX_S)) (crt.Vi64 1) (VAL_int64 n)).
  2: { have Hbad := @crt_contract_guard_false V h T_i64 (Relop_i (ROI_le SX_S))
         (T_const (crt.Vi64 1)) (T_local 1%num) (crt.Vi64 1) (VAL_int64 n) erefl Hn Hnlo.
       apply: hdenote_ktrue_Himpl_introl. crt_false_antecedent. }
  case Hnhi: (app_relop (Relop_i (ROI_le SX_S)) (VAL_int64 n) (crt.Vi64 2147483647)).
  2: { have Hbad := @crt_contract_guard_false V h T_i64 (Relop_i (ROI_le SX_S))
         (T_local 1%num) (T_const (crt.Vi64 2147483647)) (VAL_int64 n) (crt.Vi64 2147483647) Hn erefl Hnhi.
       apply: hdenote_ktrue_Himpl_introl. crt_false_antecedent. }
  have Hmods : moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n).
  { rewrite !crt_contract_le in Hmlo Hmhi Hnlo Hnhi.
    rewrite !crt_contract_signed_one in Hmlo Hnlo.
    rewrite !crt_contract_signed_M in Hmhi Hnhi.
    move/Z.leb_le: Hmlo => Hmlo. move/Z.leb_le: Hmhi => Hmhi.
    move/Z.leb_le: Hnlo => Hnlo. move/Z.leb_le: Hnhi => Hnhi.
    unfold moduli. lia. }
  have [rs Hrs] := Htotal m n Hmods.
  apply: hdenote_ktrue_Himpl_intror. by rewrite /= Hm Hn Hpin Hrs.
Qed.

Definition crt_public_period_total (FI : fun_interp) : Prop :=
  forall m n : i64, exists rs,
    FI 3 [:: VAL_int64 m; VAL_int64 n] = Some rs.

Definition crt_public_solve_total (FI : fun_interp) : Prop :=
  forall a m b n : i64, exists rs,
    FI 4 [:: VAL_int64 a; VAL_int64 m; VAL_int64 b; VAL_int64 n] = Some rs.

Lemma crt_public_period_total_payload (FI : fun_interp) :
  crt_public_period_total FI ->
  forall (V : valuation) (h : aheap), val_fun V = FI ->
  hassert_denote V (ktrue crt.crt__PublicContracts_hspec2) h.
Proof.
  move=> Htotal V h Hpin. rewrite /crt.crt__PublicContracts_hspec2.
  case: (crt_leaf_i64_or_kfalse V h 0%num) => [[m Hm]|Hbad].
  2: { apply: hdenote_ktrue_Himpl_introl.
       exact: hdenote_kfalse_Hand_introl Hbad. }
  case: (crt_leaf_i64_or_kfalse V h 1%num) => [[n Hn]|Hbad].
  2: { apply: hdenote_ktrue_Himpl_introl.
       exact: hdenote_kfalse_Hand_intror Hbad. }
  apply: hdenote_ktrue_Himpl_intror.
  have [rs Hrs] := Htotal m n.
  by rewrite /= Hm Hn Hpin Hrs.
Qed.

Lemma crt_public_solve_total_payload (FI : fun_interp) :
  crt_public_solve_total FI ->
  forall (V : valuation) (h : aheap), val_fun V = FI ->
  hassert_denote V (ktrue crt.crt__PublicContracts_hspec1) h.
Proof.
  move=> Htotal V h Hpin. rewrite /crt.crt__PublicContracts_hspec1.
  case: (crt_leaf_i64_or_kfalse V h 0%num) => [[a Ha]|Hbad].
  2: { apply: hdenote_ktrue_Himpl_introl.
       exact: hdenote_kfalse_Hand_introl Hbad. }
  case: (crt_leaf_i64_or_kfalse V h 1%num) => [[m Hm]|Hbad].
  2: { apply: hdenote_ktrue_Himpl_introl.
       apply: hdenote_kfalse_Hand_intror.
       exact: hdenote_kfalse_Hand_introl Hbad. }
  case: (crt_leaf_i64_or_kfalse V h 2%num) => [[b Hb]|Hbad].
  2: { apply: hdenote_ktrue_Himpl_introl.
       apply: hdenote_kfalse_Hand_intror.
       apply: hdenote_kfalse_Hand_intror.
       exact: hdenote_kfalse_Hand_introl Hbad. }
  case: (crt_leaf_i64_or_kfalse V h 3%num) => [[n Hn]|Hbad].
  2: { apply: hdenote_ktrue_Himpl_introl.
       apply: hdenote_kfalse_Hand_intror.
       apply: hdenote_kfalse_Hand_intror.
       exact: hdenote_kfalse_Hand_intror Hbad. }
  apply: hdenote_ktrue_Himpl_intror.
  have [rs Hrs] := Htotal a m b n.
  by rewrite /= Ha Hm Hb Hn Hpin Hrs.
Qed.

(* An explicit interpretation for just the two public symbols.  The function
   bodies must realize the supplied results for EVERY i64 input, including
   invalid inputs and both machine extrema. *)
Definition crt_public_interp
    (p : i64 -> i64 -> value_num)
    (s : i64 -> i64 -> i64 -> i64 -> value_num) : fun_interp :=
  fun i args =>
    match i, args with
    | 3, [:: VAL_int64 m; VAL_int64 n] => Some [:: p m n]
    | 4, [:: VAL_int64 a; VAL_int64 m; VAL_int64 b; VAL_int64 n] =>
        Some [:: s a m b n]
    | _, _ => None
    end.

(* One interpretation for all five exact generated symbols.  Helper claims
   occur precisely on their visible source domains; both public symbols are
   interpreted for the entire i64 domain. *)
Definition crt_model_interp : fun_interp :=
  fun i args =>
    match i, args with
    | 0, [:: VAL_int64 m; VAL_int64 n] =>
        if crt_moduli_b (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n)
        then Some [:: crt.Vi64 (Z.gcd (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n))]
        else None
    | 1, [:: VAL_int64 z; VAL_int64 d] =>
        if ((1 <=? Wasm_int.Int64.signed d) && (Wasm_int.Int64.signed d <=? M))%Z
        then Some [:: crt.Vi64 (Wasm_int.Int64.signed z mod Wasm_int.Int64.signed d)]
        else None
    | 2, [:: VAL_int64 b; VAL_int64 a] =>
        if ((1 <=? Wasm_int.Int64.signed b) &&
            (Wasm_int.Int64.signed b <? Wasm_int.Int64.signed a) &&
            (Wasm_int.Int64.signed a <=? M) &&
            (Z.gcd (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed b) =? 1))%Z
        then Some [:: crt.Vi64 (crt_inverse_Z (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed a))]
        else None
    | 3, [:: VAL_int64 m; VAL_int64 n] =>
        Some [:: crt.Vi64 (crt_period_Z (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n))]
    | 4, [:: VAL_int64 a; VAL_int64 m; VAL_int64 b; VAL_int64 n] =>
        Some [:: crt.Vi64 (crt_solve_Z (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
          (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n))]
    | _, _ => None
    end.

Lemma crt_model_gcd_total : crt_helper_gcd_total crt_model_interp.
Proof.
  move=> m n Hmods. rewrite /crt_model_interp (proj2 (crt_moduli_b_spec _ _) Hmods).
  by eexists.
Qed.

Lemma crt_model_normalize_total : crt_helper_normalize_total crt_model_interp.
Proof.
  move=> z d Hd. rewrite /crt_model_interp.
  have Hguard : ((1 <=? Wasm_int.Int64.signed d) &&
    (Wasm_int.Int64.signed d <=? M))%Z = true.
  { apply/andb_true_iff. split; apply/Z.leb_le; lia. }
  rewrite Hguard. by eexists.
Qed.

Lemma crt_model_period_total : crt_public_period_total crt_model_interp.
Proof. move=> m n. by eexists. Qed.

Lemma crt_model_solve_total : crt_public_solve_total crt_model_interp.
Proof. move=> a m b n. by eexists. Qed.

Section Host.
Context `{ho : host}.

Theorem crt_model_realized_from_execution (rt : module_runtime crt.crt) :
  (forall m n : i64,
    moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) ->
    fun_computes_at rt 0 [:: VAL_int64 m; VAL_int64 n]
      [:: crt.Vi64 (Z.gcd (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n))]) ->
  (forall z d : i64, (1 <= Wasm_int.Int64.signed d <= M)%Z ->
    fun_computes_at rt 1 [:: VAL_int64 z; VAL_int64 d]
      [:: crt.Vi64 (Wasm_int.Int64.signed z mod Wasm_int.Int64.signed d)]) ->
  (forall b a : i64,
    eea_inputs (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed b) ->
    Z.gcd (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed b) = 1%Z ->
    fun_computes_at rt 2 [:: VAL_int64 b; VAL_int64 a]
      [:: crt.Vi64 (crt_inverse_Z (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed a))]) ->
  (forall m n : i64, fun_computes_at rt 3 [:: VAL_int64 m; VAL_int64 n]
      [:: crt.Vi64 (crt_period_Z (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n))]) ->
  (forall a m b n : i64, fun_computes_at rt 4
      [:: VAL_int64 a; VAL_int64 m; VAL_int64 b; VAL_int64 n]
      [:: crt.Vi64 (crt_solve_Z (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
        (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n))]) ->
  interp_realized_at rt crt_model_interp.
Proof.
  move=> Hg Hn Hi Hp Hs i args rs. rewrite /crt_model_interp.
  case: i => [|[|[|[|[|i]]]]] //.
  - case: args => [|[v32|m|vf32|vf64] [|[w32|n|wf32|wf64] args]] //;
      case: args => [|v args] //.
    case Hguard: (crt_moduli_b (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n)) => //.
    move=> [<-]. apply: Hg. exact (proj1 (crt_moduli_b_spec _ _) Hguard).
  - case: args => [|[v32|z|vf32|vf64] [|[w32|d|wf32|wf64] args]] //;
      case: args => [|v args] //.
    case Hguard: (((1 <=? Wasm_int.Int64.signed d) && (Wasm_int.Int64.signed d <=? M))%Z) => //.
    move=> [<-]. apply: Hn. apply andb_true_iff in Hguard.
    destruct Hguard as [Hlo Hhi]. apply Z.leb_le in Hlo, Hhi. lia.
  - case: args => [|[v32|b|vf32|vf64] [|[w32|a|wf32|wf64] args]] //;
      case: args => [|v args] //.
    case Hguard: (((1 <=? Wasm_int.Int64.signed b) &&
      (Wasm_int.Int64.signed b <? Wasm_int.Int64.signed a) &&
      (Wasm_int.Int64.signed a <=? M) &&
      (Z.gcd (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed b) =? 1))%Z) => //.
    move=> [<-]. rewrite !andb_true_iff in Hguard.
    destruct Hguard as [[[Hlo Hlt] Hhi] Hcop].
    apply Z.leb_le in Hlo, Hhi. apply Z.ltb_lt in Hlt. apply Z.eqb_eq in Hcop.
    apply: Hi; [unfold eea_inputs; lia | exact Hcop].
  - case: args => [|[a32|m|af32|af64] [|[b32|n|bf32|bf64] args]] //;
      case: args => [|v args] //.
    move=> [<-]. exact: Hp.
  - case: args => [|[a32|a|af32|af64] [|[m32|m|mf32|mf64]
      [|[b32|b|bf32|bf64] [|[n32|n|nf32|nf64] args]]]] //;
      case: args => [|v args] //.
    move=> [<-]. exact: Hs.
Qed.

Lemma crt_public_interp_realized_at (rt : module_runtime crt.crt)
    (p : i64 -> i64 -> value_num)
    (s : i64 -> i64 -> i64 -> i64 -> value_num) :
  (forall m n, fun_computes_at rt 3
    [:: VAL_int64 m; VAL_int64 n] [:: p m n]) ->
  (forall a m b n, fun_computes_at rt 4
    [:: VAL_int64 a; VAL_int64 m; VAL_int64 b; VAL_int64 n] [:: s a m b n]) ->
  interp_realized_at rt (crt_public_interp p s).
Proof.
  move=> Hp Hs i args rs. rewrite /crt_public_interp.
  case: i => [|[|[|[|[|i]]]]] //.
  - case: args => [|[a32|m|af32|af64] [|[b32|n|bf32|bf64] args]] //;
      case: args => [|v args] //.
    move=> [<-]. exact: Hp.
  - case: args => [|[a32|a|af32|af64] [|[m32|m|mf32|mf64]
      [|[b32|b|bf32|bf64] [|[n32|n|nf32|nf64] args]]]] //;
      case: args => [|v args] //.
    move=> [<-]. exact: Hs.
Qed.

Theorem crt_public_totality_clauses_from_execution
    (rt : module_runtime crt.crt)
    (p : i64 -> i64 -> value_num)
    (s : i64 -> i64 -> i64 -> i64 -> value_num) :
  (forall m n, fun_computes_at rt 3
    [:: VAL_int64 m; VAL_int64 n] [:: p m n]) ->
  (forall a m b n, fun_computes_at rt 4
    [:: VAL_int64 a; VAL_int64 m; VAL_int64 b; VAL_int64 n] [:: s a m b n]) ->
  ValidSpec crt.crt
    [:: crt.crt__PublicContracts_hspec1; crt.crt__PublicContracts_hspec2].
Proof.
  move=> Hp Hs. right. exists rt. move=> h.
  exists (crt_public_interp p s). split.
  - exact: crt_public_interp_realized_at Hp Hs.
  - move=> V Hpin. constructor.
    + refine (@crt_public_solve_total_payload (crt_public_interp p s) _ V h Hpin).
      move=> a m b n. by exists [:: s a m b n].
    + constructor; last constructor.
      refine (@crt_public_period_total_payload (crt_public_interp p s) _ V h Hpin).
      move=> m n. by exists [:: p m n].
Qed.

End Host.

Print Assumptions crt_public_totality_clauses_from_execution.
