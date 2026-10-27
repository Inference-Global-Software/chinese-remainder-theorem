(* Exact compiler-generated scalar assertions, under the shared execution-realized interpretation. *)
From Coq Require Import ZArith NArith Lia List Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations host.
From WasmVerifier Require Import Assertions Semantics NumericDischarge Automation Activation Verifier.
From CRT Require Import CRTStatements CRTMath CRTSystemStatements CRTSystemArithmetic CRTFinite.
From CRTWasm Require Import CRTContracts CRTSpecPayloads.
From CRTSystems Require Import FullWidthExecution ScalarResultFacts MergeValidation.
From CRTSystems Require Import SystemSpecModel.
Module SM := CRTSystemGenerated.main.
Import FullWidth FiniteSystem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Close Scope Z_scope.
Lemma sp_gcd_term V a b m n :
  val_fun V = system_model_interp ->
  term_denote V a = Some (SM.Vi64 m) -> term_denote V b = Some (SM.Vi64 n) ->
  word m -> word n -> moduli m n ->
  term_denote V (T_app 0 [::a;b]) = Some (SM.Vi64 (Z.gcd m n)).
Proof.
  move=> Hpin Ha Hb Hm Hn Hd. cbn [term_denote]. rewrite Ha Hb Hpin /system_model_interp. cbn [SM.Vi64].
  by rewrite (crt_i64_signed_repr Hm) (crt_i64_signed_repr Hn) (proj2 (sp_moduli_b_spec _ _) Hd).
Qed.

Lemma sp_normalize_term V a b z d :
  val_fun V = system_model_interp ->
  term_denote V a = Some (SM.Vi64 z) -> term_denote V b = Some (SM.Vi64 d) ->
  word z -> word d -> (1 <= d <= MAX)%Z ->
  term_denote V (T_app 1 [::a;b]) = Some (SM.Vi64 (z mod d)).
Proof.
  move=> Hpin Ha Hb Hz Hd Hbound. cbn [term_denote]. rewrite Ha Hb Hpin /system_model_interp. cbn [SM.Vi64].
  rewrite (crt_i64_signed_repr Hz) (crt_i64_signed_repr Hd).
  have Hguard : ((1 <=? d) && (d <=? MAX))%Z = true.
  { apply/andb_true_iff. split; apply/Z.leb_le; lia. }
  by rewrite Hguard.
Qed.

Lemma sp_inverse_term V a b B A :
  val_fun V = system_model_interp ->
  term_denote V a = Some (SM.Vi64 B) -> term_denote V b = Some (SM.Vi64 A) ->
  word B -> word A -> eea_inputs A B -> Z.gcd A B = 1%Z ->
  term_denote V (T_app 2 [::a;b]) = Some (SM.Vi64 (inverse_model B A)).
Proof.
  move=> Hpin Ha Hb HB HA Hin Hcop. cbn [term_denote]. rewrite Ha Hb Hpin /system_model_interp. cbn [SM.Vi64].
  by rewrite (crt_i64_signed_repr HB) (crt_i64_signed_repr HA) (proj2 (sp_inverse_b_spec B A) (conj Hin Hcop)).
Qed.

Lemma sp_solve_term V ta tm tb tn a m b n :
  val_fun V = system_model_interp ->
  term_denote V ta = Some (SM.Vi64 a) -> term_denote V tm = Some (SM.Vi64 m) ->
  term_denote V tb = Some (SM.Vi64 b) -> term_denote V tn = Some (SM.Vi64 n) ->
  word a -> word m -> word b -> word n ->
  term_denote V (T_app 5 [::ta;tm;tb;tn]) = Some (SM.Vi64 (sp_solve a m b n)).
Proof.
  move=> Hpin Ha Hm Hb Hn HaW HmW HbW HnW. cbn [term_denote].
  rewrite Ha Hm Hb Hn Hpin /system_model_interp. cbn [SM.Vi64].
  by rewrite (crt_i64_signed_repr HaW) (crt_i64_signed_repr HmW)
    (crt_i64_signed_repr HbW) (crt_i64_signed_repr HnW).
Qed.

Lemma sp_period_term V ta tm tb tn a m b n :
  val_fun V = system_model_interp ->
  term_denote V ta = Some (SM.Vi64 a) -> term_denote V tm = Some (SM.Vi64 m) ->
  term_denote V tb = Some (SM.Vi64 b) -> term_denote V tn = Some (SM.Vi64 n) ->
  word a -> word m -> word b -> word n ->
  term_denote V (T_app 6 [::ta;tm;tb;tn]) = Some (SM.Vi64 (sp_period a m b n)).
Proof.
  move=> Hpin Ha Hm Hb Hn HaW HmW HbW HnW. cbn [term_denote].
  rewrite Ha Hm Hb Hn Hpin /system_model_interp. cbn [SM.Vi64].
  by rewrite (crt_i64_signed_repr HaW) (crt_i64_signed_repr HmW)
    (crt_i64_signed_repr HbW) (crt_i64_signed_repr HnW).
Qed.

Lemma sp_add_mod_term V tx ty td x y d :
 val_fun V = system_model_interp ->
 term_denote V tx = Some (SM.Vi64 x) -> term_denote V ty = Some (SM.Vi64 y) -> term_denote V td = Some (SM.Vi64 d) ->
 word x -> word y -> word d -> (1 <= d <= MAX)%Z -> (0 <= x < d)%Z -> (0 <= y < d)%Z ->
 term_denote V (T_app 3 [::tx;ty;td]) = Some (SM.Vi64 (add_mod x y d)).
Proof.
 move=> Hpin Hx Hy Hd Wx Wy Wd Bd Bx By.
 cbn [term_denote]. rewrite Hx Hy Hd Hpin /system_model_interp. cbn [SM.Vi64].
 rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy) (crt_i64_signed_repr Wd).
 by rewrite (proj2 (sp_mod_b_spec x y d) (conj Bd (conj Bx By))).
Qed.
Lemma sp_mul_mod_term V tx ty td x y d :
 val_fun V = system_model_interp ->
 term_denote V tx = Some (SM.Vi64 x) -> term_denote V ty = Some (SM.Vi64 y) -> term_denote V td = Some (SM.Vi64 d) ->
 word x -> word y -> word d -> (1 <= d <= MAX)%Z -> (0 <= x < d)%Z -> (0 <= y < d)%Z ->
 term_denote V (T_app 4 [::tx;ty;td]) = Some (SM.Vi64 (mul_mod x y d)).
Proof.
 move=> Hpin Hx Hy Hd Wx Wy Wd Bd Bx By.
 cbn [term_denote]. rewrite Hx Hy Hd Hpin /system_model_interp. cbn [SM.Vi64].
 rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy) (crt_i64_signed_repr Wd).
 by rewrite (proj2 (sp_mod_b_spec x y d) (conj Bd (conj Bx By))).
Qed.
Ltac sp_bound := first [lia | unfold moduli,word,eea_inputs,MAX,i64_min,i64_max in *; lia].
Ltac sp_word :=
  first [assumption | apply FullWidthExecution.crt_rem_word; [sp_word | sp_bound] | apply crt_contract_signed_word |
    exact (proj2 (sp_result_words _ _ _ _)) |
    exact (proj1 (sp_result_words _ _ _ _)) |
    unfold word, MAX, i64_min, i64_max in *; lia].

Ltac sp_eval :=
  first [assumption |
    match goal with
    | |- term_denote ?V (T_const ?c) = Some ?v => reflexivity
    | |- term_denote ?V (T_local ?i) = Some ?v =>
        cbn [term_denote val_push val_loc];
        match goal with H : val_loc ?W i = Some (VAL_int64 ?x) |- _ =>
          exact (crt_payload_local_term H) end
    | |- term_denote ?V (T_lvar ?i) = _ =>
        let tv := eval cbn [term_denote val_push val_log nth_error] in (term_denote V (T_lvar i)) in
        first [lazymatch tv with Some (SM.Vi64 ?z) => reflexivity end |
          lazymatch tv with Some (VAL_int64 ?x) =>
            apply (@crt_payload_decoded_term V (T_lvar i) x); reflexivity end |
          reflexivity]
    | |- term_denote _ (T_relop _ _ _ _) = _ =>
        eapply term_denote_relop_value; sp_eval
    | |- term_denote _ (T_app 0 _) = _ =>
        eapply sp_gcd_term; [assumption | sp_eval | sp_eval |
          sp_word | sp_word | assumption]
    | |- term_denote _ (T_app 1 _) = _ =>
        eapply sp_normalize_term; [assumption | sp_eval | sp_eval |
          sp_word | sp_word | sp_bound]
    | |- term_denote _ (T_app 2 _) = _ =>
        eapply sp_inverse_term; [assumption | sp_eval | sp_eval |
          sp_word | sp_word | assumption | assumption]
    | |- term_denote _ (T_app 5 _) = _ =>
        eapply sp_solve_term; [assumption | sp_eval | sp_eval |
          sp_eval | sp_eval | sp_word | sp_word |
          sp_word | sp_word]
    | |- term_denote _ (T_app 6 _) = _ =>
        eapply sp_period_term; [assumption | sp_eval | sp_eval | sp_eval | sp_eval | sp_word | sp_word | sp_word | sp_word]
    | |- term_denote _ (T_app 3 _) = _ =>
        eapply sp_add_mod_term; [assumption | sp_eval | sp_eval | sp_eval | sp_word | sp_word | sp_word | lia | lia | sp_bound]
    | |- term_denote _ (T_app 4 _) = _ =>
        eapply sp_mul_mod_term; [assumption | sp_eval | sp_eval | sp_eval | sp_word | sp_word | sp_word | lia | lia | sp_bound]
    | |- term_denote _ (T_binop _ (Binop_i (BOI_rem SX_S)) _ _) = _ =>
        eapply term_denote_binop_value; [sp_eval | sp_eval |];
        apply FullWidthExecution.crt_i64_rem_exact; [sp_word | sp_bound]
    | |- term_denote _ (T_binop _ (Binop_i BOI_mul) _ _) = _ =>
        eapply term_denote_binop_value; [sp_eval | sp_eval |];
        rewrite i64_mul_some crt_i64_mul_repr; [reflexivity | sp_word | sp_word]
    | |- term_denote _ (T_binop _ (Binop_i BOI_add) _ _) = _ =>
        eapply term_denote_binop_value; [sp_eval | sp_eval |];
        rewrite i64_add_some crt_i64_add_repr; [reflexivity | sp_word | sp_word]
    | |- term_denote _ (T_binop _ (Binop_i BOI_sub) _ _) = _ =>
        eapply term_denote_binop_value; [sp_eval | sp_eval |];
        rewrite i64_sub_some crt_i64_sub_repr; [reflexivity | sp_word | sp_word]
    | |- term_denote _ (T_binop _ (Binop_i (BOI_div SX_S)) _ _) = _ =>
        eapply term_denote_binop_value; [sp_eval | sp_eval |];
        apply crt_i64_div_positive_exact; sp_bound
    end].

Ltac sp_relation :=
  rewrite ?crt_contract_le ?crt_contract_lt ?crt_contract_ge ?crt_contract_gt
    ?crt_contract_eq ?crt_contract_ne;
  repeat (rewrite crt_contract_signed_repr; [|sp_word]);
  first [apply Z.leb_le | apply Z.ltb_lt | apply Z.eqb_eq |
    apply negb_true_iff; apply Z.eqb_neq]; first [lia | unfold MAX in *; lia].

Ltac sp_assert :=
  first [apply hdenote_strictify_Hand_true_intro; sp_assert |
    eapply crt_payload_rel_true; [sp_eval | sp_eval | sp_relation] |
    eapply crt_payload_eq; [sp_eval | sp_eval | sp_bound]].

Ltac sp_decode H :=
  rewrite ?crt_contract_le ?crt_contract_lt ?crt_contract_ge ?crt_contract_gt
    ?crt_contract_eq ?crt_contract_ne in H;
  repeat (rewrite crt_contract_signed_repr in H; [|sp_word]);
  fold MAX in H;
  first [apply Z.leb_le in H | apply Z.leb_gt in H | apply Z.ltb_lt in H |
    apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H |
    apply negb_true_iff in H; apply Z.eqb_neq in H | apply negb_false_iff in H; apply Z.eqb_eq in H].

Ltac sp_decode_formula H :=
  rewrite ?crt_contract_le ?crt_contract_lt ?crt_contract_ge ?crt_contract_gt
    ?crt_contract_eq ?crt_contract_ne in H;
  repeat (rewrite crt_contract_signed_repr in H; [|sp_word]);
  fold MAX in H;
  rewrite ?orb_true_iff ?orb_false_iff ?andb_true_iff ?andb_false_iff
    ?Z.leb_le ?Z.leb_gt ?Z.ltb_lt ?Z.ltb_ge ?Z.eqb_eq ?Z.eqb_neq in H.

Ltac sp_intro :=
  first [apply crt_payload_imp_and; sp_intro |
    apply crt_payload_imp_local |
    eapply crt_payload_imp_rel; [sp_eval | sp_eval |]].


Lemma sp_gcd_total_payload V h : val_fun V = system_model_interp ->
 hassert_denote V (ktrue SM.main__HelperContracts_hspec1) h.
Proof.
 move=> Hpin. unfold SM.main__HelperContracts_hspec1,ktrue.
 sp_intro. move=> m Hm. sp_intro. move=> n Hn.
 sp_intro. move=> Hmlo. sp_decode Hmlo. sp_intro. move=> Hnlo. sp_decode Hnlo.
 have Wm := crt_contract_signed_word m. have Wn := crt_contract_signed_word n.
 have Hmods : moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n).
 { unfold moduli,word in *; fold MAX in *; lia. }
 cbn [strictify hassert_denote stack_denote term_denote].
 rewrite Hm Hn Hpin /system_model_interp (proj2 (sp_moduli_b_spec _ _) Hmods). discriminate.
Qed.
Lemma sp_normalize_total_payload V h : val_fun V = system_model_interp ->
 hassert_denote V (ktrue SM.main__HelperContracts_hspec3) h.
Proof.
 move=> Hpin. unfold SM.main__HelperContracts_hspec3,ktrue.
 sp_intro. move=> z Hz. sp_intro. move=> d Hd. sp_intro. move=> Hlo. sp_decode Hlo.
 have Wd := crt_contract_signed_word d.
 have Hguard : ((1 <=? Wasm_int.Int64.signed d) && (Wasm_int.Int64.signed d <=? MAX))%Z = true.
 { rewrite andb_true_iff !Z.leb_le. unfold word in Wd; fold MAX in Wd; lia. }
 cbn [strictify hassert_denote stack_denote term_denote].
 rewrite Hz Hd Hpin /system_model_interp Hguard. discriminate.
Qed.
Lemma sp_gcd_characterization_payload V h : val_fun V = system_model_interp ->
  hassert_denote V (ktrue SM.main__HelperContracts_hspec2) h.
Proof.
  move=> Hpin. unfold SM.main__HelperContracts_hspec2, ktrue.
  sp_intro. move=> m Hm. sp_intro. move=> n Hn.
  sp_intro. move=> Hmlo.
  sp_intro. move=> Hnlo. sp_decode Hmlo. sp_decode Hnlo.
  have Wm := crt_contract_signed_word m. have Wn := crt_contract_signed_word n.
  have Hmods : moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n).
  { unfold moduli,word in *; fold MAX in *; lia. }
  have [Hg [Hgm [Hgn [Hrm [Hrn Hgreat]]]]] := sp_gcd_contract Hmods.
  apply hdenote_strictify_Hand_true_intro; first sp_assert.
  apply hdenote_strictify_Hand_true_intro.
  - apply hdenote_strictify_Hand_true_intro.
    + eapply crt_payload_rel_true.
      * sp_eval.
      * sp_eval.
      * sp_relation.
    + sp_assert.
  -
  sp_intro. move=> d Hd.
  sp_intro. move=> Hdlo. sp_decode Hdlo.
  have Wd := crt_contract_signed_word d. have Hdhi : (Wasm_int.Int64.signed d <= MAX)%Z by exact (proj2 Wd).
  eapply crt_payload_short_and; [sp_eval | sp_eval |].
  eapply crt_payload_imp_test; [reflexivity|]. move=> Htest.
  apply andb_true_iff in Htest. destruct Htest as [Hdm Hdn].
  rewrite !crt_contract_eq in Hdm Hdn.
  rewrite (crt_contract_signed_repr (@crt_rem_word (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed d) (crt_contract_signed_word m) ltac:(lia))) in Hdm.
  rewrite (crt_contract_signed_repr (@crt_rem_word (Wasm_int.Int64.signed n) (Wasm_int.Int64.signed d) (crt_contract_signed_word n) ltac:(lia))) in Hdn.
  change ((Z.rem (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed d) =? 0)%Z = true) in Hdm.
  change ((Z.rem (Wasm_int.Int64.signed n) (Wasm_int.Int64.signed d) =? 0)%Z = true) in Hdn.
  apply Z.eqb_eq in Hdm, Hdn.
  have Hgd := Hgreat (Wasm_int.Int64.signed d) ltac:(lia) Hdm Hdn.
  sp_assert.
Qed.

Lemma sp_normalize_correct_payload V h : val_fun V = system_model_interp ->
  hassert_denote V (ktrue SM.main__HelperContracts_hspec4) h.
Proof.
  move=> Hpin. unfold SM.main__HelperContracts_hspec4, ktrue.
  sp_intro. move=> z Hz. sp_intro. move=> d Hd.
  sp_intro. move=> Hlo. sp_decode Hlo.
  have Wd := crt_contract_signed_word d. have Hhi : (Wasm_int.Int64.signed d <= MAX)%Z by exact (proj2 Wd).
  have Hdw : (1 <= Wasm_int.Int64.signed d <= MAX)%Z by lia.
  have [Hnorm [Hrange [Hrw Hnw]]] := normalize_proved _ _ (crt_contract_signed_word z) Hdw.
  apply hdenote_strictify_Hand_true_intro; first sp_assert.
  apply hdenote_strictify_Hand_true_intro.
  - eapply crt_payload_imp_rel; [sp_eval | sp_eval |]. move=> Htest.
    rewrite crt_contract_lt (crt_contract_signed_repr Hrw) in Htest.
    change ((Z.rem (Wasm_int.Int64.signed z) (Wasm_int.Int64.signed d) <? 0)%Z = true) in Htest.
    rewrite Htest in Hnorm. sp_assert.
  - eapply crt_payload_imp_rel_false; [sp_eval | sp_eval |]. move=> Htest.
    rewrite crt_contract_lt (crt_contract_signed_repr Hrw) in Htest.
    change ((Z.rem (Wasm_int.Int64.signed z) (Wasm_int.Int64.signed d) <? 0)%Z = false) in Htest.
    rewrite Htest in Hnorm. sp_assert.
Qed.


Lemma sp_mul_range_payload V h : val_fun V = system_model_interp ->
 hassert_denote V (ktrue SM.main__HelperContracts_hspec6) h.
Proof.
 move=> Hpin. unfold SM.main__HelperContracts_hspec6,ktrue.
 sp_intro. move=> x Hx. sp_intro. move=> y Hy. sp_intro. move=> d Hd.
 sp_intro. move=> Hdlo. sp_decode Hdlo.
 sp_intro. move=> Hxlo. sp_decode Hxlo. sp_intro. move=> Hxhi. sp_decode Hxhi.
 sp_intro. move=> Hylo. sp_decode Hylo. sp_intro. move=> Hyhi. sp_decode Hyhi.
 have Wd := crt_contract_signed_word d. have Hdhi : (Wasm_int.Int64.signed d <= MAX)%Z by exact (proj2 Wd).
 have [Hval [Hrange Hword]] := mul_mod_proved (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed d) ltac:(lia) ltac:(lia) ltac:(lia).
 sp_assert.
Qed.
Lemma sp_add_correct_payload V h : val_fun V = system_model_interp ->
 hassert_denote V (ktrue SM.main__HelperContracts_hspec5) h.
Proof.
 move=> Hpin. unfold SM.main__HelperContracts_hspec5,ktrue.
 sp_intro. move=> x Hx. sp_intro. move=> y Hy. sp_intro. move=> d Hd.
 sp_intro. move=> Hdlo. sp_decode Hdlo.
 sp_intro. move=> Hxlo. sp_decode Hxlo. sp_intro. move=> Hxhi. sp_decode Hxhi.
 sp_intro. move=> Hylo. sp_decode Hylo. sp_intro. move=> Hyhi. sp_decode Hyhi.
 have Wd := crt_contract_signed_word d. have Hdhi : (Wasm_int.Int64.signed d <= MAX)%Z by exact (proj2 Wd).
 have [Hval [Hrange [Hdiff [Hword Hsum]]]] := add_mod_proved (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed d) ltac:(lia) ltac:(lia) ltac:(lia).
 apply hdenote_strictify_Hand_true_intro; first sp_assert.
 apply hdenote_strictify_Hand_true_intro.
 - eapply crt_payload_imp_rel; [sp_eval | sp_eval |]. move=> Htest. sp_decode Htest.
   have Hresult : add_mod (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed d) =
     (Wasm_int.Int64.signed x - (Wasm_int.Int64.signed d - Wasm_int.Int64.signed y))%Z.
   { rewrite /add_mod. have E : (Wasm_int.Int64.signed d - Wasm_int.Int64.signed y <=? Wasm_int.Int64.signed x)%Z = true by apply/Z.leb_le. by rewrite E. }
   sp_assert.
 - eapply crt_payload_imp_rel_false; [sp_eval | sp_eval |]. move=> Htest. sp_decode Htest.
   have Hresult : add_mod (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed d) =
     (Wasm_int.Int64.signed x + Wasm_int.Int64.signed y)%Z.
   { rewrite /add_mod. have E : (Wasm_int.Int64.signed d - Wasm_int.Int64.signed y <=? Wasm_int.Int64.signed x)%Z = false by apply/Z.leb_gt. by rewrite E. }
   sp_assert.
Qed.
Lemma sp_inverse_total_payload V h : val_fun V = system_model_interp ->
 hassert_denote V (ktrue SM.main__HelperContracts_hspec7) h.
Proof.
 move=> Hpin. unfold SM.main__HelperContracts_hspec7,ktrue.
 sp_intro. move=> B HB. sp_intro. move=> A HA.
 sp_intro. move=> Hlo. sp_decode Hlo. sp_intro. move=> Hlt. sp_decode Hlt.
 have WA := crt_contract_signed_word A. have Hhi : (Wasm_int.Int64.signed A <= MAX)%Z by exact (proj2 WA).
 have Hin : eea_inputs (Wasm_int.Int64.signed A) (Wasm_int.Int64.signed B) by unfold eea_inputs; lia.
 have Hmods : moduli (Wasm_int.Int64.signed A) (Wasm_int.Int64.signed B) by unfold moduli; lia.
 have [Hg [Hga [Hgb _]]] := sp_gcd_contract Hmods.
 eapply crt_payload_imp_eq; [sp_eval | sp_eval | sp_word | sp_word |]. move=> Hcop.
 cbn [strictify hassert_denote stack_denote term_denote].
 rewrite HB HA Hpin /system_model_interp (proj2 (sp_inverse_b_spec _ _) (conj Hin Hcop)). discriminate.
Qed.
Lemma sp_inverse_correct_payload V h : val_fun V = system_model_interp ->
 hassert_denote V (ktrue SM.main__HelperContracts_hspec8) h.
Proof.
 move=> Hpin. unfold SM.main__HelperContracts_hspec8,ktrue.
 sp_intro. move=> B HB. sp_intro. move=> A HA.
 sp_intro. move=> Hlo. sp_decode Hlo. sp_intro. move=> Hlt. sp_decode Hlt.
 have WA := crt_contract_signed_word A. have Hhi : (Wasm_int.Int64.signed A <= MAX)%Z by exact (proj2 WA).
 have Hin : eea_inputs (Wasm_int.Int64.signed A) (Wasm_int.Int64.signed B) by unfold eea_inputs; lia.
 have Hmods : moduli (Wasm_int.Int64.signed A) (Wasm_int.Int64.signed B) by unfold moduli; lia.
 have [Hg [Hga [Hgb _]]] := sp_gcd_contract Hmods.
 eapply crt_payload_imp_eq; [sp_eval | sp_eval | sp_word | sp_word |]. move=> Hcop.
 have [Hu Hmul] := sp_inverse_contract Hin Hcop. sp_assert.
Qed.
Theorem system_helper_payloads V h : val_fun V = system_model_interp ->
 Forall (fun P => hassert_denote V (ktrue P) h) SM.main__HelperContracts_specs.
Proof.
 move=> Hpin. repeat constructor.
 - exact: sp_gcd_total_payload.
 - exact: sp_gcd_characterization_payload.
 - exact: sp_normalize_total_payload.
 - exact: sp_normalize_correct_payload.
 - exact: sp_add_correct_payload.
 - exact: sp_mul_range_payload.
 - exact: sp_inverse_total_payload.
 - exact: sp_inverse_correct_payload.
Qed.
Open Scope Z_scope.
Lemma sp_invalid_contract a m b n : word a -> word m -> word b -> word n ->
 ~ domain a m b n -> sp_solve a m b n = -2 /\ sp_period a m b n = -2.
Proof.
 move=> Wa Wm Wb Wn Hbad. have Hb : merge_bad a m b n = true.
 { case E: (merge_bad a m b n); first reflexivity. exfalso. apply Hbad. exact: (proj1 (merge_bad_false_domain Wa Wm Wb Wn) E). }
 rewrite (merge_bad_model Wa Wm Wb Wn) in Hb.
 rewrite /sp_solve /sp_period /merge. case E: (validb (a,m) && validb (b,n)); first by rewrite E in Hb. by split.
Qed.
Lemma sp_inconsistent_contract a m b n : domain a m b n -> Z.rem (b-a) (Z.gcd m n) <> 0 ->
 sp_solve a m b n = -1 /\ sp_period a m b n = -1.
Proof.
 move=> Hd Hrem. have [[Hm Hn] _] := Hd. have Hg := CRTMath.gcd_positive m n ltac:(lia).
 have Hnc : ~ compatible a m b n by move=> Hc; apply Hrem; apply Z.rem_divide; lia || exact Hc.
 have Hc := merge_contract a m b n Hd.
 rewrite /sp_solve /sp_period. case E: (merge a m b n) Hc => [| | |r p] /= Hc; try tauto.
Qed.
Lemma sp_overflow_contract a m b n : domain a m b n -> Z.rem (b-a) (Z.gcd m n) = 0 ->
 MAX/n < m/Z.gcd m n -> sp_solve a m b n = -3 /\ sp_period a m b n = -3.
Proof.
 move=> Hd Hrem Hguard. have [[Hm Hn] _] := Hd. have Hg := CRTMath.gcd_positive m n ltac:(lia).
 have Hcompat : compatible a m b n by apply Z.rem_divide; lia || exact Hrem.
 have Hlarge := proj1 (proj1 (lcm_guard_proved m n (proj1 Hd))) ltac:(lia).
 have Hc := merge_contract a m b n Hd.
 rewrite /sp_solve /sp_period. case E: (merge a m b n) Hc => [| | |r p] /= Hc; try tauto.
 destruct Hc as [_ [Hp [HB _]]]. lia.
Qed.
Lemma sp_fits_contract a m b n : domain a m b n -> Z.rem (b-a) (Z.gcd m n) = 0 ->
 m/Z.gcd m n <= MAX/n -> 0 <= sp_solve a m b n /\
 sp_period a m b n = (m/Z.gcd m n)*n /\ 1 <= sp_period a m b n.
Proof.
 move=> Hd Hrem Hguard. have [[Hm Hn] _] := Hd. have Hg := CRTMath.gcd_positive m n ltac:(lia).
 have Hcompat : compatible a m b n by apply Z.rem_divide; lia || exact Hrem.
 have Hsmall : Z.lcm m n <= MAX.
 { have Hiff := proj1 (lcm_guard_proved m n (proj1 Hd)). lia. }
 have Hc := merge_contract a m b n Hd.
 have [_ [_ [_ [_ [_ [_ [HL _]]]]]]] := reduction_proved m n ltac:(lia) ltac:(lia).
 rewrite /sp_solve /sp_period. case E: (merge a m b n) Hc => [| | |r p] /= Hc; try tauto; try (destruct Hc; lia).
 destruct Hc as [_ [Hp [HB [Hr Hsol]]]]. unfold period in *. lia.
Qed.
Close Scope Z_scope.
Lemma sp_solve_total_payload V h : val_fun V = system_model_interp ->
 hassert_denote V (ktrue SM.main__PublicContracts_hspec1) h.
Proof.
 move=> Hpin. unfold SM.main__PublicContracts_hspec1,ktrue.
 sp_intro. move=> a Ha. sp_intro. move=> m Hm. sp_intro. move=> b Hb. sp_intro. move=> n Hn.
 cbn [strictify hassert_denote stack_denote term_denote]. rewrite Ha Hm Hb Hn Hpin /system_model_interp. discriminate.
Qed.
Lemma sp_period_total_payload V h : val_fun V = system_model_interp ->
 hassert_denote V (ktrue SM.main__PublicContracts_hspec2) h.
Proof.
 move=> Hpin. unfold SM.main__PublicContracts_hspec2,ktrue.
 sp_intro. move=> a Ha. sp_intro. move=> m Hm. sp_intro. move=> b Hb. sp_intro. move=> n Hn.
 cbn [strictify hassert_denote stack_denote term_denote]. rewrite Ha Hm Hb Hn Hpin /system_model_interp. discriminate.
Qed.
Lemma sp_soundness_payload V h : val_fun V = system_model_interp ->
 hassert_denote V (ktrue SM.main__PublicContracts_hspec4) h.
Proof.
 move=> Hpin. unfold SM.main__PublicContracts_hspec4,ktrue.
 sp_intro. move=> a Ha. sp_intro. move=> m Hm. sp_intro. move=> b Hb. sp_intro. move=> n Hn.
 sp_intro. move=> Htest. sp_decode Htest.
 have [Hd [Hrange [Hremm Hremn]]] := sp_success_contract Htest.
 have [[HmB HnB] [HaB HbB]] := Hd. have Hmods := proj1 Hd.
 sp_assert.
Qed.
Lemma sp_uniqueness_payload V h : val_fun V = system_model_interp ->
 hassert_denote V (ktrue SM.main__PublicContracts_hspec5) h.
Proof.
 move=> Hpin. unfold SM.main__PublicContracts_hspec5,ktrue.
 sp_intro. move=> a Ha. sp_intro. move=> m Hm. sp_intro. move=> b Hb. sp_intro. move=> n Hn.
 sp_intro. move=> Hmlo. sp_decode Hmlo. sp_intro. move=> Hnlo. sp_decode Hnlo.
 sp_intro. move=> Halo. sp_decode Halo. sp_intro. move=> Hahi. sp_decode Hahi.
 sp_intro. move=> Hblo. sp_decode Hblo. sp_intro. move=> Hbhi. sp_decode Hbhi.
 have Wm := crt_contract_signed_word m. have Wn := crt_contract_signed_word n.
 have Hmods : moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n).
 { unfold moduli,word in *; fold MAX in *; lia. }
 have Hdom : domain (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
 (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n) by unfold domain; tauto.
 sp_intro. move=> y Hy. sp_intro. move=> Hylo. sp_decode Hylo. sp_intro. move=> Hyhi. sp_decode Hyhi.
 eapply crt_payload_short_and; [sp_eval | sp_eval |].
 eapply crt_payload_imp_test; [reflexivity|]. move=> Htest. apply andb_true_iff in Htest.
 destruct Htest as [Hym Hyn]. sp_decode Hym. sp_decode Hyn.
 have Hyrange : (0 <= Wasm_int.Int64.signed y < sp_period (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n))%Z by lia.
 have Hunique := sp_unique_contract Hdom Hyrange Hym Hyn. sp_assert.
Qed.
Lemma sp_classification_payload V h : val_fun V = system_model_interp ->
 hassert_denote V (ktrue SM.main__PublicContracts_hspec3) h.
Proof.
 move=> Hpin. unfold SM.main__PublicContracts_hspec3,ktrue.
 sp_intro. move=> a Ha. sp_intro. move=> m Hm. sp_intro. move=> b Hb. sp_intro. move=> n Hn.
 have Wa := crt_contract_signed_word a. have Wm := crt_contract_signed_word m.
 have Wb := crt_contract_signed_word b. have Wn := crt_contract_signed_word n.
 do 5 (eapply crt_payload_short_or; [sp_eval | sp_eval |]).
 apply hdenote_strictify_Hand_true_intro.
 - eapply crt_payload_imp_test; [reflexivity|]. move=> Hbad. sp_decode_formula Hbad.
   have Hnd : ~ domain (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
     (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n) by unfold domain,moduli; lia.
   have [Hx HL] := sp_invalid_contract Wa Wm Wb Wn Hnd. sp_assert.
 - eapply crt_payload_imp_test_false; [reflexivity|]. move=> Hgood. sp_decode_formula Hgood.
   have Hd : domain (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
     (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n).
   { unfold domain,moduli,word in *; fold MAX in *; lia. }
   have Hmods := proj1 Hd. have [[HmB HnB] [HaB HbB]] := Hd.
   have [Hg [Hmq [Hnq [Wg [Wmq [Wnq [Wdiff [Wrem Wdiv]]]]]]]] := reduction_machine_bounds_proved _ _ _ _ Hd.
   have Hmaxq : (0 <= MAX / Wasm_int.Int64.signed n <= MAX)%Z.
   { split; [apply Z.div_pos; unfold MAX,i64_max in *; lia | apply Z.div_le_upper_bound; unfold MAX,i64_max in *; nia]. }
   have Wmaxq := nonnegative_word _ Hmaxq.
   apply hdenote_strictify_Hand_true_intro.
   + eapply crt_payload_imp_rel; [sp_eval | sp_eval |]. move=> Htest. sp_decode Htest.
     have [Hx HL] := sp_inconsistent_contract Hd Htest. sp_assert.
   + eapply crt_payload_imp_rel_false; [sp_eval | sp_eval |]. move=> Htest. sp_decode Htest.
     apply hdenote_strictify_Hand_true_intro.
     * eapply crt_payload_imp_rel; [sp_eval | sp_eval |]. move=> Hover. sp_decode Hover.
       have [Hx HL] := sp_overflow_contract Hd Htest Hover. sp_assert.
     * eapply crt_payload_imp_rel_false; [sp_eval | sp_eval |]. move=> Hfit. sp_decode Hfit.
       have [Hx [HL Hp]] := sp_fits_contract Hd Htest Hfit.
       have Wprod := proj2 (lcm_guard_proved _ _ Hmods) Hfit. sp_assert.
Qed.
Theorem system_public_payloads V h : val_fun V = system_model_interp ->
 Forall (fun P => hassert_denote V (ktrue P) h) SM.main__PublicContracts_specs.
Proof.
 move=> Hpin. repeat constructor.
 - exact: sp_solve_total_payload.
 - exact: sp_period_total_payload.
 - exact: sp_classification_payload.
 - exact: sp_soundness_payload.
 - exact: sp_uniqueness_payload.
Qed.
Section Host.
Context `{ho:host}.
Theorem system_helper_contracts_from_realization (rt : module_runtime SM.main) :
 interp_realized_at rt system_model_interp -> ValidSpec SM.main SM.main__HelperContracts_specs.
Proof.
 move=> Hreal. right. exists rt. move=> h. exists system_model_interp. split; first exact Hreal.
 move=> V Hpin. exact: system_helper_payloads.
Qed.
Theorem system_public_contracts_from_realization (rt : module_runtime SM.main) :
 interp_realized_at rt system_model_interp -> ValidSpec SM.main SM.main__PublicContracts_specs.
Proof.
 move=> Hreal. right. exists rt. move=> h. exists system_model_interp. split; first exact Hreal.
 move=> V Hpin. exact: system_public_payloads.
Qed.
End Host.
Print Assumptions system_helper_payloads.
Print Assumptions system_public_payloads.
