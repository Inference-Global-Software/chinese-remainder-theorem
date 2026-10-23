(* Exact generated assertions under the concrete CRT interpretation.
   Realization of that interpretation is always an explicit hypothesis. *)
From Coq Require Import ZArith NArith Lia List Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations host.
From WasmVerifier Require Import Assertions Semantics NumericDischarge Automation Activation Verifier.
From CRT Require Import CRTStatements CRTMath CRTLoops.
From CRTWasm Require Import CRTAPIModel CRTContracts CRTExecution.
From CRTGenerated Require Import crt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Close Scope Z_scope.

Lemma crt_payload_imp_and V d p q r h :
  hassert_denote V (strictify d true (Himpl p (Himpl q r))) h ->
  hassert_denote V (strictify d true (Himpl (HA_and p q) r)) h.
Proof. cbn [Himpl Hor strictify hassert_denote negb]. tauto. Qed.

Lemma crt_payload_imp_local V d i p h :
  (forall x : i64, val_loc V i = Some (VAL_int64 x) ->
    hassert_denote V (strictify d true p) h) ->
  hassert_denote V (strictify d true (Himpl (HA_has_type (T_local i) T_i64) p)) h.
Proof.
  move=> H. case: (crt_leaf_i64_or_kfalse V h i) => [[x Hx]|Hbad].
  - apply: hdenote_strictify_Himpl_intror. exact: H Hx.
  - apply: hdenote_strictify_Himpl_introl. exact Hbad.
Qed.

Lemma crt_payload_imp_rel V d nt op a b va vb p h :
  term_denote V a = Some va -> term_denote V b = Some vb ->
  (app_relop op va vb = true -> hassert_denote V (strictify d true p) h) ->
  hassert_denote V (strictify d true
    (Himpl (HA_not (term_eq (T_relop nt op a b) (T_const (crt.Vi32 0)))) p)) h.
Proof.
  move=> Ha Hb H. case E: (app_relop op va vb).
  - apply: hdenote_strictify_Himpl_intror. exact: H E.
  - apply: hdenote_strictify_Himpl_introl.
    exists (crt.Vi32 0). split; last by []. by rewrite /= Ha Hb E.
Qed.

Lemma crt_payload_rel_true V d nt op a b va vb h :
  term_denote V a = Some va -> term_denote V b = Some vb ->
  app_relop op va vb = true ->
  hassert_denote V (strictify d true
    (HA_not (term_eq (T_relop nt op a b) (T_const (crt.Vi32 0))))) h.
Proof.
  move=> Ha Hb H. rewrite /term_eq /= Ha Hb H.
  split; [by eexists |]. split; [by eexists |].
  move=> [v [[<-] Hv]]. inversion Hv.
Qed.

Lemma crt_payload_imp_rel_false V d nt op a b va vb p h :
  term_denote V a = Some va -> term_denote V b = Some vb ->
  (app_relop op va vb = false -> hassert_denote V (strictify d true p) h) ->
  hassert_denote V (strictify d true
    (Himpl (term_eq (T_relop nt op a b) (T_const (crt.Vi32 0))) p)) h.
Proof.
  move=> Ha Hb H. case E: (app_relop op va vb).
  - apply: hdenote_strictify_Himpl_introl.
    exact: (@crt_payload_rel_true V d nt op a b va vb h Ha Hb E).
  - apply: hdenote_strictify_Himpl_intror. exact: H E.
Qed.

Lemma crt_payload_test_true V d t h :
  term_denote V t = Some (crt.Vi32 1) ->
  hassert_denote V (strictify d true (HA_not (term_eq t (T_const (crt.Vi32 0))))) h.
Proof.
  move=> Ht. rewrite /term_eq /= Ht.
  split; [by eexists|]. split; [by eexists|]. move=> [v [[<-] E]]. discriminate.
Qed.

Lemma crt_payload_imp_test V d t b p h :
  term_denote V t = Some (VAL_int32 (wasm_bool b)) ->
  (b = true -> hassert_denote V (strictify d true p) h) ->
  hassert_denote V (strictify d true (Himpl (HA_not (term_eq t (T_const (crt.Vi32 0)))) p)) h.
Proof.
  move=> Ht H. case E: b.
  - apply: hdenote_strictify_Himpl_intror. exact: H E.
  - apply: hdenote_strictify_Himpl_introl. exists (crt.Vi32 0).
    split; last reflexivity. by rewrite Ht E.
Qed.

Lemma crt_payload_imp_test_false V d t b p h :
  term_denote V t = Some (VAL_int32 (wasm_bool b)) ->
  (b = false -> hassert_denote V (strictify d true p) h) ->
  hassert_denote V (strictify d true (Himpl (term_eq t (T_const (crt.Vi32 0))) p)) h.
Proof.
  move=> Ht H. case E: b.
  - apply: hdenote_strictify_Himpl_introl. apply crt_payload_test_true. by rewrite Ht E.
  - apply: hdenote_strictify_Himpl_intror. exact: H E.
Qed.

Lemma crt_payload_short_and V d t u p h b1 b2 :
  let V' := val_push (VAL_int32 (wasm_bool (b1 && b2))) V in
  term_denote V' t = Some (VAL_int32 (wasm_bool b1)) ->
  term_denote V' u = Some (VAL_int32 (wasm_bool b2)) ->
  hassert_denote V' (strictify d.+1 true p) h ->
  hassert_denote V (strictify d true
    (HA_ex (HA_and
      (Hor (HA_and (HA_not (term_eq t (T_const (crt.Vi32 0)))) (term_eq (T_lvar 0) u))
           (HA_and (term_eq t (T_const (crt.Vi32 0))) (term_eq (T_lvar 0) (T_const (crt.Vi32 0))))) p))) h.
Proof.
  cbn zeta. move=> Ht Hu Hp. apply: hdenote_strictify_Hex_intro.
  apply hdenote_strictify_Hand_true_intro; last exact Hp.
  case E: b1 in Ht Hu *.
  - apply hdenote_strictify_Hor_introl. apply hdenote_strictify_Hand_true_intro.
    + apply crt_payload_test_true. exact Ht.
    + eapply hdenote_strictify_term_eq_intro; [reflexivity | exact Hu].
  - apply hdenote_strictify_Hor_intror. apply hdenote_strictify_Hand_true_intro.
    + eapply hdenote_strictify_term_eq_intro; [exact Ht | reflexivity].
    + eapply hdenote_strictify_term_eq_intro; reflexivity.
Qed.

Lemma crt_payload_short_or V d t u p h b1 b2 :
  let V' := val_push (VAL_int32 (wasm_bool (b1 || b2))) V in
  term_denote V' t = Some (VAL_int32 (wasm_bool b1)) ->
  term_denote V' u = Some (VAL_int32 (wasm_bool b2)) ->
  hassert_denote V' (strictify d.+1 true p) h ->
  hassert_denote V (strictify d true
    (HA_ex (HA_and
      (Hor (HA_and (HA_not (term_eq t (T_const (crt.Vi32 0)))) (term_eq (T_lvar 0) (T_const (crt.Vi32 1))))
           (HA_and (term_eq t (T_const (crt.Vi32 0))) (term_eq (T_lvar 0) u))) p))) h.
Proof.
  cbn zeta. move=> Ht Hu Hp. apply: hdenote_strictify_Hex_intro.
  apply hdenote_strictify_Hand_true_intro; last exact Hp.
  case E: b1 in Ht Hu *.
  - apply hdenote_strictify_Hor_introl. apply hdenote_strictify_Hand_true_intro.
    + apply crt_payload_test_true. exact Ht.
    + eapply hdenote_strictify_term_eq_intro; reflexivity.
  - apply hdenote_strictify_Hor_intror. apply hdenote_strictify_Hand_true_intro.
    + eapply hdenote_strictify_term_eq_intro; [exact Ht | reflexivity].
    + eapply hdenote_strictify_term_eq_intro; [reflexivity | exact Hu].
Qed.

Ltac crt_payload_term :=
  cbn [term_denote val_push val_loc val_fun val_log nth_error];
  repeat match goal with H : val_loc ?V ?i = Some ?v |- context [val_loc ?V ?i] => rewrite H end;
  reflexivity.

Ltac crt_payload_intro :=
  first [apply crt_payload_imp_and; crt_payload_intro |
    apply crt_payload_imp_local |
    eapply crt_payload_imp_rel; [crt_payload_term | crt_payload_term |]].

Ltac crt_payload_zguards :=
  repeat match goal with
  | H : app_relop _ _ _ = true |- _ =>
      rewrite ?crt_contract_le ?crt_contract_lt ?crt_contract_ge ?crt_contract_gt
        ?crt_contract_eq ?crt_contract_ne in H;
      rewrite ?crt_contract_signed_one ?crt_contract_signed_M in H;
      first [apply Z.leb_le in H | apply Z.ltb_lt in H | apply Z.eqb_eq in H]
  end.

Lemma crt_payload_inverse_guard B A :
  eea_inputs A B -> Z.gcd A B = 1%Z ->
  ((1 <=? B) && (B <? A) && (A <=? M) && (Z.gcd A B =? 1))%Z = true.
Proof.
  move=> [[HB HBA] HA] Hcop. rewrite !andb_true_iff.
  repeat split; [apply Z.leb_le | apply Z.ltb_lt | apply Z.leb_le | apply Z.eqb_eq]; lia.
Qed.

Lemma crt_payload_inverse_total V h : val_fun V = crt_model_interp ->
  hassert_denote V (ktrue crt.crt__HelperContracts_hspec5) h.
Proof.
  move=> Hpin. unfold crt.crt__HelperContracts_hspec5, ktrue.
  crt_payload_intro. move=> B HB. crt_payload_intro. move=> A HA.
  crt_payload_intro. move=> Hlo. crt_payload_intro. move=> Hlt.
  crt_payload_intro. move=> Hhi. crt_payload_zguards.
  have Hin : eea_inputs (Wasm_int.Int64.signed A) (Wasm_int.Int64.signed B).
  { unfold eea_inputs. lia. }
  have Hmods : moduli (Wasm_int.Int64.signed A) (Wasm_int.Int64.signed B).
  { unfold moduli. lia. }
  have Hgword : word (Z.gcd (Wasm_int.Int64.signed A) (Wasm_int.Int64.signed B)).
  { have [Hg [Hga _]] := crt_gcd_Z_source_contract _ _ Hmods.
    unfold word, i64_min, i64_max. unfold M in Hhi. lia. }
  case Hcop: (Z.gcd (Wasm_int.Int64.signed A) (Wasm_int.Int64.signed B) =? 1)%Z.
  - apply Z.eqb_eq in Hcop. apply: hdenote_strictify_Himpl_intror.
    cbn [strictify hassert_denote stack_denote term_denote].
    rewrite HB HA Hpin /crt_model_interp (crt_payload_inverse_guard Hin Hcop). discriminate.
  - apply: hdenote_strictify_Himpl_introl.
    rewrite /= HA HB Hpin /crt_model_interp (proj2 (crt_moduli_b_spec _ _) Hmods).
    split; [by eexists |]. split; [by eexists |].
    move=> [v [[<-] Heq]].
    have Hsigned := f_equal (fun v => match v with VAL_int64 x => Wasm_int.Int64.signed x | _ => 0%Z end) (f_equal (fun ov => match ov with Some v => v | None => crt.Vi64 0 end) Heq).
    change (1%Z = Wasm_int.Int64.signed (Wasm_int.Int64.repr (Z.gcd (Wasm_int.Int64.signed A) (Wasm_int.Int64.signed B)))) in Hsigned.
    rewrite crt_contract_signed_repr in Hsigned; last exact Hgword.
    apply Z.eqb_neq in Hcop. apply Hcop. symmetry. exact Hsigned.
Qed.

Lemma crt_payload_gcd_term V a b m n :
  val_fun V = crt_model_interp ->
  term_denote V a = Some (crt.Vi64 m) -> term_denote V b = Some (crt.Vi64 n) ->
  word m -> word n -> moduli m n ->
  term_denote V (T_app 0 [::a;b]) = Some (crt.Vi64 (Z.gcd m n)).
Proof.
  move=> Hpin Ha Hb Hm Hn Hd. cbn [term_denote]. rewrite Ha Hb Hpin /crt_model_interp. cbn [crt.Vi64].
  by rewrite (crt_i64_signed_repr Hm) (crt_i64_signed_repr Hn) (proj2 (crt_moduli_b_spec _ _) Hd).
Qed.

Lemma crt_payload_normalize_term V a b z d :
  val_fun V = crt_model_interp ->
  term_denote V a = Some (crt.Vi64 z) -> term_denote V b = Some (crt.Vi64 d) ->
  word z -> word d -> (1 <= d <= M)%Z ->
  term_denote V (T_app 1 [::a;b]) = Some (crt.Vi64 (z mod d)).
Proof.
  move=> Hpin Ha Hb Hz Hd Hbound. cbn [term_denote]. rewrite Ha Hb Hpin /crt_model_interp. cbn [crt.Vi64].
  rewrite (crt_i64_signed_repr Hz) (crt_i64_signed_repr Hd).
  have Hguard : ((1 <=? d) && (d <=? M))%Z = true.
  { apply/andb_true_iff. split; apply/Z.leb_le; lia. }
  by rewrite Hguard.
Qed.

Lemma crt_payload_inverse_term V a b B A :
  val_fun V = crt_model_interp ->
  term_denote V a = Some (crt.Vi64 B) -> term_denote V b = Some (crt.Vi64 A) ->
  word B -> word A -> eea_inputs A B -> Z.gcd A B = 1%Z ->
  term_denote V (T_app 2 [::a;b]) = Some (crt.Vi64 (crt_inverse_Z B A)).
Proof.
  move=> Hpin Ha Hb HB HA Hin Hcop. cbn [term_denote]. rewrite Ha Hb Hpin /crt_model_interp. cbn [crt.Vi64].
  by rewrite (crt_i64_signed_repr HB) (crt_i64_signed_repr HA) (crt_payload_inverse_guard Hin Hcop).
Qed.

Lemma crt_payload_period_term V a b m n :
  val_fun V = crt_model_interp ->
  term_denote V a = Some (crt.Vi64 m) -> term_denote V b = Some (crt.Vi64 n) ->
  word m -> word n ->
  term_denote V (T_app 3 [::a;b]) = Some (crt.Vi64 (crt_period_Z m n)).
Proof.
  move=> Hpin Ha Hb Hm Hn. cbn [term_denote]. rewrite Ha Hb Hpin /crt_model_interp. cbn [crt.Vi64].
  by rewrite (crt_i64_signed_repr Hm) (crt_i64_signed_repr Hn).
Qed.

Lemma crt_payload_solve_term V ta tm tb tn a m b n :
  val_fun V = crt_model_interp ->
  term_denote V ta = Some (crt.Vi64 a) -> term_denote V tm = Some (crt.Vi64 m) ->
  term_denote V tb = Some (crt.Vi64 b) -> term_denote V tn = Some (crt.Vi64 n) ->
  word a -> word m -> word b -> word n ->
  term_denote V (T_app 4 [::ta;tm;tb;tn]) = Some (crt.Vi64 (crt_solve_Z a m b n)).
Proof.
  move=> Hpin Ha Hm Hb Hn HaW HmW HbW HnW. cbn [term_denote].
  rewrite Ha Hm Hb Hn Hpin /crt_model_interp. cbn [crt.Vi64].
  by rewrite (crt_i64_signed_repr HaW) (crt_i64_signed_repr HmW)
    (crt_i64_signed_repr HbW) (crt_i64_signed_repr HnW).
Qed.

Lemma crt_payload_imp_eq V d a b x y p h :
  term_denote V a = Some (crt.Vi64 x) -> term_denote V b = Some (crt.Vi64 y) ->
  word x -> word y ->
  (x = y -> hassert_denote V (strictify d true p) h) ->
  hassert_denote V (strictify d true (Himpl (term_eq a b) p)) h.
Proof.
  move=> Ha Hb Hx Hy H. case: (Z.eq_dec x y) => [Heq|Hne].
  - apply: hdenote_strictify_Himpl_intror. exact: H Heq.
  - apply: hdenote_strictify_Himpl_introl. rewrite /term_eq /= Ha Hb.
    split; [by eexists|]. split; [by eexists|]. move=> [v [[<-] Heq]].
    change (Some (VAL_int64 (Wasm_int.Int64.repr y)) = Some (VAL_int64 (Wasm_int.Int64.repr x))) in Heq.
    have E := f_equal (fun ov => match ov with Some (VAL_int64 z) => z | _ => Wasm_int.Int64.zero end) Heq.
    have := f_equal Wasm_int.Int64.signed E.
    rewrite (crt_i64_signed_repr Hx) (crt_i64_signed_repr Hy). congruence.
Qed.

Lemma crt_payload_local_term V i x : val_loc V i = Some (VAL_int64 x) ->
  term_denote V (T_local i) = Some (crt.Vi64 (Wasm_int.Int64.signed x)).
Proof. by rewrite crt_contract_repr_signed. Qed.

Lemma crt_payload_decoded_term V t x : term_denote V t = Some (VAL_int64 x) ->
  term_denote V t = Some (crt.Vi64 (Wasm_int.Int64.signed x)).
Proof. by rewrite crt_contract_repr_signed. Qed.

Lemma crt_payload_eq V d t u x y h :
  term_denote V t = Some (crt.Vi64 x) -> term_denote V u = Some (crt.Vi64 y) ->
  x = y -> hassert_denote V (strictify d true (term_eq t u)) h.
Proof. move=> Ht Hu E. subst y. exact: hdenote_strictify_term_eq_intro Ht Hu. Qed.

Lemma crt_payload_imp_bound V d v p h :
  (forall x : i64, v = VAL_int64 x ->
    hassert_denote (val_push v V) (strictify d.+1 true p) h) ->
  hassert_denote (val_push v V) (strictify d.+1 true
    (Himpl (HA_has_type (T_lvar 0) T_i64) p)) h.
Proof.
  move=> H. case: v H => [c32|x|f32v|f64v] H.
  - apply: hdenote_strictify_Himpl_introl. rewrite /=. move=> [v [[<-] E]]. discriminate.
  - apply: hdenote_strictify_Himpl_intror. exact: H erefl.
  - apply: hdenote_strictify_Himpl_introl. rewrite /=. move=> [v [[<-] E]]. discriminate.
  - apply: hdenote_strictify_Himpl_introl. rewrite /=. move=> [v [[<-] E]]. discriminate.
Qed.

Ltac crt_payload_word :=
  first [assumption | apply crt_rem_word; [crt_payload_word | lia] | apply crt_contract_signed_word |
    exact (proj2 (crt_period_Z_correct _ _)) |
    exact (proj2 (crt_solve_Z_correct _ _ _ _)) |
    unfold word, i64_min, i64_max in *; unfold M in *; lia].

Ltac crt_payload_eval :=
  first [assumption |
    match goal with
    | |- term_denote ?V (T_const ?c) = Some ?v => reflexivity
    | |- term_denote ?V (T_local ?i) = Some ?v =>
        cbn [term_denote val_push val_loc];
        match goal with H : val_loc ?W i = Some (VAL_int64 ?x) |- _ =>
          exact (crt_payload_local_term H) end
    | |- term_denote ?V (T_lvar ?i) = _ =>
        let tv := eval cbn [term_denote val_push val_log nth_error] in (term_denote V (T_lvar i)) in
        first [lazymatch tv with Some (crt.Vi64 ?z) => reflexivity end |
          lazymatch tv with Some (VAL_int64 ?x) =>
            apply (@crt_payload_decoded_term V (T_lvar i) x); reflexivity end |
          reflexivity]
    | |- term_denote _ (T_relop _ _ _ _) = _ =>
        eapply term_denote_relop_value; crt_payload_eval
    | |- term_denote _ (T_app 0 _) = _ =>
        eapply crt_payload_gcd_term; [assumption | crt_payload_eval | crt_payload_eval |
          crt_payload_word | crt_payload_word | assumption]
    | |- term_denote _ (T_app 1 _) = _ =>
        eapply crt_payload_normalize_term; [assumption | crt_payload_eval | crt_payload_eval |
          crt_payload_word | crt_payload_word | lia]
    | |- term_denote _ (T_app 2 _) = _ =>
        eapply crt_payload_inverse_term; [assumption | crt_payload_eval | crt_payload_eval |
          crt_payload_word | crt_payload_word | assumption | assumption]
    | |- term_denote _ (T_app 3 _) = _ =>
        eapply crt_payload_period_term; [assumption | crt_payload_eval | crt_payload_eval |
          crt_payload_word | crt_payload_word]
    | |- term_denote _ (T_app 4 _) = _ =>
        eapply crt_payload_solve_term; [assumption | crt_payload_eval | crt_payload_eval |
          crt_payload_eval | crt_payload_eval | crt_payload_word | crt_payload_word |
          crt_payload_word | crt_payload_word]
    | |- term_denote _ (T_binop _ (Binop_i (BOI_rem SX_S)) _ _) = _ =>
        eapply term_denote_binop_value; [crt_payload_eval | crt_payload_eval |];
        apply crt_i64_rem_exact; [crt_payload_word | lia]
    | |- term_denote _ (T_binop _ (Binop_i BOI_mul) _ _) = _ =>
        eapply term_denote_binop_value; [crt_payload_eval | crt_payload_eval |];
        rewrite i64_mul_some crt_i64_mul_repr; [reflexivity | crt_payload_word | crt_payload_word]
    | |- term_denote _ (T_binop _ (Binop_i BOI_add) _ _) = _ =>
        eapply term_denote_binop_value; [crt_payload_eval | crt_payload_eval |];
        rewrite i64_add_some crt_i64_add_repr; [reflexivity | crt_payload_word | crt_payload_word]
    | |- term_denote _ (T_binop _ (Binop_i BOI_sub) _ _) = _ =>
        eapply term_denote_binop_value; [crt_payload_eval | crt_payload_eval |];
        rewrite i64_sub_some crt_i64_sub_repr; [reflexivity | crt_payload_word | crt_payload_word]
    | |- term_denote _ (T_binop _ (Binop_i (BOI_div SX_S)) _ _) = _ =>
        eapply term_denote_binop_value; [crt_payload_eval | crt_payload_eval |];
        apply crt_i64_div_positive_exact; lia
    end].

Ltac crt_payload_relation :=
  rewrite ?crt_contract_le ?crt_contract_lt ?crt_contract_ge ?crt_contract_gt
    ?crt_contract_eq ?crt_contract_ne;
  repeat (rewrite crt_contract_signed_repr; [|crt_payload_word]);
  first [apply Z.leb_le | apply Z.ltb_lt | apply Z.eqb_eq |
    apply negb_true_iff; apply Z.eqb_neq]; first [lia | unfold M in *; lia].

Ltac crt_payload_assert :=
  first [apply hdenote_strictify_Hand_true_intro; crt_payload_assert |
    eapply crt_payload_rel_true; [crt_payload_eval | crt_payload_eval | crt_payload_relation] |
    eapply crt_payload_eq; [crt_payload_eval | crt_payload_eval | lia]].

Ltac crt_payload_decode H :=
  rewrite ?crt_contract_le ?crt_contract_lt ?crt_contract_ge ?crt_contract_gt
    ?crt_contract_eq ?crt_contract_ne in H;
  repeat (rewrite crt_contract_signed_repr in H; [|crt_payload_word]);
  fold M in H;
  first [apply Z.leb_le in H | apply Z.leb_gt in H | apply Z.ltb_lt in H |
    apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H].

Ltac crt_payload_decode_formula H :=
  rewrite ?crt_contract_le ?crt_contract_lt ?crt_contract_ge ?crt_contract_gt
    ?crt_contract_eq ?crt_contract_ne in H;
  repeat (rewrite crt_contract_signed_repr in H; [|crt_payload_word]);
  fold M in H;
  rewrite ?orb_true_iff ?orb_false_iff ?andb_true_iff ?andb_false_iff
    ?Z.leb_le ?Z.leb_gt ?Z.ltb_lt ?Z.ltb_ge ?Z.eqb_eq ?Z.eqb_neq in H.

Ltac crt_payload_intro_eval :=
  first [apply crt_payload_imp_and; crt_payload_intro_eval |
    apply crt_payload_imp_local |
    eapply crt_payload_imp_rel; [crt_payload_eval | crt_payload_eval |]].

Ltac crt_payload_public_domain a Ha m Hm b Hb n Hn :=
  crt_payload_intro_eval; intros a Ha;
  crt_payload_intro_eval; intros m Hm;
  crt_payload_intro_eval; intros b Hb;
  crt_payload_intro_eval; intros n Hn;
  let H1 := fresh "Hmlo" in let H2 := fresh "Hmhi" in
  let H3 := fresh "Hnlo" in let H4 := fresh "Hnhi" in
  let H5 := fresh "Halo" in let H6 := fresh "Hahi" in
  let H7 := fresh "Hblo" in let H8 := fresh "Hbhi" in
  crt_payload_intro_eval; intros H1; crt_payload_decode H1;
  crt_payload_intro_eval; intros H2; crt_payload_decode H2;
  crt_payload_intro_eval; intros H3; crt_payload_decode H3;
  crt_payload_intro_eval; intros H4; crt_payload_decode H4;
  crt_payload_intro_eval; intros H5; crt_payload_decode H5;
  crt_payload_intro_eval; intros H6; crt_payload_decode H6;
  crt_payload_intro_eval; intros H7; crt_payload_decode H7;
  crt_payload_intro_eval; intros H8; crt_payload_decode H8.

Lemma crt_payload_solve_compatibility V h : val_fun V = crt_model_interp ->
  hassert_denote V (ktrue crt.crt__PublicContracts_hspec5) h.
Proof.
  move=> Hpin. unfold crt.crt__PublicContracts_hspec5, ktrue.
  crt_payload_public_domain a Ha m Hm b Hb n Hn.
  have Hmods : moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) by unfold moduli; lia.
  have Hdom : domain (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
    (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n) by unfold domain; tauto.
  have [Hg [Hgm [Hgn _]]] := crt_gcd_Z_source_contract _ _ Hmods.
  have [Hyes Hno] := crt_solve_Z_compatibility_contract _ _ _ _ Hdom.
  apply hdenote_strictify_Hand_true_intro.
  - eapply crt_payload_imp_rel; [crt_payload_eval | crt_payload_eval |]. move=> Htest.
    crt_payload_decode Htest. have Hx := Hyes Htest. crt_payload_assert.
  - eapply crt_payload_imp_rel_false; [crt_payload_eval | crt_payload_eval |]. move=> Htest.
    crt_payload_decode Htest. have Hx := Hno Htest. crt_payload_assert.
Qed.

Lemma crt_payload_solve_soundness V h : val_fun V = crt_model_interp ->
  hassert_denote V (ktrue crt.crt__PublicContracts_hspec6) h.
Proof.
  move=> Hpin. unfold crt.crt__PublicContracts_hspec6, ktrue.
  crt_payload_public_domain a Ha m Hm b Hb n Hn.
  have Hmods : moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) by unfold moduli; lia.
  have Hdom : domain (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
    (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n) by unfold domain; tauto.
  crt_payload_intro_eval. move=> Htest. crt_payload_decode Htest.
  have [Hrange [Hremm Hremn]] := crt_solve_Z_solution_contract _ _ _ _ Hdom Htest.
  crt_payload_assert.
Qed.

Lemma crt_payload_canonical_uniqueness V h : val_fun V = crt_model_interp ->
  hassert_denote V (ktrue crt.crt__PublicContracts_hspec7) h.
Proof.
  move=> Hpin. unfold crt.crt__PublicContracts_hspec7, ktrue.
  crt_payload_public_domain a Ha m Hm b Hb n Hn.
  have Hmods : moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) by unfold moduli; lia.
  have Hdom : domain (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
    (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n) by unfold domain; tauto.
  crt_payload_intro_eval. move=> y Hy.
  crt_payload_intro_eval. move=> Hylo. crt_payload_decode Hylo.
  crt_payload_intro_eval. move=> Hyhi. crt_payload_decode Hyhi.
  eapply crt_payload_short_and; [crt_payload_eval | crt_payload_eval |].
  eapply crt_payload_imp_test; [reflexivity|]. move=> Htest.
  apply andb_true_iff in Htest. destruct Htest as [Hym Hyn].
  crt_payload_decode Hym. crt_payload_decode Hyn.
  have HL : crt_period_Z (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) =
    period (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n).
  { by rewrite /crt_period_Z (proj2 (crt_moduli_b_spec _ _) Hmods). }
  have Hcanon : canonical (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
    (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n) (Wasm_int.Int64.signed y).
  { split; [rewrite -HL; lia |]. apply crt_remainders_solution; try assumption; lia. }
  have Hunique := crt_solve_Z_unique _ _ _ _ _ Hdom Hcanon.
  crt_payload_assert.
Qed.

Lemma crt_payload_solve_validation V h : val_fun V = crt_model_interp ->
  hassert_denote V (ktrue crt.crt__PublicContracts_hspec3) h.
Proof.
  move=> Hpin. unfold crt.crt__PublicContracts_hspec3, ktrue.
  crt_payload_intro_eval. move=> a Ha. crt_payload_intro_eval. move=> m Hm.
  crt_payload_intro_eval. move=> b Hb. crt_payload_intro_eval. move=> n Hn.
  do 7 (eapply crt_payload_short_or; [crt_payload_eval | crt_payload_eval |]).
  have [Hinvalid Hvalid] := crt_solve_Z_domain_contract (Wasm_int.Int64.signed a)
    (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n).
  apply hdenote_strictify_Hand_true_intro.
  - eapply crt_payload_imp_test; [reflexivity|]. move=> Hbad. crt_payload_decode_formula Hbad.
    have Hnd : ~ domain (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
      (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n).
    { unfold domain, moduli. lia. }
    have Hx := Hinvalid Hnd. crt_payload_assert.
  - eapply crt_payload_imp_test_false; [reflexivity|]. move=> Hgood. crt_payload_decode_formula Hgood.
    have Hd : domain (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
      (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n).
    { unfold domain, moduli. lia. }
    have Hx := Hvalid Hd. crt_payload_assert.
Qed.

Lemma crt_payload_period_contract V h : val_fun V = crt_model_interp ->
  hassert_denote V (ktrue crt.crt__PublicContracts_hspec4) h.
Proof.
  move=> Hpin. unfold crt.crt__PublicContracts_hspec4, ktrue.
  crt_payload_intro_eval. move=> m Hm. crt_payload_intro_eval. move=> n Hn.
  do 3 (eapply crt_payload_short_or; [crt_payload_eval | crt_payload_eval |]).
  apply hdenote_strictify_Hand_true_intro.
  - eapply crt_payload_imp_test; [reflexivity|]. move=> Hbad. crt_payload_decode_formula Hbad.
    have Hnd : ~ moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n).
    { unfold moduli. lia. }
    have Hp : crt_period_Z (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) = (-2)%Z.
    { unfold crt_period_Z. case E: (crt_moduli_b _ _); last reflexivity.
      exfalso. apply Hnd. exact (proj1 (crt_moduli_b_spec _ _) E). }
    crt_payload_assert.
  - eapply crt_payload_imp_test_false; [reflexivity|]. move=> Hgood. crt_payload_decode_formula Hgood.
    have Hmods : moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n).
    { unfold moduli. lia. }
    have [Hmrange Hnrange] := Hmods.
    have [Hg [Hgm [Hgn _]]] := crt_gcd_Z_source_contract _ _ Hmods.
    have [Hbound Hword] := crt_period_bounds _ _ Hmods.
    have Hquot : (0 <= Wasm_int.Int64.signed m / Z.gcd (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) <= M)%Z.
    { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; nia. }
    have Hp : crt_period_Z (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) =
      period (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n).
    { by rewrite /crt_period_Z (proj2 (crt_moduli_b_spec _ _) Hmods). }
    unfold period in Hp, Hbound, Hword. crt_payload_assert.
Qed.

Lemma crt_payload_impossibility V h : val_fun V = crt_model_interp ->
  hassert_denote V (ktrue crt.crt__PublicContracts_hspec8) h.
Proof.
  move=> Hpin. unfold crt.crt__PublicContracts_hspec8, ktrue.
  crt_payload_public_domain a Ha m Hm b Hb n Hn.
  have Hmods : moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) by unfold moduli; lia.
  have Hdom : domain (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
    (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n) by unfold domain; tauto.
  crt_payload_intro_eval. move=> y Hy.
  crt_payload_intro_eval. move=> Hylo. crt_payload_decode Hylo.
  crt_payload_intro_eval. move=> Hyhi. crt_payload_decode Hyhi.
  crt_payload_intro_eval. move=> Hreject. crt_payload_decode Hreject.
  have [Hbadm|Hbadn] := crt_solve_Z_impossibility_contract _ _ _ _ _ Hdom Hreject Hylo.
  - apply hdenote_strictify_Hor_introl. crt_payload_assert.
  - apply hdenote_strictify_Hor_intror. crt_payload_assert.
Qed.

Lemma crt_payload_exists_unique V h : val_fun V = crt_model_interp ->
  hassert_denote V (ktrue crt.crt__PublicContracts_hspec9) h.
Proof.
  move=> Hpin. unfold crt.crt__PublicContracts_hspec9, ktrue.
  crt_payload_public_domain a Ha m Hm b Hb n Hn.
  have Hmods : moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n) by unfold moduli; lia.
  have Hdom : domain (Wasm_int.Int64.signed a) (Wasm_int.Int64.signed m)
    (Wasm_int.Int64.signed b) (Wasm_int.Int64.signed n) by unfold domain; tauto.
  have [Hg [Hgm [Hgn _]]] := crt_gcd_Z_source_contract _ _ Hmods.
  eapply crt_payload_imp_eq; [crt_payload_eval | crt_payload_eval | crt_payload_word | crt_payload_word |].
  move=> Hcompatible.
  have [x [Hxword [[Hxlo Hxhi] [Hxm [Hxn [Hxs Hunique]]]]]] :=
    crt_solve_Z_existence_contract _ _ _ _ Hdom Hcompatible.
  apply (@hdenote_strictify_Hex_intro V 0 _ h (crt.Vi64 x)).
  apply hdenote_strictify_Hand_true_intro; first crt_payload_assert.
  apply hdenote_strictify_Hand_true_intro; first crt_payload_assert.
  apply hdenote_strictify_Hand_true_intro; first crt_payload_assert.
  apply hdenote_strictify_Hall_intro. move=> v.
  apply crt_payload_imp_and. apply crt_payload_imp_bound. move=> y ->.
  crt_payload_intro_eval. move=> Hylo. crt_payload_decode Hylo.
  crt_payload_intro_eval. move=> Hyhi. crt_payload_decode Hyhi.
  eapply crt_payload_short_and; [crt_payload_eval | crt_payload_eval |].
  eapply crt_payload_imp_test; [reflexivity|]. move=> Htest.
  apply andb_true_iff in Htest. destruct Htest as [Hym Hyn].
  crt_payload_decode Hym. crt_payload_decode Hyn.
  have Hyx := Hunique (Wasm_int.Int64.signed y) ltac:(lia) Hym Hyn.
  crt_payload_assert.
Qed.

Lemma crt_payload_inverse_correct V h : val_fun V = crt_model_interp ->
  hassert_denote V (ktrue crt.crt__HelperContracts_hspec6) h.
Proof.
  move=> Hpin. unfold crt.crt__HelperContracts_hspec6, ktrue.
  crt_payload_intro. move=> B HB. crt_payload_intro. move=> A HA.
  crt_payload_intro. move=> Hlo. crt_payload_intro. move=> Hlt.
  crt_payload_intro. move=> Hhi. crt_payload_zguards.
  have Hin : eea_inputs (Wasm_int.Int64.signed A) (Wasm_int.Int64.signed B).
  { unfold eea_inputs. lia. }
  have Hmods : moduli (Wasm_int.Int64.signed A) (Wasm_int.Int64.signed B).
  { unfold moduli. lia. }
  have [Hg [Hga [Hgb _]]] := crt_gcd_Z_source_contract _ _ Hmods.
  eapply crt_payload_imp_eq.
  - crt_payload_eval.
  - crt_payload_eval.
  - crt_payload_word.
  - crt_payload_word.
  -
  move=> Hcop.
  have [Hu [Hrem Hprod]] := crt_inverse_Z_source_contract _ _ Hin Hcop.
  crt_payload_assert.
Qed.

Lemma crt_payload_gcd_characterization V h : val_fun V = crt_model_interp ->
  hassert_denote V (ktrue crt.crt__HelperContracts_hspec2) h.
Proof.
  move=> Hpin. unfold crt.crt__HelperContracts_hspec2, ktrue.
  crt_payload_intro. move=> m Hm. crt_payload_intro. move=> n Hn.
  crt_payload_intro. move=> Hmlo. crt_payload_intro. move=> Hmhi.
  crt_payload_intro. move=> Hnlo. crt_payload_intro. move=> Hnhi. crt_payload_zguards.
  have Hmods : moduli (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n).
  { unfold moduli. lia. }
  have [Hg [Hgm [Hgn [Hrm [Hrn Hgreat]]]]] := crt_gcd_Z_source_contract _ _ Hmods.
  apply hdenote_strictify_Hand_true_intro; first crt_payload_assert.
  apply hdenote_strictify_Hand_true_intro; first crt_payload_assert.
  crt_payload_intro. move=> d Hd.
  crt_payload_intro. move=> Hdlo. crt_payload_intro. move=> Hdhi. crt_payload_zguards.
  eapply crt_payload_short_and; [crt_payload_eval | crt_payload_eval |].
  eapply crt_payload_imp_test; [reflexivity|]. move=> Htest.
  apply andb_true_iff in Htest. destruct Htest as [Hdm Hdn].
  rewrite !crt_contract_eq in Hdm Hdn.
  rewrite (crt_contract_signed_repr (@crt_rem_word (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed d) (crt_contract_signed_word m) ltac:(lia))) in Hdm.
  rewrite (crt_contract_signed_repr (@crt_rem_word (Wasm_int.Int64.signed n) (Wasm_int.Int64.signed d) (crt_contract_signed_word n) ltac:(lia))) in Hdn.
  change ((Z.rem (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed d) =? 0)%Z = true) in Hdm.
  change ((Z.rem (Wasm_int.Int64.signed n) (Wasm_int.Int64.signed d) =? 0)%Z = true) in Hdn.
  apply Z.eqb_eq in Hdm, Hdn.
  have Hgd := Hgreat (Wasm_int.Int64.signed d) ltac:(lia) Hdm Hdn.
  crt_payload_assert.
Qed.

Lemma crt_payload_normalize_correct V h : val_fun V = crt_model_interp ->
  hassert_denote V (ktrue crt.crt__HelperContracts_hspec4) h.
Proof.
  move=> Hpin. unfold crt.crt__HelperContracts_hspec4, ktrue.
  crt_payload_intro. move=> z Hz. crt_payload_intro. move=> d Hd.
  crt_payload_intro. move=> Hlo. crt_payload_intro. move=> Hhi. crt_payload_zguards.
  have Hdw : (1 <= Wasm_int.Int64.signed d <= M)%Z by lia.
  have [Hnorm [Hrange [Hrw Hnw]]] := normalize_proved _ _ (crt_contract_signed_word z) Hdw.
  apply hdenote_strictify_Hand_true_intro; first crt_payload_assert.
  apply hdenote_strictify_Hand_true_intro.
  - eapply crt_payload_imp_rel; [crt_payload_eval | crt_payload_eval |]. move=> Htest.
    rewrite crt_contract_lt (crt_contract_signed_repr Hrw) in Htest.
    change ((Z.rem (Wasm_int.Int64.signed z) (Wasm_int.Int64.signed d) <? 0)%Z = true) in Htest.
    rewrite Htest in Hnorm. crt_payload_assert.
  - eapply crt_payload_imp_rel_false; [crt_payload_eval | crt_payload_eval |]. move=> Htest.
    rewrite crt_contract_lt (crt_contract_signed_repr Hrw) in Htest.
    change ((Z.rem (Wasm_int.Int64.signed z) (Wasm_int.Int64.signed d) <? 0)%Z = false) in Htest.
    rewrite Htest in Hnorm. crt_payload_assert.
Qed.

Print Assumptions crt_payload_inverse_total.
Print Assumptions crt_payload_inverse_correct.
Print Assumptions crt_payload_normalize_correct.
Print Assumptions crt_payload_gcd_characterization.

Theorem crt_helper_payloads V h : val_fun V = crt_model_interp ->
  Forall (fun P => hassert_denote V (ktrue P) h) crt.crt__HelperContracts_specs.
Proof.
  move=> Hpin. repeat constructor.
  - exact: (@crt_helper_gcd_total_payload crt_model_interp crt_model_gcd_total V h Hpin).
  - exact: crt_payload_gcd_characterization Hpin.
  - exact: (@crt_helper_normalize_total_payload crt_model_interp crt_model_normalize_total V h Hpin).
  - exact: crt_payload_normalize_correct Hpin.
  - exact: crt_payload_inverse_total Hpin.
  - exact: crt_payload_inverse_correct Hpin.
Qed.

Theorem crt_public_payloads V h : val_fun V = crt_model_interp ->
  Forall (fun P => hassert_denote V (ktrue P) h) crt.crt__PublicContracts_specs.
Proof.
  move=> Hpin. repeat constructor.
  - exact: (@crt_public_solve_total_payload crt_model_interp crt_model_solve_total V h Hpin).
  - exact: (@crt_public_period_total_payload crt_model_interp crt_model_period_total V h Hpin).
  - exact: crt_payload_solve_validation Hpin.
  - exact: crt_payload_period_contract Hpin.
  - exact: crt_payload_solve_compatibility Hpin.
  - exact: crt_payload_solve_soundness Hpin.
  - exact: crt_payload_canonical_uniqueness Hpin.
  - exact: crt_payload_impossibility Hpin.
  - exact: crt_payload_exists_unique Hpin.
Qed.

Section Host.
Context `{ho : host}.

Theorem crt_helper_contracts_from_realization (rt : module_runtime crt.crt) :
  interp_realized_at rt crt_model_interp ->
  ValidSpec crt.crt crt.crt__HelperContracts_specs.
Proof.
  move=> Hreal. right. exists rt. move=> h.
  exists crt_model_interp. split; [exact Hreal |].
  move=> V Hpin. exact (@crt_helper_payloads V h Hpin).
Qed.

Theorem crt_public_contracts_from_realization (rt : module_runtime crt.crt) :
  interp_realized_at rt crt_model_interp ->
  ValidSpec crt.crt crt.crt__PublicContracts_specs.
Proof.
  move=> Hreal. right. exists rt. move=> h.
  exists crt_model_interp. split; [exact Hreal |].
  move=> V Hpin. exact (@crt_public_payloads V h Hpin).
Qed.

Theorem crt_contracts_from_realization (rt : module_runtime crt.crt) :
  interp_realized_at rt crt_model_interp ->
  ValidSpec crt.crt crt.crt__HelperContracts_specs /\
  ValidSpec crt.crt crt.crt__PublicContracts_specs.
Proof.
  move=> Hreal. split.
  - exact: crt_helper_contracts_from_realization Hreal.
  - exact: crt_public_contracts_from_realization Hreal.
Qed.

End Host.

Print Assumptions crt_helper_payloads.
Print Assumptions crt_helper_contracts_from_realization.
Print Assumptions crt_payload_solve_validation.
Print Assumptions crt_payload_period_contract.
Print Assumptions crt_payload_solve_compatibility.
Print Assumptions crt_payload_solve_soundness.
Print Assumptions crt_payload_canonical_uniqueness.
Print Assumptions crt_payload_impossibility.
Print Assumptions crt_payload_exists_unique.
Print Assumptions crt_public_payloads.
Print Assumptions crt_public_contracts_from_realization.
Print Assumptions crt_contracts_from_realization.
