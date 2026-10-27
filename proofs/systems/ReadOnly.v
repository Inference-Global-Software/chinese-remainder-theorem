From Coq Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint ro_bi (b : basic_instruction) : bool :=
  match b with
  | BI_block _ bs | BI_loop _ bs => all ro_bi bs
  | BI_if _ bs cs => all ro_bi bs && all ro_bi cs
  | BI_const_num _ | BI_const_vec _ | BI_ref_null _ | BI_ref_func _
  | BI_unop _ _ | BI_binop _ _ | BI_testop _ _ | BI_relop _ _
  | BI_cvtop _ _ _ _ | BI_drop | BI_select _
  | BI_local_get _ | BI_local_set _ | BI_local_tee _
  | BI_load _ _ _ | BI_nop | BI_unreachable
  | BI_br _ | BI_br_if _ | BI_br_table _ _ | BI_return | BI_call _ => true
  | _ => false
  end.

Section Host.
Context `{ho : host}.

Fixpoint ro_ai (a : administrative_instruction) : bool :=
  match a with
  | AI_basic b => ro_bi b
  | AI_label _ cont body => all ro_ai cont && all ro_ai body
  | AI_frame _ _ body => all ro_ai body
  | AI_return_invoke _ => false
  | _ => true
  end.
Definition ro_es := all ro_ai.

Definition ro_store (s : store_record) : Prop :=
  forall addr fi, lookup_N (s_funcs s) addr = Some fi ->
    match fi with
    | FC_func_native _ _ def => is_true (all ro_bi (modfunc_body def))
    | FC_func_host _ _ => False
    end.

Lemma ro_es_cat xs ys : ro_es (xs ++ ys) = (ro_es xs && ro_es ys).
Proof. exact: all_cat. Qed.

Lemma ro_es_subseq pre es post : ro_es (pre ++ es ++ post) -> ro_es es.
Proof. rewrite !ro_es_cat. by move/andP=> [_ /andP [H _]]. Qed.

Lemma ro_es_values vs : ro_es (v_to_e_list vs).
Proof.
  elim: vs => [|v vs IH] //=.
  destruct v as [v|v|r]; simpl; try exact IH.
  destruct r; exact IH.
Qed.

Lemma ro_es_basic bs : ro_es (to_e_list bs) = all ro_bi bs.
Proof. by elim: bs => [|b bs IH] //=; rewrite IH. Qed.

Lemma ro_lfill_extract k (lh : lholed k) es :
  ro_es (lfill lh es) -> ro_es es.
Proof.
  induction lh; simpl; rewrite !ro_es_cat ro_es_values /=.
  - by move/andP => [H _].
  - by move/andP => [/andP [_ H] _]; apply IHlh.
Qed.

Lemma ro_lfill_replace k (lh : lholed k) es es' :
  ro_es (lfill lh es) -> ro_es es' -> ro_es (lfill lh es').
Proof.
  induction lh; simpl; rewrite !ro_es_cat ro_es_values /=.
  - move/andP => [_ Htail] Hnew. by apply/andP.
  - move/andP => [/andP [Hcont Hbody] Htail] Hnew.
    apply/andP; split; last exact Htail.
    apply/andP; split; first exact Hcont.
    exact: IHlh Hbody Hnew.
Qed.

Lemma ro_ai_value v : ro_ai (v_to_e v).
Proof. destruct v as [v|v|r]; try reflexivity. destruct r; reflexivity. Qed.

Lemma ro_es_const vs : const_list vs -> ro_es vs.
Proof. move=> /const_es_exists [vs' ->]. exact: ro_es_values. Qed.

Lemma ro_simple_preserved es es' : reduce_simple es es' -> ro_es es -> ro_es es'.
Proof.
  intros HR. destruct HR; simpl; intros Hro;
    try reflexivity; try exact: ro_es_const;
    try exact: ro_es_values.
  all: try solve [change (ro_ai (v_to_e _) && true); rewrite ro_ai_value].
  all: try solve [move: Hro; rewrite /ro_es /=; move/andP=> [/andP [? ?] _]; assumption].
  all: try solve [move: Hro; rewrite /ro_es /= !andbT; move/andP=> [? ?]; assumption].
  all: try solve [rewrite /ro_es /= !ro_ai_value].
  - rewrite ro_es_cat (ro_es_const H) /=.
    move/andP: Hro => [/andP [Hes _] _]. exact Hes.
  - destruct v as [v|v|r]; try reflexivity. destruct r; reflexivity.
Qed.

Lemma ro_reduce_preserved hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  ro_store s -> ro_es es -> hs' = hs /\ s' = s /\ ro_es es'.
Proof.
  intros HR. induction HR; intros Hstore Hro; subst;
    try solve [split; [reflexivity|]; split; [reflexivity|];
      first [reflexivity | exact: ro_simple_preserved Hro |
        rewrite /ro_es /= ro_ai_value; reflexivity]].
  all: try solve [move: Hro; rewrite ?ro_es_cat /ro_es /= ?andbF; discriminate].
  all: try solve [exfalso; exact: Hstore H].
  - have Hbs : all ro_bi es.
    { move: Hro; rewrite ro_es_cat /ro_es /= !andbT; by move/andP=> [_ Hb]. }
    split; [reflexivity|]; split; [reflexivity|].
    change (ro_es (vs ++ to_e_list es) && true).
    by rewrite andbT ro_es_cat ro_es_basic (ro_es_const H0) Hbs.
  - have Hbs : all ro_bi es.
    { move: Hro; rewrite ro_es_cat /ro_es /= !andbT; by move/andP=> [_ Hb]. }
    split; [reflexivity|]; split; [reflexivity|].
    change ((all ro_bi es && true) && ro_es (vs ++ to_e_list es) && true).
    by rewrite !andbT ro_es_cat ro_es_basic (ro_es_const H0) Hbs.
  - have Hbs : all ro_bi es := Hstore _ _ H.
    split; [reflexivity|]; split; [reflexivity|].
    change ((ro_es (to_e_list es) && true) && true).
    by rewrite !andbT ro_es_basic Hbs.
  - split; [reflexivity|]; split; [reflexivity|].
    by rewrite ro_es_cat (ro_es_const H3) /ro_es /=.
  - have Hin := ro_lfill_extract Hro.
    destruct (IHHR Hstore Hin) as [-> [-> Hout]].
    split; [reflexivity|]; split; [reflexivity|].
    exact: ro_lfill_replace Hro Hout.
  - have Hin : ro_es es.
    { move: Hro. by rewrite /ro_es /= andbT. }
    destruct (IHHR Hstore Hin) as [-> [-> Hout]].
    split; [reflexivity|]; split; [reflexivity|].
    change (ro_es es' && true). by rewrite Hout.
Qed.

(* The invariant must be retained at every intermediate configuration. *)
Theorem ro_reduce_trans_preserved hs s f es hs' s' f' es' :
  ro_store s -> ro_es es ->
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  hs' = hs /\ s' = s /\ ro_es es'.
Proof.
  intros HP HE HR.
  have Hgeneral : forall x y, reduce_trans x y ->
    let '(h0, s0, _, e0) := x in
    let '(h1, s1, _, e1) := y in
    ro_store s0 -> ro_es e0 -> h1 = h0 /\ s1 = s0 /\ ro_es e1.
  { intros x y H. induction H.
    - destruct x as [[[h0 s0] f0] e0], y as [[[h1 s1] f1] e1].
      exact (ro_reduce_preserved H).
    - destruct x as [[[h0 s0] f0] e0]. auto.
    - destruct x as [[[h0 s0] f0] e0], y as [[[h1 s1] f1] e1],
        z as [[[h2 s2] f2] e2].
      intros HS HE0. destruct (IHclos_refl_trans1 HS HE0) as [-> [-> HE1]].
      exact (IHclos_refl_trans2 HS HE1). }
  exact (Hgeneral _ _ HR HP HE).
Qed.

End Host.
