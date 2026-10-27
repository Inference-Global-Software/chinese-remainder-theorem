(* Fixed-store adaptation of the pinned WasmVerifier MultiExitK and Loop rules.
   ReadOnly store preservation justifies every continuation and backedge. *)
From Coq Require Import ZArith NArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit
 MultiExitK Loop Activation Verifier.
From CRTSystems Require Import ReadOnly SystemRuntime.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Host.
Context `{ho : host}.
Context (mem : meminst).
Lemma system_frame_agrees f : f_inst f = system_inst -> frame_agrees (triv_ctx SM.main) f.
Proof. move=> H. by rewrite /frame_agrees H /system_inst /triv_ctx. Qed.
Lemma system_code_store_preserved hs f vs es hs' s' f' es' :
 all ro_bi es ->
 reduce_trans (hs, system_store mem, f, vn_to_e vs ++ to_e_list es) (hs',s',f',es') ->
 s' = system_store mem.
Proof.
 move=> Hro HR.
 have HE : ro_es (vn_to_e vs ++ to_e_list es).
 { rewrite ro_es_cat ro_es_basic Hro andbT.
   clear - vs hfc memory ho. induction vs; simpl; auto. }
 exact (proj1 (proj2 (ro_reduce_trans_preserved (system_store_readonly (mem:=mem)) HE HR))).
Qed.
Definition system_triple P es Q :=
 forall f, f_inst f = system_inst -> sem_triple_at (system_store mem) f P es Q.
Definition system_mx P es Qn Qr Qb :=
 forall f, f_inst f = system_inst -> sem_mx_at (system_store mem) f P es Qn Qr Qb.
Definition system_mxk (P : assertion) (es : seq basic_instruction)
                   (Qn Qr : assertion) (Qb : nat -> assertion) : Prop :=
  forall hs f V vs h,
    assertion_denote V P (vs, h) -> reifies_sto (system_store mem) f h V -> f_inst f = system_inst ->
    exists s' f' V' vs' h',
      val_rigid V' = val_rigid V /\ reifies_sto s' f' h' V' /\
      ( (reduce_trans (hs, system_store mem, f, vn_to_e vs ++ to_e_list es) (hs, s', f', vn_to_e vs')
         /\ assertion_denote V' Qn (vs', h'))
        \/ (exists (i : nat) (lh : lholed i),
              reduce_trans (hs, system_store mem, f, vn_to_e vs ++ to_e_list es)
                           (hs, s', f', lfill lh (vn_to_e vs' ++ [:: AI_basic BI_return]))
              /\ assertion_denote V' Qr (vs', h'))
        \/ (exists (k d : nat) (lh : lholed d),
              reduce_trans (hs, system_store mem, f, vn_to_e vs ++ to_e_list es)
                 (hs, s', f',
                  lfill lh (vn_to_e vs' ++ [:: AI_basic (BI_br (N.of_nat (d + k)))]))
              /\ assertion_denote V' (Qb k) (vs', h')) ).


Lemma system_mxk_of_pure P es Qn Qr Qb :
 sem_mxk (triv_ctx SM.main) P es Qn Qr Qb -> system_mxk P es Qn Qr Qb.
Proof. move=> H hs f V vs h HP Hr Hi. exact (H hs (system_store mem) f V vs h HP Hr (system_frame_agrees Hi)). Qed.
Lemma system_mxk_lift P es Qn Qr Qb : system_triple P es Qn -> system_mxk P es Qn Qr Qb.
Proof.
 move=> H hs f V vs h HP Hr Hi.
 have [s' [f' [V' [vs' [h' [Hlog [Hred [HQ Hr']]]]]]]] := H f Hi hs V vs h HP Hr.
 exists s', f', V', vs', h'. split; first exact Hlog. split; first exact Hr'. left; by split.
Qed.
Lemma system_mx_of_mxk_pure_normal P es Qn :
 system_mxk P es Qn (AS_base [::] HA_false) (fun _ => AS_base [::] HA_false) ->
 forall Qr Qb, system_mx P es Qn Qr Qb.
Proof.
 move=> H Qr Qb f Hi hs V vs h HP Hr.
 have [s' [f' [V' [vs' [h' [Hlog [Hr' Hd]]]]]]] := H hs f V vs h HP Hr Hi.
 exists s', f', V', vs', h'. split; first exact Hlog. split; first exact Hr'.
 case: Hd => [[Hred HQ]|[[i [lh [Hred HQ]]]|[k [d [lh [Hred HQ]]]]]].
 - left. by split.
 - exfalso. by case: HQ.
 - exfalso. by case: HQ.
Qed.
Lemma system_mxk_conseq P P' es Qn Qn' Qr Qr' (Qb Qb' : nat -> assertion) :
  aentails P P' -> aentails Qn' Qn -> aentails Qr' Qr ->
  (forall k, aentails (Qb' k) (Qb k)) ->
  system_mxk P' es Qn' Qr' Qb' -> system_mxk P es Qn Qr Qb.
Proof.
  move=> HP HQn HQr HQb H hs f V vs h HPd Hr Hagree.
  have HP' := HP V (vs, h) HPd.
  have [s' [f' [V' [vs' [h' [Hlog [Hr' Hd]]]]]]] :=
    H hs f V vs h HP' Hr Hagree.
  exists s', f', V', vs', h'. split; first exact: Hlog. split; first exact: Hr'.
  case: Hd => [[Hred HQ]|[[i [lh [Hred HQ]]]|[k [d [lh [Hred HQ]]]]]].
  - left. split; first exact: Hred. exact: (HQn V' (vs', h') HQ).
  - right; left. exists i, lh. split; first exact: Hred. exact: (HQr V' (vs', h') HQ).
  - right; right. exists k, d, lh. split; first exact: Hred.
    exact: (HQb k V' (vs', h') HQ).
Qed.

(** Sequencing — [return] and any [br k] are absorbing (skip the rest of the block). *)
Lemma system_mxk_seq P Q1 Qn Qr (Qb : nat -> assertion) es1 es2 :
  all ro_bi es1 ->
  system_mxk P es1 Q1 Qr Qb -> system_mxk Q1 es2 Qn Qr Qb ->
  system_mxk P (es1 ++ es2) Qn Qr Qb.
Proof.
  move=> Hro H1 H2 hs f V vs h HP Hr Hagree.
  have [s1 [f1 [V1 [vs1 [h1 [Hlog1 [Hr1 Hd1]]]]]]] :=
    H1 hs f V vs h HP Hr Hagree.
  case: Hd1 => [[Hred1 HQ1]|[[i1 [lh1 [Hred1 HQ1]]]|[k1 [d1 [lh1 [Hred1 HQ1]]]]]].
  - have Hstore := system_code_store_preserved Hro Hred1. subst s1.
    have Hagree1 : f_inst f1 = system_inst.
    { rewrite (reduce_trans_frame_inst Hred1). exact: Hagree. }
    have [s2 [f2 [V2 [vs2 [h2 [Hlog2 [Hr2 Hd2]]]]]]] :=
      H2 hs f1 V1 vs1 h1 HQ1 Hr1 Hagree1.
    have Hs1 := reduce_trans_suffix (to_e_list es2) Hred1.
    exists s2, f2, V2, vs2, h2.
    split; first by rewrite Hlog2 Hlog1. split; first exact: Hr2.
    have Hcompose : forall (X : host_state * store_record * frame * seq administrative_instruction),
        reduce_trans (hs, (system_store mem), f1, vn_to_e vs1 ++ to_e_list es2) X ->
        reduce_trans (hs, system_store mem, f, vn_to_e vs ++ to_e_list (es1 ++ es2)) X.
    { move=> X HX. apply: (rtt_trans (y := (hs, (system_store mem), f1, vn_to_e vs1 ++ to_e_list es2))).
      - rewrite to_e_list_cat catA. exact: Hs1.
      - exact: HX. }
    case: Hd2 => [[Hred2 HQ2]|[[i2 [lh2 [Hred2 HQ2]]]|[k2 [d2 [lh2 [Hred2 HQ2]]]]]].
    + left. by split; [ apply: Hcompose | ].
    + right; left. exists i2, lh2. by split; [ apply: Hcompose | ].
    + right; right. exists k2, d2, lh2. by split; [ apply: Hcompose | ].
  - have Hs1 := reduce_trans_suffix (to_e_list es2) Hred1.
    rewrite lfill_append in Hs1.
    exists s1, f1, V1, vs1, h1.
    split; first exact: Hlog1. split; first exact: Hr1.
    right; left. exists i1, (lh_append lh1 (to_e_list es2)). split; last exact: HQ1.
    rewrite to_e_list_cat catA. exact: Hs1.
  - have Hs1 := reduce_trans_suffix (to_e_list es2) Hred1.
    rewrite lfill_append in Hs1.
    exists s1, f1, V1, vs1, h1.
    split; first exact: Hlog1. split; first exact: Hr1.
    right; right. exists k1, d1, (lh_append lh1 (to_e_list es2)). split; last exact: HQ1.
    rewrite to_e_list_cat catA. exact: Hs1.
Qed.

(** Structured [block] with level-indexed breaks: catches break-0 (→ block normal exit
    [Q], via [br_caught]), sends break-(k+1) to break-k (the [lholed] gains one [LH_rec]
    layer, the [br] index unchanged), and lets [return] pass through. *)
Lemma system_mxk_block S H (es : seq basic_instruction) Q Qr (Qb : nat -> assertion)
                    (bt : block_type) (t1s t2s : seq value_type) :
  expand_ctx (triv_ctx SM.main) bt = Some (Tf t1s t2s) ->
  length S = length t1s ->
  (forall (V' : valuation) (vs' : seq value_num) (h' : aheap),
      assertion_denote V' Q (vs', h') -> length vs' = length t2s) ->
  Qb 0%nat = Q ->
  system_mxk (AS_base S H) es Q Qr Qb ->
  system_mxk (AS_base S H) [:: BI_block bt es] Q Qr (fun j => Qb j.+1).
Proof.
  move=> Hexp Harity Hqlen HQb0 Hbody hs f V vs h HP Hr Hagree.
  move: HP => /= [Hsd Hhd].
  have Hvslen := stack_denote_length Hsd.
  have [s' [f' [V' [vs' [h' [Hlog [Hr' Hd]]]]]]] :=
    Hbody hs f V vs h (conj Hsd Hhd) Hr Hagree.
  exists s', f', V', vs', h'. split; first exact: Hlog. split; first exact: Hr'.
  have Hsz : length (vn_to_e vs) = length t1s by rewrite length_vn_to_e Hvslen Harity.
  have Hentry : reduce_trans (hs, system_store mem, f, vn_to_e vs ++ to_e_list [:: BI_block bt es])
                  (hs, system_store mem, f, [:: AI_label (length t2s) [::] (vn_to_e vs ++ to_e_list es)]).
  { apply: rtt_step1. eapply r_block.
    - rewrite (@expand_frame_agrees (triv_ctx SM.main) f bt (system_frame_agrees Hagree)). exact: Hexp.
    - exact: const_list_vn_to_e.
    - reflexivity.
    - exact: (esym Hsz).
    - reflexivity. }
  case: Hd => [[Hred HQ]|[[i [lh [Hred HQ]]]|[k [d [lh [Hred HQ]]]]]].
  - (* fall through — leave the block normally *)
    left. split; last exact: HQ.
    apply: (rtt_trans Hentry).
    apply: (rtt_trans (y := (hs, s', f', [:: AI_label (length t2s) [::] (vn_to_e vs')]))).
    + have Hlift := reduce_trans_lfill (label_ctx (length t2s))
        (x := (hs, system_store mem, f, vn_to_e vs ++ to_e_list es))
        (y := (hs, s', f', vn_to_e vs')) Hred.
      move: Hlift. by rewrite /cfg_lfill !lfill_label_ctx.
    + apply: rtt_step1. apply: r_simple. apply: rs_label_const.
      exact: const_list_vn_to_e.
  - (* return passes through, picking up the block's label layer *)
    right; left. exists (i.+1), (LH_rec [::] (length t2s) [::] lh [::]).
    split; last exact: HQ.
    apply: (rtt_trans Hentry).
    have Hlift := reduce_trans_lfill (label_ctx (length t2s))
      (x := (hs, system_store mem, f, vn_to_e vs ++ to_e_list es))
      (y := (hs, s', f', lfill lh (vn_to_e vs' ++ [:: AI_basic BI_return]))) Hred.
    move: Hlift. rewrite /cfg_lfill !lfill_label_ctx lfill_LH_rec_nil => Hlift.
    exact: Hlift.
  - (* break at level k *)
    destruct k as [|k'].
    + (* break-0 — caught by this block, exit normally with vs' *)
      left. split; last by rewrite -HQb0.
      apply: (rtt_trans Hentry).
      apply: (rtt_trans (y := (hs, s', f',
                [:: AI_label (length t2s) [::]
                      (lfill lh (vn_to_e vs' ++ [:: AI_basic (BI_br (N.of_nat (d + 0)))]))]))).
      * have Hlift := reduce_trans_lfill (label_ctx (length t2s))
          (x := (hs, system_store mem, f, vn_to_e vs ++ to_e_list es))
          (y := (hs, s', f',
                 lfill lh (vn_to_e vs' ++ [:: AI_basic (BI_br (N.of_nat (d + 0)))]))) Hred.
        move: Hlift. by rewrite /cfg_lfill !lfill_label_ctx.
      * have Hlen' : length vs' = length t2s by apply: (Hqlen V' vs' h'); rewrite -HQb0.
        rewrite addn0.
        have Hc := br_caught [::] lh hs s' f' Hlen'.
        move: Hc. by rewrite cats0.
    + (* break-(k'+1) — passes the block, becoming break-k' *)
      right; right. exists k', (d.+1), (LH_rec [::] (length t2s) [::] lh [::]).
      split; last exact: HQ.
      apply: (rtt_trans Hentry).
      have Hlift := reduce_trans_lfill (label_ctx (length t2s))
        (x := (hs, system_store mem, f, vn_to_e vs ++ to_e_list es))
        (y := (hs, s', f',
               lfill lh (vn_to_e vs' ++ [:: AI_basic (BI_br (N.of_nat (d + k'.+1)))]))) Hred.
      move: Hlift. rewrite /cfg_lfill !lfill_label_ctx lfill_LH_rec_nil.
      by rewrite addSnnS.
Qed.

(** Break posts used inside an [if] branch.  A branch-local [br 0] is caught by
    the branch's implicit block and becomes the conditional's normal result;
    [br (k+1)] escapes that block and is the whole conditional's [br k]. *)
Definition mxk_if_break_post (Qn : assertion) (Qb : nat -> assertion)
    (k : nat) : assertion :=
  match k with
  | 0%nat => Qn
  | k'.+1 => Qb k'
  end.

(** Level-indexed multi-exit [if]/[else].  Both branches may fall through,
    return, break to the branch block, or break past it.  The branch block catches
    level 0 and shifts every successor level down exactly once, yielding [Qb] for
    the conditional as a whole.  [t2s] is arbitrary, so this includes valued
    [if (result ...)] instructions used for short-circuit expressions. *)
Lemma system_mxk_if (cond : term) (H : hassert)
      (Qn Qr : assertion) (Qb : nat -> assertion)
      (tb : block_type) (es1 es2 : seq basic_instruction)
      (t2s : seq value_type) :
  expand_ctx (triv_ctx SM.main) tb = Some (Tf [::] t2s) ->
  (forall V' vs' h',
      assertion_denote V' Qn (vs', h') -> length vs' = length t2s) ->
  system_mxk
    (AS_base [::] (HA_and H (HA_not (term_eq cond i32_zero_term))))
    es1 Qn Qr (mxk_if_break_post Qn Qb) ->
  system_mxk (AS_base [::] (HA_and H (term_eq cond i32_zero_term)))
    es2 Qn Qr (mxk_if_break_post Qn Qb) ->
  system_mxk (AS_base [:: cond] (HA_and (HA_has_type cond T_i32) H))
    [:: BI_if tb es1 es2] Qn Qr Qb.
Proof.
  move=> Hexp Hqlen H1 H2 hs f V vs h HP Hr Hagree.
  move: HP => /= [Hsd [[cv [Econd Tcond]] Hh]].
  have Hvs : vs = [:: cv] by move: Hsd; rewrite /= Econd; case=> <-.
  subst vs.
  have Hb1 :
      system_mxk
        (AS_base [::] (HA_and H (HA_not (term_eq cond i32_zero_term))))
        [:: BI_block tb es1] Qn Qr Qb.
  { apply: (@system_mxk_block [::]
              (HA_and H (HA_not (term_eq cond i32_zero_term)))
              es1 Qn Qr (mxk_if_break_post Qn Qb) tb [::] t2s).
    - exact: Hexp.
    - by [].
    - exact: Hqlen.
    - by [].
    - exact: H1. }
  have Hb2 :
      system_mxk (AS_base [::] (HA_and H (term_eq cond i32_zero_term)))
        [:: BI_block tb es2] Qn Qr Qb.
  { apply: (@system_mxk_block [::]
              (HA_and H (term_eq cond i32_zero_term))
              es2 Qn Qr (mxk_if_break_post Qn Qb) tb [::] t2s).
    - exact: Hexp.
    - by [].
    - exact: Hqlen.
    - by [].
    - exact: H2. }
  destruct cv as [c|c|c|c]; simpl in Tcond; try discriminate Tcond.
  have [Hcz|Hcz] := eqVneq c (Wasm_int.int_zero i32m).
  - (* zero: select the else block with [cond = 0] available *)
    have Hde2 : assertion_denote V
        (AS_base [::] (HA_and H (term_eq cond i32_zero_term))) ([::], h).
    { split => //. split; first exact: Hh.
      rewrite term_eq_denoteE. exists (VAL_int32 (Wasm_int.int_zero i32m)).
      split; last by [].
      by rewrite Econd Hcz. }
    have [s' [f' [V' [vs' [h' [Hlog [Hr' Hd]]]]]]] :=
      Hb2 hs f V [::] h Hde2 Hr Hagree.
    have Hstep :
        reduce_trans
          (hs, system_store mem, f,
            vn_to_e [:: VAL_int32 c] ++ to_e_list [:: BI_if tb es1 es2])
          (hs, system_store mem, f, [:: AI_basic (BI_block tb es2)]).
    { apply: rtt_step1. apply: r_simple. apply: rs_if_false. exact: Hcz. }
    exists s', f', V', vs', h'.
    split; first exact: Hlog. split; first exact: Hr'.
    case: Hd => [[Hred HQ]|[[i [lh [Hred HQ]]]|[k [d [lh [Hred HQ]]]]]].
    + left. split; last exact: HQ. exact: (rtt_trans Hstep Hred).
    + right; left. exists i, lh. split; last exact: HQ.
      exact: (rtt_trans Hstep Hred).
    + right; right. exists k, d, lh. split; last exact: HQ.
      exact: (rtt_trans Hstep Hred).
  - (* nonzero: select the then block with [cond <> 0] available *)
    have Hcc : c <> Wasm_int.int_zero i32m by apply/eqP.
    have Hde1 : assertion_denote V
        (AS_base [::] (HA_and H (HA_not (term_eq cond i32_zero_term))))
        ([::], h).
    { split => //. split; first exact: Hh.
      move=> Hcontra. rewrite term_eq_denoteE Econd in Hcontra.
      case: Hcontra => v [Hv1 Hv2].
      apply: Hcc. move: Hv1 Hv2. rewrite /i32_zero_term /=. congruence. }
    have [s' [f' [V' [vs' [h' [Hlog [Hr' Hd]]]]]]] :=
      Hb1 hs f V [::] h Hde1 Hr Hagree.
    have Hstep :
        reduce_trans
          (hs, system_store mem, f,
            vn_to_e [:: VAL_int32 c] ++ to_e_list [:: BI_if tb es1 es2])
          (hs, system_store mem, f, [:: AI_basic (BI_block tb es1)]).
    { apply: rtt_step1. apply: r_simple. apply: rs_if_true. exact: Hcc. }
    exists s', f', V', vs', h'.
    split; first exact: Hlog. split; first exact: Hr'.
    case: Hd => [[Hred HQ]|[[i [lh [Hred HQ]]]|[k [d [lh [Hred HQ]]]]]].
    + left. split; last exact: HQ. exact: (rtt_trans Hstep Hred).
    + right; left. exists i, lh. split; last exact: HQ.
      exact: (rtt_trans Hstep Hred).
    + right; right. exists k, d, lh. split; last exact: HQ.
      exact: (rtt_trans Hstep Hred).
Qed.

Lemma system_loop_unroll (P Pback Qn Qr : assertion)
    (Qb : nat -> assertion) (body : seq basic_instruction)
    (bt : block_type) (t1s t2s : seq value_type) :
  all ro_bi body ->
  expand_ctx (triv_ctx SM.main) bt = Some (Tf t1s t2s) ->
  (forall V vs h, assertion_denote V P (vs, h) -> length vs = length t1s) ->
  (forall V vs h, assertion_denote V Pback (vs, h) -> length vs = length t1s) ->
  system_mxk P body Qn Qr
    (fun k => if k is k'.+1 then Qb k' else Pback) ->
  system_mxk Pback [:: BI_loop bt body] Qn Qr Qb ->
  system_mxk P [:: BI_loop bt body] Qn Qr Qb.
Proof.
  move=> Hro Hexp Hlen Hlenback Hbody Hcontinue hs f V vs h HI Hr Hagree.
  have Hvslen : length vs = length t1s by apply: (Hlen V vs h).
  (* enter the loop *)
  have Hentry : reduce_trans (hs, system_store mem, f, vn_to_e vs ++ to_e_list [:: BI_loop bt body])
      (hs, system_store mem, f, [:: AI_label (length t1s) [:: AI_basic (BI_loop bt body)]
                       (vn_to_e vs ++ to_e_list body)]).
  { apply: rtt_step1. eapply r_loop.
    - by rewrite (@expand_frame_agrees (triv_ctx SM.main) f bt (system_frame_agrees Hagree)) Hexp.
    - exact: const_list_vn_to_e.
    - by rewrite length_vn_to_e Hvslen.
    - reflexivity.
    - reflexivity. }
  (* run the body *)
  have [s' [f' [V' [vs' [h' [Hlog [Hr' Hd]]]]]]] :=
    Hbody hs f V vs h HI Hr Hagree.
  case: Hd => [[Hred HQ]|[[i [lh [Hred HQ]]]|[k [d [lh [Hred HQ]]]]]].
  - (* body fell through — leave the loop with vs' (the normal exit) *)
    exists s', f', V', vs', h'. split; first exact: Hlog. split; first exact: Hr'.
    left. split; last exact: HQ.
    apply: (rtt_trans Hentry).
    apply: (rtt_trans (y := (hs, s', f',
              [:: AI_label (length t1s) [:: AI_basic (BI_loop bt body)] (vn_to_e vs')]))).
    + have Hlift := reduce_trans_lfill (loop_lh (length t1s) bt body)
        (x := (hs, system_store mem, f, vn_to_e vs ++ to_e_list body))
        (y := (hs, s', f', vn_to_e vs')) Hred.
      move: Hlift. by rewrite /cfg_lfill !lfill_loop_lh.
    + apply: rtt_step1. apply: r_simple. apply: rs_label_const.
      exact: const_list_vn_to_e.
  - (* body returned — the loop's label passes it on as one more context layer *)
    exists s', f', V', vs', h'. split; first exact: Hlog. split; first exact: Hr'.
    right; left.
    exists (i.+1), (LH_rec [::] (length t1s) [:: AI_basic (BI_loop bt body)] lh [::]).
    split; last exact: HQ.
    apply: (rtt_trans Hentry).
    have Hlift := reduce_trans_lfill (loop_lh (length t1s) bt body)
      (x := (hs, system_store mem, f, vn_to_e vs ++ to_e_list body))
      (y := (hs, s', f', lfill lh (vn_to_e vs' ++ [:: AI_basic BI_return]))) Hred.
    move: Hlift. by rewrite /cfg_lfill !lfill_loop_lh /lfill -/lfill !cats0.
  - destruct k as [|k'].
    + (* break-0 — the BACK-EDGE: the loop's own label catches it and re-enters.
         The supplied continuation proves the remaining finite run from
         [Pback]; no termination assumption is introduced by this rule. *)
      have Hstore := system_code_store_preserved Hro Hred. subst s'.
      have HI' : assertion_denote V' Pback (vs', h') := HQ.
      have Hlen' : length vs' = length t1s by apply: (Hlenback V' vs' h').
      have Hagree' : f_inst f' = system_inst.
      { rewrite (reduce_trans_frame_inst Hred). exact: Hagree. }
      have [s'' [f'' [V'' [vs'' [h'' [Hlog2 [Hr2 Hd2]]]]]]] :=
        Hcontinue hs f' V' vs' h' HI' Hr' Hagree'.
      have Hreenter : reduce_trans
          (hs, system_store mem, f, vn_to_e vs ++ to_e_list [:: BI_loop bt body])
          (hs, (system_store mem), f', vn_to_e vs' ++ to_e_list [:: BI_loop bt body]).
      { apply: (rtt_trans Hentry).
        apply: (rtt_trans (y := (hs, (system_store mem), f',
                  [:: AI_label (length t1s) [:: AI_basic (BI_loop bt body)]
                        (lfill lh (vn_to_e vs'
                                     ++ [:: AI_basic (BI_br (N.of_nat (d + 0)))]))]))).
        - have Hlift := reduce_trans_lfill (loop_lh (length t1s) bt body)
            (x := (hs, system_store mem, f, vn_to_e vs ++ to_e_list body))
            (y := (hs, (system_store mem), f',
                   lfill lh (vn_to_e vs'
                               ++ [:: AI_basic (BI_br (N.of_nat (d + 0)))]))) Hred.
          move: Hlift. by rewrite /cfg_lfill !lfill_loop_lh.
        - rewrite addn0.
          exact: (br_caught [:: AI_basic (BI_loop bt body)] lh hs (system_store mem) f' Hlen'). }
      exists s'', f'', V'', vs'', h''.
      split; first by rewrite Hlog2 Hlog. split; first exact: Hr2.
      case: Hd2 => [[Hred2 HQ2]|[[i2 [lh2 [Hred2 HQ2]]]|[k2 [d2 [lh2 [Hred2 HQ2]]]]]].
      * left. split; last exact: HQ2. exact: (rtt_trans Hreenter Hred2).
      * right; left. exists i2, lh2. split; last exact: HQ2.
        exact: (rtt_trans Hreenter Hred2).
      * right; right. exists k2, d2, lh2. split; last exact: HQ2.
        exact: (rtt_trans Hreenter Hred2).
    + (* break-(k'+1) — ESCAPES the loop: the label layer absorbs one level, the
         [br] index is unchanged ([d + k'.+1 = d.+1 + k'], [addSnnS]) *)
      exists s', f', V', vs', h'. split; first exact: Hlog. split; first exact: Hr'.
      right; right.
      exists k', (d.+1), (LH_rec [::] (length t1s) [:: AI_basic (BI_loop bt body)] lh [::]).
      split; last exact: HQ.
      apply: (rtt_trans Hentry).
      have Hlift := reduce_trans_lfill (loop_lh (length t1s) bt body)
        (x := (hs, system_store mem, f, vn_to_e vs ++ to_e_list body))
        (y := (hs, s', f',
               lfill lh (vn_to_e vs' ++ [:: AI_basic (BI_br (N.of_nat (d + k'.+1)))]))) Hred.
      move: Hlift. rewrite /cfg_lfill !lfill_loop_lh /lfill -/lfill !cats0.
      by rewrite addSnnS.
Qed.

Lemma system_triple_of_pure P es Q :
 sem_triple (triv_ctx SM.main) P es Q -> system_triple P es Q.
Proof.
 move=> H f Hi. apply: sem_triple_at_of_triple; first exact H.
 exact: system_frame_agrees.
Qed.
Lemma system_triple_of_mxk P es Q :
 system_mxk P es Q (AS_base [::] HA_false) (fun _ => AS_base [::] HA_false) ->
 system_triple P es Q.
Proof.
 move=> H f Hi hs V vs h HP Hr.
 have [s' [f' [V' [vs' [h' [Hlog [Hr' Hd]]]]]]] := H hs f V vs h HP Hr Hi.
 case: Hd => [[Hred HQ]|[[i [lh [Hred HQ]]]|[k [d [lh [Hred HQ]]]]]].
 - exists s',f',V',vs',h'. split; first exact Hlog. split; first exact Hred. by split.
 - exfalso. by case: HQ.
 - exfalso. by case: HQ.
Qed.
Lemma system_triple_seq P Q1 Q es1 es2 :
 all ro_bi es1 -> system_triple P es1 Q1 -> system_triple Q1 es2 Q ->
 system_triple P (es1++es2) Q.
Proof.
 move=> Hr H1 H2. apply: system_triple_of_mxk.
 apply: (system_mxk_seq (Q1:=Q1)); first exact Hr; apply: system_mxk_lift; assumption.
Qed.
Lemma system_if_const (b : bool) H yes no Qn Qr Qb bt t2s :
 expand_ctx (triv_ctx SM.main) bt = Some (Tf [::] t2s) ->
 (forall V vs h, assertion_denote V Qn (vs,h) -> length vs = length t2s) ->
 system_mxk (AS_base [::] H) (if b then yes else no) Qn Qr (mxk_if_break_post Qn Qb) ->
 system_mxk (AS_base [::T_const (VAL_int32 (wasm_bool b))] H)
 [::BI_if bt yes no] Qn Qr Qb.
Proof.
 move=> Hexp Hlen Hbody hs f V vs h [Hs HH] Hr Hi.
 have Hvs : vs = [::VAL_int32 (wasm_bool b)].
 { move: Hs. cbn. by move=> [<-]. } subst vs.
 have Hb : system_mxk (AS_base [::] H) [::BI_block bt (if b then yes else no)] Qn Qr Qb.
 { apply: (@system_mxk_block [::] H (if b then yes else no) Qn Qr
    (mxk_if_break_post Qn Qb) bt [::] t2s); try assumption; reflexivity. }
 have Hstep : reduce_trans
  (hs, system_store mem,f,vn_to_e [::VAL_int32 (wasm_bool b)] ++ to_e_list [::BI_if bt yes no])
  (hs, system_store mem,f,[::AI_basic (BI_block bt (if b then yes else no))]).
 { apply: rtt_step1. apply: r_simple. destruct b.
   - apply: rs_if_true. by vm_compute.
   - apply: rs_if_false. reflexivity. }
 have [s' [f' [V' [vs' [h' [Hlog [Hr' Hd]]]]]]] := Hb hs f V [::] h (conj Logic.eq_refl HH) Hr Hi.
 exists s',f',V',vs',h'. split; first exact Hlog. split; first exact Hr'.
 case: Hd => [[Hred HQ]|[[i [lh [Hred HQ]]]|[k [d [lh [Hred HQ]]]]]].
 - left. split; last exact HQ. exact: (rtt_trans Hstep Hred).
 - right; left. exists i,lh. split; last exact HQ. exact: (rtt_trans Hstep Hred).
 - right; right. exists k,d,lh. split; last exact HQ. exact: (rtt_trans Hstep Hred).
Qed.
Lemma system_mx_of_mxk_no_break P es Qn Qr Qb :
 system_mxk P es Qn Qr (fun _ => AS_base [::] HA_false) ->
 system_mx P es Qn Qr Qb.
Proof.
 move=> H f Hi hs V vs h HP Hr.
 have [s' [f' [V' [vs' [h' [Hlog [Hr' Hd]]]]]]] := H hs f V vs h HP Hr Hi.
 exists s',f',V',vs',h'. split; first exact Hlog. split; first exact Hr'.
 case: Hd => [[Hred HQ]|[[i [lh [Hred HQ]]]|[k [d [lh [Hred HQ]]]]]].
 - left. by split.
 - right; left. exists i,lh. by split.
 - exfalso. by case: HQ.
Qed.
Lemma system_mxk_of_pure_no_break P es Qn Qr Qb :
 sem_mx (triv_ctx SM.main) P es Qn Qr (AS_base [::] HA_false) ->
 system_mxk P es Qn Qr Qb.
Proof.
 move=> H hs f V vs h HP Hr Hi.
 have [s' [f' [V' [vs' [h' [Hlog [Hr' Hd]]]]]]] := H hs (system_store mem) f V vs h HP Hr (system_frame_agrees Hi).
 exists s',f',V',vs',h'. split; first exact Hlog. split; first exact Hr'.
 case: Hd => [[Hred HQ]|[[i [lh [Hred HQ]]]|[rest [Hred HQ]]]].
 - left. by split.
 - right; left. exists i,lh. by split.
 - exfalso. by case: HQ.
Qed.
End Host.
Print Assumptions system_loop_unroll.
Print Assumptions system_if_const.
