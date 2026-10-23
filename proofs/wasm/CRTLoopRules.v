(* One-step loop unfolding over real WasmCert reductions.  This form lets a
   separately proved finite mathematical run supply the recursive continuation.
   The reduction proof follows WasmVerifier.Loop.sem_loopk; it introduces no
   execution assumptions and its continuation premise must itself be proved. *)
From Coq Require Import ZArith NArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit
  MultiExitK Loop.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Host.
Context `{ho : host}.

Lemma crt_loop_unroll (G : context) (P Pback Qn Qr : assertion)
    (Qb : nat -> assertion) (body : seq basic_instruction)
    (bt : block_type) (t1s t2s : seq value_type) :
  expand_ctx G bt = Some (Tf t1s t2s) ->
  (forall V vs h, assertion_denote V P (vs, h) -> length vs = length t1s) ->
  (forall V vs h, assertion_denote V Pback (vs, h) -> length vs = length t1s) ->
  sem_mxk G P body Qn Qr
    (fun k => if k is k'.+1 then Qb k' else Pback) ->
  sem_mxk G Pback [:: BI_loop bt body] Qn Qr Qb ->
  sem_mxk G P [:: BI_loop bt body] Qn Qr Qb.
Proof.
  move=> Hexp Hlen Hlenback Hbody Hcontinue hs s f V vs h HI Hr Hagree.
  have Hvslen : length vs = length t1s by apply: (Hlen V vs h).
  (* enter the loop *)
  have Hentry : reduce_trans (hs, s, f, vn_to_e vs ++ to_e_list [:: BI_loop bt body])
      (hs, s, f, [:: AI_label (length t1s) [:: AI_basic (BI_loop bt body)]
                       (vn_to_e vs ++ to_e_list body)]).
  { apply: rtt_step1. eapply r_loop.
    - by rewrite (@expand_frame_agrees G f bt Hagree) Hexp.
    - exact: const_list_vn_to_e.
    - by rewrite length_vn_to_e Hvslen.
    - reflexivity.
    - reflexivity. }
  (* run the body *)
  have [s' [f' [V' [vs' [h' [Hlog [Hr' Hd]]]]]]] :=
    Hbody hs s f V vs h HI Hr Hagree.
  case: Hd => [[Hred HQ]|[[i [lh [Hred HQ]]]|[k [d [lh [Hred HQ]]]]]].
  - (* body fell through — leave the loop with vs' (the normal exit) *)
    exists s', f', V', vs', h'. split; first exact: Hlog. split; first exact: Hr'.
    left. split; last exact: HQ.
    apply: (rtt_trans Hentry).
    apply: (rtt_trans (y := (hs, s', f',
              [:: AI_label (length t1s) [:: AI_basic (BI_loop bt body)] (vn_to_e vs')]))).
    + have Hlift := reduce_trans_lfill (loop_lh (length t1s) bt body)
        (x := (hs, s, f, vn_to_e vs ++ to_e_list body))
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
      (x := (hs, s, f, vn_to_e vs ++ to_e_list body))
      (y := (hs, s', f', lfill lh (vn_to_e vs' ++ [:: AI_basic BI_return]))) Hred.
    move: Hlift. by rewrite /cfg_lfill !lfill_loop_lh /lfill -/lfill !cats0.
  - destruct k as [|k'].
    + (* break-0 — the BACK-EDGE: the loop's own label catches it and re-enters.
         The supplied continuation proves the remaining finite run from
         [Pback]; no termination assumption is introduced by this rule. *)
      have HI' : assertion_denote V' Pback (vs', h') := HQ.
      have Hlen' : length vs' = length t1s by apply: (Hlenback V' vs' h').
      have Hagree' : frame_agrees G f'.
      { rewrite /frame_agrees (reduce_trans_frame_inst Hred). exact: Hagree. }
      have [s'' [f'' [V'' [vs'' [h'' [Hlog2 [Hr2 Hd2]]]]]]] :=
        Hcontinue hs s' f' V' vs' h' HI' Hr' Hagree'.
      have Hreenter : reduce_trans
          (hs, s, f, vn_to_e vs ++ to_e_list [:: BI_loop bt body])
          (hs, s', f', vn_to_e vs' ++ to_e_list [:: BI_loop bt body]).
      { apply: (rtt_trans Hentry).
        apply: (rtt_trans (y := (hs, s', f',
                  [:: AI_label (length t1s) [:: AI_basic (BI_loop bt body)]
                        (lfill lh (vn_to_e vs'
                                     ++ [:: AI_basic (BI_br (N.of_nat (d + 0)))]))]))).
        - have Hlift := reduce_trans_lfill (loop_lh (length t1s) bt body)
            (x := (hs, s, f, vn_to_e vs ++ to_e_list body))
            (y := (hs, s', f',
                   lfill lh (vn_to_e vs'
                               ++ [:: AI_basic (BI_br (N.of_nat (d + 0)))]))) Hred.
          move: Hlift. by rewrite /cfg_lfill !lfill_loop_lh.
        - rewrite addn0.
          exact: (br_caught [:: AI_basic (BI_loop bt body)] lh hs s' f' Hlen'). }
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
        (x := (hs, s, f, vn_to_e vs ++ to_e_list body))
        (y := (hs, s', f',
               lfill lh (vn_to_e vs' ++ [:: AI_basic (BI_br (N.of_nat (d + k'.+1)))]))) Hred.
      move: Hlift. rewrite /cfg_lfill !lfill_loop_lh /lfill -/lfill !cats0.
      by rewrite addSnnS.
Qed.

End Host.
Print Assumptions crt_loop_unroll.
