(* Real semantics for the exact scratch-local overflow checks emitted in
   any three distinct scratch registers. The multiplication guard argument generalizes the checked
   WasmVerifier Issue316OverflowExample proof over its preserved local frame. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit
  NumericDischarge Automation Activation Verifier MultiExitK Loop.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTLoops.
From CRTGenerated Require Import main.
From CRTWasm Require Import CRTExecution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Section Host.
Context `{ho : host}.
Context (ia ib ir : N).
Context (IndexAB : ib <> ia) (IndexAR : ia <> ir) (IndexBR : ib <> ir).
Lemma crt_general_mul_inner G H (ca cb : i64) :
  pinned ia (VAL_int64 ca) H ->
  pinned ib (VAL_int64 cb) H ->
  pinned ir (VAL_int64 (Wasm_int.Int64.mul ca cb)) H ->
  (Wasm_int.Int64.min_signed <=
     Wasm_int.Int64.signed ca * Wasm_int.Int64.signed cb <=
     Wasm_int.Int64.max_signed)%Z ->
  Wasm_int.Int64.signed cb <> 0%Z ->
  sem_triple G
    (AS_base [::] H)
    [:: BI_local_get ib; BI_const_num (Issue316OverflowExample.Vi64 (-1));
        BI_relop T_i64 (Relop_i ROI_eq);
        BI_if (BT_valtype None)
          [:: BI_local_get ia;
              BI_const_num (Issue316OverflowExample.Vi64 (-9223372036854775808));
              BI_relop T_i64 (Relop_i ROI_eq);
              BI_if (BT_valtype None) [:: BI_unreachable] [::]]
          [:: BI_local_get ir; BI_local_get ib;
              BI_binop T_i64 (Binop_i (BOI_div SX_S));
              BI_local_get ia; BI_relop T_i64 (Relop_i ROI_ne);
              BI_if (BT_valtype None) [:: BI_unreachable] [::]]]
    (AS_base [::] H).
Proof.
  move=> PinA PinB PinR Hrange Hnz.
  apply: (sem_seq
            (es1 := [:: BI_local_get ib; BI_const_num (Issue316OverflowExample.Vi64 (-1));
                        BI_relop T_i64 (Relop_i ROI_eq)])
            (es2 := [:: BI_if (BT_valtype None)
                          [:: BI_local_get ia;
                              BI_const_num (Issue316OverflowExample.Vi64 (-9223372036854775808));
                              BI_relop T_i64 (Relop_i ROI_eq);
                              BI_if (BT_valtype None) [:: BI_unreachable] [::]]
                          [:: BI_local_get ir; BI_local_get ib;
                              BI_binop T_i64 (Binop_i (BOI_div SX_S));
                              BI_local_get ia;
                              BI_relop T_i64 (Relop_i ROI_ne);
                              BI_if (BT_valtype None)
                                [:: BI_unreachable] [::]]])
            (Q := AS_base [:: T_const (VAL_int32 (wasm_bool
                     (app_relop (Relop_i ROI_eq) (VAL_int64 cb) (Issue316OverflowExample.Vi64 (-1)))))]
                    H)).
  { apply: test_pin_const; by [ apply: PinB | vm_compute ]. }
  case: (Z.eq_dec (Wasm_int.Int64.signed cb) (-1)) => [Hm|Hm].
  - have Hcb : cb = Wasm_int.Int64.repr (-1).
    { by rewrite -[cb]Wasm_int.Int64.repr_signed Hm. }
    have Htest : app_relop (Relop_i ROI_eq) (VAL_int64 cb) (Issue316OverflowExample.Vi64 (-1)) = true.
    { rewrite Vi64_mone -Hcb i64_eq_app. exact: Wasm_int.Int64.eq_true. }
    rewrite Htest.
    have Hane : Wasm_int.Int64.signed ca <> Wasm_int.Int64.min_signed.
    { move: Hrange. rewrite Hm i64_min_signed_val i64_max_signed_val. lia. }
    apply: guard_if_true.
    apply: (sem_seq
              (es1 := [:: BI_local_get ia;
                          BI_const_num (Issue316OverflowExample.Vi64 (-9223372036854775808));
                          BI_relop T_i64 (Relop_i ROI_eq)])
              (es2 := [:: BI_if (BT_valtype None) [:: BI_unreachable] [::]])
              (Q := AS_base [:: T_const (VAL_int32 (wasm_bool
                       (app_relop (Relop_i ROI_eq) (VAL_int64 ca)
                          (Issue316OverflowExample.Vi64 (-9223372036854775808)))))] H)).
    { apply: test_pin_const; by [ apply: PinA | vm_compute ]. }
    have Hmin : app_relop (Relop_i ROI_eq) (VAL_int64 ca)
                  (Issue316OverflowExample.Vi64 (-9223372036854775808)) = false.
    { rewrite Vi64_min. exact: (i64_min_signed_eq_false Hane). }
    rewrite Hmin. apply: guard_if_false. exact: sem_nil_same.
  - have Hcb : cb <> Wasm_int.Int64.repr (-1).
    { move=> Hbad. apply: Hm. by rewrite Hbad i64_signed_mone. }
    have Htest : app_relop (Relop_i ROI_eq) (VAL_int64 cb) (Issue316OverflowExample.Vi64 (-1)) = false.
    { rewrite Vi64_mone i64_eq_app.
      exact: (Wasm_int.Int64.eq_false cb (Wasm_int.Int64.repr (-1)) Hcb). }
    rewrite Htest.
    apply: guard_if_false.
    apply: (sem_seq
              (es1 := [:: BI_local_get ir; BI_local_get ib;
                          BI_binop T_i64 (Binop_i (BOI_div SX_S));
                          BI_local_get ia; BI_relop T_i64 (Relop_i ROI_ne)])
              (es2 := [:: BI_if (BT_valtype None) [:: BI_unreachable] [::]])
              (Q := AS_base [:: T_const (VAL_int32 (wasm_bool
                       (app_relop (Relop_i ROI_ne) (VAL_int64 ca)
                          (VAL_int64 ca))))] H)).
    { apply: (sem_seq
                (es1 := [:: BI_local_get ir])
                (es2 := [:: BI_local_get ib;
                            BI_binop T_i64 (Binop_i (BOI_div SX_S));
                            BI_local_get ia;
                            BI_relop T_i64 (Relop_i ROI_ne)])
                (Q := AS_base
                        [:: T_const (VAL_int64 (Wasm_int.Int64.mul ca cb))]
                        H)).
      - apply: (get_pinned_frame (Sf := [::])). exact: PinR.
      - apply: (sem_seq
                  (es1 := [:: BI_local_get ib])
                  (es2 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S));
                              BI_local_get ia;
                              BI_relop T_i64 (Relop_i ROI_ne)])
                  (Q := AS_base
                          [:: T_const (VAL_int64 (Wasm_int.Int64.mul ca cb));
                              T_const (VAL_int64 cb)] H)).
        + apply: (get_pinned_frame
                    (Sf := [:: T_const (VAL_int64 (Wasm_int.Int64.mul ca cb))])).
          exact: PinB.
        + apply: (sem_seq
                    (es1 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))])
                    (es2 := [:: BI_local_get ia;
                                BI_relop T_i64 (Relop_i ROI_ne)])
                    (Q := AS_base [:: T_const (VAL_int64 ca)] H)).
          * apply: binop_consts;
              [ by vm_compute | by [] | by []
              | exact: (i64_mul_div_s_roundtrip Hnz Hrange) ].
          * apply: (sem_seq
                      (es1 := [:: BI_local_get ia])
                      (es2 := [:: BI_relop T_i64 (Relop_i ROI_ne)])
                      (Q := AS_base [:: T_const (VAL_int64 ca);
                                        T_const (VAL_int64 ca)]
                              H)).
            -- apply: (get_pinned_frame (Sf := [:: T_const (VAL_int64 ca)])).
               exact: PinA.
            -- apply: relop_consts; by vm_compute. }
    rewrite i64_ne_self_false. apply: guard_if_false. exact: sem_nil_same.
Qed.

(** The guard itself.  [b = 0] skips it outright -- the product is zero and
    nothing can have overflowed -- and [b <> 0] enters the arms above. *)
Lemma crt_general_mul_guard G H (ca cb : i64) :
  pinned ia (VAL_int64 ca) H ->
  pinned ib (VAL_int64 cb) H ->
  pinned ir (VAL_int64 (Wasm_int.Int64.mul ca cb)) H ->
  (Wasm_int.Int64.min_signed <=
     Wasm_int.Int64.signed ca * Wasm_int.Int64.signed cb <=
     Wasm_int.Int64.max_signed)%Z ->
  sem_triple G
    (AS_base [::] H)
    [:: BI_local_get ib; BI_const_num (Issue316OverflowExample.Vi64 0);
        BI_relop T_i64 (Relop_i ROI_ne);
        BI_if (BT_valtype None)
          [:: BI_local_get ib; BI_const_num (Issue316OverflowExample.Vi64 (-1));
              BI_relop T_i64 (Relop_i ROI_eq);
              BI_if (BT_valtype None)
                [:: BI_local_get ia;
                    BI_const_num (Issue316OverflowExample.Vi64 (-9223372036854775808));
                    BI_relop T_i64 (Relop_i ROI_eq);
                    BI_if (BT_valtype None) [:: BI_unreachable] [::]]
                [:: BI_local_get ir; BI_local_get ib;
                    BI_binop T_i64 (Binop_i (BOI_div SX_S));
                    BI_local_get ia; BI_relop T_i64 (Relop_i ROI_ne);
                    BI_if (BT_valtype None) [:: BI_unreachable] [::]]]
          [::]]
    (AS_base [::] H).
Proof.
  move=> PinA PinB PinR Hrange.
  apply: (sem_seq
            (es1 := [:: BI_local_get ib; BI_const_num (Issue316OverflowExample.Vi64 0);
                        BI_relop T_i64 (Relop_i ROI_ne)])
            (es2 := [:: BI_if (BT_valtype None)
                          [:: BI_local_get ib; BI_const_num (Issue316OverflowExample.Vi64 (-1));
                              BI_relop T_i64 (Relop_i ROI_eq);
                              BI_if (BT_valtype None)
                                [:: BI_local_get ia;
                                    BI_const_num
                                      (Issue316OverflowExample.Vi64 (-9223372036854775808));
                                    BI_relop T_i64 (Relop_i ROI_eq);
                                    BI_if (BT_valtype None)
                                      [:: BI_unreachable] [::]]
                                [:: BI_local_get ir; BI_local_get ib;
                                    BI_binop T_i64 (Binop_i (BOI_div SX_S));
                                    BI_local_get ia;
                                    BI_relop T_i64 (Relop_i ROI_ne);
                                    BI_if (BT_valtype None)
                                      [:: BI_unreachable] [::]]]
                          [::]])
            (Q := AS_base [:: T_const (VAL_int32 (wasm_bool
                     (app_relop (Relop_i ROI_ne) (VAL_int64 cb) (Issue316OverflowExample.Vi64 0))))]
                    H)).
  { apply: test_pin_const; by [ apply: PinB | vm_compute ]. }
  case: (Z.eq_dec (Wasm_int.Int64.signed cb) 0) => [Hz|Hnz].
  - have Hcb : cb = Wasm_int.Int64.zero
      by apply: (proj1 (i64_signed_zero_iff cb)).
    have Htest : app_relop (Relop_i ROI_ne) (VAL_int64 cb) (Issue316OverflowExample.Vi64 0) = false.
    { rewrite Vi64_zero -Hcb. exact: i64_ne_self_false. }
    rewrite Htest. apply: guard_if_false. exact: sem_nil_same.
  - have Hcbz : cb <> Wasm_int.Int64.zero.
    { move=> Hbad. apply: Hnz. by apply: (proj2 (i64_signed_zero_iff cb)). }
    have Htest : app_relop (Relop_i ROI_ne) (VAL_int64 cb) (Issue316OverflowExample.Vi64 0) = true.
    { rewrite Vi64_zero i64_ne_app.
      by rewrite (Wasm_int.Int64.eq_false cb Wasm_int.Int64.zero Hcbz). }
    rewrite Htest. apply: guard_if_true. exact: (crt_general_mul_inner PinA PinB PinR Hrange Hnz).
Qed.


Ltac pinned_tac :=
  solve [ exact: pinned_bare | apply: pinned_left; pinned_tac
        | apply: pinned_right; pinned_tac ].
Ltac present_tac :=
  solve [ exact: loc_present_defined | exact: loc_present_pin
        | apply: loc_present_left; present_tac
        | apply: loc_present_right; present_tac ].
Local Notation ArithB H cb :=
  (HA_and (term_eq (T_local ib) (T_const (VAL_int64 cb))) H).
Local Notation ArithA H ca cb :=
  (HA_and (term_eq (T_local ia) (T_const (VAL_int64 ca))) (ArithB H cb)).
Local Notation ArithR H ca cb cr :=
  (HA_and (term_eq (T_local ir) (T_const (VAL_int64 cr))) (ArithA H ca cb)).

Definition crt_general_mul_guard_code : seq basic_instruction :=
  [:: BI_local_get ib; BI_const_num (Issue316OverflowExample.Vi64 0);
        BI_relop T_i64 (Relop_i ROI_ne);
        BI_if (BT_valtype None)
          [:: BI_local_get ib; BI_const_num (Issue316OverflowExample.Vi64 (-1));
              BI_relop T_i64 (Relop_i ROI_eq);
              BI_if (BT_valtype None)
                [:: BI_local_get ia;
                    BI_const_num (Issue316OverflowExample.Vi64 (-9223372036854775808));
                    BI_relop T_i64 (Relop_i ROI_eq);
                    BI_if (BT_valtype None) [:: BI_unreachable] [::]]
                [:: BI_local_get ir; BI_local_get ib;
                    BI_binop T_i64 (Binop_i (BOI_div SX_S));
                    BI_local_get ia; BI_relop T_i64 (Relop_i ROI_ne);
                    BI_if (BT_valtype None) [:: BI_unreachable] [::]]]
          [::]].
Definition crt_general_checked_mul_code : seq basic_instruction :=
  [:: BI_local_set ib; BI_local_tee ia; BI_local_get ib;
      BI_binop T_i64 (Binop_i BOI_mul); BI_local_set ir] ++
  crt_general_mul_guard_code ++ [:: BI_local_get ir].

Lemma crt_general_checked_mul_sem G H (ca cb : i64) :
  loc_stable ia (VAL_int64 ca) H ->
  loc_stable ib (VAL_int64 cb) H ->
  loc_stable ir (VAL_int64 (Wasm_int.Int64.mul ca cb)) H ->
  loc_present ia H -> loc_present ib H -> loc_present ir H ->
  (Wasm_int.Int64.min_signed <=
     Wasm_int.Int64.signed ca * Wasm_int.Int64.signed cb <=
     Wasm_int.Int64.max_signed)%Z ->
  sem_triple G (AS_base [:: T_const (VAL_int64 ca); T_const (VAL_int64 cb)] H)
    crt_general_checked_mul_code
    (AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.mul ca cb))] H).
Proof.
  move=> StA StB StR PrA PrB PrR Hrange.
  rewrite /crt_general_checked_mul_code.
  apply: (sem_seq (es1 := [:: BI_local_set ib])
    (Q := AS_base [:: T_const (VAL_int64 ca)] (ArithB H cb))).
  { apply: (sem_frame_consts (vf := [:: VAL_int64 ca])).
    exact: (sem_local_set_const_frame StB PrB). }
  apply: (sem_seq (es1 := [:: BI_local_tee ia])
    (Q := AS_base [:: T_const (VAL_int64 ca)] (ArithA H ca cb))).
  { apply: sem_local_tee_const_frame.
    - apply: loc_stable_and; [by apply: loc_stable_pin_other | exact StA].
    - apply: loc_present_right. exact PrA. }
  apply: (sem_seq (es1 := [:: BI_local_get ib])
    (Q := AS_base [:: T_const (VAL_int64 ca); T_const (VAL_int64 cb)] (ArithA H ca cb))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i BOI_mul)])
    (Q := AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.mul ca cb))] (ArithA H ca cb))).
  { apply: binop_consts; [by vm_compute | by [] | by [] | exact: i64_mul_some]. }
  apply: (sem_seq (es1 := [:: BI_local_set ir])
    (Q := AS_base [::] (ArithR H ca cb (Wasm_int.Int64.mul ca cb)))).
  { apply: sem_local_set_const_frame.
    - apply: loc_stable_and; first by apply: loc_stable_pin_other.
      apply: loc_stable_and; first by apply: loc_stable_pin_other. exact StR.
    - apply: loc_present_right. apply: loc_present_right. exact PrR. }
  apply: (sem_seq (es1 := crt_general_mul_guard_code)
    (Q := AS_base [::] (ArithR H ca cb (Wasm_int.Int64.mul ca cb)))).
  { apply: crt_general_mul_guard; [pinned_tac | pinned_tac | pinned_tac | exact Hrange]. }
  apply: (sem_conseq
    (P' := AS_base [::] (ArithR H ca cb (Wasm_int.Int64.mul ca cb)))
    (Q' := AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.mul ca cb))]
      (ArithR H ca cb (Wasm_int.Int64.mul ca cb)))).
  - by [].
  - move=> V [vs h] [Hs [_ [_ [_ HH]]]]. by split.
  - apply: get_pinned_frame. pinned_tac.
Qed.

Definition crt_general_checked_sub_code : seq basic_instruction :=
  [:: BI_local_set ib; BI_local_tee ia; BI_local_get ib;
      BI_binop T_i64 (Binop_i BOI_sub); BI_local_tee ir;
      BI_local_get ia; BI_relop T_i64 (Relop_i (ROI_lt SX_S));
      BI_local_get ib; BI_const_num (Issue316OverflowExample.Vi64 0);
      BI_relop T_i64 (Relop_i (ROI_gt SX_S)); BI_relop T_i32 (Relop_i ROI_ne);
      BI_if (BT_valtype None) [:: BI_unreachable] [::]; BI_local_get ir].
Lemma crt_general_checked_sub_sem G H (ca cb : i64) :
  loc_stable ia (VAL_int64 ca) H ->
  loc_stable ib (VAL_int64 cb) H ->
  loc_stable ir (VAL_int64 (Wasm_int.Int64.sub ca cb)) H ->
  loc_present ia H -> loc_present ib H -> loc_present ir H ->
  (Wasm_int.Int64.min_signed <=
     Wasm_int.Int64.signed ca - Wasm_int.Int64.signed cb <=
     Wasm_int.Int64.max_signed)%Z ->
  sem_triple G (AS_base [:: T_const (VAL_int64 ca); T_const (VAL_int64 cb)] H)
    crt_general_checked_sub_code
    (AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.sub ca cb))] H).
Proof.
  move=> StA StB StR PrA PrB PrR Hrange.
  rewrite /crt_general_checked_sub_code.
  apply: (sem_seq (es1 := [:: BI_local_set ib])
    (Q := AS_base [:: T_const (VAL_int64 ca)] (ArithB H cb))).
  { apply: (sem_frame_consts (vf := [:: VAL_int64 ca])).
    exact: (sem_local_set_const_frame StB PrB). }
  apply: (sem_seq (es1 := [:: BI_local_tee ia])
    (Q := AS_base [:: T_const (VAL_int64 ca)] (ArithA H ca cb))).
  { apply: sem_local_tee_const_frame.
    - apply: loc_stable_and; [by apply: loc_stable_pin_other | exact StA].
    - apply: loc_present_right. exact PrA. }
  apply: (sem_seq (es1 := [:: BI_local_get ib])
    (Q := AS_base [:: T_const (VAL_int64 ca); T_const (VAL_int64 cb)] (ArithA H ca cb))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i BOI_sub)])
    (Q := AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.sub ca cb))] (ArithA H ca cb))).
  { apply: binop_consts; [by vm_compute | by [] | by [] | exact: i64_sub_some]. }
  apply: (sem_seq (es1 := [:: BI_local_tee ir])
    (Q := AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.sub ca cb))]
      (ArithR H ca cb (Wasm_int.Int64.sub ca cb)))).
  { apply: sem_local_tee_const_frame.
    - apply: loc_stable_and; first by apply: loc_stable_pin_other.
      apply: loc_stable_and; first by apply: loc_stable_pin_other. exact StR.
    - apply: loc_present_right. apply: loc_present_right. exact PrR. }
  apply: (sem_seq (es1 := [:: BI_local_get ia])
    (Q := AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.sub ca cb)); T_const (VAL_int64 ca)] (ArithR H ca cb (Wasm_int.Int64.sub ca cb)))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_relop T_i64 (Relop_i (ROI_lt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.sub ca cb)) (VAL_int64 ca))))] (ArithR H ca cb (Wasm_int.Int64.sub ca cb)))).
  { apply: relop_consts; by []. }
  apply: (sem_seq (es1 := [:: BI_local_get ib])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.sub ca cb)) (VAL_int64 ca)))); T_const (VAL_int64 cb)] (ArithR H ca cb (Wasm_int.Int64.sub ca cb)))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_const_num (Issue316OverflowExample.Vi64 0)])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.sub ca cb)) (VAL_int64 ca)))); T_const (VAL_int64 cb); T_const (Issue316OverflowExample.Vi64 0)] (ArithR H ca cb (Wasm_int.Int64.sub ca cb)))).
  { exact: sem_const_framed. }
  apply: (sem_seq (es1 := [:: BI_relop T_i64 (Relop_i (ROI_gt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.sub ca cb)) (VAL_int64 ca)))); T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_gt SX_S)) (VAL_int64 cb) (Issue316OverflowExample.Vi64 0))))] (ArithR H ca cb (Wasm_int.Int64.sub ca cb)))).
  { apply: (sem_frame_consts (vf := [:: VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.sub ca cb)) (VAL_int64 ca)))])). apply: relop_consts; by []. }
  apply: (sem_seq (es1 := [:: BI_relop T_i32 (Relop_i ROI_ne)])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i ROI_ne) (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.sub ca cb)) (VAL_int64 ca)))) (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_gt SX_S)) (VAL_int64 cb) (Issue316OverflowExample.Vi64 0)))))))] (ArithR H ca cb (Wasm_int.Int64.sub ca cb)))).
  { apply: relop_consts; by []. }
  have Hguard := i64_sub_signed_guard_false Hrange.
  rewrite -Vi64_zero in Hguard. rewrite Hguard.
  apply: (sem_seq (es1 := [:: BI_if (BT_valtype None) [:: BI_unreachable] [::]])
    (Q := AS_base [::] (ArithR H ca cb (Wasm_int.Int64.sub ca cb)))).
  { apply: guard_if_false. exact: sem_nil_same. }
  apply: (sem_conseq
    (P' := AS_base [::] (ArithR H ca cb (Wasm_int.Int64.sub ca cb)))
    (Q' := AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.sub ca cb))]
      (ArithR H ca cb (Wasm_int.Int64.sub ca cb)))).
  - by [].
  - move=> V [vs h] [Hs [_ [_ [_ HH]]]]. by split.
  - apply: get_pinned_frame. pinned_tac.
Qed.
Definition crt_general_checked_add_code : seq basic_instruction :=
  [:: BI_local_set ib; BI_local_tee ia; BI_local_get ib;
      BI_binop T_i64 (Binop_i BOI_add); BI_local_tee ir;
      BI_local_get ia; BI_relop T_i64 (Relop_i (ROI_lt SX_S));
      BI_local_get ib; BI_const_num (Issue316OverflowExample.Vi64 0);
      BI_relop T_i64 (Relop_i (ROI_lt SX_S)); BI_relop T_i32 (Relop_i ROI_ne);
      BI_if (BT_valtype None) [:: BI_unreachable] [::]; BI_local_get ir].
Lemma crt_general_checked_add_sem G H (ca cb : i64) :
  loc_stable ia (VAL_int64 ca) H ->
  loc_stable ib (VAL_int64 cb) H ->
  loc_stable ir (VAL_int64 (Wasm_int.Int64.add ca cb)) H ->
  loc_present ia H -> loc_present ib H -> loc_present ir H ->
  (Wasm_int.Int64.min_signed <=
     Wasm_int.Int64.signed ca + Wasm_int.Int64.signed cb <=
     Wasm_int.Int64.max_signed)%Z ->
  sem_triple G (AS_base [:: T_const (VAL_int64 ca); T_const (VAL_int64 cb)] H)
    crt_general_checked_add_code
    (AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.add ca cb))] H).
Proof.
  move=> StA StB StR PrA PrB PrR Hrange.
  rewrite /crt_general_checked_add_code.
  apply: (sem_seq (es1 := [:: BI_local_set ib])
    (Q := AS_base [:: T_const (VAL_int64 ca)] (ArithB H cb))).
  { apply: (sem_frame_consts (vf := [:: VAL_int64 ca])).
    exact: (sem_local_set_const_frame StB PrB). }
  apply: (sem_seq (es1 := [:: BI_local_tee ia])
    (Q := AS_base [:: T_const (VAL_int64 ca)] (ArithA H ca cb))).
  { apply: sem_local_tee_const_frame.
    - apply: loc_stable_and; [by apply: loc_stable_pin_other | exact StA].
    - apply: loc_present_right. exact PrA. }
  apply: (sem_seq (es1 := [:: BI_local_get ib])
    (Q := AS_base [:: T_const (VAL_int64 ca); T_const (VAL_int64 cb)] (ArithA H ca cb))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i BOI_add)])
    (Q := AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.add ca cb))] (ArithA H ca cb))).
  { apply: binop_consts; [by vm_compute | by [] | by [] | exact: i64_add_some]. }
  apply: (sem_seq (es1 := [:: BI_local_tee ir])
    (Q := AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.add ca cb))]
      (ArithR H ca cb (Wasm_int.Int64.add ca cb)))).
  { apply: sem_local_tee_const_frame.
    - apply: loc_stable_and; first by apply: loc_stable_pin_other.
      apply: loc_stable_and; first by apply: loc_stable_pin_other. exact StR.
    - apply: loc_present_right. apply: loc_present_right. exact PrR. }
  apply: (sem_seq (es1 := [:: BI_local_get ia])
    (Q := AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.add ca cb)); T_const (VAL_int64 ca)] (ArithR H ca cb (Wasm_int.Int64.add ca cb)))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_relop T_i64 (Relop_i (ROI_lt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.add ca cb)) (VAL_int64 ca))))] (ArithR H ca cb (Wasm_int.Int64.add ca cb)))).
  { apply: relop_consts; by []. }
  apply: (sem_seq (es1 := [:: BI_local_get ib])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.add ca cb)) (VAL_int64 ca)))); T_const (VAL_int64 cb)] (ArithR H ca cb (Wasm_int.Int64.add ca cb)))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_const_num (Issue316OverflowExample.Vi64 0)])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.add ca cb)) (VAL_int64 ca)))); T_const (VAL_int64 cb); T_const (Issue316OverflowExample.Vi64 0)] (ArithR H ca cb (Wasm_int.Int64.add ca cb)))).
  { exact: sem_const_framed. }
  apply: (sem_seq (es1 := [:: BI_relop T_i64 (Relop_i (ROI_lt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.add ca cb)) (VAL_int64 ca)))); T_const (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 cb) (Issue316OverflowExample.Vi64 0))))] (ArithR H ca cb (Wasm_int.Int64.add ca cb)))).
  { apply: (sem_frame_consts (vf := [:: VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.add ca cb)) (VAL_int64 ca)))])). apply: relop_consts; by []. }
  apply: (sem_seq (es1 := [:: BI_relop T_i32 (Relop_i ROI_ne)])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (app_relop (Relop_i ROI_ne) (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 (Wasm_int.Int64.add ca cb)) (VAL_int64 ca)))) (VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_S)) (VAL_int64 cb) (Issue316OverflowExample.Vi64 0)))))))] (ArithR H ca cb (Wasm_int.Int64.add ca cb)))).
  { apply: relop_consts; by []. }
  have Hguard := i64_add_signed_guard_false Hrange.
  rewrite -Vi64_zero in Hguard. rewrite Hguard.
  apply: (sem_seq (es1 := [:: BI_if (BT_valtype None) [:: BI_unreachable] [::]])
    (Q := AS_base [::] (ArithR H ca cb (Wasm_int.Int64.add ca cb)))).
  { apply: guard_if_false. exact: sem_nil_same. }
  apply: (sem_conseq
    (P' := AS_base [::] (ArithR H ca cb (Wasm_int.Int64.add ca cb)))
    (Q' := AS_base [:: T_const (VAL_int64 (Wasm_int.Int64.add ca cb))]
      (ArithR H ca cb (Wasm_int.Int64.add ca cb)))).
  - by [].
  - move=> V [vs h] [Hs [_ [_ [_ HH]]]]. by split.
  - apply: get_pinned_frame. pinned_tac.
Qed.
End Host.
Print Assumptions crt_general_checked_mul_sem.
Print Assumptions crt_general_checked_sub_sem.

Print Assumptions crt_general_checked_add_sem.
