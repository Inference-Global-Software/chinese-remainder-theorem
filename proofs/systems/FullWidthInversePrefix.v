(* Exact instruction execution for the extended Euclidean recurrence used by
   inverse_coprime. The finite mathematical run supplies loop termination. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit
  NumericDischarge Automation Activation Verifier MultiExitK Loop.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRT Require Import CRTStatements CRTLoops.
From CRTWasm Require Import CRTCheckedArithmetic CRTLoopRules.
From CRT Require Import CRTSystemStatements CRTSystemArithmetic.
From CRTSystems Require Import FullWidthExecution.
From CRTSystemGenerated Require Import main.
Module SM := CRTSystemGenerated.main.
Import FullWidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Theorem eea_run_terminates : forall A B e,
  eea_inputs A B -> eea_inv A B e ->
  exists final, eea_run e final /\ eea_inv A B final /\ r1 final = 0.
Proof.
  intros A B e Hin.
  remember (Z.to_nat (r1 e)) as k eqn:Hk.
  revert e Hk.
  induction k as [k IH] using lt_wf_ind.
  intros e Hk Hinv.
  destruct (Z.eq_dec (r1 e) 0) as [Hzero | Hnonzero].
  - exists e. repeat first [assumption | split]. apply eea_run_done. exact Hzero.
  - assert (Hpos : 0 < r1 e) by (destruct Hinv as (Hb & _); lia).
    destruct (eea_step_proved A B e Hin Hinv Hpos) as (Hnext & Hmod & Hless).
    destruct (IH (Z.to_nat (r1 (eea_step e))) ltac:(lia)
      (eea_step e) Logic.eq_refl Hnext) as (final & Hrun & Hfinal & Hzero).
    exists final. repeat first [assumption | split].
    apply eea_run_next; assumption.
Qed.


Section Host.
Context `{ho : host}.
Ltac pinned_tac :=
  solve [ exact: pinned_bare | apply: pinned_left; pinned_tac
        | apply: pinned_right; pinned_tac ].
Ltac present_tac :=
  solve [ exact: loc_present_defined | exact: loc_present_pin
        | apply: loc_present_left; present_tac
        | apply: loc_present_right; present_tac ].
Lemma stable_true i c : loc_stable i c HA_true.
Proof. by []. Qed.
Ltac stable_tac :=
  first [exact: stable_true |
  solve [ exact: loc_stable_defined_self | exact: loc_stable_pin_self
        | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other
        | apply: loc_stable_and; stable_tac ] ].
Ltac heap_build :=
  first [assumption | lazymatch goal with
    | |- hassert_denote ?V (HA_and ?P ?Q) ?h => split; heap_build
    | |- hassert_denote ?V HA_true ?h => exact I
    | |- hassert_denote ?V (HA_defined (T_local ?i)) ?h =>
      match goal with
      | Hp : hassert_denote V (term_eq (T_local i) (T_const ?c)) h |- _ =>
        destruct Hp as [v [Hv He]]; exists v; exact Hv
      end
    end].
Ltac heap_unpack :=
  repeat match goal with
  | Hp : hassert_denote ?V (HA_and ?P ?Q) ?h |- _ =>
    let H1 := fresh "Hloc" in let H2 := fresh "Hloc" in destruct Hp as [H1 H2]
  end.
Lemma checked_mul_Z G H x y :
  loc_stable 12%num (SM.Vi64 x) H -> loc_stable 13%num (SM.Vi64 y) H ->
  loc_stable 14%num (SM.Vi64 (x * y)) H ->
  loc_present 12%num H -> loc_present 13%num H -> loc_present 14%num H ->
  word x -> word y -> word (x * y) ->
  sem_triple G (AS_base [:: T_const (SM.Vi64 x); T_const (SM.Vi64 y)] H)
    crt_checked_mul_code (AS_base [:: T_const (SM.Vi64 (x * y))] H).
Proof.
  move=> SA SB SR PA PB PR Wx Wy Wxy.
  have E := crt_i64_mul_repr Wx Wy.
  have Range : Wasm_int.Int64.min_signed <=
    Wasm_int.Int64.signed (Wasm_int.Int64.repr x) *
    Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy)
      i64_min_signed_val i64_max_signed_val. exact Wxy. }
  have SR' : loc_stable 14%num (VAL_int64
    (Wasm_int.Int64.mul (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y))) H.
  { rewrite E. exact SR. }
  have P := crt_checked_mul_sem SA SB SR' PA PB PR Range.
  rewrite E in P. exact: P.
Qed.
Lemma checked_sub_Z G H x y :
  loc_stable 12%num (SM.Vi64 x) H -> loc_stable 13%num (SM.Vi64 y) H ->
  loc_stable 14%num (SM.Vi64 (x - y)) H ->
  loc_present 12%num H -> loc_present 13%num H -> loc_present 14%num H ->
  word x -> word y -> word (x - y) ->
  sem_triple G (AS_base [:: T_const (SM.Vi64 x); T_const (SM.Vi64 y)] H)
    crt_checked_sub_code (AS_base [:: T_const (SM.Vi64 (x - y))] H).
Proof.
  move=> SA SB SR PA PB PR Wx Wy Wxy.
  have E := crt_i64_sub_repr Wx Wy.
  have Range : Wasm_int.Int64.min_signed <=
    Wasm_int.Int64.signed (Wasm_int.Int64.repr x) -
    Wasm_int.Int64.signed (Wasm_int.Int64.repr y) <= Wasm_int.Int64.max_signed.
  { rewrite (crt_i64_signed_repr Wx) (crt_i64_signed_repr Wy)
      i64_min_signed_val i64_max_signed_val. exact Wxy. }
  have SR' : loc_stable 14%num (VAL_int64
    (Wasm_int.Int64.sub (Wasm_int.Int64.repr x) (Wasm_int.Int64.repr y))) H.
  { rewrite E. exact SR. }
  have P := crt_checked_sub_sem SA SB SR' PA PB PR Range.
  rewrite E in P. exact: P.
Qed.

Definition inverse_head A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r0 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (HA_defined (T_local 8%num))
    (HA_and (HA_defined (T_local 9%num))
    (HA_and (HA_defined (T_local 10%num))
    (HA_and (HA_defined (T_local 11%num))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).
Definition inverse_ready_1 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r0 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (HA_defined (T_local 8%num))
    (HA_and (HA_defined (T_local 9%num))
    (HA_and (HA_defined (T_local 10%num))
    (HA_and (HA_defined (T_local 11%num))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_stage_1 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r0 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (HA_defined (T_local 9%num))
    (HA_and (HA_defined (T_local 10%num))
    (HA_and (HA_defined (T_local 11%num))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_ready_2 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r0 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (HA_defined (T_local 9%num))
    (HA_and (HA_defined (T_local 10%num))
    (HA_and (HA_defined (T_local 11%num))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_stage_2 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r0 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (HA_defined (T_local 10%num))
    (HA_and (HA_defined (T_local 11%num))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_ready_3 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r0 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (HA_defined (T_local 10%num))
    (HA_and (HA_defined (T_local 11%num))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_stage_3 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r0 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (HA_defined (T_local 11%num))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_ready_4 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r0 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (HA_defined (T_local 11%num))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_stage_4 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r0 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_ready_5 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (HA_defined (T_local 2%num))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_stage_5 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_ready_6 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (HA_defined (T_local 3%num))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_stage_6 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s0 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_ready_7 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (HA_defined (T_local 4%num))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_stage_7 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_ready_8 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (HA_defined (T_local 5%num))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_stage_8 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t0 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_ready_9 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (HA_defined (T_local 6%num))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_stage_9 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_ready_10 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (HA_defined (T_local 7%num))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_stage_10 A B e : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e))))
    (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s1 e))))
    (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t1 e))))
    (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e))))
    (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e))))
    (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))))
    (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).

Definition inverse_update_code : seq basic_instruction :=
  [:: BI_local_get 2%num] ++
  [:: BI_local_get 3%num] ++
  [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))] ++
  [:: BI_local_set 8%num] ++
  [:: BI_local_get 2%num] ++
  [:: BI_local_get 3%num] ++
  [:: BI_binop T_i64 (Binop_i (BOI_rem SX_S))] ++
  [:: BI_local_set 9%num] ++
  [:: BI_local_get 4%num] ++
  [:: BI_local_get 8%num] ++
  [:: BI_local_get 5%num] ++
  crt_checked_mul_code ++
  crt_checked_sub_code ++
  [:: BI_local_set 10%num] ++
  [:: BI_local_get 6%num] ++
  [:: BI_local_get 8%num] ++
  [:: BI_local_get 7%num] ++
  crt_checked_mul_code ++
  crt_checked_sub_code ++
  [:: BI_local_set 11%num] ++
  [:: BI_local_get 3%num] ++
  [:: BI_local_set 2%num] ++
  [:: BI_local_get 9%num] ++
  [:: BI_local_set 3%num] ++
  [:: BI_local_get 5%num] ++
  [:: BI_local_set 4%num] ++
  [:: BI_local_get 10%num] ++
  [:: BI_local_set 5%num] ++
  [:: BI_local_get 7%num] ++
  [:: BI_local_set 6%num] ++
  [:: BI_local_get 11%num] ++
  [:: BI_local_set 7%num].

Ltac heap_from HH := cbv beta iota zeta delta [inverse_head inverse_ready_1 inverse_stage_1 inverse_ready_2 inverse_stage_2 inverse_ready_3 inverse_stage_3 inverse_ready_4 inverse_stage_4 inverse_ready_5 inverse_stage_5 inverse_ready_6 inverse_stage_6 inverse_ready_7 inverse_stage_7 inverse_ready_8 inverse_stage_8 inverse_ready_9 inverse_stage_9 inverse_ready_10 inverse_stage_10] in HH |- *; heap_unpack; heap_build.

Lemma inverse_update_sem A B e :
  eea_inputs A B -> eea_inv A B e -> 0 < r1 e ->
  sem_triple (triv_ctx SM.main) (AS_base [::] (inverse_head A B e))
    inverse_update_code (AS_base [::] (inverse_head A B (eea_step e))).
Proof.
  move=> Hin Hinv Hpos.
  have Numeric := eea_iteration_numeric_refinement Hin Hinv Hpos.
  destruct Numeric as (DivExact & RemExact & _).
  have Bounds := eea_step_bounds_proved A B e Hin Hinv Hpos.
  destruct Bounds as (Hq & _ & _ & _ & _ & _ & Wsp & Wsn & Wtp & Wtn).
  have HA : A <= MAX := proj2 Hin.
  have HB : B <= MAX by clear -Hin; destruct Hin as [[_ HB] HA]; lia.
  destruct Hinv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs0 & Hs1 & Ht0 & Ht1).
  have Wq : word (r0 e / r1 e) by clear -Hq HA; apply: crt_modulus_word; lia.
  have Ws0 : word (s0 e) by apply: (abs_word_small _ B); assumption.
  have Ws1 : word (s1 e) by apply: (abs_word_small _ B); assumption.
  have Wt0 : word (t0 e) by apply: (abs_word_small _ A); assumption.
  have Wt1 : word (t1 e) by apply: (abs_word_small _ A); assumption.
  rewrite /inverse_update_code.
  apply: (sem_seq (es1 := [:: BI_local_get 2%num])
    (Q := AS_base [:: T_const (SM.Vi64 (r0 e))] (inverse_head A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_get 3%num])
    (Q := AS_base [:: T_const (SM.Vi64 (r0 e)); T_const (SM.Vi64 (r1 e))] (inverse_head A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_div SX_S))])
    (Q := AS_base [:: T_const (SM.Vi64 (r0 e / r1 e))] (inverse_head A B e))).
  { apply: binop_consts; [by vm_compute | by [] | by [] | exact DivExact]. }
  apply: (sem_seq (es1 := [:: BI_local_set 8%num])
    (Q := AS_base [::] (inverse_stage_1 A B e))).
  { apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 (r0 e / r1 e))] (inverse_ready_1 A B e))
      (Q' := AS_base [::] (HA_and (term_eq (T_local 8%num) (T_const (SM.Vi64 (r0 e / r1 e)))) (inverse_ready_1 A B e)))).
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 2%num])
    (Q := AS_base [:: T_const (SM.Vi64 (r0 e))] (inverse_stage_1 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_get 3%num])
    (Q := AS_base [:: T_const (SM.Vi64 (r0 e)); T_const (SM.Vi64 (r1 e))] (inverse_stage_1 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_binop T_i64 (Binop_i (BOI_rem SX_S))])
    (Q := AS_base [:: T_const (SM.Vi64 (r0 e mod r1 e))] (inverse_stage_1 A B e))).
  { apply: binop_consts; [by vm_compute | by [] | by [] | exact RemExact]. }
  apply: (sem_seq (es1 := [:: BI_local_set 9%num])
    (Q := AS_base [::] (inverse_stage_2 A B e))).
  { apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 (r0 e mod r1 e))] (inverse_ready_2 A B e))
      (Q' := AS_base [::] (HA_and (term_eq (T_local 9%num) (T_const (SM.Vi64 (r0 e mod r1 e)))) (inverse_ready_2 A B e)))).
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 4%num])
    (Q := AS_base [:: T_const (SM.Vi64 (s0 e))] (inverse_stage_2 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_get 8%num])
    (Q := AS_base [:: T_const (SM.Vi64 (s0 e)); T_const (SM.Vi64 (r0 e / r1 e))] (inverse_stage_2 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_get 5%num])
    (Q := AS_base [:: T_const (SM.Vi64 (s0 e)); T_const (SM.Vi64 (r0 e / r1 e)); T_const (SM.Vi64 (s1 e))] (inverse_stage_2 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := crt_checked_mul_code)
    (Q := AS_base [:: T_const (SM.Vi64 (s0 e)); T_const (SM.Vi64 ((r0 e / r1 e) * s1 e))] (inverse_stage_2 A B e))).
  { apply: (sem_frame_consts (vf := [:: SM.Vi64 (s0 e)])). apply: checked_mul_Z; [stable_tac | stable_tac | stable_tac | present_tac | present_tac | present_tac | exact Wq | exact Ws1 | exact Wsp]. }
  apply: (sem_seq (es1 := crt_checked_sub_code)
    (Q := AS_base [:: T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))] (inverse_stage_2 A B e))).
  { apply: checked_sub_Z; [stable_tac | stable_tac | stable_tac | present_tac | present_tac | present_tac | exact Ws0 | exact Wsp | exact Wsn]. }
  apply: (sem_seq (es1 := [:: BI_local_set 10%num])
    (Q := AS_base [::] (inverse_stage_3 A B e))).
  { apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))] (inverse_ready_3 A B e))
      (Q' := AS_base [::] (HA_and (term_eq (T_local 10%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e))))) (inverse_ready_3 A B e)))).
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 6%num])
    (Q := AS_base [:: T_const (SM.Vi64 (t0 e))] (inverse_stage_3 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_get 8%num])
    (Q := AS_base [:: T_const (SM.Vi64 (t0 e)); T_const (SM.Vi64 (r0 e / r1 e))] (inverse_stage_3 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_get 7%num])
    (Q := AS_base [:: T_const (SM.Vi64 (t0 e)); T_const (SM.Vi64 (r0 e / r1 e)); T_const (SM.Vi64 (t1 e))] (inverse_stage_3 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := crt_checked_mul_code)
    (Q := AS_base [:: T_const (SM.Vi64 (t0 e)); T_const (SM.Vi64 ((r0 e / r1 e) * t1 e))] (inverse_stage_3 A B e))).
  { apply: (sem_frame_consts (vf := [:: SM.Vi64 (t0 e)])). apply: checked_mul_Z; [stable_tac | stable_tac | stable_tac | present_tac | present_tac | present_tac | exact Wq | exact Wt1 | exact Wtp]. }
  apply: (sem_seq (es1 := crt_checked_sub_code)
    (Q := AS_base [:: T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))] (inverse_stage_3 A B e))).
  { apply: checked_sub_Z; [stable_tac | stable_tac | stable_tac | present_tac | present_tac | present_tac | exact Wt0 | exact Wtp | exact Wtn]. }
  apply: (sem_seq (es1 := [:: BI_local_set 11%num])
    (Q := AS_base [::] (inverse_stage_4 A B e))).
  { apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))] (inverse_ready_4 A B e))
      (Q' := AS_base [::] (HA_and (term_eq (T_local 11%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e))))) (inverse_ready_4 A B e)))).
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 3%num])
    (Q := AS_base [:: T_const (SM.Vi64 (r1 e))] (inverse_stage_4 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 2%num])
    (Q := AS_base [::] (inverse_stage_5 A B e))).
  { apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 (r1 e))] (inverse_ready_5 A B e))
      (Q' := AS_base [::] (HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 (r1 e)))) (inverse_ready_5 A B e)))).
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 9%num])
    (Q := AS_base [:: T_const (SM.Vi64 (r0 e mod r1 e))] (inverse_stage_5 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 3%num])
    (Q := AS_base [::] (inverse_stage_6 A B e))).
  { apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 (r0 e mod r1 e))] (inverse_ready_6 A B e))
      (Q' := AS_base [::] (HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 (r0 e mod r1 e)))) (inverse_ready_6 A B e)))).
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 5%num])
    (Q := AS_base [:: T_const (SM.Vi64 (s1 e))] (inverse_stage_6 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 4%num])
    (Q := AS_base [::] (inverse_stage_7 A B e))).
  { apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 (s1 e))] (inverse_ready_7 A B e))
      (Q' := AS_base [::] (HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 (s1 e)))) (inverse_ready_7 A B e)))).
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 10%num])
    (Q := AS_base [:: T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))] (inverse_stage_7 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 5%num])
    (Q := AS_base [::] (inverse_stage_8 A B e))).
  { apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e)))] (inverse_ready_8 A B e))
      (Q' := AS_base [::] (HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 (s0 e - ((r0 e / r1 e) * s1 e))))) (inverse_ready_8 A B e)))).
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 7%num])
    (Q := AS_base [:: T_const (SM.Vi64 (t1 e))] (inverse_stage_8 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 6%num])
    (Q := AS_base [::] (inverse_stage_9 A B e))).
  { apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 (t1 e))] (inverse_ready_9 A B e))
      (Q' := AS_base [::] (HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 (t1 e)))) (inverse_ready_9 A B e)))).
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 11%num])
    (Q := AS_base [:: T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))] (inverse_stage_9 A B e))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 7%num])
    (Q := AS_base [::] (inverse_stage_10 A B e))).
  { apply: (sem_conseq (P' := AS_base [:: T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e)))] (inverse_ready_10 A B e))
      (Q' := AS_base [::] (HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 (t0 e - ((r0 e / r1 e) * t1 e))))) (inverse_ready_10 A B e)))).
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
    - apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_conseq (P' := AS_base [::] (inverse_stage_10 A B e))
    (Q' := AS_base [::] (inverse_stage_10 A B e))).
  - by [].
  - move=> V [vs h] [Hs HH]. split; first exact Hs. heap_from HH.
  - exact: sem_nil_same.
Qed.
Lemma inverse_condition_sem A B e : word (r1 e) ->
  sem_triple (triv_ctx SM.main) (AS_base [::] (inverse_head A B e))
    [:: BI_local_get 3%num; BI_const_num (SM.Vi64 0);
      BI_relop T_i64 (Relop_i (ROI_gt SX_S)); BI_testop T_i32 TO_eqz]
    (AS_base [:: T_const (VAL_int32 (wasm_bool (negb (0 <? r1 e))))] (inverse_head A B e)).
Proof.
  move=> W1.
  apply: (sem_seq (es1 := [:: BI_local_get 3%num; BI_const_num (SM.Vi64 0);
      BI_relop T_i64 (Relop_i (ROI_gt SX_S))])
    (Q := AS_base [:: T_const (VAL_int32 (wasm_bool (0 <? r1 e)))] (inverse_head A B e))).
  - rewrite -(crt_i64_gt_zero W1).
    apply: test_pin_const; [pinned_tac | by [] | by [] | by []].
  - exact: crt_eqz_bool_sem.
Qed.
Definition inverse_loop_code : seq basic_instruction :=
  [:: BI_local_get 3%num; BI_const_num (SM.Vi64 0);
      BI_relop T_i64 (Relop_i (ROI_gt SX_S)); BI_testop T_i32 TO_eqz;
      BI_br_if 1%num] ++ inverse_update_code ++ [:: BI_br 0%num].
Lemma inverse_loop_run_sem A B e final : eea_run e final ->
  eea_inputs A B -> eea_inv A B e ->
  sem_mxk (triv_ctx SM.main) (AS_base [::] (inverse_head A B e))
    [:: BI_loop (BT_valtype None) inverse_loop_code]
    (AS_base [::] (inverse_head A B final)) crt_false_assert
    (fun k => if k is 0%nat then AS_base [::] (inverse_head A B final) else crt_false_assert).
Proof.
  move=> Hrun. induction Hrun as [e Hz | e final Hpos Hrun IH]; intros Hin Hinv.
  - apply: (crt_loop_unroll (Pback := crt_false_assert) (t1s := [::]) (t2s := [::])).
    + by [].
    + move=> V vs h [Hs _]. by case: Hs => <-.
    + move=> V vs h [_ Hfalse]. by case: Hfalse.
    + rewrite /inverse_loop_code.
      apply: (sem_mxk_seq
        (es1 := [:: BI_local_get 3%num; BI_const_num (SM.Vi64 0);
          BI_relop T_i64 (Relop_i (ROI_gt SX_S)); BI_testop T_i32 TO_eqz])
        (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool true))] (inverse_head A B e))).
      * apply: sem_mxk_lift.
        have W1 : word (r1 e) by rewrite Hz; unfold word, i64_min, i64_max; lia.
        have HC := inverse_condition_sem (A := A) (B := B) W1.
        by rewrite Hz in HC.
      * apply: (sem_mxk_seq (es1 := [:: BI_br_if 1%num]) (Q1 := crt_false_assert)).
        -- apply: (crt_br_if_true_sem (k := 1%nat)). by [].
        -- apply: sem_mxk_lift. exact: sem_false.
    + apply: sem_mxk_lift. exact: sem_false.
  - have Hnext := proj1 (eea_step_proved A B e Hin Hinv Hpos).
    have W1 : word (r1 e).
    { clear -Hin Hinv. destruct Hin as [_ HA].
      destruct Hinv as (H1 & H10 & H0 & _).
      unfold word, MAX, i64_min, i64_max in *. lia. }
    have Htest : (0 <? r1 e) = true by apply/Z.ltb_lt.
    apply: (crt_loop_unroll (Pback := AS_base [::] (inverse_head A B (eea_step e)))
      (t1s := [::]) (t2s := [::])).
    + by [].
    + move=> V vs h [Hs _]. by case: Hs => <-.
    + move=> V vs h [Hs _]. by case: Hs => <-.
    + rewrite /inverse_loop_code.
      apply: (sem_mxk_seq
        (es1 := [:: BI_local_get 3%num; BI_const_num (SM.Vi64 0);
          BI_relop T_i64 (Relop_i (ROI_gt SX_S)); BI_testop T_i32 TO_eqz])
        (Q1 := AS_base [:: T_const (VAL_int32 (wasm_bool false))] (inverse_head A B e))).
      * apply: sem_mxk_lift.
        have HC := inverse_condition_sem (A := A) (B := B) W1.
        by rewrite Htest in HC.
      * apply: (sem_mxk_seq (es1 := [:: BI_br_if 1%num])
          (Q1 := AS_base [::] (inverse_head A B e))).
        -- apply: sem_mxk_lift. exact: crt_br_if_false_sem.
        -- apply: (sem_mxk_seq (es1 := inverse_update_code)
             (Q1 := AS_base [::] (inverse_head A B (eea_step e)))).
           ++ apply: sem_mxk_lift. exact: inverse_update_sem.
           ++ apply: (sem_mxk_br_k (k := 0%nat)). by [].
    + exact: (IH Hin Hnext).
Qed.
Lemma inverse_block_run_sem A B e final : eea_run e final ->
  eea_inputs A B -> eea_inv A B e ->
  sem_mxk (triv_ctx SM.main) (AS_base [::] (inverse_head A B e))
    [:: BI_block (BT_valtype None) [:: BI_loop (BT_valtype None) inverse_loop_code]]
    (AS_base [::] (inverse_head A B final)) crt_false_assert (fun _ => crt_false_assert).
Proof.
  move=> Hrun Hin Hinv.
  apply: (sem_mxk_block (t1s := [::]) (t2s := [::])
    (Qb := fun k => if k is 0%nat then AS_base [::] (inverse_head A B final) else crt_false_assert)).
  - by [].
  - by [].
  - move=> V vs h [Hs _]. by case: Hs => <-.
  - by [].
  - exact: (inverse_loop_run_sem Hrun Hin Hinv).
Qed.
Lemma pure_mxk_triple G P es Q :
  sem_mxk G P es Q crt_false_assert (fun _ => crt_false_assert) ->
  sem_triple G P es Q.
Proof.
  move=> HM hs st f V vs h HP Hr Hagree.
  have [st' [f' [V' [vs' [h' [Hlog [Hr' HD]]]]]]] := HM hs st f V vs h HP Hr Hagree.
  case: HD => [[Hred HQ] | [[i [lh [Hred [_ Hfalse]]]] | [k [d [lh [Hred [_ Hfalse]]]]]]].
  - exists st', f', V', vs', h'. split; first exact Hlog.
    split; first exact Hred. split; [exact HQ | exact Hr'].
  - by case: Hfalse.
  - by case: Hfalse.
Qed.

Definition inverse_entry A B : hassert :=
  (HA_and (term_eq (T_local 0%num) (T_const (SM.Vi64 (B))))
    (HA_and (term_eq (T_local 1%num) (T_const (SM.Vi64 (A))))
    (HA_and (HA_defined (T_local 2%num))
    (HA_and (HA_defined (T_local 3%num))
    (HA_and (HA_defined (T_local 4%num))
    (HA_and (HA_defined (T_local 5%num))
    (HA_and (HA_defined (T_local 6%num))
    (HA_and (HA_defined (T_local 7%num))
    (HA_and (HA_defined (T_local 8%num))
    (HA_and (HA_defined (T_local 9%num))
    (HA_and (HA_defined (T_local 10%num))
    (HA_and (HA_defined (T_local 11%num))
    (HA_and (HA_defined (T_local 12%num))
    (HA_and (HA_defined (T_local 13%num))
    (HA_and (HA_defined (T_local 14%num))
    HA_true))))))))))))))).
Definition inverse_initial_1 A B : hassert :=
  HA_and (term_eq (T_local 2%num) (T_const (SM.Vi64 A))) (inverse_entry A B).
Definition inverse_initial_2 A B : hassert :=
  HA_and (term_eq (T_local 3%num) (T_const (SM.Vi64 B))) (inverse_initial_1 A B).
Definition inverse_initial_3 A B : hassert :=
  HA_and (term_eq (T_local 4%num) (T_const (SM.Vi64 1))) (inverse_initial_2 A B).
Definition inverse_initial_4 A B : hassert :=
  HA_and (term_eq (T_local 5%num) (T_const (SM.Vi64 0))) (inverse_initial_3 A B).
Definition inverse_initial_5 A B : hassert :=
  HA_and (term_eq (T_local 6%num) (T_const (SM.Vi64 0))) (inverse_initial_4 A B).
Definition inverse_initial_6 A B : hassert :=
  HA_and (term_eq (T_local 7%num) (T_const (SM.Vi64 1))) (inverse_initial_5 A B).
Definition inverse_prologue_code : seq basic_instruction :=
  [:: BI_local_get 1%num;
      BI_local_set 2%num;
      BI_local_get 0%num;
      BI_local_set 3%num;
      BI_const_num (SM.Vi64 1);
      BI_local_set 4%num;
      BI_const_num (SM.Vi64 0);
      BI_local_set 5%num;
      BI_const_num (SM.Vi64 0);
      BI_local_set 6%num;
      BI_const_num (SM.Vi64 1);
      BI_local_set 7%num].
Lemma inverse_prologue_sem A B :
  sem_triple (triv_ctx SM.main) (AS_base [::] (inverse_entry A B))
    inverse_prologue_code (AS_base [::] (inverse_head A B (eea_init A B))).
Proof.
  rewrite /inverse_prologue_code.
  apply: (sem_seq (es1 := [:: BI_local_get 1%num])
    (Q := AS_base [:: T_const (SM.Vi64 A)] (inverse_entry A B))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 2%num])
    (Q := AS_base [::] (inverse_initial_1 A B))).
  { apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_local_get 0%num])
    (Q := AS_base [:: T_const (SM.Vi64 B)] (inverse_initial_1 A B))).
  { apply: get_pinned_frame. pinned_tac. }
  apply: (sem_seq (es1 := [:: BI_local_set 3%num])
    (Q := AS_base [::] (inverse_initial_2 A B))).
  { apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_const_num (SM.Vi64 1)])
    (Q := AS_base [:: T_const (SM.Vi64 1)] (inverse_initial_2 A B))).
  { exact: sem_const_framed. }
  apply: (sem_seq (es1 := [:: BI_local_set 4%num])
    (Q := AS_base [::] (inverse_initial_3 A B))).
  { apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_const_num (SM.Vi64 0)])
    (Q := AS_base [:: T_const (SM.Vi64 0)] (inverse_initial_3 A B))).
  { exact: sem_const_framed. }
  apply: (sem_seq (es1 := [:: BI_local_set 5%num])
    (Q := AS_base [::] (inverse_initial_4 A B))).
  { apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_const_num (SM.Vi64 0)])
    (Q := AS_base [:: T_const (SM.Vi64 0)] (inverse_initial_4 A B))).
  { exact: sem_const_framed. }
  apply: (sem_seq (es1 := [:: BI_local_set 6%num])
    (Q := AS_base [::] (inverse_initial_5 A B))).
  { apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_seq (es1 := [:: BI_const_num (SM.Vi64 1)])
    (Q := AS_base [:: T_const (SM.Vi64 1)] (inverse_initial_5 A B))).
  { exact: sem_const_framed. }
  apply: (sem_seq (es1 := [:: BI_local_set 7%num])
    (Q := AS_base [::] (inverse_initial_6 A B))).
  { apply: sem_local_set_const_frame; [stable_tac | present_tac]. }
  apply: (sem_conseq (P' := AS_base [::] (inverse_initial_6 A B))
    (Q' := AS_base [::] (inverse_initial_6 A B))).
  - by [].
  - move=> V [vs h] [Hs HH]. split; first exact Hs.
    cbv beta iota zeta delta [inverse_entry inverse_initial_1 inverse_initial_2 inverse_initial_3 inverse_initial_4 inverse_initial_5 inverse_initial_6 inverse_head] in HH |- *.
    heap_unpack. heap_build.
  - exact: sem_nil_same.
Qed.
Lemma inverse_body_shape : modfunc_body SM.inverse_coprime =
  inverse_prologue_code ++
  [:: BI_block (BT_valtype None) [:: BI_loop (BT_valtype None) inverse_loop_code];
      BI_local_get 6%num; BI_local_get 1%num; BI_call 1%num; BI_return; BI_unreachable].
Proof. by []. Qed.
Lemma inverse_prefix_sem A B final : eea_inputs A B ->
  eea_run (eea_init A B) final ->
  sem_triple (triv_ctx SM.main) (AS_base [::] (inverse_entry A B))
    (inverse_prologue_code ++
      [:: BI_block (BT_valtype None) [:: BI_loop (BT_valtype None) inverse_loop_code]])
    (AS_base [::] (inverse_head A B final)).
Proof.
  move=> Hin Hrun.
  apply: (sem_seq (es1 := inverse_prologue_code)
    (Q := AS_base [::] (inverse_head A B (eea_init A B)))).
  - exact: inverse_prologue_sem.
  - apply: pure_mxk_triple. apply: inverse_block_run_sem.
    + exact Hrun.
    + exact Hin.
    + exact: eea_init_proved.
Qed.
End Host.
Print Assumptions inverse_update_sem.
Print Assumptions inverse_prefix_sem.
