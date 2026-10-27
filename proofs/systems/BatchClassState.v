(* Local states for the exact classifier; scratch slots are present but unconstrained. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From WasmVerifier Require Import Assertions Triples Semantics Pure Control MultiExit MultiExitK NumericDischarge Automation Activation Verifier.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRTSystems Require Import SystemRuntime SystemControl SystemCalls FullWidthExecution BatchArithmetic BatchCount BatchValidation BatchPair.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition bc_pin k v := term_eq (T_local k) (T_const v).
Definition BCBase rb mb count := HA_and (bc_pin 0%num (SM.Vi32 (Z.of_N rb)))
 (HA_and (bc_pin 1%num (SM.Vi32 (Z.of_N mb)))
 (HA_and (bc_pin 2%num (SM.Vi32 (Z.of_nat count)))
 (HA_and (HA_defined (T_local 3%num)) (HA_and (HA_defined (T_local 4%num))
 (HA_and (HA_defined (T_local 5%num)) (HA_and (HA_defined (T_local 6%num))
 (HA_and (HA_defined (T_local 7%num)) (HA_and (HA_defined (T_local 8%num))
 (HA_and (HA_defined (T_local 9%num)) (HA_and (HA_defined (T_local 10%num))
 (HA_and (HA_defined (T_local 11%num)) (HA_and (HA_defined (T_local 12%num))
 (HA_defined (T_local 13%num)))))))))))))).
Definition BCHead rb mb count s i := HA_and (bc_pin 3%num (SM.Vi64 s))
 (HA_and (bc_pin 4%num (SM.Vi32 (Z.of_nat i))) (BCBase rb mb count)).
Definition BCRow rb mb count s i j := HA_and (bc_pin 5%num (SM.Vi32 (Z.of_nat j))) (BCHead rb mb count s i).
Definition BCExit rb mb count s := HA_and (bc_pin 3%num (SM.Vi64 s)) (BCBase rb mb count).
Ltac bc_unfold := unfold BCRow, BCHead, BCExit, BCBase, bc_pin.
Ltac bc_pinned := solve [exact: pinned_bare | apply: pinned_left; bc_pinned | apply: pinned_right; bc_pinned].
Ltac bc_present := solve [exact: loc_present_defined | exact: loc_present_pin | apply: loc_present_left; bc_present | apply: loc_present_right; bc_present].
Ltac bc_stable := solve [exact: loc_stable_defined_self | exact: loc_stable_pin_self | by apply: loc_stable_defined_other | by apply: loc_stable_pin_other | apply: loc_stable_and; bc_stable].
Ltac bc_heap HH :=
 lazymatch type of HH with
 | hassert_denote ?V ?H ?h =>
   lazymatch goal with
   | |- hassert_denote V (HA_and ?P ?Q) h => split; bc_heap HH
   | |- hassert_denote V (HA_defined (T_local ?i)) h =>
     let Hp := fresh "Hp" in assert (Hp : loc_present i H) by bc_present; exact (Hp V h HH)
   | |- hassert_denote V (term_eq (T_local ?i) (T_const ?c)) h =>
     let Hp := fresh "Hp" in assert (Hp : pinned i c H) by bc_pinned;
     exists c; split; first exact (Hp V h HH); reflexivity
   end
 end.
Section Host.
Context `{ho:host}.
Lemma bc_head_exit rb mb count s i S : aentails (AS_base S (BCHead rb mb count s i)) (AS_base S (BCExit rb mb count s)).
Proof. move=> V [vs h] [Hs HH]. split; first exact Hs. bc_unfold. unfold BCRow, BCHead, BCExit, BCBase, bc_pin in HH. bc_heap HH. Qed.
Lemma bc_row_exit rb mb count s i j S : aentails (AS_base S (BCRow rb mb count s i j)) (AS_base S (BCExit rb mb count s)).
Proof. move=> V [vs h] [Hs HH]. split; first exact Hs. bc_unfold. unfold BCRow, BCHead, BCExit, BCBase, bc_pin in HH. bc_heap HH. Qed.
Lemma bc_set_head_i rb mb count s i j :
 sem_triple (triv_ctx SM.main) (AS_base [::T_const (SM.Vi32 (Z.of_nat j))] (BCHead rb mb count s i))
 [::BI_local_set 4%num] (AS_base [::] (BCHead rb mb count s j)).
Proof.
 pose H := BCExit rb mb count s.
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi32 (Z.of_nat j))] H)
 (Q':=AS_base [::] (HA_and (bc_pin 4%num (SM.Vi32 (Z.of_nat j))) H))).
 - unfold H; bc_unfold. move=> V [vs h] [Hs HH]. split; first exact Hs. bc_heap HH.
 - unfold H; bc_unfold. move=> V [vs h] [Hs HH]. split; first exact Hs. bc_heap HH.
 - unfold H; bc_unfold. apply: sem_local_set_const_frame; [bc_stable|bc_present].
Qed.
Lemma bc_set_head_status rb mb count s i t :
 sem_triple (triv_ctx SM.main) (AS_base [::T_const (SM.Vi64 t)] (BCHead rb mb count s i))
 [::BI_local_set 3%num] (AS_base [::] (BCHead rb mb count t i)).
Proof.
 pose H := HA_and (bc_pin 4%num (SM.Vi32 (Z.of_nat i))) (BCBase rb mb count).
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi64 t)] H)
 (Q':=AS_base [::] (HA_and (bc_pin 3%num (SM.Vi64 t)) H))).
 - unfold H; bc_unfold. move=> V [vs h] [Hs HH]. split; first exact Hs. bc_heap HH.
 - unfold H; bc_unfold. move=> V [vs h] [Hs HH]. split; first exact Hs. bc_heap HH.
 - unfold H; bc_unfold. apply: sem_local_set_const_frame; [bc_stable|bc_present].
Qed.
Lemma bc_set_row_j rb mb count s i j k :
 sem_triple (triv_ctx SM.main) (AS_base [::T_const (SM.Vi32 (Z.of_nat k))] (BCRow rb mb count s i j))
 [::BI_local_set 5%num] (AS_base [::] (BCRow rb mb count s i k)).
Proof.
 pose H := BCHead rb mb count s i.
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi32 (Z.of_nat k))] H)
 (Q':=AS_base [::] (HA_and (bc_pin 5%num (SM.Vi32 (Z.of_nat k))) H))).
 - unfold H; bc_unfold. move=> V [vs h] [Hs HH]. split; first exact Hs. bc_heap HH.
 - unfold H; bc_unfold. move=> V [vs h] [Hs HH]. split; first exact Hs. bc_heap HH.
 - unfold H; bc_unfold. apply: sem_local_set_const_frame; [bc_stable|bc_present].
Qed.
Lemma bc_set_row_status rb mb count s i j t :
 sem_triple (triv_ctx SM.main) (AS_base [::T_const (SM.Vi64 t)] (BCRow rb mb count s i j))
 [::BI_local_set 3%num] (AS_base [::] (BCRow rb mb count t i j)).
Proof.
 pose H := HA_and (bc_pin 5%num (SM.Vi32 (Z.of_nat j))) (HA_and (bc_pin 4%num (SM.Vi32 (Z.of_nat i))) (BCBase rb mb count)).
 apply: (sem_conseq (P':=AS_base [::T_const (SM.Vi64 t)] H)
 (Q':=AS_base [::] (HA_and (bc_pin 3%num (SM.Vi64 t)) H))).
 - unfold H; bc_unfold. move=> V [vs h] [Hs HH]. split; first exact Hs. bc_heap HH.
 - unfold H; bc_unfold. move=> V [vs h] [Hs HH]. split; first exact Hs. bc_heap HH.
 - unfold H; bc_unfold. apply: sem_local_set_const_frame; [bc_stable|bc_present].
Qed.
Definition bc_inc_value idx := [::BI_local_get idx;BI_const_num (SM.Vi32 1)] ++ batch_checked_add_code 8%num 9%num 10%num.
Lemma bc_inc_value_sem H idx i : (i <= 16)%coq_nat ->
 pinned idx (SM.Vi32 (Z.of_nat i)) H ->
 (forall z, loc_stable 8%num (SM.Vi32 z) H) ->
 (forall z, loc_stable 9%num (SM.Vi32 z) H) ->
 (forall z, loc_stable 10%num (SM.Vi32 z) H) ->
 loc_present 8%num H -> loc_present 9%num H -> loc_present 10%num H ->
 sem_triple (triv_ctx SM.main) (AS_base [::] H) (bc_inc_value idx)
 (AS_base [::T_const (SM.Vi32 (Z.of_nat (S i)))] H).
Proof.
 move=> Hi Hp S8 S9 S10 P8 P9 P10. rewrite /bc_inc_value Nat2Z.inj_succ.
 replace (Z.succ (Z.of_nat i)) with (Z.of_nat i + 1) by lia.
 apply: (sem_seq (Q:=AS_base [::T_const (SM.Vi32 (Z.of_nat i));T_const (SM.Vi32 1)] H)).
 - apply: (sem_seq (es1:=[::BI_local_get idx]) (Q:=AS_base [::T_const (SM.Vi32 (Z.of_nat i))] H));
   [exact: get_pinned_frame|exact: sem_const_framed].
 - apply: batch_checked_add_Z; try assumption; try (by []); try (unfold batch_word32; lia).
Qed.
Lemma bc_inc_head rb mb count s i : (i <= 16)%coq_nat ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (BCHead rb mb count s i))
 (bc_inc_value 4%num ++ [::BI_local_set 4%num])
 (AS_base [::] (BCHead rb mb count s (S i))).
Proof.
 move=> Hi. apply: (sem_seq (Q:=AS_base [::T_const (SM.Vi32 (Z.of_nat (S i)))] (BCHead rb mb count s i))).
 - apply: bc_inc_value_sem; first exact Hi; bc_unfold; try bc_pinned; try bc_present; move=> z; bc_stable.
 - exact: bc_set_head_i.
Qed.
Lemma bc_inc_row rb mb count s i j : (j <= 16)%coq_nat ->
 sem_triple (triv_ctx SM.main) (AS_base [::] (BCRow rb mb count s i j))
 (bc_inc_value 5%num ++ [::BI_local_set 5%num])
 (AS_base [::] (BCRow rb mb count s i (S j))).
Proof.
 move=> Hj. apply: (sem_seq (Q:=AS_base [::T_const (SM.Vi32 (Z.of_nat (S j)))] (BCRow rb mb count s i j))).
 - apply: bc_inc_value_sem; first exact Hj; bc_unfold; try bc_pinned; try bc_present; move=> z; bc_stable.
 - exact: bc_set_row_j.
Qed.
End Host.
