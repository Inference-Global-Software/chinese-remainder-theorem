(* Relate exact bounded cursor recurrences to the unbounded finite-list model. *)
From Coq Require Import ZArith NArith Lia List Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From CRT Require Import CRTStatements CRTSystemStatements CRTFinite.
From CRTSystems Require Import BatchValidateLoop BatchPairRow BatchPairLoop.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition bc_entry rs ms i :=
 (Wasm_int.Int64.signed (List.nth i rs (Wasm_int.Int64.repr 0)),
  Wasm_int.Int64.signed (List.nth i ms (Wasm_int.Int64.repr 0))).
Fixpoint bc_entries fuel i rs ms := match fuel with
 O => [::] | S k => bc_entry rs ms i :: bc_entries k (S i) rs ms end.
Definition bc_classify count rs ms :=
 if FiniteSystem.validate_loop (bc_entries count 0 rs ms) then
 if FiniteSystem.pair_loop (bc_entries count 0 rs ms) then 0 else -1 else -2.
Lemma bc_validate_status fuel i rs ms :
 snd (bc_validate fuel i rs ms) =
 if FiniteSystem.validate_loop (bc_entries fuel i rs ms) then 0 else -2.
Proof.
 move: i. induction fuel; move=> i; cbn [bc_validate bc_entries FiniteSystem.validate_loop]; first reflexivity.
 rewrite /bc_bad -/(bc_entry rs ms i). case: (FiniteSystem.validb (bc_entry rs ms i)); cbn; [exact: IHfuel|reflexivity].
Qed.
Lemma bc_validate_success fuel i rs ms : snd (bc_validate fuel i rs ms)=0 ->
 forall j, (i<=j)%coq_nat -> (j<Nat.add i fuel)%coq_nat -> bc_bad rs ms j=false.
Proof.
 move: i. induction fuel; move=> i; cbn [bc_validate].
 - intros; lia.
 - case E:(bc_bad rs ms i); first by cbn; discriminate.
   move=> H j Hlo Hhi. destruct (Nat.eq_dec i j) as [<-|Hneq]; first exact E.
   apply: (IHfuel (S i) H); lia.
Qed.
Lemma bc_pair_row_model fuel i j rs ms :
 snd (bc_pair_row fuel i j rs ms) =
 if FiniteSystem.pair_row (bc_entry rs ms i) (bc_entries fuel j rs ms) then 0 else -1.
Proof.
 move: j. induction fuel; move=> j; cbn [bc_pair_row bc_entries FiniteSystem.pair_row]; first reflexivity.
 rewrite /bc_pair_bad -/(bc_entry rs ms i) -/(bc_entry rs ms j).
 case: (FiniteSystem.compatb (bc_entry rs ms i) (bc_entry rs ms j)); cbn; [exact: IHfuel|reflexivity].
Qed.
Lemma bc_pairs_model fuel i rs ms :
 snd (bc_pairs fuel i rs ms) =
 if FiniteSystem.pair_loop (bc_entries fuel i rs ms) then 0 else -1.
Proof.
 move: i. induction fuel; move=> i; cbn [bc_pairs bc_entries FiniteSystem.pair_loop]; first reflexivity.
 rewrite bc_pair_row_model. case: (FiniteSystem.pair_row (bc_entry rs ms i) (bc_entries fuel (S i) rs ms)); cbn;
 [exact: IHfuel|reflexivity].
Qed.
Lemma bc_entries_nth fuel i rs ms j : (j<fuel)%coq_nat ->
 List.nth_error (bc_entries fuel i rs ms) j = Some (bc_entry rs ms (Nat.add i j)).
Proof.
 move: i j. induction fuel; move=> i j Hj; first lia.
 destruct j; cbn [bc_entries List.nth_error]; first by rewrite Nat.add_0_r.
 rewrite IHfuel; first by rewrite Nat.add_succ_r Nat.add_succ_l. lia.
Qed.
Lemma bc_entries_length fuel i rs ms : List.length (bc_entries fuel i rs ms)=fuel.
Proof. move: i. induction fuel; move=> i; cbn; [reflexivity|by rewrite IHfuel]. Qed.
Lemma bc_entries_valid count rs ms :
 FiniteSystem.validate_loop (bc_entries count 0 rs ms)=true <-> bc_all_valid count rs ms.
Proof.
 split.
 - move=> H. rewrite /bc_all_valid. have E : snd (bc_validate count 0 rs ms)=0 by rewrite bc_validate_status H.
   move=> i Hi. apply: (bc_validate_success E); lia.
 - move=> H. apply validate_loop_spec. apply List.Forall_forall. move=> c Hin.
   apply List.In_nth_error in Hin as [i Hi]. have Hlen : (i<count)%coq_nat.
   { rewrite -(bc_entries_length count 0 rs ms). apply List.nth_error_Some. rewrite Hi. discriminate. }
   have Ei := bc_entries_nth 0%nat rs ms Hlen. rewrite Hi Nat.add_0_l in Ei. inversion Ei; subst c.
   apply validb_spec. have Hv := H i Hlen. rewrite /bc_bad -/(bc_entry rs ms i) in Hv. by apply Bool.negb_false_iff in Hv.
Qed.
