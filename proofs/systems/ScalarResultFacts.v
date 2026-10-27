(* Range and classification facts for the complete scalar mathematical result. *)
From Coq Require Import ZArith Lia List.
From CRT Require Import CRTStatements CRTSystemStatements CRTSystemArithmetic CRTFinite.
Import FullWidth FiniteSystem.
Open Scope Z_scope.
Lemma scalar_result_values_word a m b n :
 word (solve_value (merge a m b n)) /\ word (period_value (merge a m b n)).
Proof.
 pose proof (scalar_model_proved a m b n) as H.
 destruct (merge a m b n) as [| | |r p]; cbn in *.
 - unfold word,i64_min,i64_max; lia.
 - unfold word,i64_min,i64_max; lia.
 - unfold word,i64_min,i64_max; lia.
 - destruct H as [_ [_ [Hp [HL [Hr Hsol]]]]]. split; apply nonnegative_word; lia.
Qed.
