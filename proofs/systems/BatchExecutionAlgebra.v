(* Transfer helpers: the refinement premises must be discharged by concrete
   compiled batch execution theorems in the final closed public targets. *)
From Coq Require Import ZArith NArith Lia List Bool Sorting.Permutation.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations opsem properties host.
From CRT Require Import CRTStatements CRTSystemStatements CRTSystemArithmetic CRTFinite.
From CRTSystems Require Import SystemRuntime SystemMemory SystemExecutionBridge ScalarExecutionTargets BatchClassModel.
Module SM := CRTSystemGenerated.main.
Import FullWidth FiniteSystem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Definition be_active c rs ms := bc_entries (Z.to_nat c) 0 rs ms.
Definition be_batch_result c rs ms :=
 if (0 <=? c) && (c <=? 16) then system_model (be_active c rs ms) else Invalid.
Definition be_args rb mb c := [::SM.Vi32 (Z.of_N rb);SM.Vi32 (Z.of_N mb);SM.Vi32 c].
Lemma be_result_count c rs ms : 0<=c<=16 -> be_batch_result c rs ms = system_model (be_active c rs ms).
Proof.
 move=> H. rewrite /be_batch_result. have E : ((0<=?c)&&(c<=?16))=true by apply Bool.andb_true_iff; split; apply Z.leb_le; lia. by rewrite E.
Qed.
Lemma be_result_permutation c ra ma rb mb :
 Permutation (be_active c ra ma) (be_active c rb mb) ->
 be_batch_result c ra ma = be_batch_result c rb mb.
Proof.
 move=> H. rewrite /be_batch_result. case: ((0<=?c)&&(c<=?16)); last reflexivity. exact: permutation_proved.
Qed.
Lemma be_success_observed c rs ms r p :
 r=solve_value (be_batch_result c rs ms) -> p=period_value (be_batch_result c rs ms) -> 0<=r ->
 be_batch_result c rs ms = Success r p /\ 0<=c<=16 /\
 valid (be_active c rs ms) /\ p<=MAX /\ Rep (be_active c rs ms) r p.
Proof.
 move=> Er Ep Hr.
 have E : be_batch_result c rs ms = Success r p.
 { destruct (be_batch_result c rs ms) as [| | |r' p'] eqn:E; cbn in Er,Ep; try lia. by subst r p. }
 have Hcount : 0<=c<=16.
 { move: E. rewrite /be_batch_result. case Ec: ((0<=?c)&&(c<=?16)); last discriminate.
   apply Bool.andb_true_iff in Ec as [H0 H16]. apply Z.leb_le in H0. apply Z.leb_le in H16. lia. }
 have Hpost := finite_model_proved (be_active c rs ms).
 rewrite -(be_result_count rs ms Hcount) E in Hpost.
 case: Hpost => [HV [_ [HP HR]]]. split; first exact E. split; first exact Hcount. by split; [|split].
Qed.
Lemma be_model_composition ca ra ma cb rb mb r p s q :
 r=solve_value (be_batch_result ca ra ma) -> p=period_value (be_batch_result ca ra ma) -> 0<=r ->
 s=solve_value (be_batch_result cb rb mb) -> q=period_value (be_batch_result cb rb mb) -> 0<=s ->
 merge r p s q = system_model (be_active ca ra ma ++ be_active cb rb mb).
Proof.
 move=> Er Ep Hr Es Eq Hs.
 have [_ [_ [HA [Hp HR]]]] := be_success_observed Er Ep Hr.
 have [_ [_ [HB [Hq HS]]]] := be_success_observed Es Eq Hs.
 apply: (result_post_unique (be_active ca ra ma ++ be_active cb rb mb)).
 - exact: (merge_composition_proved _ _ r p s q HA HB HR HS Hp Hq).
 - exact: finite_model_proved.
Qed.
Section Host.
Context `{ho:host}.
Definition be_refines mem hs rb mb c rs ms :=
 (forall r, system_run mem hs 8%num (be_args rb mb c) r -> r=solve_value (be_batch_result c rs ms)) /\
 (forall p, system_run mem hs 9%num (be_args rb mb c) p -> p=period_value (be_batch_result c rs ms)).
Lemma be_execution_permutation memA memB hsA hsB ptrRA ptrMA ptrRB ptrMB c rsA msA rsB msB rA pA rB pB :
 be_refines memA hsA ptrRA ptrMA c rsA msA -> be_refines memB hsB ptrRB ptrMB c rsB msB ->
 Permutation (be_active c rsA msA) (be_active c rsB msB) ->
 system_run memA hsA 8%num (be_args ptrRA ptrMA c) rA -> system_run memA hsA 9%num (be_args ptrRA ptrMA c) pA ->
 system_run memB hsB 8%num (be_args ptrRB ptrMB c) rB -> system_run memB hsB 9%num (be_args ptrRB ptrMB c) pB ->
 rA=rB /\ pA=pB.
Proof.
 move=> [Ar Ap] [Br Bp] HP HAr HAp HBr HBp.
 have E := be_result_permutation HP. rewrite (Ar _ HAr) (Br _ HBr) (Ap _ HAp) (Bp _ HBp) E. by split.
Qed.
Lemma be_execution_success mem hs ptrR ptrM c rs ms r p :
 be_refines mem hs ptrR ptrM c rs ms ->
 system_run mem hs 8%num (be_args ptrR ptrM c) r -> system_run mem hs 9%num (be_args ptrR ptrM c) p ->
 0<=r -> 0<=c<=16 /\ valid (be_active c rs ms) /\ p<=MAX /\ Rep (be_active c rs ms) r p.
Proof.
 move=> [Hs Hp] Hr Hperiod Hnonneg. have [_ H] := be_success_observed (Hs _ Hr) (Hp _ Hperiod) Hnonneg. exact H.
Qed.
Lemma be_execution_composition_model memA memB hsA hsB ptrRA ptrMA ptrRB ptrMB ca cb rsA msA rsB msB r p s q :
 be_refines memA hsA ptrRA ptrMA ca rsA msA -> be_refines memB hsB ptrRB ptrMB cb rsB msB ->
 system_run memA hsA 8%num (be_args ptrRA ptrMA ca) r -> system_run memA hsA 9%num (be_args ptrRA ptrMA ca) p ->
 system_run memB hsB 8%num (be_args ptrRB ptrMB cb) s -> system_run memB hsB 9%num (be_args ptrRB ptrMB cb) q ->
 0<=r -> 0<=s ->
 merge r p s q = system_model (be_active ca rsA msA ++ be_active cb rsB msB).
Proof.
 move=> [Ar Ap] [Br Bp] HAr HAp HBr HBp Hr Hs.
 exact: (be_model_composition (Ar _ HAr) (Ap _ HAp) Hr (Br _ HBr) (Bp _ HBp) Hs).
Qed.
Lemma be_execution_composition memA memB memM hsA hsB hsM ptrRA ptrMA ptrRB ptrMB ca cb rsA msA rsB msB r p s q :
 be_refines memA hsA ptrRA ptrMA ca rsA msA -> be_refines memB hsB ptrRB ptrMB cb rsB msB ->
 system_run memA hsA 8%num (be_args ptrRA ptrMA ca) r -> system_run memA hsA 9%num (be_args ptrRA ptrMA ca) p ->
 system_run memB hsB 8%num (be_args ptrRB ptrMB cb) s -> system_run memB hsB 9%num (be_args ptrRB ptrMB cb) q ->
 0<=r -> 0<=s ->
 total_correct (system_run memM hsM 5%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q])
 (fun x => x=solve_value (system_model (be_active ca rsA msA ++ be_active cb rsB msB)) /\
 result_post (be_active ca rsA msA ++ be_active cb rsB msB) (system_model (be_active ca rsA msA ++ be_active cb rsB msB))) /\
 total_correct (system_run memM hsM 6%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q])
 (fun x => x=period_value (system_model (be_active ca rsA msA ++ be_active cb rsB msB)) /\
 result_post (be_active ca rsA msA ++ be_active cb rsB msB) (system_model (be_active ca rsA msA ++ be_active cb rsB msB))).
Proof.
 move=> HA HB HAr HAp HBr HBp Hr Hs.
 have E := be_execution_composition_model HA HB HAr HAp HBr HBp Hr Hs.
 have Wr := system_run_word HAr. have Wp := system_run_word HAp.
 have Ws := system_run_word HBr. have Wq := system_run_word HBp.
 split.
 - apply: (system_run_total_correct (result:=solve_value (merge r p s q))).
   + exact: system_merge_solve_exec_exists.
   + split; [by rewrite E|exact: finite_model_proved].
 - apply: (system_run_total_correct (result:=period_value (merge r p s q))).
   + exact: system_merge_period_exec_exists.
   + split; [by rewrite E|exact: finite_model_proved].
Qed.
Lemma be_execution_concat memA memB memC memM hsA hsB hsC hsM ptrRA ptrMA ptrRB ptrMB ptrRC ptrMC ca cb cc rsA msA rsB msB rsC msC r p s q xM pM xC pC :
 be_refines memA hsA ptrRA ptrMA ca rsA msA -> be_refines memB hsB ptrRB ptrMB cb rsB msB ->
 be_refines memC hsC ptrRC ptrMC cc rsC msC -> 0<=cc<=16 ->
 Permutation (be_active ca rsA msA ++ be_active cb rsB msB) (be_active cc rsC msC) ->
 system_run memA hsA 8%num (be_args ptrRA ptrMA ca) r -> system_run memA hsA 9%num (be_args ptrRA ptrMA ca) p ->
 system_run memB hsB 8%num (be_args ptrRB ptrMB cb) s -> system_run memB hsB 9%num (be_args ptrRB ptrMB cb) q ->
 0<=r -> 0<=s ->
 system_run memM hsM 5%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q] xM ->
 system_run memM hsM 6%num [::SM.Vi64 r;SM.Vi64 p;SM.Vi64 s;SM.Vi64 q] pM ->
 system_run memC hsC 8%num (be_args ptrRC ptrMC cc) xC -> system_run memC hsC 9%num (be_args ptrRC ptrMC cc) pC ->
 xM=xC /\ pM=pC.
Proof.
 move=> HA HB [Cr Cp] Hcount Hperm HAr HAp HBr HBp Hr Hs HMx HMp HCx HCp.
 have [HMsolve HMperiod] := be_execution_composition memM hsM HA HB HAr HAp HBr HBp Hr Hs.
 have [_ [EMx _]] := proj2 HMsolve _ HMx. have [_ [EMp _]] := proj2 HMperiod _ HMp.
 have Ecx := Cr _ HCx. have Ecp := Cp _ HCp.
 rewrite (be_result_count rsC msC Hcount) in Ecx Ecp.
 have E := permutation_proved _ _ Hperm. rewrite EMx EMp Ecx Ecp E. by split.
Qed.
End Host.
