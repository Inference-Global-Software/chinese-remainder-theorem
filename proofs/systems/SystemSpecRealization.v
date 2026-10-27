(* Every scalar interpretation claim runs in the same actual initial runtime. *)
From Coq Require Import ZArith NArith Lia Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations host.
From WasmVerifier Require Import Assertions Semantics Activation Verifier.
From CRT Require Import CRTStatements CRTSystemStatements CRTSystemArithmetic.
From CRTWasm Require Import CRTContracts.
From CRTSystems Require Import SystemRuntime FullWidthExecution AddModExecution SystemCalls
 FullWidthInverseExecution MulModExecution MergeSolveExecution MergePeriodExecution SystemSpecModel.
Module SM := CRTSystemGenerated.main.
Import FullWidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.
Lemma system_spec_signed_argument (x : i64) : SM.Vi64 (Wasm_int.Int64.signed x) = VAL_int64 x.
Proof. change (VAL_int64 (Wasm_int.Int64.repr (Wasm_int.Int64.signed x)) = VAL_int64 x). by rewrite Wasm_int.Int64.repr_signed. Qed.
Section Host.
Context `{ho : host}.
Theorem checked_system_model_realized : interp_realized_at system_initial_runtime system_model_interp.
Proof.
 move=> i args rs. rewrite /system_model_interp.
 case: i => [|[|[|[|[|[|[|i]]]]]]] //.
 - case: args => [|[m32|m|mf32|mf64] [|[n32|n|nf32|nf64] args]] //; case: args => [|v args] //.
   case Hg: (sp_moduli_b (Wasm_int.Int64.signed m) (Wasm_int.Int64.signed n)) => //.
   move=> [<-].
   have Hmod := proj1 (sp_moduli_b_spec _ _) Hg.
   apply: fun_computes_at_of_computes.
   + exists SM.gcd_positive. eexists. split; reflexivity.
   + have H := gcd_machine_computes Hmod. by rewrite !system_spec_signed_argument in H.
 - case: args => [|[z32|z|zf32|zf64] [|[d32|d|df32|df64] args]] //; case: args => [|v args] //.
   case Hg: ((1 <=? Wasm_int.Int64.signed d) && (Wasm_int.Int64.signed d <=? MAX)) => //.
   move=> [<-].
   apply andb_true_iff in Hg. destruct Hg as [Hlo Hhi]. apply Z.leb_le in Hlo,Hhi.
   apply: fun_computes_at_of_computes.
   + exists SM.normalize. eexists. split; reflexivity.
   + have H := normalize_machine_computes (crt_contract_signed_word z) (conj Hlo Hhi).
     by rewrite !system_spec_signed_argument in H.
 - case: args => [|[B32|B|Bf32|Bf64] [|[A32|A|Af32|Af64] args]] //; case: args => [|v args] //.
   case Hg: (sp_inverse_b (Wasm_int.Int64.signed B) (Wasm_int.Int64.signed A)) => //.
   move=> [<-].
   have [Hin Hcop] := proj1 (sp_inverse_b_spec _ _) Hg.
   have H := inverse_machine_computes (ho:=ho) system_initial_memory Hin Hcop.
   rewrite !system_spec_signed_argument in H. exact (@SystemCalls.system_computes_initial hfc memory ho system_initial_memory _ _ _ H Logic.eq_refl).
 - case: args => [|[x32|x|xf32|xf64] [|[y32|y|yf32|yf64] [|[d32|d|df32|df64] args]]] //; case: args => [|v args] //.
   case Hg: (sp_mod_b (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed d)) => //.
   move=> [<-].
   have [Hd [Hx Hy]] := proj1 (sp_mod_b_spec _ _ _) Hg.
   apply: fun_computes_at_of_computes.
   + exists SM.add_mod. eexists. split; reflexivity.
   + have H := add_mod_machine_computes Hd Hx Hy. by rewrite !system_spec_signed_argument in H.
 - case: args => [|[x32|x|xf32|xf64] [|[y32|y|yf32|yf64] [|[d32|d|df32|df64] args]]] //; case: args => [|v args] //.
   case Hg: (sp_mod_b (Wasm_int.Int64.signed x) (Wasm_int.Int64.signed y) (Wasm_int.Int64.signed d)) => //.
   move=> [<-].
   have [Hd [Hx Hy]] := proj1 (sp_mod_b_spec _ _ _) Hg.
   have H := mul_mod_machine_computes (ho:=ho) system_initial_memory Hd Hx Hy.
   rewrite !system_spec_signed_argument in H. exact (@SystemCalls.system_computes_initial hfc memory ho system_initial_memory _ _ _ H Logic.eq_refl).
 - case: args => [|[a32|a|af32|af64] [|[m32|m|mf32|mf64] [|[b32|b|bf32|bf64] [|[n32|n|nf32|nf64] args]]]] //; case: args => [|v args] //.
   move=> [<-].
   have H := merge_solve_machine_computes (ho:=ho) system_initial_memory
     (crt_contract_signed_word a) (crt_contract_signed_word m) (crt_contract_signed_word b) (crt_contract_signed_word n).
   rewrite !system_spec_signed_argument in H. exact (@SystemCalls.system_computes_initial hfc memory ho system_initial_memory _ _ _ H Logic.eq_refl).
 - case: args => [|[a32|a|af32|af64] [|[m32|m|mf32|mf64] [|[b32|b|bf32|bf64] [|[n32|n|nf32|nf64] args]]]] //; case: args => [|v args] //.
   move=> [<-].
   have H := merge_period_machine_computes (ho:=ho) system_initial_memory
     (crt_contract_signed_word a) (crt_contract_signed_word m) (crt_contract_signed_word b) (crt_contract_signed_word n).
   rewrite !system_spec_signed_argument in H. exact (@SystemCalls.system_computes_initial hfc memory ho system_initial_memory _ _ _ H Logic.eq_refl).
Qed.
End Host.
Print Assumptions checked_system_model_realized.
