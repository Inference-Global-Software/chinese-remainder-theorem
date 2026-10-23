(* Complete certificates for the exact compiler-emitted CRT module and source
   contracts. Every application in the interpretation is backed by a checked
   execution of its actual Wasm body in the same instantiated runtime. *)
From Coq Require Import ZArith NArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes numerics operations host.
From WasmVerifier Require Import Assertions Semantics Activation Verifier.
From CRT Require Import CRTStatements.
From CRTGenerated Require Import crt.
From CRTWasm Require Import CRTAPIModel CRTContracts CRTModule CRTExecution
  CRTInverseExecution CRTPublicExecution CRTSolveExecution CRTSpecPayloads.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma crt_signed_argument (x : i64) :
  crt.Vi64 (Wasm_int.Int64.signed x) = VAL_int64 x.
Proof.
  change (VAL_int64 (Wasm_int.Int64.repr (Wasm_int.Int64.signed x)) = VAL_int64 x).
  by rewrite Wasm_int.Int64.repr_signed.
Qed.

Section Host.
Context `{ho : host}.

Theorem checked_model_realized : interp_realized_at crt_runtime crt_model_interp.
Proof.
  apply: crt_model_realized_from_execution.
  - move=> m n Hmod.
    apply: fun_computes_at_of_computes.
    + exists crt.gcd_positive. eexists. split; reflexivity.
    + have H := gcd_machine_computes Hmod.
      by rewrite !crt_signed_argument in H.
  - move=> z d Hd.
    apply: fun_computes_at_of_computes.
    + exists crt.normalize. eexists. split; reflexivity.
    + have H := normalize_machine_computes (crt_contract_signed_word z) Hd.
      by rewrite !crt_signed_argument in H.
  - move=> b a Hin Hcop.
    have H := inverse_machine_computes Hin Hcop.
    by rewrite !crt_signed_argument in H.
  - exact: period_machine_computes_i64.
  - exact: solve_machine_computes_i64.
Qed.

Theorem checked_helper_contracts :
  ValidSpec crt.crt crt.crt__HelperContracts_specs.
Proof. exact: crt_helper_contracts_from_realization checked_model_realized. Qed.

Theorem checked_public_contracts :
  ValidSpec crt.crt crt.crt__PublicContracts_specs.
Proof. exact: crt_public_contracts_from_realization checked_model_realized. Qed.

Theorem checked_crt_certificate :
  ValidModule crt.crt /\
  ValidSpec crt.crt crt.crt__HelperContracts_specs /\
  ValidSpec crt.crt crt.crt__PublicContracts_specs.
Proof.
  split; first exact: checked_valid_module.
  split; [exact: checked_helper_contracts | exact: checked_public_contracts].
Qed.

End Host.

Print Assumptions checked_model_realized.
Print Assumptions checked_helper_contracts.
Print Assumptions checked_public_contracts.
Print Assumptions checked_crt_certificate.
