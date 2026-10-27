(* Exact emitted source contracts, realized together in the actual initial store. *)
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import host.
From WasmVerifier Require Import Assertions Semantics Verifier.
From CRTSystems Require Import SystemRuntime SystemSpecModel SystemSpecRealization SystemSpecPayloads.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Host.
Context `{ho : host}.
Theorem checked_helper_contracts : ValidSpec SM.main SM.main__HelperContracts_specs.
Proof. exact: system_helper_contracts_from_realization checked_system_model_realized. Qed.
Theorem checked_public_contracts : ValidSpec SM.main SM.main__PublicContracts_specs.
Proof. exact: system_public_contracts_from_realization checked_system_model_realized. Qed.
Theorem checked_scalar_contracts_shared_runtime :
 interp_realized_at system_initial_runtime system_model_interp /\
 forall V h, val_fun V = system_model_interp ->
 Forall (fun P => hassert_denote V (ktrue P) h) SM.main__HelperContracts_specs /\
 Forall (fun P => hassert_denote V (ktrue P) h) SM.main__PublicContracts_specs.
Proof.
 split; first exact: checked_system_model_realized.
 move=> V h Hpin. split; [exact: system_helper_payloads|exact: system_public_payloads].
Qed.
End Host.
Print Assumptions checked_helper_contracts.
Print Assumptions checked_public_contracts.
Print Assumptions checked_scalar_contracts_shared_runtime.
