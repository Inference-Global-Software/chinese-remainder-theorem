(* Normal-result uniqueness for actual WasmCert reductions. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host.
From CRTWasm Require Import CRTStorePure CRTExecutionComposition CRTDirectFlatJoin.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Theorem crt_reduce_trans_normal_unique hs s f es hs1 s1 f1 vs1 hs2 s2 f2 vs2 :
  crt_resource_free_native_store s ->
  reduce_trans (hs, s, f, es) (hs1, s1, f1, v_to_e_list vs1) ->
  reduce_trans (hs, s, f, es) (hs2, s2, f2, v_to_e_list vs2) -> vs1 = vs2.
Proof.
  intros HP H1 H2.
  exact (crt_reduce_trans_unique_from_flat crt_direct_flat_join HP H1 H2).
Qed.

End Host.

Print Assumptions crt_reduce_trans_normal_unique.
