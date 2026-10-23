(* Empty resource vectors exclude successful reads in every reachable store. *)
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations host.
From CRTWasm Require Import CRTStorePure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Lemma crt_empty_sglob_val s inst idx :
  crt_resource_free_native_store s -> sglob_val s inst idx = None.
Proof.
  move=> HP. rewrite /sglob_val /sglob /sglob_ind
    (crt_empty_globals HP).
  destruct (lookup_N (inst_globals inst) idx); simpl; rewrite ?crt_lookup_N_nil; reflexivity.
Qed.

Lemma crt_empty_smem s inst :
  crt_resource_free_native_store s -> smem s inst = None.
Proof.
  move=> HP. rewrite /smem /smem_ind (crt_empty_memories HP).
  destruct (lookup_N (inst_mems inst) N0); simpl; rewrite ?crt_lookup_N_nil; reflexivity.
Qed.

Lemma crt_empty_stab s inst idx :
  crt_resource_free_native_store s -> stab s inst idx = None.
Proof.
  move=> HP. rewrite /stab /stab_ind (crt_empty_tables HP).
  destruct (lookup_N (inst_tables inst) idx); simpl; rewrite ?crt_lookup_N_nil; reflexivity.
Qed.

Lemma crt_empty_stab_elem s inst idx elem :
  crt_resource_free_native_store s -> stab_elem s inst idx elem = None.
Proof.
  move=> HP. rewrite /stab_elem (crt_empty_tables HP).
  destruct (lookup_N (inst_tables inst) idx); simpl; rewrite ?crt_lookup_N_nil; reflexivity.
Qed.

Lemma crt_empty_selem s inst idx :
  crt_resource_free_native_store s -> selem s inst idx = None.
Proof.
  move=> HP. rewrite /selem (crt_empty_elements HP).
  destruct (lookup_N (inst_elems inst) idx); simpl; rewrite ?crt_lookup_N_nil; reflexivity.
Qed.

Lemma crt_empty_sdata s inst idx :
  crt_resource_free_native_store s -> sdata s inst idx = None.
Proof.
  move=> HP. rewrite /sdata (crt_empty_data HP).
  destruct (lookup_N (inst_datas inst) idx); simpl; rewrite ?crt_lookup_N_nil; reflexivity.
Qed.

End Host.
