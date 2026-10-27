(* Closed signatures for the infrastructure gate; no public CRT correctness
   claim is made by these operational targets. *)
From Coq Require Import NArith ZArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host.
From WasmVerifier Require Import Semantics Activation Verifier.
From CRTSystemGenerated Require main.
From CRTSystems Require Import ReadOnly ReadOnlyConfluence SystemRuntime SystemMemory SystemArrayExecution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Host.
Context `{ho : host}.

Theorem exact_initial_runtime : module_runtime main.main.
Proof. exact: system_initial_runtime. Qed.

Theorem exact_system_valid_module : ValidModule main.main.
Proof. exact: system_valid_module. Qed.

Theorem exact_system_store_readonly mem : ro_store (system_store mem).
Proof. exact: system_store_readonly. Qed.

Theorem exact_ro_reduce_trans_preserved hs s f es hs' s' f' es' :
  ro_store s -> ro_es es ->
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  hs' = hs /\ s' = s /\ ro_es es'.
Proof. exact: ro_reduce_trans_preserved. Qed.

Theorem exact_ro_reduce_trans_normal_unique hs s f es hs1 s1 f1 vs1 hs2 s2 f2 vs2 :
  ro_store s -> ro_es es ->
  reduce_trans (hs, s, f, es) (hs1, s1, f1, v_to_e_list vs1) ->
  reduce_trans (hs, s, f, es) (hs2, s2, f2, v_to_e_list vs2) -> vs1 = vs2.
Proof. exact: ro_reduce_trans_normal_unique. Qed.

Theorem exact_system_inputs_inhabited residues moduli :
  size residues = 16%nat -> size moduli = 16%nat ->
  exists m, system_input_memory m 0%num 128%num residues moduli.
Proof. exact: system_inputs_inhabited. Qed.

Theorem exact_classifier_read_exec hs m f base xs i x :
  f_inst f = system_inst -> array_region m base xs ->
  List.nth_error xs i = Some x ->
  lookup_N (f_locs f) 7%num = Some (VAL_num (main.Vi32 (Z.of_nat i))) ->
  reduce_trans
    (hs,system_store m,f,
      vn_to_e [::main.Vi32 (Z.of_N base); main.Vi32 (Z.of_nat i)] ++
      to_e_list classifier_read_slice)
    (hs,system_store m,f,[::AI_basic (BI_const_num (VAL_int64 x))]).
Proof. exact: classifier_read_exec. Qed.

Theorem exact_classifier_read_all_normal hs m f base xs i x hs' s' f' vs :
  f_inst f = system_inst -> array_region m base xs ->
  List.nth_error xs i = Some x ->
  lookup_N (f_locs f) 7%num = Some (VAL_num (main.Vi32 (Z.of_nat i))) ->
  reduce_trans
    (hs,system_store m,f,
      vn_to_e [::main.Vi32 (Z.of_N base); main.Vi32 (Z.of_nat i)] ++
      to_e_list classifier_read_slice) (hs',s',f',v_to_e_list vs) ->
  vs = [::VAL_num (VAL_int64 x)].
Proof. exact: classifier_read_all_normal. Qed.

End Host.
