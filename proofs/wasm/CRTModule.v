(* Structural typing of the exact generated module. This theorem alone says
   nothing about termination, traps, or the CRT behavioral contracts. *)
From Coq Require Import NArith String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import bytes datatypes operations opsem typing instantiation_spec host.
From WasmVerifier Require Import Assertions Semantics Verifier Automation Activation.
From CRTGenerated Require main.
From CRTWasm Require Import CRTStorePure.

Section Host.
Context `{ho : host}.

Theorem checked_valid_module : ValidModule main.main.
Proof. valid_module. Qed.

Definition crt_pair_type : function_type :=
  Tf [:: T_num T_i64; T_num T_i64] [:: T_num T_i64].
Definition crt_solver_type : function_type :=
  Tf [:: T_num T_i64; T_num T_i64; T_num T_i64; T_num T_i64] [:: T_num T_i64].

Definition crt_inst : moduleinst :=
  Build_moduleinst (mod_types main.main)
    [:: N.of_nat 0; N.of_nat 1; N.of_nat 2; N.of_nat 3; N.of_nat 4]
    [::] [::] [::] [::] [::]
    [:: Build_exportinst (list_byte_of_string "crt_period"%string) (EV_func (N.of_nat 3));
        Build_exportinst (list_byte_of_string "crt_solve"%string) (EV_func (N.of_nat 4))].

Definition crt_store : store_record :=
  Build_store_record
    [:: FC_func_native crt_pair_type crt_inst main.gcd_positive;
        FC_func_native crt_pair_type crt_inst main.normalize;
        FC_func_native crt_pair_type crt_inst main.inverse_coprime;
        FC_func_native crt_pair_type crt_inst main.crt_period;
        FC_func_native crt_solver_type crt_inst main.crt_solve]
    [::] [::] [::] [::] [::].

Lemma crt_allocates :
  alloc_module empty_store main.main [::] [::] [::] (crt_store, crt_inst).
Proof.
  by rewrite /alloc_module /empty_store /crt_store /crt_inst /main.main
    /crt_pair_type /crt_solver_type /main.gcd_positive /main.normalize
    /main.inverse_coprime /main.crt_period /main.crt_solve
    /alloc_funcs /alloc_Xs /alloc_func /add_func /gen_func_instance /=.
Qed.

Lemma crt_runtime_typing : exists expts, module_typing main.main [::] expts.
Proof.
  destruct checked_valid_module as [impts [expts Htyping]].
  assert (Hnil : impts = [::]).
  { pose proof Htyping as Hshape.
    rewrite /module_typing /main.main in Hshape.
    decompose [ex and] Hshape.
    match goal with
    | H : List.Forall2 _ [::] impts |- _ => inversion H; reflexivity
    end. }
  subst impts. by exists expts.
Qed.

Lemma crt_instantiates (hs : host_state) :
  instantiate empty_store main.main [::]
    (crt_store, Build_frame [::] crt_inst, [::]).
Proof.
  destruct crt_runtime_typing as [expts Htyping].
  rewrite /instantiate.
  exists [::], [::], expts, hs, crt_inst, [::], [::].
  split; first exact: Htyping.
  split; first by apply: List.Forall2_nil.
  split; first by apply: List.Forall2_nil.
  split; first exact: crt_allocates.
  rewrite /instantiate_globals /instantiate_elems /main.main /=.
  repeat split; by [].
Qed.

Lemma crt_initializes (hs : host_state) :
  reduce_trans
    (hs, crt_store, Build_frame [::] crt_inst, to_e_list [::])
    (hs, crt_store, Build_frame [::] crt_inst, [::]).
Proof. by rewrite /to_e_list; exact: rtt_refl. Qed.

Definition crt_runtime : module_runtime main.main :=
  {| runtime_store := crt_store;
     runtime_inst := crt_inst;
     runtime_alloc_store := crt_store;
     runtime_init := [::];
     runtime_module_typing := crt_runtime_typing;
     runtime_allocates := ex_intro _ [::] (ex_intro _ [::] crt_allocates);
     runtime_instantiates := crt_instantiates;
     runtime_initializes := crt_initializes |}.

Lemma crt_store_resource_free : crt_resource_free_native_store crt_store.
Proof.
  apply crt_resource_free_of_native_functions. repeat constructor.
Qed.

End Host.

Print Assumptions checked_valid_module.
Print Assumptions crt_runtime.
Print Assumptions crt_store_resource_free.
