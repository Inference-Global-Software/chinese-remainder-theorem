From Coq Require Import NArith ZArith String List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import bytes datatypes operations opsem typing instantiation_spec host.
From WasmVerifier Require Import Assertions Semantics Verifier Automation Activation.
From CRTSystemGenerated Require main.
From CRTSystems Require Import ReadOnly ReadOnlyConfluence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Host.
Context `{ho : host}.

Theorem system_valid_module : ValidModule main.main.
Proof. valid_module. Qed.

Definition system_inst : moduleinst :=
  Build_moduleinst (mod_types main.main)
    [::0%num;1%num;2%num;3%num;4%num;5%num;6%num;7%num;8%num;9%num]
    [::] [::0%num] [::0%num] [::] [::]
    [::Build_exportinst (list_byte_of_string "crt_merge_solve"%string) (EV_func 5%num);
       Build_exportinst (list_byte_of_string "crt_merge_period"%string) (EV_func 6%num);
       Build_exportinst (list_byte_of_string "crt_system_solve"%string) (EV_func 8%num);
       Build_exportinst (list_byte_of_string "crt_system_period"%string) (EV_func 9%num);
       Build_exportinst (list_byte_of_string "memory"%string) (EV_mem 0%num);
       Build_exportinst (list_byte_of_string "__stack_pointer"%string) (EV_global 0%num)].

Definition system_functions := map (fun fd => gen_func_instance fd system_inst)
  (mod_funcs main.main).
Definition system_store (mem : meminst) : store_record :=
  Build_store_record system_functions [::] [::mem]
    [::Build_globalinst {| tg_mut := MUT_var; tg_t := T_num T_i32 |}
        (VAL_num (main.Vi32 65536))] [::] [::].
Definition system_initial_memory : meminst :=
  gen_mem_instance (Build_limits 1%num (Some 1%num)).

Lemma system_allocates :
  alloc_module empty_store main.main [::] [::VAL_num (main.Vi32 65536)] [::]
    (system_store system_initial_memory, system_inst).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma system_runtime_typing : exists expts, module_typing main.main [::] expts.
Proof.
  destruct system_valid_module as [impts [expts Htyping]].
  assert (Hnil : impts = [::]).
  { pose proof Htyping as Hshape.
    rewrite /module_typing /main.main in Hshape.
    decompose [ex and] Hshape.
    match goal with H : List.Forall2 _ [::] impts |- _ => inversion H; reflexivity end. }
  subst impts. by exists expts.
Qed.

Lemma system_instantiates (hs : host_state) :
  instantiate empty_store main.main [::]
    (system_store system_initial_memory, Build_frame [::] system_inst, [::]).
Proof.
  destruct system_runtime_typing as [expts Htyping].
  rewrite /instantiate.
  exists [::], [::], expts, hs, system_inst, [::VAL_num (main.Vi32 65536)], [::].
  split; first exact Htyping.
  split; first by constructor.
  split; first by constructor.
  split; first exact system_allocates.
  split.
  - rewrite /instantiate_globals /main.main /=.
    constructor; last constructor. apply rtt_refl.
  - rewrite /instantiate_elems /main.main /=. repeat split; by [].
Qed.

Definition system_initial_runtime : module_runtime main.main :=
  {| runtime_store := system_store system_initial_memory;
     runtime_inst := system_inst;
     runtime_alloc_store := system_store system_initial_memory;
     runtime_init := [::];
     runtime_module_typing := system_runtime_typing;
     runtime_allocates := ex_intro _ [::VAL_num (main.Vi32 65536)]
       (ex_intro _ [::] system_allocates);
     runtime_instantiates := system_instantiates;
     runtime_initializes := fun hs => rtt_refl _ |}.

Lemma system_store_readonly mem : ro_store (system_store mem).
Proof.
  intros addr fi Hlookup.
  have Hfs : List.Forall
    (fun f => match f with
      | FC_func_native _ _ def => is_true (all ro_bi (modfunc_body def))
      | FC_func_host _ _ => False end) system_functions.
  { vm_compute. repeat constructor. }
  rewrite List.Forall_forall in Hfs. apply Hfs.
  apply List.nth_error_In with (n:=N.to_nat addr).
  exact Hlookup.
Qed.

Definition system_run (mem : meminst) (hs : host_state) (idx : N)
    (args : seq value_num) (result : Z) : Prop :=
  exists hs' s' f' (v : i64),
    reduce_trans
      (hs, system_store mem, Build_frame [::] system_inst,
       vn_to_e args ++ [::AI_basic (BI_call idx)])
      (hs', s', f', [::AI_basic (BI_const_num (VAL_int64 v))]) /\
    result = Wasm_int.Int64.signed v.

Lemma system_run_unique mem hs idx args r1 r2 :
  system_run mem hs idx args r1 -> system_run mem hs idx args r2 -> r1=r2.
Proof.
  move=> [h1 [s1 [f1 [v1 [H1 ->]]]]] [h2 [s2 [f2 [v2 [H2 ->]]]]].
  have Hro : ro_es (vn_to_e args ++ [::AI_basic (BI_call idx)]).
  { rewrite ro_es_cat. apply/andP; split; last reflexivity.
    clear - args hfc memory ho.
    induction args as [|v args IH]; simpl; [reflexivity|exact IH]. }
  have HE := ro_reduce_trans_normal_unique
    (vs1:=[::VAL_num (VAL_int64 v1)]) (vs2:=[::VAL_num (VAL_int64 v2)])
    (system_store_readonly (mem:=mem)) Hro H1 H2.
  inversion HE. reflexivity.
Qed.

End Host.
