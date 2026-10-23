(* Direct WasmCert reductions, before enclosing label and frame contexts.
   Constructors adapted from WasmCert 2.2.0 opsem.v, commit
   0fd83fa708922721132b6d6737179568d1f1d553.
   Copyright 2019–2024 Martin Bodin, Philippa Gardner, Jean Pichon,
   Xiaojia Rao, Conrad Watt. See LICENSE.wasmcert for the MIT license. *)
From Coq Require Import ZArith NArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import datatypes operations opsem host properties.
From CRTWasm Require Import CRTStorePure CRTResourceReads
  CRTExecutionContexts CRTSimpleDeterminism CRTCallInversion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Inductive crt_direct_reduce : host_state -> store_record -> frame -> list administrative_instruction ->
                   host_state -> store_record -> frame -> list administrative_instruction -> Prop :=
  | cdr_simple :
      forall e e' s f hs,
        reduce_simple e e' ->
        crt_direct_reduce hs s f e hs s f e'
  | cdr_ref_func:
    forall hs s f addr x,
      lookup_N f.(f_inst).(inst_funcs) x = Some addr ->
      crt_direct_reduce hs s f [::AI_basic (BI_ref_func x)] hs s f [::AI_ref addr]
  | cdr_block :
    forall hs s f vs es n m tb t1s t2s,
      expand f.(f_inst) tb = Some (Tf t1s t2s) ->
      const_list vs ->
      length vs = n ->
      length t1s = n ->
      length t2s = m ->
      crt_direct_reduce hs s f (vs ++ [::AI_basic (BI_block tb es)]) hs s f [::AI_label m [::] (vs ++ to_e_list es)]
  | cdr_loop :
      forall hs s f vs es n m tb t1s t2s,
      expand f.(f_inst) tb = Some (Tf t1s t2s) ->
      const_list vs ->
      length vs = n ->
      length t1s = n ->
      length t2s = m ->
      crt_direct_reduce hs s f (vs ++ [::AI_basic (BI_loop tb es)]) hs s f [::AI_label n [::AI_basic (BI_loop tb es)] (vs ++ to_e_list es)]
  (** calling operations **)
  | cdr_call :
      forall s f (i: funcidx) a hs,
        lookup_N f.(f_inst).(inst_funcs) i = Some a ->
        crt_direct_reduce hs s f [::AI_basic (BI_call i)] hs s f [::AI_invoke a]
  | cdr_call_indirect_success :
      forall s f x (y: typeidx) a cl i hs,
        stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = Some (VAL_ref_func a) ->
        lookup_N s.(s_funcs) a = Some cl ->
        lookup_N f.(f_inst).(inst_types) y = Some (cl_type cl) ->
        crt_direct_reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_invoke a]
  | cdr_call_indirect_failure_mismatch :
      forall s f x (y: typeidx) a cl i hs,
        stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = Some (VAL_ref_func a) ->
        lookup_N s.(s_funcs) a = Some cl ->
        lookup_N f.(f_inst).(inst_types) y <> Some (cl_type cl) ->
        crt_direct_reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_trap]
  | cdr_call_indirect_failure_bound :
      forall s f x (y: typeidx) i hs,
        stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = None ->
        crt_direct_reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_trap]
  | cdr_call_indirect_failure_null_ref :
      forall s f x (y: typeidx) i hs t,
        stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = Some (VAL_ref_null t) ->
        crt_direct_reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_trap]
(* https://webassembly.github.io/tail-call/core/exec/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-return-call-x *)
  | cdr_return_call :
      forall s f i a hs,
        reduce hs s f [::AI_basic (BI_call i)] hs s f [::AI_invoke a] ->
        crt_direct_reduce hs s f [::AI_basic (BI_return_call i)] hs s f [::AI_return_invoke a]

  (* https://webassembly.github.io/tail-call/core/exec/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-return-call-indirect-x-y *)
  | cdr_return_call_indirect_success :
      forall s f x y a v hs,
        reduce hs s f [::v_to_e v; AI_basic (BI_call_indirect x y)] hs s f [::AI_invoke a] ->
        crt_direct_reduce hs s f [::v_to_e v; AI_basic (BI_return_call_indirect x y)] hs s f [::AI_return_invoke a]
  | cdr_return_call_indirect_failure :
      forall s f x y v hs,
        reduce hs s f [::v_to_e v; AI_basic (BI_call_indirect x y)] hs s f [::AI_trap] ->
        crt_direct_reduce hs s f [::v_to_e v; AI_basic (BI_return_call_indirect x y)] hs s f [::AI_trap]

  | cdr_invoke_native :
      forall addr cl ts1 ts2 code x ts es ves vs n m k defaults s f inst hs,
        lookup_N s.(s_funcs) addr = Some cl ->
        cl = FC_func_native (Tf ts1 ts2) inst code ->
        code = Build_module_func x ts es ->
        ves = v_to_e_list vs ->
        length vs = n ->
        length ts = k ->
        length ts1 = n ->
        length ts2 = m ->
        default_vals ts = Some defaults ->
        crt_direct_reduce hs s f (ves ++ [::AI_invoke addr]) hs s f [::AI_frame m (Build_frame (vs ++ defaults) inst) [::AI_label m [::] (to_e_list es)]]
  | cdr_invoke_host_success :
      forall a cl h t1s t2s ves vcs m n s s' r f hs hs',
        lookup_N s.(s_funcs) a = Some cl ->
        cl = FC_func_host (Tf t1s t2s) h ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        host_application hs s (Tf t1s t2s) h vcs hs' (Some (s', r)) ->
        crt_direct_reduce hs s f (ves ++ [::AI_invoke a]) hs' s' f (result_to_stack r)
  | cdr_invoke_host_diverge :
      forall a cl t1s t2s h ves vcs n m s f hs hs',
        lookup_N s.(s_funcs) a = Some cl ->
        cl = FC_func_host (Tf t1s t2s) h ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        host_application hs s (Tf t1s t2s) h vcs hs' None ->
        crt_direct_reduce hs s f (ves ++ [::AI_invoke a]) hs' s f [::AI_trap]
  (* https://webassembly.github.io/tail-call/core/exec/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-return-call-indirect-x-y *)
  | cdr_return_invoke :
      forall a cl t1s t2s n m vs es i (lh: lholed i) f f0 hs s,
        lookup_N s.(s_funcs) a = Some cl ->
        cl_type cl = Tf t1s t2s ->
        length t1s = n ->
        length t2s = m ->
        const_list vs ->
        length vs = n ->
        lfill lh (vs ++ [::AI_return_invoke a]) = es ->
        crt_direct_reduce hs s f [::AI_frame m f0 es] hs s f (vs ++ [::AI_invoke a])
               
  (** get, set, load, and store operations **)
  | cdr_local_get :
      forall f v j s hs,
        lookup_N f.(f_locs) j = Some v ->
        crt_direct_reduce hs s f [::AI_basic (BI_local_get j)] hs s f [::v_to_e v]
  | cdr_local_set :
      forall f f' i v s vd hs,
        f'.(f_inst) = f.(f_inst) ->
        N.to_nat i < length f.(f_locs) ->
        f'.(f_locs) = set_nth vd f.(f_locs) (N.to_nat i) v ->
        crt_direct_reduce hs s f [::v_to_e v; AI_basic (BI_local_set i)] hs s f' [::]
  | cdr_global_get :
      forall s f i v hs,
        sglob_val s f.(f_inst) i = Some v ->
        crt_direct_reduce hs s f [::AI_basic (BI_global_get i)] hs s f [::v_to_e v]
  | cdr_global_set :
      forall s f i v s' hs,
        supdate_glob s f.(f_inst) i v = Some s' ->
        crt_direct_reduce hs s f [::v_to_e v; AI_basic (BI_global_set i)] hs s' f [::]

(** table **)
| cdr_table_get_success :
  forall x i tabv s f hs,
    stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = Some tabv ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_table_get x)] hs s f [::v_to_e (VAL_ref tabv)]
| cdr_table_get_failure :
  forall x i s f hs,
    stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = None ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_table_get x)] hs s f [::AI_trap]
| cdr_table_set_success :
  forall x i tabv s s' f hs,
    stab_update s f.(f_inst) x (Wasm_int.N_of_uint i32m i) tabv = Some s' ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); AI_basic (BI_table_set x)] hs s' f [::]
| cdr_table_set_failure :
  forall x i tabv s f hs,
    stab_update s f.(f_inst) x (Wasm_int.N_of_uint i32m i) tabv = None ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); AI_basic (BI_table_set x)] hs s f [::AI_trap]
| cdr_table_size :
  forall x tab sz s f hs,
    stab s f.(f_inst) x = Some tab ->
    tab_size tab = sz ->
    crt_direct_reduce hs s f [:: AI_basic (BI_table_size x)] hs s f [::$VN (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat sz)))]
| cdr_table_grow_success :
  forall x n sz tabinit s f s' hs,
    stab_grow s f.(f_inst) x (Wasm_int.N_of_uint i32m n) tabinit = Some (s', sz) ->
    crt_direct_reduce hs s f [::v_to_e (VAL_ref tabinit); $VN (VAL_int32 n); AI_basic (BI_table_grow x)]
      hs s' f [::$VN (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat sz)))]
| cdr_table_grow_failure :
  forall x n tabinit s f hs,
    stab_grow s f.(f_inst) x (Wasm_int.N_of_uint i32m n) tabinit = None ->
    crt_direct_reduce hs s f [::v_to_e (VAL_ref tabinit); $VN (VAL_int32 n); AI_basic (BI_table_grow x)]
      hs s f [::$VN (VAL_int32 int32_minus_one)]
| cdr_table_fill_bound :
  forall x i n tab tabv s f hs,
    let i_z := Wasm_int.Z_of_uint i32m i in
    let n_z := Wasm_int.Z_of_uint i32m n in
    stab s f.(f_inst) x = Some tab ->
    (Z.add i_z n_z > Z.of_nat (tab_size tab))%Z ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); $VN (VAL_int32 n); AI_basic (BI_table_fill x)]
      hs s f [::AI_trap]
| cdr_table_fill_return :
  forall x i n tab tabv s f hs,
    let i_z := Wasm_int.Z_of_uint i32m i in
    let n_z := Wasm_int.Z_of_uint i32m n in
    stab s f.(f_inst) x = Some tab ->
    (Z.add i_z n_z <= Z.of_nat (tab_size tab))%Z ->
    (n_z = 0)%Z ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); $VN (VAL_int32 n); AI_basic (BI_table_fill x)]
      hs s f [::]
| cdr_table_fill_step :
  forall x i n tab tabv n' i' s f hs,
    let i_z := Wasm_int.Z_of_uint i32m i in
    let n_z := Wasm_int.Z_of_uint i32m n in
    stab s f.(f_inst) x = Some tab ->
    (Z.add i_z n_z <= Z.of_nat (tab_size tab))%Z ->
    (n_z <> 0)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    i' = Wasm_int.int_of_Z i32m (Z.add i_z 1) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); $VN (VAL_int32 n); AI_basic (BI_table_fill x)]
      hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); AI_basic (BI_table_set x);
              $VN (VAL_int32 i'); v_to_e (VAL_ref tabv); $VN (VAL_int32 n'); AI_basic (BI_table_fill x)]
| cdr_table_copy_bound :
  forall x y src dst n tabx taby s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tabx ->
    stab s f.(f_inst) y = Some taby ->
    ((src_z + n_z > Z.of_nat (tab_size taby))%Z \/
     (dst_z + n_z > Z.of_nat (tab_size tabx))%Z) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_copy x y)]
      hs s f [::AI_trap]
| cdr_table_copy_return :
  forall x y src dst n tabx taby s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tabx ->
    stab s f.(f_inst) y = Some taby ->
    (src_z + n_z <= Z.of_nat (tab_size taby))%Z ->
    (dst_z + n_z <= Z.of_nat (tab_size tabx))%Z ->
    (n_z = 0)%Z ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_copy x y)]
      hs s f [::]
| cdr_table_copy_forward :
  forall x y src dst n tabx taby src' dst' n' s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tabx ->
    stab s f.(f_inst) y = Some taby ->
    (src_z + n_z <= Z.of_nat (tab_size taby))%Z ->
    (dst_z + n_z <= Z.of_nat (tab_size tabx))%Z ->
    (n_z <> 0)%Z ->
    (dst_z <= src_z)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.add src_z 1) ->
    dst' = Wasm_int.int_of_Z i32m (Z.add dst_z 1) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_copy x y)]
      hs s f [:: $VN (VAL_int32 dst); $VN (VAL_int32 src); AI_basic (BI_table_get y); AI_basic (BI_table_set x);
              $VN (VAL_int32 dst'); $VN (VAL_int32 src'); $VN (VAL_int32 n'); AI_basic (BI_table_copy x y)]
| cdr_table_copy_backward :
  forall x y src dst n tabx taby src' dst' n' s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tabx ->
    stab s f.(f_inst) y = Some taby ->
    (src_z + n_z <= Z.of_nat (tab_size taby))%Z ->
    (dst_z + n_z <= Z.of_nat (tab_size tabx))%Z ->
    (n_z <> 0)%Z ->
    (dst_z > src_z)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.sub (Z.add src_z n_z) 1) ->
    dst' = Wasm_int.int_of_Z i32m (Z.sub (Z.add dst_z n_z) 1) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_copy x y)]
      hs s f [:: $VN (VAL_int32 dst'); $VN (VAL_int32 src'); AI_basic (BI_table_get y); AI_basic (BI_table_set x);
              $VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n'); AI_basic (BI_table_copy x y)]
| cdr_table_init_bound :
  forall x y src dst n tab elem s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tab ->
    selem s f.(f_inst) y = Some elem ->
    ((src_z + n_z > Z.of_nat (elem_size elem))%Z \/
     (dst_z + n_z > Z.of_nat (tab_size tab))%Z) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_init x y)]
      hs s f [::AI_trap]
| cdr_table_init_return :
  forall x y src dst n tab elem s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tab ->
    selem s f.(f_inst) y = Some elem ->
    (src_z + n_z <= Z.of_nat (elem_size elem))%Z ->
    (dst_z + n_z <= Z.of_nat (tab_size tab))%Z ->
    (n_z = 0)%Z ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_init x y)]
      hs s f [::]
| cdr_table_init_step :
  forall x y src dst n tab elem src' dst' n' v s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tab ->
    selem s f.(f_inst) y = Some elem ->
    (src_z + n_z <= Z.of_nat (elem_size elem))%Z ->
    (dst_z + n_z <= Z.of_nat (tab_size tab))%Z ->
    (n_z <> 0)%Z ->
    lookup_N elem.(eleminst_elem) (Wasm_int.N_of_uint i32m src) = Some v ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.add src_z 1) ->
    dst' = Wasm_int.int_of_Z i32m (Z.add dst_z 1) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_init x y)]
      hs s f [:: $VN (VAL_int32 dst); v_to_e (VAL_ref v); AI_basic (BI_table_set x);
              $VN (VAL_int32 dst'); $VN (VAL_int32 src'); $VN (VAL_int32 n'); AI_basic (BI_table_init x y)]
| cdr_elem_drop:
  forall x hs s f s',
    selem_drop s f.(f_inst) x = Some s' ->
    crt_direct_reduce hs s f [::AI_basic (BI_elem_drop x)] hs s' f [::]
           
(** memory **)
| cdr_load_success :
  forall s f t bs k marg m hs,
    smem s f.(f_inst) = Some m ->
    load m (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) (tnum_length t) = Some bs ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); AI_basic (BI_load t None marg)] hs s f [::$VN (wasm_deserialise bs t)]
| cdr_load_failure :
  forall s f t k marg m hs,
    smem s f.(f_inst) = Some m ->
    load m (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) (tnum_length t) = None ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); AI_basic (BI_load t None marg)] hs s f [::AI_trap]
| cdr_load_packed_success :
  forall s f t tp k marg m bs sx hs,
    smem s f.(f_inst) = Some m ->
    load_packed sx m (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) (tp_length tp) (tnum_length t) = Some bs ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); AI_basic (BI_load t (Some (tp, sx)) marg)] hs s f [::$VN (wasm_deserialise bs t)]
| cdr_load_packed_failure :
  forall s f t tp k marg m sx hs,
    smem s f.(f_inst) = Some m ->
    load_packed sx m (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) (tp_length tp) (tnum_length t) = None ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); AI_basic (BI_load t (Some (tp, sx)) marg)] hs s f [::AI_trap]
| cdr_load_vec_success :
  forall s f m lvarg marg k v hs,
    smem s f.(f_inst) = Some m ->
    load_vec m (Wasm_int.N_of_uint i32m k) lvarg marg = Some v ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); AI_basic (BI_load_vec lvarg marg)] hs s f [::$VV v]
| cdr_load_vec_failure :
  forall s f m lvarg marg k hs,
    smem s f.(f_inst) = Some m ->
    load_vec m (Wasm_int.N_of_uint i32m k) lvarg marg = None ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); AI_basic (BI_load_vec lvarg marg)] hs s f [::AI_trap]
| cdr_load_vec_lane_success :
  forall s f m width marg x k v v' hs,
    smem s f.(f_inst) = Some m ->
    load_vec_lane m (Wasm_int.N_of_uint i32m k) v width marg x = Some v' ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); $VV v; AI_basic (BI_load_vec_lane width marg x)] hs s f [::$VV v']
| cdr_load_vec_lane_failure :
  forall s f m width marg x k v hs,
    smem s f.(f_inst) = Some m ->
    load_vec_lane m (Wasm_int.N_of_uint i32m k) v width marg x = None ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); $VV v; AI_basic (BI_load_vec_lane width marg x)] hs s f [::AI_trap]
| cdr_store_success :
  forall t v s f k marg s' hs,
    smem_store s f.(f_inst) (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) v t = Some s' ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); $VN v; AI_basic (BI_store t None marg)] hs s' f [::]
| cdr_store_failure :
  forall t v s f k marg hs,
    smem_store s f.(f_inst) (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) v t = None ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); $VN v; AI_basic (BI_store t None marg)] hs s f [::AI_trap]
| cdr_store_packed_success :
  forall t v s s' f k marg tp hs,
    smem_store_packed s f.(f_inst) (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) v tp = Some s' ->
    typeof_num v = t ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); $VN v; AI_basic (BI_store t (Some tp) marg)] hs s' f [::]
| cdr_store_packed_failure :
  forall t v s f k marg tp hs,
    smem_store_packed s f.(f_inst) (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) v tp = None ->
    typeof_num v = t ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); $VN v; AI_basic (BI_store t (Some tp) marg)] hs s f [::AI_trap]
| cdr_store_vec_success :
  forall s s' f marg k v hs,
    smem_store_vec s f.(f_inst) (Wasm_int.N_of_uint i32m k) v marg = Some s' ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); $VV v; AI_basic (BI_store_vec marg)] hs s' f [::]
| cdr_store_vec_failure :
  forall s f marg k v hs,
    smem_store_vec s f.(f_inst) (Wasm_int.N_of_uint i32m k) v marg = None ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); $VV v; AI_basic (BI_store_vec marg)] hs s f [::AI_trap]
| cdr_store_vec_lane_success :
  forall s s' f width marg x k v hs,
    smem_store_vec_lane s f.(f_inst) (Wasm_int.N_of_uint i32m k) v width marg x = Some s' ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); $VV v; AI_basic (BI_store_vec_lane width marg x)] hs s' f [::]
| cdr_store_vec_lane_failure :
  forall s f width marg x k v hs,
    smem_store_vec_lane s f.(f_inst) (Wasm_int.N_of_uint i32m k) v width marg x = None ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 k); $VV v; AI_basic (BI_store_vec_lane width marg x)] hs s f [::AI_trap]
| cdr_memory_size :
  forall f m n s hs,
    smem s f.(f_inst) = Some m ->
    mem_size m = n ->
    crt_direct_reduce hs s f [::AI_basic (BI_memory_size)] hs s f [::$VN (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n)))]
| cdr_memory_grow_success :
  forall s f s' sz c hs,
    smem_grow s f.(f_inst) (Wasm_int.N_of_uint i32m c) = Some (s', sz) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 c); AI_basic BI_memory_grow] hs s' f [::$VN (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N sz)))]
| cdr_memory_grow_failure :
  forall s f c hs,
    smem_grow s f.(f_inst) (Wasm_int.N_of_uint i32m c) = None ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 c); AI_basic BI_memory_grow] hs s f [::$VN (VAL_int32 int32_minus_one)]
| cdr_memory_fill_bound:
  forall s f mem d n v hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let d_z := Wasm_int.Z_of_uint i32m d in
    smem s f.(f_inst) = Some mem ->
    (Z.add n_z d_z > Z.of_N (mem_length mem))%Z ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 d); $VN (VAL_int32 v); $VN (VAL_int32 n); AI_basic (BI_memory_fill)]
           hs s f [::AI_trap]
| cdr_memory_fill_return:
  forall s f mem d n v hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let d_z := Wasm_int.Z_of_uint i32m d in
    smem s f.(f_inst) = Some mem ->
    (Z.add n_z d_z <= Z.of_N (mem_length mem))%Z ->
    (n_z = 0)%Z ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 d); $VN (VAL_int32 v); $VN (VAL_int32 n); AI_basic (BI_memory_fill)]
           hs s f [::]
| cdr_memory_fill_step:
  forall s f mem d n d' n' v hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let d_z := Wasm_int.Z_of_uint i32m d in
    smem s f.(f_inst) = Some mem ->
    (Z.add n_z d_z <= Z.of_N (mem_length mem))%Z ->
    (n_z <> 0)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    d' = Wasm_int.int_of_Z i32m (Z.add d_z 1) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 d); $VN (VAL_int32 v); $VN (VAL_int32 n); AI_basic (BI_memory_fill)]
      hs s f [::$VN (VAL_int32 d); $VN (VAL_int32 v); AI_basic (BI_store T_i32 (Some Tp_i8) (Build_memarg N0 N0));
                $VN (VAL_int32 d'); $VN (VAL_int32 v); $VN (VAL_int32 n'); AI_basic (BI_memory_fill)]
| cdr_memory_copy_bound :
  forall src dst n mem s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    ((Z.add src_z n_z > Z.of_N (mem_length mem))%Z \/
     (Z.add dst_z n_z > Z.of_N (mem_length mem))%Z) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_copy)]
      hs s f [::AI_trap]
| cdr_memory_copy_return :
  forall src dst n mem s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    (Z.add src_z n_z <= Z.of_N (mem_length mem))%Z ->
    (Z.add dst_z n_z <= Z.of_N (mem_length mem))%Z ->
    (n_z = 0)%Z ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_copy)]
      hs s f [::]
| cdr_memory_copy_forward :
  forall src dst n mem src' dst' n' s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    (Z.add src_z n_z <= Z.of_N (mem_length mem))%Z ->
    (Z.add dst_z n_z <= Z.of_N (mem_length mem))%Z ->
    (n_z <> 0)%Z ->
    (dst_z <= src_z)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.add src_z 1) ->
    dst' = Wasm_int.int_of_Z i32m (Z.add dst_z 1) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_copy)]
      hs s f [:: $VN (VAL_int32 dst); $VN (VAL_int32 src); AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg N0 N0)); AI_basic (BI_store T_i32 (Some (Tp_i8)) (Build_memarg N0 N0));
              $VN (VAL_int32 dst'); $VN (VAL_int32 src'); $VN (VAL_int32 n'); AI_basic (BI_memory_copy)]
| cdr_memory_copy_backward :
  forall src dst n mem src' dst' n' s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    (Z.add src_z n_z <= Z.of_N (mem_length mem))%Z ->
    (Z.add dst_z n_z <= Z.of_N (mem_length mem))%Z ->
    (n_z <> 0)%Z ->
    (dst_z > src_z)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.add src_z (Z.sub n_z 1)) ->
    dst' = Wasm_int.int_of_Z i32m (Z.add dst_z (Z.sub n_z 1)) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_copy)]
      hs s f [:: $VN (VAL_int32 dst'); $VN (VAL_int32 src'); AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg N0 N0)); AI_basic (BI_store T_i32 (Some (Tp_i8)) (Build_memarg N0 N0));
              $VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n'); AI_basic (BI_memory_copy)]
| cdr_memory_init_bound :
  forall x src dst n mem data s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    sdata s f.(f_inst) x = Some data ->
    ((Z.add src_z n_z > Z.of_nat (data_size data))%Z \/
     (Z.add dst_z n_z > Z.of_N (mem_length mem))%Z) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_init x)]
      hs s f [::AI_trap]
| cdr_memory_init_return :
  forall x src dst n mem data s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    sdata s f.(f_inst) x = Some data ->
    (Z.add src_z n_z <= Z.of_nat (data_size data))%Z ->
    (Z.add dst_z n_z <= Z.of_N (mem_length mem))%Z ->
    (n_z = 0)%Z ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_init x)]
      hs s f [::]
| cdr_memory_init_step :
  forall x src dst n mem data src' dst' n' b s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    sdata s f.(f_inst) x = Some data ->
    (Z.add src_z n_z <= Z.of_nat (data_size data))%Z ->
    (Z.add dst_z n_z <= Z.of_N (mem_length mem))%Z ->
    (n_z <> 0)%Z ->
    lookup_N data.(datainst_data) (Wasm_int.N_of_uint i32m src) = Some b ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.add src_z 1) ->
    dst' = Wasm_int.int_of_Z i32m (Z.add dst_z 1) ->
    crt_direct_reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_init x)]
      hs s f [:: $VN (VAL_int32 dst); v_to_e (VAL_num (wasm_deserialise [::b] T_i32)); AI_basic (BI_store T_i32 (Some Tp_i8) (Build_memarg N0 N0));
              $VN (VAL_int32 dst'); $VN (VAL_int32 src'); $VN (VAL_int32 n'); AI_basic (BI_memory_init x)]
| cdr_data_drop:
  forall x hs s f s',
    sdata_drop s f.(f_inst) x = Some s' ->
    crt_direct_reduce hs s f [::AI_basic (BI_data_drop x)] hs s' f [::]
               
  .

Lemma crt_direct_reduce_sound hs s f es hs' s' f' es' :
  crt_direct_reduce hs s f es hs' s' f' es' ->
  reduce hs s f es hs' s' f' es'.
Proof. intros H. destruct H.
  - eapply r_simple; eauto.
  - eapply r_ref_func; eauto.
  - eapply r_block; eauto.
  - eapply r_loop; eauto.
  - eapply r_call; eauto.
  - eapply r_call_indirect_success; eauto.
  - eapply r_call_indirect_failure_mismatch; eauto.
  - eapply r_call_indirect_failure_bound; eauto.
  - eapply r_call_indirect_failure_null_ref; eauto.
  - eapply r_return_call; eauto.
  - eapply r_return_call_indirect_success; eauto.
  - eapply r_return_call_indirect_failure; eauto.
  - eapply r_invoke_native; eauto.
  - eapply r_invoke_host_success; eauto.
  - eapply r_invoke_host_diverge; eauto.
  - eapply r_return_invoke; eauto.
  - eapply r_local_get; eauto.
  - eapply r_local_set; eauto.
  - eapply r_global_get; eauto.
  - eapply r_global_set; eauto.
  - eapply r_table_get_success; eauto.
  - eapply r_table_get_failure; eauto.
  - eapply r_table_set_success; eauto.
  - eapply r_table_set_failure; eauto.
  - eapply r_table_size; eauto.
  - eapply r_table_grow_success; eauto.
  - eapply r_table_grow_failure; eauto.
  - eapply r_table_fill_bound; eauto.
  - eapply r_table_fill_return; eauto.
  - eapply r_table_fill_step; eauto.
  - eapply r_table_copy_bound; eauto.
  - eapply r_table_copy_return; eauto.
  - eapply r_table_copy_forward; eauto.
  - eapply r_table_copy_backward; eauto.
  - eapply r_table_init_bound; eauto.
  - eapply r_table_init_return; eauto.
  - eapply r_table_init_step; eauto.
  - eapply r_elem_drop; eauto.
  - eapply r_load_success; eauto.
  - eapply r_load_failure; eauto.
  - eapply r_load_packed_success; eauto.
  - eapply r_load_packed_failure; eauto.
  - eapply r_load_vec_success; eauto.
  - eapply r_load_vec_failure; eauto.
  - eapply r_load_vec_lane_success; eauto.
  - eapply r_load_vec_lane_failure; eauto.
  - eapply r_store_success; eauto.
  - eapply r_store_failure; eauto.
  - eapply r_store_packed_success; eauto.
  - eapply r_store_packed_failure; eauto.
  - eapply r_store_vec_success; eauto.
  - eapply r_store_vec_failure; eauto.
  - eapply r_store_vec_lane_success; eauto.
  - eapply r_store_vec_lane_failure; eauto.
  - eapply r_memory_size; eauto.
  - eapply r_memory_grow_success; eauto.
  - eapply r_memory_grow_failure; eauto.
  - eapply r_memory_fill_bound; eauto.
  - eapply r_memory_fill_return; eauto.
  - eapply r_memory_fill_step; eauto.
  - eapply r_memory_copy_bound; eauto.
  - eapply r_memory_copy_return; eauto.
  - eapply r_memory_copy_forward; eauto.
  - eapply r_memory_copy_backward; eauto.
  - eapply r_memory_init_bound; eauto.
  - eapply r_memory_init_return; eauto.
  - eapply r_memory_init_step; eauto.
  - eapply r_data_drop; eauto.
Qed.

Ltac crt_direct_empty_read Hpure :=
  match goal with
  | H : sglob_val _ _ _ = Some _ |- _ => rewrite (crt_empty_sglob_val _ _ Hpure) in H; discriminate
  | H : smem _ _ = Some _ |- _ => rewrite (crt_empty_smem _ Hpure) in H; discriminate
  | H : stab _ _ _ = Some _ |- _ => rewrite (crt_empty_stab _ _ Hpure) in H; discriminate
  | H : stab_elem _ _ _ _ = Some _ |- _ => rewrite (crt_empty_stab_elem _ _ _ Hpure) in H; discriminate
  | H : selem _ _ _ = Some _ |- _ => rewrite (crt_empty_selem _ _ Hpure) in H; discriminate
  | H : sdata _ _ _ = Some _ |- _ => rewrite (crt_empty_sdata _ _ Hpure) in H; discriminate
  | H : lookup_N (s_funcs _) _ = Some (FC_func_host _ _) |- _ =>
      exfalso; exact (crt_no_host_function Hpure H)
  end.

Ltac crt_direct_empty_write Hpure Hupdate :=
  destruct Hpure as [Htables Hmems Hglobals Helems Hdata Hnative];
  unfold supdate_glob, supdate_glob_s, sglob_ind,
    stab_update, stab_grow, selem_drop,
    smem_store, smem_store_packed, smem_store_vec,
    smem_store_vec_lane, smem_grow, sdata_drop in Hupdate;
  rewrite ?Htables ?Hmems ?Hglobals ?Helems ?Hdata in Hupdate;
  rewrite ?crt_lookup_N_nil in Hupdate;
  repeat first [progress rewrite ?crt_lookup_N_nil in Hupdate |
    match type of Hupdate with
    | context [lookup_N ?xs ?idx] =>
        let E := fresh "Elookup" in destruct (lookup_N xs idx) eqn:E in Hupdate
    end];
  cbn [option_bind option_map] in Hupdate;
  rewrite ?crt_lookup_N_nil in Hupdate;
  first [discriminate Hupdate |
    match goal with E : lookup_N [::] _ = Some _ |- _ =>
      rewrite crt_lookup_N_nil in E; discriminate E
    end].

Ltac crt_direct_resources Hpure :=
  first [crt_direct_empty_read Hpure |
    match goal with
    | H : ?op = Some _ |- _ => crt_direct_empty_write Hpure H
    end].

Lemma crt_append_singleton_inj (xs ys : seq administrative_instruction) x y :
  xs ++ [:: x] = ys ++ [:: y] -> xs = ys /\ x = y.
Proof. exact: app_inj_tail. Qed.

Ltac crt_direct_split_last src :=
  lazymatch src with
  | [::?e] => constr:((([::] : seq administrative_instruction), e))
  | ?e :: ?es =>
      let p := crt_direct_split_last es in
      lazymatch p with (?pre, ?op) => constr:(((e :: pre), op)) end
  | ?pre ++ [::?op] => constr:(((pre : seq administrative_instruction), op))
  end.

Ltac crt_direct_split_sources :=
  match goal with
  | H : @eq (seq administrative_instruction) ?src1 ?src2 |- _ =>
    let p1 := crt_direct_split_last src1 in
    let p2 := crt_direct_split_last src2 in
    lazymatch p1 with (?pre1, ?op1) =>
    lazymatch p2 with (?pre2, ?op2) =>
      change (pre1 ++ [::op1] = pre2 ++ [::op2]) in H;
      let Hpre := fresh "Hpre" in let Hop := fresh "Hop" in
      apply crt_append_singleton_inj in H as [Hpre Hop];
      inversion Hop; subst; clear Hop
    end end
  end.

Lemma crt_direct_vref_const r : is_const (vref_to_e r) = true.
Proof. destruct r; reflexivity. Qed.

Ltac crt_direct_prove_const_list :=
  first [assumption | apply v_to_e_const |
    rewrite /const_list /= ?crt_direct_vref_const /is_const ?v2e2v; reflexivity].

Ltac crt_direct_trap_absent :=
  match goal with
  | H : lfill ?lh [:: AI_trap] = ?src |- _ =>
    let p := crt_direct_split_last src in
    lazymatch p with (?pre, ?op) =>
      let Hp := fresh "Hprefix" in
      assert (Hp : const_list pre) by crt_direct_prove_const_list;
      let HE := fresh "Htrap" in
      have [HE _] := crt_escape_in_flat_source
        (lh := lh) (escape := AI_trap) (vs := pre) (op := op) Hp
        ltac:(discriminate) ltac:(discriminate) H;
      discriminate HE
    end
  end.

Lemma crt_set_nth_default_irrelevant (T : Type) (xs : seq T) i v d1 d2 :
  i < length xs -> set_nth d1 xs i v = set_nth d2 xs i v.
Proof.
  elim: xs i => [|x xs IH] [|i] //=.
  move=> H. f_equal. exact: IH.
Qed.

Lemma crt_frame_ext (f1 f2 : frame) :
  f_locs f1 = f_locs f2 -> f_inst f1 = f_inst f2 -> f1 = f2.
Proof. destruct f1, f2; simpl; congruence. Qed.

Lemma crt_direct_reduce_deterministic hs s f es hs1 s1 f1 es1 hs2 s2 f2 es2 :
  crt_resource_free_native_store s ->
  crt_direct_reduce hs s f es hs1 s1 f1 es1 ->
  crt_direct_reduce hs s f es hs2 s2 f2 es2 ->
  (hs1, s1, f1, es1) = (hs2, s2, f2, es2).
Proof.
  move=> HP H1 H2.
  inversion H1; subst; clear H1; try (crt_direct_resources HP);
    inversion H2; subst; clear H2; try (crt_direct_resources HP);
    try reflexivity; try congruence; try lia.
  all: try match goal with
  | H : reduce_simple ?es ?es1, H' : reduce_simple ?es ?es2 |- _ =>
    have -> := crt_simple_deterministic H H'; reflexivity
  end.
  all: repeat crt_direct_split_sources.
  all: try reflexivity; try congruence.
  all: try match goal with H : reduce_simple _ _ |- _ => inversion H; subst; clear H end.
  all: repeat crt_direct_split_sources.
  all: try reflexivity; try congruence.
  all: try crt_direct_trap_absent.
  all: try match goal with H : ?src = lfill ?lh [:: AI_trap] |- _ =>
    symmetry in H; crt_direct_trap_absent end.
  all: try match goal with H : is_true (const_list (lfill ?lh ?es)) |- _ =>
    exfalso; apply crt_lfill_const_inv in H;
    apply const_list_split in H as [_ H]; discriminate H end.
  all: try match goal with H : [:: AI_trap] = lfill ?lh ?es |- _ => symmetry in H end.
  all: try match goal with
  | H : lfill ?lh (?vs ++ [:: ?e]) = [:: AI_trap],
    Hc : is_true (const_list ?vs) |- _ =>
    exfalso; exact (crt_lfill_escape_not_trap (lh := lh) (e := e) Hc
      ltac:(discriminate) ltac:(discriminate) H)
  end.
  all: try match goal with
  | H : lfill ?lh (?vs ++ [:: ?e]) = lfill ?lh' (?vs' ++ [:: ?e']),
    Hc : is_true (const_list ?vs), Hc' : is_true (const_list ?vs') |- _ =>
    let HE := fresh "Hescape" in
    have [HE _] := crt_lfill_escape_head_unique
      (lh := lh) (lh' := lh') (vs := vs) (vs' := vs') (e := e) (e' := e')
      Hc Hc' ltac:(discriminate) ltac:(discriminate) H;
    discriminate HE
  end.
  all: repeat match goal with
  | H : v_to_e_list ?vs = v_to_e_list ?vs' |- _ => apply v_to_e_inj in H; subst
  | H : v_to_e ?v = v_to_e ?v' |- _ => apply ve_inj in H; subst
  end; try reflexivity; try congruence.
  all: try match goal with
  | H : lfill ?lh (?vs ++ [:: AI_return_invoke ?a]) =
        lfill ?lh' (?vs' ++ [:: AI_return_invoke ?a']),
    Hc : is_true (const_list ?vs), Hc' : is_true (const_list ?vs') |- _ =>
    let HE := fresh "Hescape" in
    have [HE _] := crt_lfill_escape_head_unique
      (lh := lh) (lh' := lh') (vs := vs) (vs' := vs')
      (e := AI_return_invoke a) (e' := AI_return_invoke a')
      Hc Hc' ltac:(discriminate) ltac:(discriminate) H;
    inversion HE; subst;
    let HL := fresh "Hlength" in
    assert (HL : length vs = length vs') by congruence;
    let HV := fresh "Hvalues" in
    have [HV _] := crt_lfill_escape_unique
      (lh := lh) (lh' := lh') (vs := vs) (vs' := vs')
      (e := AI_return_invoke a) (e' := AI_return_invoke a)
      Hc Hc' HL ltac:(discriminate) ltac:(discriminate) H;
    rewrite HV; reflexivity
  end.
  6: {
    have Ef : f1 = f2.
    { apply crt_frame_ext; last congruence. rewrite H3 H14.
      exact: crt_set_nth_default_irrelevant H0. }
    by rewrite Ef.
  }
  5: {
    have [HE _] := crt_lfill_escape_head_unique
      (lh := lh0) (lh' := lh) (vs := vs0) (vs' := vs)
      (e := AI_return_invoke a0) (e' := AI_return_invoke a)
      H14 H5 ltac:(discriminate) ltac:(discriminate) H20.
    have Ea : a0 = a by injection HE. subst a0.
    have HL : length vs0 = length vs by congruence.
    have [HV _] := crt_lfill_escape_unique
      (lh := lh0) (lh' := lh) (vs := vs0) (vs' := vs)
      (e := AI_return_invoke a) (e' := AI_return_invoke a)
      H14 H5 HL ltac:(discriminate) ltac:(discriminate) H20.
    by rewrite HV.
  }
  all: try match goal with
  | H : reduce _ _ _ [:: v_to_e _; AI_basic (BI_call_indirect _ _)]
      _ _ _ [:: AI_invoke _] |- _ =>
    let HE := fresh "Hindirect" in
    have [_ [_ [_ HE]]] := crt_reduce_indirect_empty_inv H HP erefl;
    discriminate HE
  end.
  have [addr [HL [_ [_ [_ HE]]]]] := crt_reduce_call_inv H erefl.
  have [addr' [HL' [_ [_ [_ HE']]]]] := crt_reduce_call_inv H5 erefl.
  congruence.
Qed.

End Host.

Print Assumptions crt_direct_reduce_deterministic.
