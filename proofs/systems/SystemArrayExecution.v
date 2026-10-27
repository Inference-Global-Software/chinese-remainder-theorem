(* This contiguous read is extracted from the first validation loop of the
   emitted classifier.  Its frame already contains the index in scratch 7;
   the operand prefix is the array pointer and index established immediately
   before the slice. *)
From Coq Require Import NArith ZArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import bytes datatypes operations opsem host properties.
From WasmVerifier Require Import Memory Semantics.
From CRTSystemGenerated Require main.
From CRTSystems Require Import ReadOnly ReadOnlyConfluence SystemRuntime SystemMemory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition classifier_read_slice : seq basic_instruction :=
  match List.nth_error (modfunc_body main.system_classify) 9 with
  | Some (BI_block _ [:: BI_loop _ body]) => take 8 (drop 8 body)
  | _ => [::]
  end.

Lemma classifier_read_shape : classifier_read_slice =
  [:: BI_local_get 7%num; BI_const_num (main.Vi32 16);
      BI_relop T_i32 (Relop_i (ROI_ge SX_U));
      BI_if (BT_valtype None) [::BI_unreachable] [::];
      BI_const_num (main.Vi32 8); BI_binop T_i32 (Binop_i BOI_mul);
      BI_binop T_i32 (Binop_i BOI_add); BI_load T_i64 None (main.Ma 0%num 3%num)].
Proof. reflexivity. Qed.

Lemma system_u32_repr z : (0 <= z < 4294967296)%Z ->
  Wasm_int.Int32.unsigned (Wasm_int.Int32.repr z) = z.
Proof. move=> H. apply Wasm_int.Int32.unsigned_repr.
  change (0 <= z <= 4294967295)%Z. lia. Qed.

Lemma system_index_guard i : (0 <= i < 16)%Z ->
  app_relop (Relop_i (ROI_ge SX_U)) (main.Vi32 i) (main.Vi32 16) = false.
Proof.
  move=> Hi. rewrite /app_relop /app_relop_i /main.Vi32 /=.
  rewrite /Wasm_int.Int32.ltu (system_u32_repr (z:=i) ltac:(lia)).
  rewrite (system_u32_repr (z:=16) ltac:(lia)).
  destruct (Coqlib.zlt i 16); simpl; [reflexivity|lia].
Qed.

Lemma system_index_mul i : (0 <= i < 16)%Z ->
  app_binop (Binop_i BOI_mul) (main.Vi32 i) (main.Vi32 8) = Some (main.Vi32 (i*8)).
Proof.
  move=> Hi. rewrite /app_binop /app_binop_i /main.Vi32 /= /Wasm_int.Int32.imul /Wasm_int.Int32.mul.
  rewrite (system_u32_repr (z:=i) ltac:(lia)) (system_u32_repr (z:=8) ltac:(lia)). reflexivity.
Qed.

Lemma system_address_add base i : (0 <= base < 4294967296)%Z -> (0 <= i < 16)%Z ->
  app_binop (Binop_i BOI_add) (main.Vi32 base) (main.Vi32 (i*8)) =
    Some (main.Vi32 (base+i*8)).
Proof.
  move=> Hb Hi. rewrite /app_binop /app_binop_i /main.Vi32 /= /Wasm_int.Int32.iadd /Wasm_int.Int32.add.
  by rewrite (system_u32_repr Hb) (system_u32_repr (z:=i*8) ltac:(lia)).
Qed.

Section Host.
Context `{ho : host}.

Lemma system_flat_reduce hs s f pre es es' post :
  reduce_trans (hs,s,f,es) (hs,s,f,es') ->
  reduce_trans (hs,s,f,v_to_e_list pre ++ es ++ post)
    (hs,s,f,v_to_e_list pre ++ es' ++ post).
Proof. move=> H. exact (reduce_trans_lfill (LH_base pre post) H). Qed.
Arguments system_flat_reduce {hs s f pre es es' post} _.

Lemma system_array_load hs m f base xs i x :
  f_inst f = system_inst -> array_region m base xs ->
  List.nth_error xs i = Some x ->
  reduce_trans
    (hs,system_store m,f,[::AI_basic (BI_const_num (main.Vi32 (Z.of_N (base+8*N.of_nat i))));
        AI_basic (BI_load T_i64 None (main.Ma 0%num 3%num))])
    (hs,system_store m,f,[::AI_basic (BI_const_num (VAL_int64 x))]).
Proof.
  move=> Hf Hr Hi.
  have Hindex : (N.of_nat i < 16)%num.
  { have H := List.nth_error_Some xs i. have Hlt : (i < size xs)%coq_nat.
    { rewrite size_length. apply H. by rewrite Hi. }
    rewrite (proj1 Hr) in Hlt. lia. }
  have [_ Hwrap] := array_region_bounds Hr Hindex.
  rewrite -(deserialise_serialise_i64 x).
  eapply load_num_reduces.
  - by rewrite /smem Hf /system_store /system_inst /=.
  - change (load m (Z.to_N (Wasm_int.Int32.unsigned
      (Wasm_int.Int32.repr (Z.of_N (base+8*N.of_nat i))))) 0%num 8%num = Some (serialise_num (VAL_int64 x))).
    rewrite (system_u32_repr (z:=Z.of_N (base+8*N.of_nat i)) ltac:(lia)) N2Z.id.
    exact (array_cells_lookup (proj2 (proj2 (proj2 Hr))) Hi).
Qed.
Definition system_array_guard :=
  BI_if (BT_valtype None) [::BI_unreachable] [::].

Lemma system_guard_exec hs s f i : (0 <= i < 16)%Z ->
  reduce_trans
    (hs,s,f,to_e_list [:: BI_const_num (main.Vi32 i); BI_const_num (main.Vi32 16);
      BI_relop T_i32 (Relop_i (ROI_ge SX_U)); system_array_guard])
    (hs,s,f,[::]).
Proof.
  move=> Hi.
  eapply rtt_trans with (y:=(hs,s,f,
    [:: AI_basic (BI_const_num (main.Vi32 0)); AI_basic system_array_guard])).
  - have Hrel : reduce_trans (hs,s,f,to_e_list
      [:: BI_const_num (main.Vi32 i); BI_const_num (main.Vi32 16);
          BI_relop T_i32 (Relop_i (ROI_ge SX_U))])
      (hs,s,f,[::AI_basic (BI_const_num (main.Vi32 0))]).
    { rewrite /main.Vi32.
      have H := @rs_relop (main.Vi32 i) (main.Vi32 16) T_i32
        (Relop_i (ROI_ge SX_U)) ltac:(reflexivity).
      rewrite (system_index_guard Hi) in H.
      apply rtt_step1. apply r_simple. exact H. }
    exact (system_flat_reduce (pre:=[::]) (post:=[::AI_basic system_array_guard]) Hrel).
  - eapply rtt_trans with (y:=(hs,s,f,[::AI_basic (BI_block (BT_valtype None) [::])])).
    + apply rtt_step1. apply r_simple. apply rs_if_false. reflexivity.
    + eapply rtt_trans with (y:=(hs,s,f,[::AI_label 0 [::] [::]])).
      * apply rtt_step1. eapply r_block with (vs:=[::]) (t1s:=[::]) (t2s:=[::]); reflexivity.
      * apply rtt_step1. apply r_simple. apply rs_label_const. reflexivity.
Qed.

Theorem classifier_read_exec hs m f base xs i x :
  f_inst f = system_inst -> array_region m base xs ->
  List.nth_error xs i = Some x ->
  lookup_N (f_locs f) 7%num = Some (VAL_num (main.Vi32 (Z.of_nat i))) ->
  reduce_trans
    (hs,system_store m,f,
      vn_to_e [::main.Vi32 (Z.of_N base); main.Vi32 (Z.of_nat i)] ++
      to_e_list classifier_read_slice)
    (hs,system_store m,f,[::AI_basic (BI_const_num (VAL_int64 x))]).
Proof.
  move=> Hf Hr Hnth Hlocal.
  have Hi : (0 <= Z.of_nat i < 16)%Z.
  { have Hlt : (i < size xs)%coq_nat.
    { rewrite size_length. apply List.nth_error_Some. by rewrite Hnth. }
    rewrite (proj1 Hr) in Hlt. lia. }
  have Hb : (0 <= Z.of_N base < 4294967296)%Z.
  { destruct Hr as [_ [_ [Hw _]]]. lia. }
  rewrite classifier_read_shape.
  set tail := to_e_list [::BI_const_num (main.Vi32 8);
    BI_binop T_i32 (Binop_i BOI_mul); BI_binop T_i32 (Binop_i BOI_add);
    BI_load T_i64 None (main.Ma 0%num 3%num)].
  eapply rtt_trans with (y:=(hs,system_store m,f,
    vn_to_e [::main.Vi32 (Z.of_N base); main.Vi32 (Z.of_nat i)] ++
    to_e_list [::BI_const_num (main.Vi32 (Z.of_nat i)); BI_const_num (main.Vi32 16);
      BI_relop T_i32 (Relop_i (ROI_ge SX_U)); system_array_guard] ++ tail)).
  - apply (system_flat_reduce (pre:=[::VAL_num (main.Vi32 (Z.of_N base));
      VAL_num (main.Vi32 (Z.of_nat i))])
      (es:=[::AI_basic (BI_local_get 7%num)])
      (es':=[::AI_basic (BI_const_num (main.Vi32 (Z.of_nat i)))])
      (post:= to_e_list [::BI_const_num (main.Vi32 16);
        BI_relop T_i32 (Relop_i (ROI_ge SX_U)); system_array_guard] ++ tail)).
    apply rtt_step1. eapply r_local_get with (v:=VAL_num (main.Vi32 (Z.of_nat i))). exact Hlocal.
  - eapply rtt_trans with (y:=(hs,system_store m,f,
      vn_to_e [::main.Vi32 (Z.of_N base); main.Vi32 (Z.of_nat i)] ++ tail)).
    + exact (system_flat_reduce (pre:=[::VAL_num (main.Vi32 (Z.of_N base));
        VAL_num (main.Vi32 (Z.of_nat i))]) (post:=tail)
        (system_guard_exec hs (system_store m) f Hi)).
    + eapply rtt_trans with (y:=(hs,system_store m,f,
        to_e_list [::BI_const_num (main.Vi32 (Z.of_N base));
          BI_const_num (main.Vi32 (Z.of_nat i*8)); BI_binop T_i32 (Binop_i BOI_add);
          BI_load T_i64 None (main.Ma 0%num 3%num)])).
      * apply (system_flat_reduce (pre:=[::VAL_num (main.Vi32 (Z.of_N base))])
          (es:=to_e_list [::BI_const_num (main.Vi32 (Z.of_nat i));
            BI_const_num (main.Vi32 8); BI_binop T_i32 (Binop_i BOI_mul)])
          (es':=[::AI_basic (BI_const_num (main.Vi32 (Z.of_nat i*8)))])
          (post:=to_e_list [::BI_binop T_i32 (Binop_i BOI_add);
            BI_load T_i64 None (main.Ma 0%num 3%num)])).
        apply rtt_step1. apply r_simple. apply rs_binop_success;
          [reflexivity|exact (system_index_mul Hi)].
      * eapply rtt_trans with (y:=(hs,system_store m,f,to_e_list
          [::BI_const_num (main.Vi32 (Z.of_N base+Z.of_nat i*8));
              BI_load T_i64 None (main.Ma 0%num 3%num)])).
        -- apply (system_flat_reduce (pre:=[::])
             (es:=to_e_list [::BI_const_num (main.Vi32 (Z.of_N base));
               BI_const_num (main.Vi32 (Z.of_nat i*8)); BI_binop T_i32 (Binop_i BOI_add)])
             (es':=[::AI_basic (BI_const_num (main.Vi32 (Z.of_N base+Z.of_nat i*8)))])
             (post:=to_e_list [::BI_load T_i64 None (main.Ma 0%num 3%num)])).
           apply rtt_step1. apply r_simple. apply rs_binop_success;
             [reflexivity|exact (system_address_add Hb Hi)].
        -- have Heq : (Z.of_N base+Z.of_nat i*8 = Z.of_N (base+8*N.of_nat i))%Z by lia.
           rewrite Heq. exact (system_array_load hs Hf Hr Hnth).
Qed.

Theorem classifier_read_all_normal hs m f base xs i x hs' s' f' vs :
  f_inst f = system_inst -> array_region m base xs ->
  List.nth_error xs i = Some x ->
  lookup_N (f_locs f) 7%num = Some (VAL_num (main.Vi32 (Z.of_nat i))) ->
  reduce_trans
    (hs,system_store m,f,
      vn_to_e [::main.Vi32 (Z.of_N base); main.Vi32 (Z.of_nat i)] ++
      to_e_list classifier_read_slice) (hs',s',f',v_to_e_list vs) ->
  vs = [::VAL_num (VAL_int64 x)].
Proof.
  move=> Hf Hr Hnth Hlocal Hrun.
  eapply ro_reduce_trans_normal_unique; last exact (classifier_read_exec hs Hf Hr Hnth Hlocal).
  - apply system_store_readonly.
  - rewrite classifier_read_shape. reflexivity.
  - exact Hrun.
Qed.

End Host.
