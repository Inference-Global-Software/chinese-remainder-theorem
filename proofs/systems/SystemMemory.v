(* Host input preparation is separate from module instantiation.  This model
   uses the abstract Wasm memory laws and admits overlapping equal inputs. *)
From Coq Require Import NArith ZArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import bytes datatypes operations opsem host properties instantiation_spec.
From WasmVerifier Require Import Memory Semantics.
From CRTSystems Require Import SystemRuntime.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Host.
Context `{ho : host}.

Definition system_memory_valid (m : meminst) : Prop :=
  meminst_type m = Build_limits 1%num (Some 1%num) /\
  operations.mem_length m = 65536%num.

Fixpoint array_cells (m : meminst) (base : N) (xs : seq i64) : Prop :=
  match xs with
  | [::] => True
  | x :: tail => load m base 0%num 8%num = Some (serialise_num (VAL_int64 x)) /\
      array_cells m (base + 8)%num tail
  end.

Definition array_region (m : meminst) (base : N) (xs : seq i64) : Prop :=
  size xs = 16%nat /\ (base + 128 <= operations.mem_length m)%num /\
  (base + 128 <= 4294967296)%num /\ array_cells m base xs.

Definition system_input_memory m residues_ptr moduli_ptr residues moduli : Prop :=
  system_memory_valid m /\ array_region m residues_ptr residues /\
  array_region m moduli_ptr moduli.

Lemma array_cells_lookup m base xs i x :
  array_cells m base xs -> List.nth_error xs i = Some x ->
  load m (base + 8 * N.of_nat i)%num 0%num 8%num = Some (serialise_num (VAL_int64 x)).
Proof.
  elim: xs base i => [|y ys IH] base [|i] //=.
  - move=> [Hy _] [<-]. by rewrite N.add_0_r.
  - move=> [_ Hys] Hi. have H := IH _ _ Hys Hi.
    change (load m (base + 8 * N.of_nat (S i))%num 0%num 8%num = Some (serialise_num (VAL_int64 x))).
    rewrite Nat2N.inj_succ. replace (base + 8 * N.succ (N.of_nat i))%num
      with (base + 8 + 8 * N.of_nat i)%num by lia. exact H.
Qed.

Lemma array_region_bounds m base xs i :
  array_region m base xs -> (i < 16)%num ->
  (base + 8*i + 8 <= operations.mem_length m)%num /\
  (base + 8*i < 4294967296)%num.
Proof. rewrite /array_region. move=> [_ [Hm [Hw _]]] Hi. lia. Qed.

Lemma array_cells_write_before m m' base xs a x :
  store m a 0%num (serialise_num (VAL_int64 x)) 8 = Some m' ->
  (a + 8 <= base)%num -> array_cells m base xs -> array_cells m' base xs.
Proof.
  move=> Hw. elim: xs base => [|y ys IH] base //= Hb [Hy Hys].
  split; last (apply: IH; [lia|exact Hys]).
  rewrite (load_store_disjoint Hw); first exact Hy.
  right. simpl. lia.
Qed.

Lemma write_i64_exists m a x :
  (a + 8 <= operations.mem_length m)%num ->
  exists m', store m a 0%num (serialise_num (VAL_int64 x)) 8 = Some m' /\
    meminst_type m' = meminst_type m /\
    operations.mem_length m' = operations.mem_length m /\
    load m' a 0%num 8%num = Some (serialise_num (VAL_int64 x)).
Proof.
  move=> Hb.
  have Hsize : size (serialise_num (VAL_int64 x)) = 8%nat.
  { have H := serialise_num_length (VAL_int64 x). apply (f_equal N.to_nat) in H. rewrite Nat2N.id in H. exact H. }
  have Hfill : bytes_takefill #00 8 (serialise_num (VAL_int64 x)) = serialise_num (VAL_int64 x).
  { exact: bytes_takefill_id Hsize. }
  have [md' Hwrite] := write_bytes_success (bs:=serialise_num (VAL_int64 x))
    (md:=meminst_data m) (j:=a) ltac:(rewrite Hsize; exact Hb).
  exists (Build_meminst (meminst_type m) md').
  have Hstore : store m a 0%num (serialise_num (VAL_int64 x)) 8 =
      Some (Build_meminst (meminst_type m) md').
  { rewrite /store N.add_0_r.
    have -> : (a + N.of_nat 8 <=? operations.mem_length m)%num = true
      by apply/N.leb_le.
    by rewrite /write_bytes_meminst Hfill Hwrite. }
  split; first exact Hstore. split; first reflexivity. split.
  - exact (write_bytes_length Hwrite).
  - have H := load_store_same Hstore. by rewrite Hfill in H.
Qed.

(* The extra disjoint-load conclusion allows preparing two arrays in sequence. *)
Lemma prepare_array m base xs :
  (base + 8 * N.of_nat (size xs) <= operations.mem_length m)%num ->
  exists m', meminst_type m' = meminst_type m /\
    operations.mem_length m' = operations.mem_length m /\ array_cells m' base xs /\
    (forall a len, (a + len <= base \/ base + 8 * N.of_nat (size xs) <= a)%num ->
      load m' a 0%num len = load m a 0%num len).
Proof.
  elim: xs base => [|x xs IH] base Hb.
  - exists m. repeat split; auto.
  - have [mt [Ht [Hl [Hcells Hdisj]]]] := IH (base + 8)%num
      ltac:(cbn [size] in Hb; rewrite Nat2N.inj_succ in Hb; lia).
    have [m' [Hw [Ht' [Hl' Hload]]]] := write_i64_exists (m:=mt)
      (a:=base) x ltac:(rewrite Hl; cbn [size] in Hb; rewrite Nat2N.inj_succ in Hb; lia).
    exists m'. split; first congruence. split; first congruence. split.
    + split; first exact Hload. exact (array_cells_write_before Hw (N.le_refl _) Hcells).
    + intros a len Hd. rewrite (load_store_disjoint Hw).
      * apply Hdisj. cbn [size] in Hd. rewrite Nat2N.inj_succ in Hd. lia.
      * rewrite /byte_ranges_disjoint /= !N.add_0_r.
        cbn [size] in Hd. rewrite Nat2N.inj_succ in Hd. rewrite nat_bin N2Nat.id. lia.
Qed.

Theorem system_inputs_inhabited residues moduli :
  size residues = 16%nat -> size moduli = 16%nat ->
  exists m, system_input_memory m 0%num 128%num residues moduli.
Proof.
  move=> Hr Hm.
  have Hinit : system_memory_valid system_initial_memory.
  { split; first reflexivity. rewrite /system_initial_memory /gen_mem_instance
      /operations.mem_length /= memory.mem_make_length. reflexivity. }
  have [mr [Hrt [Hrl [Hrc _]]]] := prepare_array (m:=system_initial_memory)
    (base:=0%num) (xs:=residues) ltac:(rewrite Hr (proj2 Hinit); lia).
  have [m [Hmt [Hml [Hmc Hdisj]]]] := prepare_array (m:=mr)
    (base:=128%num) (xs:=moduli) ltac:(rewrite Hm Hrl (proj2 Hinit); lia).
  destruct Hinit as [Hity Hilen].
  exists m. have Hlen : operations.mem_length m = 65536%num by congruence.
  split; first (split; [congruence|exact Hlen]).
  split; rewrite /array_region; repeat split; try assumption; try (rewrite Hlen; lia); try lia.
  - clear - Hrc Hdisj Hr. move: Hrc.
    have Hkeep : forall xs base, (base + 8 * N.of_nat (size xs) <= 128)%num ->
      array_cells mr base xs -> array_cells m base xs.
    { elim=> [|x xs IH] base Hb //= [Hx Hxs]. split.
      - rewrite Hdisj; first exact Hx. left. cbn [size] in Hb.
        rewrite Nat2N.inj_succ in Hb. lia.
      - apply IH; last exact Hxs. cbn [size] in Hb. rewrite Nat2N.inj_succ in Hb. lia. }
    apply Hkeep. by rewrite Hr.
Qed.
End Host.
