From Coq Require Import NArith ZArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Wasm Require Import bytes datatypes operations opsem host properties.
From WasmVerifier Require Import Memory Assertions Semantics Activation Verifier Pure Control Automation.
From WasmVerifier.examples Require Import Issue316OverflowExample.
From CRTSystemGenerated Require main.
From CRTSystems Require Import SystemRuntime SystemMemory SystemArrayExecution.
From CRTSystems Require Import SystemControl SystemCalls.
Module SM := CRTSystemGenerated.main.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Definition array_read_tail (tmp:N) : seq basic_instruction :=
 [::BI_local_get tmp; BI_const_num (SM.Vi32 16);
 BI_relop T_i32 (Relop_i (ROI_ge SX_U));
 BI_if (BT_valtype None) [::BI_unreachable] [::];
 BI_const_num (SM.Vi32 8);BI_binop T_i32 (Binop_i BOI_mul);
 BI_binop T_i32 (Binop_i BOI_add);BI_load T_i64 None (SM.Ma 0%num 3%num)].
Lemma classifier_tail_is_generic : classifier_read_slice = array_read_tail 7%num.
Proof. exact: classifier_read_shape. Qed.
Section Host.
Context `{ho:host}.
Arguments system_flat_reduce {hfc memory ho hs s f pre es es' post} _.
Theorem array_read_tail_exec tmp hs m f base xs i x :
  f_inst f = system_inst -> array_region m base xs ->
  List.nth_error xs i = Some x ->
  lookup_N (f_locs f) tmp = Some (VAL_num (SM.Vi32 (Z.of_nat i))) ->
  reduce_trans
    (hs,system_store m,f,
      vn_to_e [::SM.Vi32 (Z.of_N base); SM.Vi32 (Z.of_nat i)] ++
      to_e_list (array_read_tail tmp))
    (hs,system_store m,f,[::AI_basic (BI_const_num (VAL_int64 x))]).
Proof.
  move=> Hf Hr Hnth Hlocal.
  have Hi : (0 <= Z.of_nat i < 16)%Z.
  { have Hlt : (i < size xs)%coq_nat.
    { rewrite size_length. apply List.nth_error_Some. by rewrite Hnth. }
    rewrite (proj1 Hr) in Hlt. lia. }
  have Hb : (0 <= Z.of_N base < 4294967296)%Z.
  { destruct Hr as [_ [_ [Hw _]]]. lia. }
  rewrite /array_read_tail.
  set tail := to_e_list [::BI_const_num (SM.Vi32 8);
    BI_binop T_i32 (Binop_i BOI_mul); BI_binop T_i32 (Binop_i BOI_add);
    BI_load T_i64 None (SM.Ma 0%num 3%num)].
  eapply rtt_trans with (y:=(hs,system_store m,f,
    vn_to_e [::SM.Vi32 (Z.of_N base); SM.Vi32 (Z.of_nat i)] ++
    to_e_list [::BI_const_num (SM.Vi32 (Z.of_nat i)); BI_const_num (SM.Vi32 16);
      BI_relop T_i32 (Relop_i (ROI_ge SX_U)); system_array_guard] ++ tail)).
  - apply (system_flat_reduce (pre:=[::VAL_num (SM.Vi32 (Z.of_N base));
      VAL_num (SM.Vi32 (Z.of_nat i))])
      (es:=[::AI_basic (BI_local_get tmp)])
      (es':=[::AI_basic (BI_const_num (SM.Vi32 (Z.of_nat i)))])
      (post:= to_e_list [::BI_const_num (SM.Vi32 16);
        BI_relop T_i32 (Relop_i (ROI_ge SX_U)); system_array_guard] ++ tail)).
    apply rtt_step1. eapply r_local_get with (v:=VAL_num (SM.Vi32 (Z.of_nat i))). exact Hlocal.
  - eapply rtt_trans with (y:=(hs,system_store m,f,
      vn_to_e [::SM.Vi32 (Z.of_N base); SM.Vi32 (Z.of_nat i)] ++ tail)).
    + exact (system_flat_reduce (pre:=[::VAL_num (SM.Vi32 (Z.of_N base));
        VAL_num (SM.Vi32 (Z.of_nat i))]) (post:=tail)
        (system_guard_exec hs (system_store m) f Hi)).
    + eapply rtt_trans with (y:=(hs,system_store m,f,
        to_e_list [::BI_const_num (SM.Vi32 (Z.of_N base));
          BI_const_num (SM.Vi32 (Z.of_nat i*8)); BI_binop T_i32 (Binop_i BOI_add);
          BI_load T_i64 None (SM.Ma 0%num 3%num)])).
      * apply (system_flat_reduce (pre:=[::VAL_num (SM.Vi32 (Z.of_N base))])
          (es:=to_e_list [::BI_const_num (SM.Vi32 (Z.of_nat i));
            BI_const_num (SM.Vi32 8); BI_binop T_i32 (Binop_i BOI_mul)])
          (es':=[::AI_basic (BI_const_num (SM.Vi32 (Z.of_nat i*8)))])
          (post:=to_e_list [::BI_binop T_i32 (Binop_i BOI_add);
            BI_load T_i64 None (SM.Ma 0%num 3%num)])).
        apply rtt_step1. apply r_simple. apply rs_binop_success;
          [reflexivity|exact (system_index_mul Hi)].
      * eapply rtt_trans with (y:=(hs,system_store m,f,to_e_list
          [::BI_const_num (SM.Vi32 (Z.of_N base+Z.of_nat i*8));
              BI_load T_i64 None (SM.Ma 0%num 3%num)])).
        -- apply (system_flat_reduce (pre:=[::])
             (es:=to_e_list [::BI_const_num (SM.Vi32 (Z.of_N base));
               BI_const_num (SM.Vi32 (Z.of_nat i*8)); BI_binop T_i32 (Binop_i BOI_add)])
             (es':=[::AI_basic (BI_const_num (SM.Vi32 (Z.of_N base+Z.of_nat i*8)))])
             (post:=to_e_list [::BI_load T_i64 None (SM.Ma 0%num 3%num)])).
           apply rtt_step1. apply r_simple. apply rs_binop_success;
             [reflexivity|exact (system_address_add Hb Hi)].
        -- have Heq : (Z.of_N base+Z.of_nat i*8 = Z.of_N (base+8*N.of_nat i))%Z by lia.
           rewrite Heq. exact (system_array_load hs Hf Hr Hnth).
Qed.

Lemma batch_triple_conseq m P P' es Q Q' :
 aentails P P' -> aentails Q' Q -> system_triple m P' es Q' -> system_triple m P es Q.
Proof.
 move=> HP HQ H f Hi hs V vs h Hp Hr.
 have [s' [f' [V' [vs' [h' [Hv [Hred [Hq Hr']]]]]]]] := H f Hi hs V vs h (HP V (vs,h) Hp) Hr.
 exists s',f',V',vs',h'. split; first exact Hv. split; first exact Hred.
 split; last exact Hr'. exact (HQ V' (vs',h') Hq).
Qed.
Lemma batch_frame_consts m (vf : seq value_num) S S' H H' es :
 system_triple m (AS_base S H) es (AS_base S' H') ->
 system_triple m (AS_base ([seq T_const v | v <- vf] ++ S) H) es
 (AS_base ([seq T_const v | v <- vf] ++ S') H').
Proof.
 move=> Htr f Hi hs V vs h [Hs HH] Hr.
 move: Hs. rewrite /= stack_denote_cat_control stack_denote_consts.
 case Es: (stack_denote V S) => [vs0|] //. case=> Hvs. subst vs.
 have [s' [f' [V' [vs' [h' [Hlog [Hred [HQ Hr']]]]]]]] :=
 Htr f Hi hs V vs0 h (conj Es HH) Hr.
 move: HQ => /= [Hs' HH'].
 exists s',f',V',(vf++vs'),h'. split; first exact Hlog. split.
 - have Hlift := reduce_trans_lfill (LH_base [seq VAL_num v | v <- vf] [::])
   (x:=(hs,system_store m,f,vn_to_e vs0 ++ to_e_list es))
   (y:=(hs,s',f',vn_to_e vs')) Hred.
   move: Hlift. rewrite /cfg_lfill /lfill /= v_to_e_list_VAL_num !cats0.
   by rewrite !vn_to_e_cat catA.
 - split; last exact Hr'. split; last exact HH'.
   by rewrite stack_denote_cat_control stack_denote_consts Hs'.
Qed.
Lemma array_read_tail_sem m base xs i x tmp H :
 array_region m base xs -> List.nth_error xs i = Some x ->
 pinned tmp (SM.Vi32 (Z.of_nat i)) H ->
 system_triple m
 (AS_base [::T_const (SM.Vi32 (Z.of_N base));T_const (SM.Vi32 (Z.of_nat i))] H)
 (array_read_tail tmp) (AS_base [::T_const (VAL_int64 x)] H).
Proof.
 move=> Hregion Hnth Hpin f Hi hs V vs h [Hs HH] Hr.
 cbn in Hs. inversion Hs; subst vs.
 have Hlr : loc_read f tmp = Some (SM.Vi32 (Z.of_nat i)).
 { rewrite -(reifies_sto_loc Hr tmp). exact (Hpin V h HH). }
 have Hlocal := loc_read_lookup Hlr.
 exists (system_store m),f,V,[::VAL_int64 x],h.
 split; first reflexivity. split.
 - exact (array_read_tail_exec hs Hi Hregion Hnth Hlocal).
 - split; last exact Hr. by split.
Qed.
Definition array_access ptr idx tmp : seq basic_instruction :=
 [::BI_local_get ptr;BI_local_get idx;BI_local_tee tmp] ++ array_read_tail tmp.
Lemma array_access_sem m base xs i x ptr idx tmp H :
 array_region m base xs -> List.nth_error xs i = Some x ->
 pinned ptr (SM.Vi32 (Z.of_N base)) H -> pinned idx (SM.Vi32 (Z.of_nat i)) H ->
 loc_present tmp H -> loc_stable tmp (SM.Vi32 (Z.of_nat i)) H ->
 system_triple m (AS_base [::] H) (array_access ptr idx tmp)
 (AS_base [::T_const (VAL_int64 x)] H).
Proof.
 move=> Hregion Hnth Hp Hi Hpresent Hstable.
 rewrite /array_access.
 apply: (system_triple_seq
  (es1:=[::BI_local_get ptr;BI_local_get idx;BI_local_tee tmp])
  (Q1:=AS_base [::T_const (SM.Vi32 (Z.of_N base));T_const (SM.Vi32 (Z.of_nat i))]
   (HA_and (term_eq (T_local tmp) (T_const (SM.Vi32 (Z.of_nat i)))) H))).
 - reflexivity.
 - apply: system_triple_of_pure.
   apply: (sem_seq (es1:=[::BI_local_get ptr])
    (Q:=AS_base [::T_const (SM.Vi32 (Z.of_N base))] H)).
   + exact: get_pinned_frame.
   + apply: (sem_seq (es1:=[::BI_local_get idx])
      (Q:=AS_base [::T_const (SM.Vi32 (Z.of_N base));T_const (SM.Vi32 (Z.of_nat i))] H)).
     * exact: get_pinned_frame.
     * apply: (sem_frame_consts (vf:=[::SM.Vi32 (Z.of_N base)])).
       exact: sem_local_tee_const_frame.
 - apply: (batch_triple_conseq
    (P':=AS_base [::T_const (SM.Vi32 (Z.of_N base));T_const (SM.Vi32 (Z.of_nat i))]
      (HA_and (term_eq (T_local tmp) (T_const (SM.Vi32 (Z.of_nat i)))) H))
    (Q':=AS_base [::T_const (VAL_int64 x)]
      (HA_and (term_eq (T_local tmp) (T_const (SM.Vi32 (Z.of_nat i)))) H))).
   + by [].
   + move=> V [vs h] [Hs [_ HH]]. by split.
   + apply: (array_read_tail_sem (xs:=xs)); [exact Hregion|exact Hnth|]. apply: pinned_left. exact: pinned_bare.
Qed.
End Host.
Print Assumptions array_access_sem.
