Require Import CoqlibCCR.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import SimModSem.
Require Import PCM.
Require Import HoareDef.
Require Import STB.
Require Import HTactics ProofMode.
Require Import HSim IProofMode.
Require Import ClightPlusSkel ClightPlusExprgen ClightPlusgen.
Require Import ClightPlusMem0 ClightPlusMem1 ClightPlusMemAux.
Require Import CProofMode CIProofMode.
Require Import vector.
Require Import vector0.
Require Import vector1.
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Clightdefs.
Require Import vector_auxiliary.

Section PROOF.

  Import ClightPlusMem1.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb vectorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).

  Variable sk: Sk.t.
  Hypothesis SKINCL1 : Sk.le (vector_compiled.(Mod.sk)) sk.
  Hypothesis SKINCL2 : Sk.le mfsk sk.
  Hypothesis SKWF : Sk.wf sk.

  Let ce := Maps.PTree.elements (prog_comp_env prog).

  Lemma sim_vector_get :
    sim_fnsem wf top2
      ("vector_get", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_get_spec))
      ("vector_get", cfunU (decomp_func sk ce f_vector_get)).
  Proof.
    Local Opaque encode_val.
    Local Opaque cast_to_ptr.
    econs; ss. red.

    unfold prog, mkprogram in ce.
    destruct (build_composite_env' composites I). ss.
    get_composite ce e. fold vector._vector in get_co.

    pose proof (incl_incl_env SKINCL1) as SKINCLENV1. unfold incl_env in SKINCLENV1.
    pose proof (incl_incl_env SKINCL2) as SKINCLENV2. unfold incl_env in SKINCLENV2.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto. i. simpl in x.
    destruct x as
      [[[[[[[[[[[[[[[[[[[
        [v data] esize] capacity] length] cells] mᵥ] tgᵥ] pᵥ] qᵥ] m_data] q_data]
        index] mvs_index] p_index] dst] mvs_dst] ofs_dst] m_dst] tg_dst] q_dst].
    unfold decomp_func, function_entry_c; ss.
    set (HIDDEN := hide 1).

    iIntros "[INV PRE]".
    iDestruct "PRE" as "[[% [V [MVS OFS]]] %]". des.
    revert H6. clarify. i. hred_r.

    unhide. hred_r. remove_tau.
    unhide. change Archi.ptr64 with true. ss. hred_r. remove_tau.
    iPoseProof (is_vector_fixed_is_ptr_val with "V") as "%".
    rewrite H3. hred_r. rewrite H3. hred_r.
    replace (alist_find vector._vector ce) with (Some co). hred_r.
    replace (ClightPlusExprgen.field_offset ce _data (co_members co))
      with (Errors.OK 0%Z)
      by (rewrite co_co_members; ss).
    hred_r.

    iPoseProof (is_vector_fixed_is_ptr_data with "V") as "%".
    iApply isim_apc. iExists (Some (4: Ord.t)).
    iPoseProof (accessor_is_vector_fixed_is_vector_handler with "V") as ([]) "[VH V_RECOVER]".
    iPoseProof (accessor_is_vector_handler_data with "VH") as (ofsᵥ) "[DATA VH_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { apply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=3%ord). apply OrdArith.lt_from_nat. lia. }
    iSplitL "INV DATA". { iSplitL "INV"; done. }
    iIntros (st_src0 st_tgt0) "[INV DATA]".
    iPoseProof ("VH_RECOVER" with "[DATA]") as "VH".
    { iFrame; ss. }
    iPoseProof ("V_RECOVER" $! () with "VH") as "V".
    clear ofsᵥ.

    Local Transparent cast_to_ptr.
    hred_r.
    iPoseProof (is_vector_fixed_is_ptr_data with "V") as "%".
    rewrite (decode_encode_ptr _ H4).
    rewrite (cast_to_ptr_ptr _ H4).
    hred_r.

    rewrite H3. hred_r. rewrite H3. hred_r.
    replace (ClightPlusExprgen.field_offset ce _esize (co_members co))
      with (Errors.OK 8%Z)
      by (rewrite co_co_members; ss).
    hred_r.

    iPoseProof (accessor_is_vector_fixed_is_vector_handler with "V") as ([]) "[VH V_RECOVER]".
    iPoseProof (accessor_is_vector_handler_esize with "VH") as (ofsᵥ) "[ESIZE VH_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { apply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=2%ord). apply OrdArith.lt_from_nat. lia. }
    iDestruct "ESIZE" as "[ESIZE %]".
    iSplitL "INV ESIZE". { iSplitL "INV". done. iSplit; done. }
    iIntros (st_src1 st_tgt1) "[INV ESIZE]".

    rewrite decode_encode_item. hred_r.
    unfold sem_mul_c. ss.
    change Archi.ptr64 with true. hred_r.
    rewrite sem_add_ptr_long_c_addl; ss. hred_r.
    rewrite cast_to_ptr_ptr.
      2: { destruct data; ss. }
    hred_r.
    remove_tau. unhide. hred_r. remove_tau.

    change Archi.ptr64 with true; ss.
    hexploit SKINCLENV2. { right. right. left. ss. }
    i. des. rewrite FIND. hred_r.
    rewrite H3. hred_r. rewrite H3. ss.
    replace (alist_find vector._vector ce) with (Some co). hred_r.
    replace (ClightPlusExprgen.field_offset ce _esize (co_members co))
      with (Errors.OK 8%Z)
      by (rewrite co_co_members; ss).
    hred_r.

    iApply isim_ccallU_load.
    { ss. }
    { apply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=1%ord). apply OrdArith.lt_from_nat. lia. }
    iSplitL "INV ESIZE". { iSplitL "INV". done. iSplit; done. }
    iIntros (st_src2 st_tgt2) "[INV ESIZE]".
    iPoseProof ("VH_RECOVER" with "ESIZE") as "VH".
    iPoseProof ("V_RECOVER" $! () with "VH") as "V".

    rewrite decode_encode_item. hred_r.
    change Archi.ptr64 with true. ss. hred_r.
    iPoseProof (points_to_is_ptr with "MVS") as "%".
    rewrite ! cast_to_ptr_ptr.
      2: { destruct data; ss. }
      2: { ss. }
    hred_r.

    des_if; ss. hred_r.
    rewrite SuccNat2Pos.pred_id.
    erewrite SKINCLGD; cycle 1.
    { ss. }
    { apply SKINCL2. }
    { apply FIND. }
    { right. right. left. reflexivity. }
    hred_r.

    replace (Vlong (Int64.mul (Int64.repr esize) (Int64.repr index)))
      with (Vptrofs (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.repr index))); cycle 1.
    { unfold Vptrofs. change Archi.ptr64 with true; ss. f_equal.
      etransitivity.
      - eapply Ptrofs_to_int64_mul_comm.
      - f_equal; eapply Ptrofs_to_int64_repr_comm.
    }

    iApply isim_ccallU_memcpy0.
    { ss. }
    { apply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=0%ord). apply OrdArith.lt_from_nat. lia. }

    iPoseProof (is_vector_fixed_cells_esize with "V") as "%".
    iPoseProof (is_vector_fixed_esize_range with "V") as "%".
    iPoseProof (accessor_is_vector_fixed_cells with "V") as ([]) "[[CELLS HO] V_RECOVER]".
    iPoseProof ((accessor_cells_cell esize data m_data cells index) with "CELLS") as ([]) "[CELL CELLS_RECOVER]"; et.
    ss.

    iSplitL "MVS OFS INV HO CELL".
    { iFrame.
      iExists mvs_dst.
      iFrame.
      iSplit.
      - iPureIntro. splits.
        + eapply Forall_lookup_1 in H13; et. ss. congruence.
        + rewrite Int64.unsigned_repr.
          * rewrite Nat2Z.id. ss.
          * lia.
        + left. ss.
        + apply Z.divide_1_l.
        + apply Z.divide_1_l.
        + rewrite Int64.unsigned_repr; lia.
        + apply Z.divide_1_l.
      - iApply offset_slide. iFrame.
    }
    iIntros (st_src3 st_tgt3) "[INV [[[HO OFS] CELL] MVS]]".
    iPoseProof (offset_slide_rev with "HO") as "HO".
    iPoseProof ("CELLS_RECOVER" $! () with "CELL") as "CELLS".
    iPoseProof ("V_RECOVER" $! () with "[CELLS HO]") as "V". { iFrame. }
    hred_r. remove_tau.

    hred_l.
    iApply isim_choose_src. iExists (Vundef↑).
    iApply isim_ret.
    iFrame. iPureIntro. ss.
  Qed.

End PROOF.
