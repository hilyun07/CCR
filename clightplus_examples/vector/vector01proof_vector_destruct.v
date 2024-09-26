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

  Lemma sim_vector_destruct :
    sim_fnsem wf top2
      ("vector_destruct", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_destruct_spec))
      ("vector_destruct", cfunU (decomp_func sk ce f_vector_destruct)).
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
    destruct x as [[[[[[[v esize] capacity] length] cells] mᵥ] tgᵥ] qᵥ].
    unfold decomp_func, function_entry_c; ss.
    set (HIDDEN := hide 1).

    iIntros "[INV PRE]".
    iDestruct "PRE" as "[[% V] %]".
    clarify. hred_r.

    unhide. hred_r. remove_tau.
    unhide. hred_r. remove_tau.
    hexploit SKINCLENV2.
    { right. left. ss. }
    i. des. rewrite FIND. hred_r.

    iPoseProof (is_vector_is_ptr_val with "V") as "%".
    rewrite H3. hred_r. rewrite H3. hred_r.
    replace (alist_find vector._vector ce) with (Some co).
    hred_r.
    replace (ClightPlusExprgen.field_offset ce _data (co_members co))
      with (Errors.OK 0%Z)
      by (rewrite co_co_members; ss).
    change Archi.ptr64 with true. ss. hred_r.

    unfold is_vector.
    iDestruct "V" as (data m_data unused_length unused) "[% [V [LPT [DATA_HO DATA_PT]]]]". des.

    iApply isim_apc. iExists (Some (3: Ord.t)).
    iPoseProof (accessor_is_vector_handler_data with "V") as (ofsᵥ) "[DATA V_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { eapply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=2%ord). eapply OrdArith.lt_from_nat. lia. }
    iSplitL "INV DATA". { iSplitL "INV"; done. }
    iIntros (st_src0 st_tgt0) "[INV DATA]".
    iPoseProof (offset_is_ptr with "DATA_HO") as "%".
    iPoseProof ("V_RECOVER" with "[DATA]") as "V".
    { iFrame; ss. }
    clear ofsᵥ.

    iPoseProof (offset_is_ptr with "DATA_HO") as "%".
    hred_r.
    rewrite (decode_encode_ptr _ H13).
    rewrite (cast_to_ptr_ptr _ H13).
    hred_r.

    des_if; ss. hred_r.
    rewrite SuccNat2Pos.pred_id.
    erewrite SKINCLGD; cycle 1.
    { ss. }
    { apply SKINCL2. }
    { apply FIND. }
    { right. left. ss. }
    hred_r.

    iApply isim_ccallU_mfree.
    { ss. }
    { eapply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=1%ord). eapply OrdArith.lt_from_nat. lia. }

    iPoseProof (list_points_to_collect with "LPT") as (mvs) "[% PT]"; et.
    rewrite H8 in H15.
    iPoseProof (points_to_collect with "[PT DATA_PT]") as "PT".
    { iSplitL "PT". iFrame.
      rewrite H15.
      replace (Z.of_nat (esize * length))%nat with (Z.of_nat esize * Z.of_nat length)%Z
        by (symmetry; apply Nat2Z.inj_mul).
      iFrame.
    }
    iSplitL "INV DATA_HO PT".
    { iFrame.
      iExists m_data, (mvs ++ unused). iFrame.
      iPureIntro. rewrite app_length. lia.
    }

    iIntros (st_src1 st_tgt1) "INV".
    hred_r. remove_tau. unhide.
    change Archi.ptr64 with true. ss.
    hred_r. remove_tau.
    rewrite H3. hred_r. rewrite H3. hred_r.
    replace (alist_find vector._vector ce) with (Some co).
    hred_r.
    replace (ClightPlusExprgen.field_offset ce _data (co_members co))
      with (Errors.OK 0%Z)
      by (rewrite co_co_members; ss).
    change (Ptrofs.repr 0) with Ptrofs.zero.
    rewrite (is_ptr_val_null_r); ss.
    hred_r.

    rewrite cast_long; ss.
    change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with Vnullptr.
    hred_r.

    iPoseProof (accessor_is_vector_handler_data with "V") as (ofsᵥ) "[DATA V_RECOVER]".
    rewrite is_ptr_val_null_r; ss.
    iApply isim_ccallU_store.
    { ss. }
    { apply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=0%ord). apply OrdArith.lt_from_nat. lia. }
    iSplitL "INV DATA".
    { iDestruct "DATA" as "[[PT HO] %]". des.
      iSplitL "INV".
      - iFrame.
      - iExists (encode_val Mptr data).
        iFrame. iPureIntro. ss.
    }
    iIntros (st_src2 st_tgt2) "[INV [PT HO]]".
    hred_r. remove_tau.
    iPoseProof ("V_RECOVER" with "[PT HO]") as "V". { iFrame; ss. }
    clear ofsᵥ.

    hred_l.
    iApply isim_choose_src. iExists (Vundef↑).
    iApply isim_ret. iFrame. iSplit; ss.

    iDestruct "V" as (ofsᵥ) "(% & PT1 & PT2 & PT3 & PT4 & HO)".
    rewrite is_ptr_val_null_r; ss.
    iPoseProof (points_to_collect with "[PT1 PT2]") as "PT". { iSplitL "PT1"; iFrame. }
    iPoseProof (points_to_collect with "[PT PT3]") as "PT". { iSplitL "PT"; iFrame. }
    iPoseProof (points_to_collect with "[PT PT4]") as "PT". { iSplitL "PT"; iFrame. }
    iExists (encode_val Mptr Vnullptr
               ++ encode_val Mint64 (Vlong (Int64.repr esize))
               ++ encode_val Mint64 (Vlong (Int64.repr capacity))
               ++ encode_val Mint64 (Vlong (Int64.repr length))).
    iExists ofsᵥ. iFrame; ss.
  Qed.

End PROOF.
