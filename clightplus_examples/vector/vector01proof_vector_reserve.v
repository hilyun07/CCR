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

  Lemma sim_vector_reserve :
    sim_fnsem wf top2
      ("vector_reserve", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_reserve_spec))
      ("vector_reserve", cfunU (decomp_func sk ce f_vector_reserve)).
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
    destruct x as [[[[[[[[v esize] capacity] length] cells] mᵥ] tgᵥ] qᵥ] min_capacity].
    unfold decomp_func, function_entry_c; ss.
    set (HIDDEN := hide 1).

    iIntros "[INV PRE]".
    iDestruct "PRE" as "[[% V] %]". des.
    clarify. hred_r.

    unhide. hred_r. remove_tau.
    unhide. hred_r. change Archi.ptr64 with true. ss. remove_tau.
    iPoseProof (is_vector_is_ptr_val with "V") as "%".
    rewrite H3. hred_r. rewrite H3. hred_r.
    replace (alist_find vector._vector ce) with (Some co). hred_r.
    replace (ClightPlusExprgen.field_offset ce _capacity (co_members co))
      with (Errors.OK 16%Z)
      by (rewrite co_co_members; ss).
    hred_r.

    iPoseProof (is_vector_esize_range with "V") as "%".
    iPoseProof (is_vector_capacity_range with "V") as "%".
    assert (0 < min_capacity <= Int64.max_unsigned)%Z by nia.

    iApply isim_apc. iExists (Some (8: Ord.t)).
    iPoseProof (accessor_is_vector_is_vector_handler with "V") as (data) "[VH V_RECOVER]".
    iPoseProof (is_vector_handler_is_ptr_data with "VH") as "%".

    iPoseProof (accessor_is_vector_handler_capacity with "VH") as (ofsᵥ) "[CAPACITY VH_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { apply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=7%ord). apply OrdArith.lt_from_nat. lia. }
    iSplitL "INV CAPACITY". { iSplitL "INV"; done. }
    iIntros (st_src0 st_tgt0) "[INV CAPACITY]".
    iPoseProof ("VH_RECOVER" with "CAPACITY") as "VH".
    clear ofsᵥ.

    Local Transparent cast_to_ptr.
    hred_r.
    rewrite decode_encode_item. ss.
    change Archi.ptr64 with true. ss.
    hred_r.

    destruct (Int64.ltu (Int64.repr capacity) (Int64.repr min_capacity)) eqn:LTU; ss; cycle 1.
    { apply Int64_ltu_false in LTU.
      rewrite ! Int64.unsigned_repr in LTU; try lia.
      change (Int.eq Int.one Int.zero) with false. hred_r.
      unhide. hred_r. remove_tau.
      iPoseProof ("V_RECOVER" $! () with "VH") as "V".
      hred_l.
      iApply isim_choose_src.
      iExists (Vundef↑).
      iApply isim_ret.
      iSplitL "INV". { iFrame. }
      replace (max capacity min_capacity) with capacity by lia.
      iSplit; ss; iSplit; ss.
    }

    apply Int64_ltu_true in LTU.
    rewrite ! Int64.unsigned_repr in LTU; try lia.
    change (Int.eq Int.zero Int.zero) with true. hred_r.
    unhide. hred_r. remove_tau.
    unhide. hred_r. remove_tau.
    unhide. hred_r. remove_tau.
    unhide. hred_r. remove_tau.
    change Archi.ptr64 with true. ss.

    hexploit SKINCLENV2. { right. right. right. left. ss. }
    i. des. rewrite FIND. hred_r.
    rewrite H3. hred_r. rewrite H3. hred_r.
    replace (alist_find vector._vector ce) with (Some co). hred_r.
    replace (ClightPlusExprgen.field_offset ce _data (co_members co))
      with (Errors.OK 0%Z)
      by (rewrite co_co_members; ss).
    hred_r.

    iPoseProof (accessor_is_vector_handler_data with "VH") as (ofsᵥ) "[DATA VH_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { apply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=6%ord). apply OrdArith.lt_from_nat. lia. }
    iSplitL "INV DATA". { iSplitL "INV"; done. }
    iIntros (st_src1 st_tgt1) "[INV DATA]".
    iPoseProof ("VH_RECOVER" with "[DATA]") as "VH". { iFrame; ss. }
    clear ofsᵥ.

    rewrite (decode_encode_ptr _ H9). hred_r.
    rewrite H3. hred_r. rewrite H3. hred_r.
    replace (ClightPlusExprgen.field_offset ce _esize (co_members co))
      with (Errors.OK 8%Z)
      by (rewrite co_co_members; ss).
    hred_r.

    iPoseProof (accessor_is_vector_handler_esize with "VH") as (ofsᵥ) "[ESIZE VH_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { apply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=5%ord). apply OrdArith.lt_from_nat. lia. }
    iSplitL "INV ESIZE". { iSplitL "INV"; done. }
    iIntros (st_src2 st_tgt2) "[INV ESIZE]".
    iPoseProof ("VH_RECOVER" with "ESIZE") as "VH".
    clear ofsᵥ.

    rewrite decode_encode_item. hred_r.
    unfold sem_mul_c. ss.
    change Archi.ptr64 with true. hred_r.
    change Archi.ptr64 with true. hred_r.
    rewrite (cast_to_ptr_ptr _ H9). hred_r.

    des_if; ss. hred_r.
    rewrite SuccNat2Pos.pred_id.
    erewrite SKINCLGD; cycle 1.
    { ss. }
    { apply SKINCL2. }
    { apply FIND. }
    { right. right. right. left. ss. }
    hred_r.
  Admitted.

End PROOF.
