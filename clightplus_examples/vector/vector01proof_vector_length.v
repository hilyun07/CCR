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

  Lemma sim_vector_length :
    sim_fnsem wf top2
      ("vector_length", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_length_spec))
      ("vector_length", cfunU (decomp_func sk ce f_vector_length)).
  Proof.
    Local Opaque encode_val.
    Local Opaque cast_to_ptr.
    econs; ss. red.

    unfold prog, mkprogram in ce.
    destruct (build_composite_env' composites I). ss.
    get_composite ce e. fold vector._vector in get_co.

    apply isim_fun_to_tgt; auto. i. simpl in x.
    destruct x as [[[[[[[[[[[v data] esize] capacity] length] cells] mᵥ] tgᵥ] pᵥ] qᵥ] m_data] q_data].
    unfold decomp_func, function_entry_c; ss.
    set (HIDDEN := hide 1).

    iIntros "[INV PRE]".
    iDestruct "PRE" as "[[% V] %]".
    clarify. hred_r.

    unhide; change Archi.ptr64 with true; ss. hred_r. remove_tau.
    iPoseProof (is_vector_fixed_is_ptr_val with "V") as "%".
    rewrite H3. hred_r. rewrite H3. hred_r.
    replace (alist_find vector._vector ce) with (Some co) by (apply get_co).
    hred_r.
    replace (ClightPlusExprgen.field_offset ce _length (co_members co)) with (Errors.OK 24%Z)
      by (rewrite co_co_members; reflexivity).
    hred_r.
    iApply isim_apc. iExists (Some (1 : Ord.t)).
    iPoseProof (accessor_is_vector_fixed_is_vector_handler with "V") as ([]) "[VH V_RECOVER]".
    iPoseProof (accessor_is_vector_handler_length with "VH") as (ofsᵥ) "[LENGTH VH_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { eapply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=0%ord). eapply OrdArith.lt_from_nat. lia. }
    iSplitL "INV LENGTH". { iSplitL "INV"; done. }
    iIntros (st_src0 st_tgt0) "[INV LENGTH]".
    iPoseProof ("VH_RECOVER" with "LENGTH") as "VH".
    iPoseProof ("V_RECOVER" $! () with "VH") as "V".

    Local Transparent cast_to_ptr.
    hred_r. rewrite decode_encode_item. ss. change Archi.ptr64 with true. ss. hred_r.

    hred_l. iApply isim_choose_src. iExists (Any.upcast (Vlong (Int64.repr length))).

    iApply isim_ret.
    iSplitL "INV"; et.
  Qed.

End PROOF.
