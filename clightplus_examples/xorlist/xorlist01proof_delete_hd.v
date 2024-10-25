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
Require Import ClightPlusMemRA ClightPlusMem0 ClightPlusMem1 ClightPlusMemAux.
Require Import CProofMode CIProofMode.
Require Import xorlist.
Require Import xorlistall0.
Require Import xorlist1.
Require Export xorlist01proof_header.
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Memory Clightdefs.

Section PROOF.

  Import ClightPlusMem1.

  Context `{@GRA.inG Mem.t Σ}.

  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb xorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).


  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.

  Let mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)); ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))].

  Section SIMFUNS.
  Variable xorlink : Clight.program.
  (* Variable xormod : Mod.t. *)
  Hypothesis VALID_link : xorlistall0._xor = Some xorlink.
  (* Hypothesis VALID_comp : compile xorlink "xorlist" = Errors.OK xormod. *)
  Let ce := Maps.PTree.elements (prog_comp_env xorlink).

  Variable sk: Sk.t.
  (* TODO: How to encapsulate fuction info? *)
  (* Hypothesis SKINCL1 : Sk.le (xormod.(Mod.sk)) sk. *)
  Hypothesis SKINCL : Sk.le mfsk sk.
  Hypothesis SKWF : Sk.wf sk.

  Lemma sim_delete_hd :
    sim_fnsem wf top2 ("delete_hd", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure delete_hd_spec))
                      ("delete_hd", cfunU (decomp_func sk ce f_delete_hd)).
  Proof.
    Local Opaque encode_val.
    eassert (_xor = _); [unfold _xor; vm_compute (Linking.link _ _); reflexivity|].
    rewrite H0 in *. clear H0. destruct Ctypes.link_build_composite_env. destruct a.
    inversion VALID_link. clear VALID_link. subst. clear a. simpl in ce. econs; ss. red.

    (* current state: 1 *)
    get_composite ce e. dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply incl_incl_env in SKINCLENV. unfold incl_env in SKINCLENV. pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto. unfold f_delete_hd. i; ss.
    unfold decomp_func, function_entry_c. ss. let H := fresh "HIDDEN" in set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss. iDestruct "PRE" as "[[% PRE] %]". unfold full_xorlist.
    iDestruct "PRE"
      as (m_hd_hdl m_tl_hdl hd_old tl_old ofs_hd_hdl ofs_tl_hdl)
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    clarify. hred_r. unhide. hred_r. unhide. remove_tau.
    rename v into hd_handler.  rename v0 into tl_handler. rename l into linput. des. clarify.
    rename H0 into tl_hdl_align. rename H1 into hd_hdl_align. rename H2 into hd_hdl_sz. rename H3 into tl_hdl_sz.

    (* stack allocation start *)
    unhide. hred_r. iApply isim_apc. iExists (Some (50%nat : Ord.t)).
    iApply isim_ccallU_salloc; ss; oauto.  iSplitL "INV"; iFrame.  { iPureIntro. ss. }
    iIntros (sts0' stt0' hhs m_hhs b_hhs) "[INV [[% hhsp] hhso]]".  rename H0 into hhs_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts1' stt1' ths m_ths b_ths) "[INV [[% thsp] thso]]". rename H0 into ths_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts2' stt2' ims m_is b_is) "[INV [[% isp] isofs]]". rename H0 into is_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts3' stt3' tos m_tos b_tos) "[INV [[% tospt] toso]]". rename H0 into tos_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts4' stt4' tns m_tns b_tns) "[INV [[% tnsp] tnso]]". rename H0 into tns_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts5' stt5' lns m_lns b_lns) "[INV [[% lnsp] lnso]]". rename H0 into lns_sz. des. hred_r.
    iPoseProof (live_trivial_offset with "hhso") as "[hhso hhs_eq]"; et.
    iPoseProof (live_trivial_offset with "thso") as "[thso ths_eq]"; et.
    iPoseProof (live_trivial_offset with "isofs") as "[isofs is_eq]"; et.
    iPoseProof (live_trivial_offset with "toso") as "[toso tos_eq]"; et.
    iPoseProof (live_trivial_offset with "tnso") as "[tnso tns_eq]"; et.
    iPoseProof (live_trivial_offset with "lnso") as "[lnso lns_eq]"; et.
    iPoseProof (equiv_dup with "hhs_eq") as "[hhs_eq hhs_eq']".
    iPoseProof (equiv_point_comm with "[hhsp hhs_eq']") as "hhsp". { iFrame. }
    iPoseProof (equiv_dup with "ths_eq") as "[ths_eq ths_eq']".
    iPoseProof (equiv_point_comm with "[thsp ths_eq']") as "thsp". { iFrame. }
    iPoseProof (equiv_dup with "is_eq") as "[is_eq is_eq']".
    iPoseProof (equiv_point_comm with "[isp is_eq']") as "isp". { iFrame. }
    iPoseProof (equiv_dup with "tos_eq") as "[tos_eq tos_eq']".
    iPoseProof (equiv_point_comm with "[tospt tos_eq']") as "tospt". { iFrame. }
    iPoseProof (equiv_dup with "tns_eq") as "[tns_eq tns_eq']".
    iPoseProof (equiv_point_comm with "[tnsp tns_eq']") as "tnsp". { iFrame. }
    iPoseProof (equiv_dup with "lns_eq") as "[lns_eq lns_eq']".
    iPoseProof (equiv_point_comm with "[lnsp lns_eq']") as "lnsp". { iFrame. }
    iPoseProof (live_has_offset with "hhso") as "[hhso hhso_ofs]".
                                                 
    iApply isim_ccallU_store;ss; oauto. iSplitL "INV hhsp hhso_ofs"; iFrame; [storezero|].
    iIntros (sts6' stt6') "[INV hhsp]". iPoseProof (live_has_offset with "thso") as "[thso thso_ofs]".
    hred_r. iApply isim_ccallU_store; ss; oauto. iSplitL "INV thsp thso_ofs"; iFrame; [storezero|].
    iIntros (sts7' stt7') "[INV thsp]". iPoseProof (live_has_offset with "isofs") as "[isofs isofs_ofs]".

    (* current state: 2 *)
    hred_r. unhide. hred_r. unhide. remove_tau.
    iApply isim_ccallU_store; ss; oauto. iSplitL "INV isp isofs_ofs"; iFrame; [storezero|].
    iIntros (sts8' stt8') "[INV isp]". hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.

    (* node hd_old = *hdH start *)
    iPoseProof (live_has_offset with "hhso") as "[hhso hhso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hhsp hhso_ofs"; iFrame; [loadzero|].
    iIntros (sts10' stt10') "[INV hhsp]". hred_r. iPoseProof (decode_encode_ptr_point with "hd_hdl_point") as "#->".
    iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%". rewrite H0. rename H0 into hd_hdl_ptr. hred_r.

    iPoseProof (xorlist_hd_deen with "LIST") as "%". rename H0 into hd_deen.
    iPoseProof (xorlist_hd_not_Vundef with "LIST") as "%". rename H0 into hd_notundef.
    iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame; [loadzero|].
    iIntros (sts0 stt0) "[INV hd_hdl_point]". rewrite hd_deen. hred_r.
    iPoseProof (@xorlist_hd_cast_to_ptr with "LIST") as "#->". hred_r.
    iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV tospt toso_ofs"; iFrame; [storezero|]. iIntros (sts11' stt11') "[INV tospt]". hred_r.

    (* node hd_old = *hdH end *)

    (* if (hd_old != NULL) start *)
    hred_r. unhide. remove_tau. unhide. remove_tau.
    iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tospt toso_ofs"; iFrame; [loadzero|]. iIntros (sts12' stt12') "[INV tospt]". hred_r.
    iPoseProof (xorlist_hd_deen with "LIST") as "#->".
    change (Vlong (Int64.repr _)) with Vnullptr. destruct linput as [|v lnext].

    (* case: nil list *)
    { ss. iDestruct "LIST" as "[NULL_tl NULL_hd]". iPoseProof (null_equiv with "NULL_tl") as "%". subst.
      iPoseProof (equiv_sym with "NULL_hd") as "H". iPoseProof (null_equiv with "H") as "%". subst.
      iApply isim_ccallU_cmp_ptr0; ss; oauto. iSplitL "INV"; iFrame. iIntros (sts1 stt1) "INV".

      hred_r. destruct (Int.eq) eqn:?; ss; clarify. clear Heqb.
      (* if (hd_old != NULL) end *)

      unhide. hred_r. unhide. remove_tau. iPoseProof (live_has_offset with "isofs") as "[isofs iso_ofs]".
      iApply isim_ccallU_load; ss; oauto. iSplitL "INV isp iso_ofs"; iFrame; [loadzero|].
      iIntros (sts13' stt13') "[INV isp]". hred_r. change Vnullptr with (Vlong Int64.zero).
      epose proof (decode_encode_val_general (Vlong _) Mint64 Mint64). unfold decode_encode_val in H0.
      rewrite H0. clear H0. rewrite cast_long. hred_r.
      (* stack free starts *)
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV lnsp lnso"; iFrame; [freezero|]. iIntros (sts21' stt21') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV tnsp tnso"; iFrame; [freezero|]. iIntros (sts22' stt22') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV tospt toso"; iFrame; [freezero|]. iIntros (sts23' stt23') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV isp isofs"; iFrame; [freezero|]. iIntros (sts24' stt24') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV thsp thso"; iFrame; [freezero|]. iIntros (sts25' stt25') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV hhsp hhso"; iFrame; [freezero|]. iIntros (sts26' stt26') "INV". hred_r.
      2:{ ss. }

      (* prove post condition *)
      hred_l. iApply isim_choose_src. iExists _. iApply isim_ret.
      iFrame. iSplit; ss. iSplit; ss. iExists _,_,_,_,_,_. iFrame. iSplit; ss. }
    (* case: not nil list *)
    ss. destruct v; try solve [iDestruct "LIST" as "[]"]. rename i into hd_item.
    iDestruct "LIST" as (i_hd_prev i_hd_next m_hd_old) "[[[[% hd_pr_eq] hd_ofs] hd_pt] LIST]". rename H0 into m_hd_size.
    iPoseProof (sub_null_r with "hd_ofs") as "%". rename H0 into hd_sub_r.

    (* node* hd_new = (node* )hd_old->link start *)
    iApply isim_ccallU_cmp_ptr4; ss; oauto. rewrite hd_sub_r. iSplitL "INV hd_ofs"; iFrame.
    { iPureIntro. r. rewrite m_hd_size. change (size_chunk Mptr) with 8%Z. change (Ptrofs.unsigned Ptrofs.zero) with 0%Z. nia. }
    iIntros (sts1 stt1) "[INV hd_ofs]". hred_r. destruct (Int.eq) eqn: ?; ss; clarify. clear Heqb.
    (* if (hd_old != NULL) end *)

    unhide. hred_r. unhide. remove_tau.

    (* item = hd_old->item start *)
    iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tospt toso_ofs"; iFrame; [loadzero|]. iIntros (sts13' stt13') "[INV tospt]". hred_r.
    iPoseProof (decode_encode_ptr_point with "hd_pt") as "#->".
    iPoseProof (points_to_is_ptr with "hd_pt") as "%". rewrite H0. rename H0 into hd_is_ptr.
    hred_r. rewrite hd_is_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    iPoseProof (points_to_split with "hd_pt") as "[hd_pt_item hd_pt_key]". change Archi.ptr64 with true. hred_r.
    change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs Ptrofs.zero).
    iPoseProof (add_null_r with "hd_ofs") as "%". rewrite H0. rename H0 into hd_add_null.
    iPoseProof (live_has_offset with "hd_ofs") as "[hd_ofs hd_ofs_ofs]".

    iApply isim_ccallU_load; ss; oauto. iSplitL "INV hd_pt_item hd_ofs_ofs"; iFrame; [loadzero|].
    iIntros (sts2 stt2) "[INV hd_pt_item]". rewrite decode_encode_item. hred_r. change Archi.ptr64 with true. hred_r.
    iPoseProof (live_has_offset with "isofs") as "[isofs iso_ofs]".
    iApply isim_ccallU_store; ss; oauto. iSplitL "INV isp iso_ofs"; iFrame; [storezero|].
    iIntros (sts14' stt14') "[INV isp]". hred_r.

    (* item = hd_old->item end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* hd_new = (node* )hd_old->link start *)
    iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tospt toso_ofs"; iFrame; [loadzero|]. iIntros (sts15' stt15') "[INV tospt]". hred_r.
    iPoseProof (decode_encode_ptr_point with "hd_pt_item") as "#->".
    
    rewrite hd_is_ptr. hred_r. rewrite hd_is_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. change Archi.ptr64 with true. hred_r.
    change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
    iPoseProof (live_has_offset with "hd_ofs") as "[hd_ofs hd_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV hd_pt_key hd_ofs_ofs"; iFrame.
    { iExists _. iSplit. { iApply _has_offset_slide. et. } iPureIntro. rewrite encode_val_length. splits; et. exists 1. ss. }
    iIntros (sts3 stt3) "[INV hd_pt_key]". change Mptr with Mint64. rewrite decode_encode_ofs.
    hred_r. rewrite ptrofs_cast_ptr. hred_r. rewrite ptrofs_cast_ptr. hred_r. 
    iPoseProof (live_has_offset with "tnso") as "[tnso tnso_ofs]". iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV tnsp tnso_ofs"; iFrame; [storezero|]. iIntros (sts16' stt16') "[INV tnsp]". hred_r.
    (* hd_new = (node* )hd_old->link end *)

    (* hdH* = hd_new start *)
    remove_tau. unhide. remove_tau. unhide. remove_tau. iPoseProof (live_has_offset with "hhso") as "[hhso hhso_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV hhsp hhso_ofs"; iFrame; [loadzero|].
    iIntros (sts17' stt17') "[INV hhsp]". hred_r.  change Mint64 with Mptr.
    iPoseProof (decode_encode_ptr_point with "hd_hdl_point") as "#->". rewrite hd_hdl_ptr. hred_r.
    iPoseProof (live_has_offset with "tnso") as "[tnso tnso_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV tnsp tnso_ofs"; iFrame; [loadzero|].
    iIntros (sts18' stt18') "[INV tnsp]". hred_r.  rewrite decode_encode_ofs. rewrite ptrofs_cast_ptr. hred_r.   
    iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".
    
    iApply isim_ccallU_store; ss; oauto. iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame; [storezero'|].
    iIntros (sts4 stt4) "[INV hd_hdl_point]".
    (* hdH* = hd_new end *)

    (* if (hd_new == NULL) start *)
    hred_r. unhide. remove_tau. unhide. remove_tau. iPoseProof (live_has_offset with "tnso") as "[tnso tnso_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV tnsp tnso_ofs"; iFrame; [loadzero|].
    iIntros (sts19' stt19') "[INV tnsp]". hred_r. rewrite decode_encode_ofs.
    replace (Vlong (Int64.repr _)) with Vnullptr by et. iPoseProof (null_equiv with "hd_pr_eq") as "%".
    assert (i_hd_prev = Ptrofs.zero).
    { unfold Vptrofs, Vnullptr in *. destruct Archi.ptr64 eqn:?; [|ss].
      apply (f_equal (fun v => match v with Vlong i => i | _ => Int64.zero end)) in H0.
      apply (f_equal Ptrofs.of_int64) in H0. rewrite Ptrofs.of_int64_to_int64 in H0; et. }
    subst. clear H0. rewrite Ptrofs.xor_zero_l. destruct lnext.
    (* case: delete from singleton list *)
    - ss. iDestruct "LIST" as "[tl_equiv NULL_next]". iPoseProof (equiv_sym with "NULL_next") as "H".
      iPoseProof (null_equiv with "H") as "%". rewrite H0. clear H0 i_hd_next.
      iApply isim_ccallU_cmp_ptr0; ss; oauto. iSplitL "INV"; iFrame. iIntros (sts5 stt5) "INV".
      hred_r. des_ifs_safe. clear Heq. unhide. remove_tau.
      (* if (hd_new == NULL) end *)

      (* tlH* = NULL start *)
      iPoseProof (live_has_offset with "thso") as "[thso thso_ofs]". iApply isim_ccallU_load; ss; oauto. 
      iSplitL "INV thsp thso_ofs"; iFrame; [loadzero|]. iIntros (sts20' stt20') "[INV thsp]". hred_r.
      iPoseProof (decode_encode_ptr_point with "tl_hdl_point") as "#->".      
      iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%". rewrite H0. rename H0 into tl_hdl_ptr.

      hred_r. change Archi.ptr64 with true. hred_r.
      iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto. iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame; [storezero'|].
      iIntros (sts6 stt6) "[INV tl_hdl_point]". hred_r. unhide. remove_tau.

      (* free(hd_old) start *)
      hexploit SKINCLENV; [instantiate (2:="free"); et|]. i. des. ss. rewrite H0. rename H0 into free_loc. hred_r.
      iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV tospt toso_ofs"; iFrame;[loadzero|]. iIntros (sts21' stt21') "[INV tospt]". hred_r.
      iPoseProof (decode_encode_ptr_point with "hd_pt_item") as "#->".
      iPoseProof ((@point_cast_ptr _ _ Es) with "hd_pt_item") as "%".
      rewrite H0. rename H0 into hd_old_cast. hred_r. des_ifs_safe. clear e.

      replace (pred _) with blk by nia. erewrite SKINCLGD; et; [|ss; et]. hred_r.

      iCombine "hd_pt_item hd_pt_key" as "hd_pt".
      replace (Val.addl tl_old (Vlong _))
        with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (inj_bytes (encode_int 8 (Int64.unsigned hd_item))))))) by et.
      iPoseProof (points_to_collect with "hd_pt") as "hd_pt". iApply isim_ccallU_mfree; ss; oauto.
      iSplitL "INV hd_pt hd_ofs"; iFrame; [iExists _,_; iFrame; ss|]. iIntros (sts7 stt7) "INV". hred_r. unhide. remove_tau.
      (* free(hd_old) end *)

      iPoseProof (live_has_offset with "isofs") as "[isofs iso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV isp iso_ofs"; iFrame; [loadzero|]. iIntros (sts22' stt22') "[INV isp]". hred_r.
      unfold Mptr. change Archi.ptr64 with true. epose proof (decode_encode_val_general (Vlong _) Mint64 Mint64).
      unfold decode_encode_val in H0. rewrite H0. clear H0. rewrite cast_long; et. hred_r.
      
      (* stack free starts *)
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV lnsp lnso"; iFrame; [freezero|]. iIntros (sts23' stt23') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV tnsp tnso"; iFrame; [freezero|]. iIntros (sts24' stt24') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV tospt toso"; iFrame; [freezero|]. iIntros (sts25' stt25') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV isp isofs"; iFrame; [freezero|]. iIntros (sts26' stt26') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV thsp thso"; iFrame; [freezero|]. iIntros (sts27' stt27') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV hhsp hhso"; iFrame; [freezero|]. iIntros (sts28' stt28') "INV". hred_r.

      (* prove post condition *)
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iFrame. iSplit; ss. iSplit; ss. iExists _,_,_,_,_,_. iFrame; ss.

    (* case: list length is more than 1 *)
    - ss. destruct v; clarify. iDestruct "LIST" as (i_hd i_hd_nn m_hd_next) "[[[[% hd_equiv] hd_next_ofs] hd_nx_pt] LIST]".
      rename H0 into m_hd_next_size. rename i into hd_next_item.
      iPoseProof (sub_null_r with "hd_next_ofs") as "%". rename H0 into hd_next_sub_r.

      (* node* hd_new = (node* )hd_old->link start *)

      iApply isim_ccallU_cmp_ptr3; ss; oauto. rewrite hd_next_sub_r. iSplitL "INV hd_next_ofs"; iFrame.
      { iPureIntro. red. rewrite m_hd_next_size. change (Ptrofs.unsigned Ptrofs.zero) with 0%Z.
        change (size_chunk Mptr) with 8%Z. nia. } iIntros (sts5 stt5) "[INV hd_next_ofs]".
      (* if (hd_new == NULL) end *)

      hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau.

      (* link = (node* )hd_new->link start *)
      iPoseProof (live_has_offset with "tnso") as "[tnso tnso_ofs]". iApply isim_ccallU_load; ss; oauto. 
      iSplitL "INV tnsp tnso_ofs"; iFrame; [loadzero|]. iIntros (sts20' stt20') "[INV tnsp]". hred_r.
      rewrite decode_encode_ofs. replace (is_ptr_val _) with true by ss. hred_r.
      replace (is_ptr_val _) with true by ss. hred_r.
            
      iPoseProof (points_to_split with "hd_nx_pt") as "[hd_nx_pt_item hd_nx_pt_key]".

      change (strings.length _) with 8. ss. unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss.
      change Archi.ptr64 with true. hred_r. change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).

      iPoseProof (live_has_offset with "hd_next_ofs") as "[hd_next_ofs hd_next_ofs_ofs]".
      iApply isim_ccallU_load; ss; oauto. iSplitL "INV hd_nx_pt_key hd_next_ofs_ofs"; iFrame.
      { iExists _. iSplit. { iApply _has_offset_slide. et. } iPureIntro. rewrite encode_val_length. splits; et. exists 1. ss. }
      iIntros (sts6 stt6) "[INV hd_nx_pt_key]". change Mptr with Mint64. rewrite decode_encode_ofs.
      (* hd_new = (node* )hd_old->link end *)

      hred_r. unhide. remove_tau. unhide. remove_tau. rewrite cast_ptrofs. hred_r.
      iPoseProof (live_has_offset with "lnso") as "[lnso lnso_ofs]".
      iApply isim_ccallU_store; ss; oauto. iSplitL "INV lnsp lnso_ofs"; iFrame; [storezero|].
      iIntros (sts21' stt21') "[INV lnsp]". hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.

      (* hd_new->link = link ^ (intptr_t)hd_old start *)
      iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_load; ss; oauto. 
      iSplitL "INV tospt toso_ofs"; iFrame; [loadzero|]. iIntros (sts22' stt22') "[INV tospt]". hred_r.
      change Mint64 with Mptr. iPoseProof (decode_encode_ptr_point with "hd_pt_item") as "#->".
      iPoseProof ((@point_cast_ptr _ _ Es) with "hd_pt_item") as "%". rewrite H0. rename H0 into hd_old_cast. hred_r.
      
      iApply isim_ccallU_capture1; ss; oauto. iSplitL "INV hd_ofs"; iFrame; [rewrite hd_sub_r; et|].
      iIntros (sts7 stt7 i) "[INV [hd_ofs hd_equiv']]".

      iCombine "hd_equiv' hd_equiv" as "hd_equiv". iPoseProof (capture_unique with "hd_equiv") as "%". clarify.
      iDestruct "hd_equiv" as "[_ hd_equiv]". hred_r. unhide. remove_tau.

      iPoseProof (live_has_offset with "tnso") as "[tnso tnso_ofs]". iApply isim_ccallU_load; ss; oauto. 
      iSplitL "INV tnsp tnso_ofs"; iFrame; [loadzero|]. iIntros (sts23' stt23') "[INV tnsp]". hred_r.
      rewrite decode_encode_ofs. replace (is_ptr_val _) with true by ss.
      hred_r. replace (is_ptr_val _) with true by ss. hred_r.
      
      unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. change Archi.ptr64 with true. hred_r.
      iPoseProof (live_has_offset with "lnso") as "[lnso lnso_ofs]". iApply isim_ccallU_load; ss; oauto. 
      iSplitL "INV lnsp lnso_ofs"; iFrame; [loadzero|]. iIntros (sts24' stt24') "[INV lnsp]". hred_r.
      rewrite decode_encode_ofs. do 2 rewrite ptrofs_cast_ptr. hred_r. des_ifs_safe. hred_r. change Archi.ptr64 with true.

      hred_r. change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
      iPoseProof (live_has_offset with "hd_next_ofs") as "[hd_next_ofs hd_next_ofs_ofs]".
      iApply isim_ccallU_store; ss; oauto. iSplitL "INV hd_nx_pt_key hd_next_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. iSplit; [|iApply _has_offset_slide; et].
        iPureIntro. rewrite encode_val_length. split; ss. exists 1. ss. }
      iIntros (sts8 stt8) "[INV hd_nx_pt_key]". hred_r. unhide. remove_tau.

      (* free(hd_old) start *)
      hexploit SKINCLENV; [instantiate (2:="free"); et|]. i. des. ss. rewrite H0. rename H0 into free_loc. hred_r.
      iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_load; ss; oauto. 
      iSplitL "INV tospt toso_ofs"; iFrame; [loadzero|]. iIntros (sts25' stt25') "[INV tospt]". hred_r.
      change Mint64 with Mptr. iPoseProof (decode_encode_ptr_point with "hd_pt_item") as "#->".
      rewrite hd_old_cast. hred_r. destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
      replace (pred _) with blk by nia. erewrite SKINCLGD; et; [|ss; et]. hred_r.

      iCombine "hd_pt_item hd_pt_key" as "hd_pt". iPoseProof (points_to_collect with "hd_pt") as "hd_pt".

      iApply isim_ccallU_mfree; ss; oauto. rewrite hd_sub_r. iSplitL "INV hd_pt hd_ofs"; iFrame.
      { iExists _,_. iFrame. iPureIntro. ss. } iIntros (sts12 stt12) "INV".
      (* free(hd_old) end *)

      hred_r. unhide. remove_tau. change Archi.ptr64 with true. ss.

      iPoseProof (live_has_offset with "isofs") as "[isofs iso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV isp iso_ofs"; iFrame;[loadzero|]. iIntros (sts26' stt26') "[INV isp]". hred_r.
      unfold Mptr. change Archi.ptr64 with true. epose proof (decode_encode_val_general (Vlong _) Mint64 Mint64).
      unfold decode_encode_val in H0. rewrite H0. clear H0. rewrite cast_long; et. hred_r.

      (* stack free starts *)
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV lnsp lnso"; iFrame; [freezero|]. iIntros (sts27' stt27') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV tnsp tnso"; iFrame; [freezero|]. iIntros (sts28' stt28') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV tospt toso"; iFrame; [freezero|]. iIntros (sts29' stt29') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV isp isofs"; iFrame; [freezero|]. iIntros (sts30' stt30') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV thsp thso"; iFrame; [freezero|]. iIntros (sts31' stt31') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV hhsp hhso"; iFrame; [freezero|]. iIntros (sts32' stt32') "INV". hred_r.

      (* prove post condition *)
      hred_l. iApply isim_choose_src. iExists _. iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
      change 8%Z with (Z.of_nat (strings.length (encode_val Mint64 (Vlong hd_next_item)))).
      iCombine "hd_nx_pt_item hd_nx_pt_key" as "hd_nx_pt".  iPoseProof (points_to_collect with "hd_nx_pt") as "hd_nx_pt".
      iExists _,_,_,_,_,_. iFrame. iSplit; ss. iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l.
      iSplit; ss. replace (Vlong (Int64.xor i i0)) with (Vptrofs i_hd_nn); et.
      clear - Heq Heq1. unfold Vptrofs in *. des_ifs. f_equal.
      rewrite int64_ptrofs_xor_comm. rewrite Ptrofs.xor_commut.
      rewrite <- Ptrofs.xor_assoc. rewrite Ptrofs.xor_idem. rewrite Ptrofs.xor_zero_l. et.
  Qed.

  End SIMFUNS.

End PROOF.
