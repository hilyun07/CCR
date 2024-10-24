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
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Memory Clightdefs.


Section LEMMA.

  Lemma f_bind_ret_r E R A (s : A -> itree E R)
    : (fun a => ` x : R <- (s a);; Ret x) = s.
  Proof. apply func_ext. i. apply bind_ret_r. Qed.

  Lemma decode_encode_ofs i : decode_val Mint64 (encode_val Mint64 (Vptrofs i)) = Vptrofs i.
  Proof.
    pose proof (decode_encode_val_general (Vptrofs i) Mint64 Mint64).
    unfold Vptrofs in *. des_ifs.
  Qed.

  Lemma decode_encode_item i : decode_val Mint64 (encode_val Mint64 (Vlong i)) = Vlong i.
  Proof. apply (decode_encode_val_general (Vlong i) Mint64 Mint64). Qed.

  Lemma decode_encode_null : decode_val Mint64 (encode_val Mint64 Vnullptr) = Vnullptr.
  Proof. rewrite (decode_encode_val_general Vnullptr Mint64 Mint64). et. Qed.

  Lemma null_zero i : Vptrofs i = Vnullptr -> i = Ptrofs.zero.
  Proof.
    unfold Vptrofs, Vnullptr. des_ifs. i.
    apply (f_equal (fun v: val => match v with Vlong i => i | _ => Int64.zero end)) in H.
    rewrite <- (Ptrofs.of_int64_to_int64 Heq i). rewrite H. et.
  Qed.

  Context `{eventE -< eff}.

  Lemma cast_ptrofs i : cast_to_ptr (Vptrofs i) = Ret (Vptrofs i).
  Proof. des_ifs. Qed.

  Lemma cast_long i : Archi.ptr64 = true -> cast_to_ptr (Vlong i) = Ret (Vlong i).
  Proof. ss. Qed.

End LEMMA.

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

  Ltac storezero := (iExists _,_; iFrame; iPureIntro; split; ss; exists 0; ss).
  Ltac loadzero := (iExists _; iFrame; iPureIntro; try rewrite encode_val_length; rewrite Mem.encode_val_change_check_false; splits; ss; exists 0; ss).
  Ltac freezero := (iExists _,_,_; iFrame; iPureIntro; try rewrite encode_val_length; des_ifs_safe).
  Ltac storezero' := iExists _,_; iFrame; iPureIntro; rewrite encode_val_length; et.

  Lemma sim_add_tl :
    sim_fnsem wf top2 ("add_tl", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure add_tl_spec))
                      ("add_tl", cfunU (decomp_func sk ce f_add_tl)).
  Proof.
    Local Opaque encode_val. Local Opaque cast_to_ptr.
    eassert (_xor = _).
    { unfold _xor. vm_compute (Linking.link _ _). reflexivity. }
    rewrite H0 in *. clear H0. destruct Ctypes.link_build_composite_env. destruct a.
    inversion VALID_link. clear VALID_link. subst.
    clear a. simpl in ce. econs; ss. red.

    (* current state: 1 *)
    get_composite ce e.

    dup SKINCL. rename SKINCL0 into SKINCLENV. apply incl_incl_env in SKINCLENV.
    unfold incl_env in SKINCLENV. pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto. unfold f_add_hd. i; ss.
    unfold decomp_func, function_entry_c. ss.
    let H := fresh "HIDDEN" in set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% PRE] %]". des. clarify. hred_r.
    rename v into hd_hdl, v0 into tl_hdl, l into lfull, i into item.

    (* stack allocation start *)
    unhide. hred_r. iApply isim_apc. iExists (Some (50%nat : Ord.t)).
    iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts0' stt0' hhs m_hhs b_hhs) "[INV [[% hhsp] hhso]]". rename H0 into hhs_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts1' stt1' ths m_ths b_ths) "[INV [[% thsp] thso]]". rename H0 into ths_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts2' stt2' tms m_tms b_tms) "[INV [[% isp] isofs]]". rename H0 into tms_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts3' stt3' ets m_ets b_ets) "[INV [[% espt] eso]]". rename H0 into ets_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts4' stt4' hs m_hs b_hs) "[INV [[% hsp] hso]]". rename H0 into hs_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts5' stt5' ts m_ts b_ts) "[INV [[% tsp] tsofs]]". rename H0 into ts_sz. des. hred_r.
    iPoseProof (live_trivial_offset with "hhso") as "[hhso hhs_eq]"; et.
    iPoseProof (live_trivial_offset with "thso") as "[thso ths_eq]"; et.
    iPoseProof (live_trivial_offset with "isofs") as "[isofs tms_eq]"; et.
    iPoseProof (live_trivial_offset with "eso") as "[eso ets_eq]"; et.
    iPoseProof (live_trivial_offset with "hso") as "[hso hds_eq]"; et.
    iPoseProof (live_trivial_offset with "tsofs") as "[tsofs tls_eq]"; et.
    iPoseProof (equiv_dup with "hhs_eq") as "[hhs_eq hhs_eq']".
    iPoseProof (equiv_point_comm with "[hhsp hhs_eq']") as "hhsp". { iFrame. }
    iPoseProof (equiv_dup with "ths_eq") as "[ths_eq ths_eq']".
    iPoseProof (equiv_point_comm with "[thsp ths_eq']") as "thsp". { iFrame. }
    iPoseProof (equiv_dup with "tms_eq") as "[tms_eq tms_eq']".
    iPoseProof (equiv_point_comm with "[isp tms_eq']") as "isp". { iFrame. }
    iPoseProof (equiv_dup with "ets_eq") as "[ets_eq ets_eq']".
    iPoseProof (equiv_point_comm with "[espt ets_eq']") as "espt". { iFrame. }
    iPoseProof (equiv_dup with "hds_eq") as "[hds_eq hds_eq']".
    iPoseProof (equiv_point_comm with "[hsp hds_eq']") as "hsp". { iFrame. }
    iPoseProof (equiv_dup with "tls_eq") as "[tls_eq tls_eq']".
    iPoseProof (equiv_point_comm with "[tsp tls_eq']") as "tsp". { iFrame. }
    iPoseProof (live_has_offset with "hhso") as "[hhso hhso_ofs]".

    iApply isim_ccallU_store;ss; oauto. iSplitL "INV hhsp hhso_ofs"; iFrame. { storezero. }
    iIntros (sts6' stt6') "[INV hhsp]". iPoseProof (live_has_offset with "thso") as "[thso thso_ofs]".
    hred_r. iApply isim_ccallU_store; ss; oauto. iSplitL "INV thsp thso_ofs"; iFrame. { storezero. }
    iIntros (sts7' stt7') "[INV thsp]". iPoseProof (live_has_offset with "isofs") as "[isofs isofs_ofs]".
    hred_r. iApply isim_ccallU_store; ss; oauto. iSplitL "INV isp isofs_ofs"; iFrame. { storezero. }
    iIntros (sts8' stt8') "[INV isp]". hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.

    (* node* entry = (node* ) malloc(sizeof(node)) start *)
    hexploit SKINCLENV; [instantiate (2:="malloc"); et|].
    i. des. ss. rewrite H0. rename H0 into malloc_loc.
    hred_r. unfold __Node, ident. des_ifs_safe.
    rewrite cast_ptrofs. hred_r.

    replace (pred _) with blk by nia. erewrite SKINCLGD; et; [|ss; et].
    hred_r. ss. rewrite co_co_sizeof.

    iApply isim_ccallU_malloc; ss; oauto. iSplitL "INV"; iFrame; [iPureIntro; ss|].
    iIntros (sts0 stt0 p_new m_new) "[INV [[% new_point] new_ofs]]".
    change (Z.to_nat _) with 16. rename H0 into m_new_size.

    hred_r. unhide. remove_tau.
    iPoseProof ((@live_cast_ptr _ _ Es) with "new_ofs") as "%".
    rewrite H0. rename H0 into new_cast_ptr.
    (* node* entry = (node* ) malloc(sizeof(node)) end *)

    hred_r. unhide. remove_tau. unhide. remove_tau. unfold full_xorlist.
    
    iDestruct "PRE" as (m_hd_hdl m_tl_hdl hd tl ofs_hd_hdl ofs_tl_hdl)
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    des. clarify. rename H0 into hd_hdl_sz. rename H1 into tl_hdl_sz.
    rename H2 into tl_hdl_align. rename H3 into hd_hdl_align.
    iPoseProof (rev_xorlist with "LIST") as "LIST".
    set (rev lfull) as l'. replace lfull with (rev l') by now unfold l'; rewrite rev_involutive; et.
    clearbody l'. clear lfull. rename l' into lfull. hred_r. rewrite new_cast_ptr. hred_r.
    iApply isim_ccallU_store;ss; oauto. iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]".
    iSplitL "INV espt eso_ofs"; iFrame; [storezero|]. iIntros (sts9' stt9') "[INV espt]".
    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.

    (* node* hd = *hd_handler start *)
    iPoseProof (live_has_offset with "hhso") as "[hhso hhso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hhsp hhso_ofs"; iFrame; [loadzero|].
    iIntros (sts10' stt10') "[INV hhsp]". hred_r. iPoseProof (decode_encode_ptr_point with "hd_hdl_point") as "#->".

    iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%".
    rewrite H0. rename H0 into hd_hdl_ptr. hred_r.

    iPoseProof (xorlist_tl_deen with "LIST") as "%". rename H0 into hd_deen.
    iPoseProof (xorlist_tl_not_Vundef with "LIST") as "%". rename H0 into hd_notundef.
    iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame; [loadzero|].
    iIntros (sts1 stt1) "[INV hd_hdl_point]". rewrite hd_deen. hred_r.
    iPoseProof (@xorlist_tl_cast_to_ptr with "LIST") as "#->". hred_r.
    iPoseProof (live_has_offset with "hso") as "[hso hso_ofs]".
    iApply isim_ccallU_store; ss; oauto. iSplitL "INV hsp hso_ofs"; iFrame. { storezero. } iIntros (sts11' stt11') "[INV hsp]". hred_r.
    
    (* node* hd = *hd_handler end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* node* tl = *tl_handler start *)
    iPoseProof (live_has_offset with "thso") as "[thso thso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV thsp thso_ofs"; iFrame; [loadzero|].
    iIntros (sts12' stt12') "[INV thsp]". hred_r.  iPoseProof (decode_encode_ptr_point with "tl_hdl_point") as "#->".
    iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%".  rewrite H0. rename H0 into tl_hdl_is_point. hred_r.

    iPoseProof (xorlist_hd_deen with "LIST") as "%". rename H0 into tl_deen.
    iPoseProof (xorlist_hd_not_Vundef with "LIST") as "%". rename H0 into tl_notundef.
    iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame; [loadzero|].
    iIntros (sts2 stt2) "[INV tl_hdl_point]". rewrite tl_deen. hred_r.
    iPoseProof (@xorlist_hd_cast_to_ptr with "LIST") as "#->". hred_r.
    iPoseProof (live_has_offset with "tsofs") as "[tsofs tsofs_ofs]".  iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV tsp tsofs_ofs"; iFrame; [storezero|]. iIntros (sts13' stt13') "[INV tsp]". hred_r.
    (* node* tl = *tl_handler end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* entry->item = item start *)
    iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV espt eso_ofs"; iFrame; [loadzero|].
    iIntros (sts14' stt14') "[INV espt]". hred_r.  iPoseProof (decode_encode_ptr_point with "new_point") as "#->".
    iPoseProof (points_to_is_ptr with "new_point") as "%".
    rename H0 into new_is_point. rewrite new_is_point. hred_r. rewrite new_is_point. hred_r.

    unfold __Node, ident. rename Heq into get_co.
    rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    iPoseProof (live_has_offset with "isofs") as "[isofs isofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.  iSplitL "INV isp isofs_ofs"; iFrame; [loadzero|].
    iIntros (sts15' stt15') "[INV isp]". hred_r. pose proof (decode_encode_val_general (Vlong item) Mint64 Mint64).
    unfold decode_encode_val in H0. rewrite H0. clear H0. rewrite cast_long. hred_r.
    replace (Coqlib.align 0 _) with 0%Z by et. replace (Ptrofs.repr 0) with Ptrofs.zero by et.
    iPoseProof (add_null_r with "new_ofs") as "%". rewrite H0. rename H0 into new_add_r.

    replace (points_to _ _ _ _) with (points_to p_new m_new (repeat Undef 8 ++ repeat Undef 8) 1) by reflexivity.
    iPoseProof (points_to_split with "new_point") as "[new_point_item new_point_key]".
    iPoseProof (sub_null_r with "new_ofs") as "%". rename H0 into new_sub_r.
    iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".

    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV new_point_item new_ofs_ofs"; iFrame; [storezero|]. iIntros (sts3 stt3) "[INV new_point_item]".
    (* entry->item = item end *)

    hred_r. unhide. remove_tau.
    (* if (hd == NULL) start *)
    iPoseProof (live_has_offset with "tsofs") as "[tsofs tsofs_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tsp tsofs_ofs"; iFrame; [loadzero|].
    iIntros (sts16' stt16') "[INV tsp]". hred_r. rewrite tl_deen.
    replace (Vlong (Int64.repr _)) with Vnullptr by et. destruct lfull.
    (* case: nil list *)
    { ss. iDestruct "LIST" as "[NULL_hd NULL_tl]".
      iPoseProof (equiv_sym with "NULL_tl") as "NULL_tl". iPoseProof (null_equiv with "NULL_tl") as "%". subst.

      iApply isim_ccallU_cmp_ptr0; ss; oauto. iSplitL "INV"; iFrame. iIntros (sts4 stt4) "INV".
      (* if (hd == NULL) end *)

      hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau.

      (* entry->link = 0 start *)
      iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV espt eso_ofs"; iFrame; [loadzero|].
      iIntros (sts17' stt17') "[INV espt]". hred_r.  iPoseProof (decode_encode_ptr_point with "new_point_item") as "#->".
      iPoseProof (points_to_is_ptr with "new_point_item") as "#->". hred_r.
      iPoseProof (points_to_is_ptr with "new_point_item") as "#->". hred_r.

      unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
      replace (Coqlib.align _ _) with 8%Z by et. replace (Vlong (Int64.repr _)) with Vnullptr by et.
      iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".
      iApply isim_ccallU_store; ss; oauto. iSplitL "INV new_point_key new_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. iSplit; cycle 1. { iApply _has_offset_slide. iFrame. } { iPureIntro. split; ss. exists 1. ss. } }
      iIntros (sts5 stt5) "[INV new_point_key]".
      (* entry->link = 0 end *)

      hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau. unhide. remove_tau.

      (* hd_handler = *tl_handler = entry start *)
      iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV espt eso_ofs"; iFrame; [loadzero|].
      iIntros (sts18' stt18') "[INV espt]". hred_r. iPoseProof (decode_encode_ptr_point with "new_point_item") as "#->".
      rewrite new_cast_ptr. hred_r. unhide. remove_tau.
      iPoseProof (live_has_offset with "thso") as "[thso thso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV thsp thso_ofs"; iFrame; [loadzero|].
      iIntros (sts19' stt19') "[INV thsp]". hred_r. iPoseProof (decode_encode_ptr_point with "tl_hdl_point") as "#->".
      rewrite tl_hdl_is_point. hred_r. rewrite new_cast_ptr. hred_r.
      iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto. iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame; [storezero|].
      iIntros (sts7 stt7) "[INV tl_hdl_point]".

      hred_r. unhide. remove_tau.
      iPoseProof (live_has_offset with "hhso") as "[hhso hhso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV hhsp hhso_ofs"; iFrame; [loadzero|].
      iIntros (sts20' stt20') "[INV hhsp]". hred_r. iPoseProof (decode_encode_ptr_point with "hd_hdl_point") as "#->".
      rewrite hd_hdl_ptr. hred_r. rewrite new_cast_ptr. hred_r.
      iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto. iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (sts8 stt8) "[INV hd_hdl_point]".

      hred_r. remove_tau.
      (* stack free starts *)
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV tsp tsofs"; iFrame; [freezero|]. iIntros (sts21' stt21') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV hsp hso"; iFrame; [freezero|]. iIntros (sts22' stt22') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV espt eso"; iFrame; [freezero|]. iIntros (sts23' stt23') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV isp isofs"; iFrame; [freezero|]. iIntros (sts24' stt24') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV thsp thso"; iFrame; [freezero|]. iIntros (sts25' stt25') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV hhsp hhso"; iFrame; [freezero|]. iIntros (sts26' stt26') "INV". hred_r.
      hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
      iCombine "new_point_item new_point_key" as "new_point".
      iPoseProof (points_to_collect with "new_point") as "new_point".

      iExists _,_,_,_,_,_. iFrame. iSplit; ss.
      change Vnullptr with (Vptrofs Ptrofs.zero) at 3 4.
      iPoseProof (equiv_refl_live with "new_ofs") as "[new_ofs new_equiv]".
      iPoseProof (equiv_dup with "NULL_tl") as "[? ?]".
      iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame. iSplit; ss. }
    ss. destruct v; clarify. iDestruct "LIST" as (i_prev i_next m_hd) "[[[[% prev_addr] tl_ofs] tl_point] LIST]".
    rename H0 into m_hd_size. iPoseProof (sub_null_r with "tl_ofs") as "%". rename H0 into tl_sub_r.

    (* if (hd == NULL) start *)

    iApply isim_ccallU_cmp_ptr3; ss; oauto. iSplitL "INV tl_ofs".
    { rewrite tl_sub_r. iFrame. iPureIntro. red. rewrite m_hd_size. ss. }
    iIntros (sts4 stt4) "[INV tl_ofs]".
    (* if (hd == NULL) end *)

    hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau. unhide. remove_tau.

    (* entry->link = (intptr_t)hd start *)
    iPoseProof (live_has_offset with "tsofs") as "[tsofs tsofs_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV tsp tsofs_ofs"; iFrame; [loadzero|].
    iIntros (sts17' stt17') "[INV tsp]". hred_r. iPoseProof (decode_encode_ptr_point with "tl_point") as "#->".
    iPoseProof ((@live_cast_ptr_ofs _ _ Es) with "tl_ofs") as "%". rewrite H0. hred_r. rename H0 into hd_cast_ptr.

    iApply isim_ccallU_capture1; ss; oauto. iSplitL "INV tl_ofs"; iFrame.
    iIntros (sts5 stt5 i_hd) "[INV [tl_ofs tl_addr]]".

    hred_r. unhide. remove_tau.
    iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]".  iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV espt eso_ofs"; iFrame; [loadzero|]. iIntros (sts18' stt18') "[INV espt]". hred_r.
    iPoseProof (decode_encode_ptr_point with "new_point_item") as "#->".

    rewrite new_is_point. hred_r. rewrite new_is_point. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    rewrite cast_ptrofs. hred_r. replace (Coqlib.align _ _) with 8%Z by et.
    iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".

    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV new_point_key new_ofs_ofs"; iFrame.
    { iExists _,_. iFrame. iSplit; cycle 1; [iApply _has_offset_slide; ss|].
      iPureIntro. split; ss. exists 1. ss. }
    iIntros (sts6 stt6) "[INV new_point_key]".
    (* entry->link = (intptr_t)hd end *)

    hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.

    (* hd->link = hd->link ^ (intptr_t)entry start *)
    iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV espt eso_ofs"; iFrame; [loadzero|].
    iIntros (sts19' stt19') "[INV espt]". hred_r. iPoseProof (decode_encode_ptr_point with "new_point_item") as "#->".
    rewrite new_cast_ptr. hred_r. iApply isim_ccallU_capture1; ss; oauto.
    iSplitL "INV new_ofs"; iFrame; [rewrite new_sub_r; et|].
    iIntros (sts7 stt7 i_new) "[INV [new_ofs new_addr]]".

    hred_r. unhide. remove_tau.

    iPoseProof (live_has_offset with "tsofs") as "[tsofs tsofs_ofs]".  iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tsp tsofs_ofs"; iFrame; [loadzero|]. iIntros (sts20' stt20') "[INV tsp]". hred_r.
    iPoseProof (decode_encode_ptr_point with "tl_point") as "#->".  iPoseProof (points_to_is_ptr with "tl_point") as "%".
    rewrite H0. rename H0 into hd_ptr. hred_r. rewrite hd_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    iPoseProof (live_has_offset with "tsofs") as "[tsofs tsofs_ofs]".  iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tsp tsofs_ofs"; iFrame; [loadzero|]. iIntros (sts21' stt21') "[INV tsp]". hred_r.
    iPoseProof (decode_encode_ptr_point with "tl_point") as "#->".

    replace (Coqlib.align _ _) with 8%Z by et. rewrite hd_ptr. hred_r. rewrite hd_ptr. hred_r.
    rewrite co_co_members. ss. hred_r. replace (Coqlib.align _ _) with 8%Z by et.

    iPoseProof (points_to_split with "tl_point") as "[tl_point_item tl_point_key]".
    iPoseProof (live_has_offset_ofs with "tl_ofs") as "[tl_ofs tl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tl_point_key tl_ofs_ofs".
    { iFrame. iExists _. iSplit; [iApply _has_offset_slide; ss|].
      iPureIntro. splits; ss. exists 1. ss. }
    iIntros (sts8 stt8) "[INV tl_point_key]".

    unfold Mptr. des_ifs_safe. rewrite decode_encode_ofs. hred_r.
    rewrite cast_ptrofs. rewrite cast_ptrofs. hred_r. des_ifs_safe.

    hred_r. rewrite cast_long; et. hred_r.
    iPoseProof (live_has_offset_ofs with "tl_ofs") as "[tl_ofs tl_ofs_ofs]".
    iApply isim_ccallU_store; ss; oauto. iSplitL "INV tl_point_key tl_ofs_ofs".
    { iFrame. iExists _,_. iFrame. iSplit. 2:{ iApply _has_offset_slide. et. }
      iPureIntro. split; ss. exists 1. ss. }
    iIntros (sts9 stt9) "[INV tl_point_key]".
    (* hd->link = hd->link ^ (intptr_t)entry end *)

    hred_r. unhide. remove_tau.

    (* *hd_handler = entry start *)
    iPoseProof (live_has_offset with "thso") as "[thso thso_ofs]".  iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV thsp thso_ofs"; iFrame; [loadzero|]. iIntros (sts22' stt22') "[INV thsp]". hred_r.
    change Mint64 with Mptr.  iPoseProof (decode_encode_ptr_point with "tl_hdl_point") as "#->".

    rewrite tl_hdl_is_point. hred_r.
    iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]".  iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV espt eso_ofs"; iFrame; [loadzero|]. iIntros (sts23' stt23') "[INV espt]". hred_r.
    iPoseProof (decode_encode_ptr_point with "new_point_item") as "#->".  rewrite new_cast_ptr. hred_r.
    iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".
    iApply isim_ccallU_store; ss; oauto. iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs".
    { iFrame. iExists _,_. iFrame. iPureIntro. rewrite encode_val_length. ss. }
    iIntros (sts10 stt10) "[INV tl_hdl_point]". hred_r. remove_tau.
    (* *hd_handler = entry end *)

    (* stack free start *)
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV tsp tsofs"; iFrame; [freezero|]. iIntros (sts24' stt24') "INV". hred_r.
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV hsp hso"; iFrame; [freezero|]. iIntros (sts25' stt25') "INV". hred_r.
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV espt eso"; iFrame; [freezero|]. iIntros (sts26' stt26') "INV". hred_r.
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV isp isofs"; iFrame; [freezero|]. iIntros (sts27' stt27') "INV". hred_r.
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV thsp thso"; iFrame; [freezero|]. iIntros (sts28' stt28') "INV". hred_r.
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV hhsp hhso"; iFrame; [freezero|]. iIntros (sts29' stt29') "INV". hred_r.
    2:{ ss. }

    (* prove post condition *)
    hred_r. remove_tau. hred_l. iApply isim_choose_src.
    iExists _. iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
    iCombine "new_point_item new_point_key" as "new_point".
    iCombine "tl_point_item tl_point_key" as "tl_point".
    iPoseProof (points_to_collect with "new_point") as "new_point".
    iPoseProof (points_to_collect with "tl_point") as "tl_point".
    iPoseProof (null_equiv with "prev_addr") as "%".
    assert (i_prev = Ptrofs.zero).
    { unfold Vptrofs, Vnullptr in *. destruct Archi.ptr64 eqn:?. 2:{ clarify. }
      apply (f_equal (fun v => match v with Vlong i => i | _ => Int64.zero end)) in H0.
      apply (f_equal Ptrofs.of_int64) in H0. rewrite Ptrofs.of_int64_to_int64 in H0; et. }
    clear H0. clarify.

    iExists _,_,_,_,_,_. iFrame. iSplit; ss. rewrite <- (rev_involutive ((rev lfull ++ _) ++ _)).
    iApply rev_xorlist. rewrite rev_app_distr. change (rev [Vlong item]) with [Vlong item].
    ss. rewrite rev_app_distr. change (rev [Vlong i]) with [Vlong i].
    ss. rewrite new_sub_r. iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame. iSplit; ss.

    iPoseProof (equiv_dup with "tl_addr") as "[tl_addr tl_addr']".
    iCombine "tl_addr' tl_point" as "tl_point".
    iPoseProof (equiv_point_comm with "tl_point") as "tl_point".
    iPoseProof (equiv_dup with "tl_addr") as "[tl_addr tl_addr']".
    iCombine "tl_addr' tl_ofs" as "tl_ofs". rewrite tl_sub_r.
    iPoseProof (equiv_live_comm with "tl_ofs") as "tl_ofs".
    iPoseProof (equiv_sym with "tl_addr") as "tl_addr". rewrite <- Heq1.
    iExists _,_,_. iFrame. instantiate (1:=i_next).
    replace (Vptrofs (Ptrofs.xor _ _)) with (Vlong (Int64.xor i0 i1)).
    - iFrame. iSplit; ss. rewrite rev_involutive. iApply xorlist_hd_prev_replace. iFrame. iApply equiv_sym. et.
    - unfold Vptrofs in *. des_ifs. f_equal. rewrite int64_ptrofs_xor_comm.
      f_equal. rewrite Ptrofs.xor_commut. f_equal. rewrite Ptrofs.xor_zero_l. et.
  Qed.

  Lemma sim_add_hd :
    sim_fnsem wf top2
      ("add_hd", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure add_hd_spec))
      ("add_hd", cfunU (decomp_func sk ce f_add_hd)).
  Proof.
    Local Opaque encode_val. Local Opaque cast_to_ptr.
    eassert (_xor = _).
    { unfold _xor. vm_compute (Linking.link _ _). reflexivity. }
    rewrite H0 in *. clear H0. destruct Ctypes.link_build_composite_env. destruct a.
    inversion VALID_link. clear VALID_link. subst.
    clear a. simpl in ce. econs; ss. red.

    (* current state: 1 *)
    get_composite ce e.

    dup SKINCL. rename SKINCL0 into SKINCLENV. apply incl_incl_env in SKINCLENV.
    unfold incl_env in SKINCLENV. pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto. unfold f_add_hd. i; ss.
    unfold decomp_func, function_entry_c. ss.
    let H := fresh "HIDDEN" in set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% PRE] %]". des. clarify. hred_r.
    rename v into hd_hdl, v0 into tl_hdl, l into lfull, i into item.

    (* stack allocation start *)
    unhide. hred_r. iApply isim_apc. iExists (Some (50%nat : Ord.t)).
    iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts0' stt0' hhs m_hhs b_hhs) "[INV [[% hhsp] hhso]]". rename H0 into hhs_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts1' stt1' ths m_ths b_ths) "[INV [[% thsp] thso]]". rename H0 into ths_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts2' stt2' tms m_tms b_tms) "[INV [[% isp] isofs]]". rename H0 into tms_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts3' stt3' ets m_ets b_ets) "[INV [[% espt] eso]]". rename H0 into ets_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts4' stt4' hs m_hs b_hs) "[INV [[% hsp] hso]]". rename H0 into hs_sz. des.
    hred_r. iApply isim_ccallU_salloc; ss; oauto. iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts5' stt5' ts m_ts b_ts) "[INV [[% tsp] tsofs]]". rename H0 into ts_sz. des. hred_r.
    iPoseProof (live_trivial_offset with "hhso") as "[hhso hhs_eq]"; et.
    iPoseProof (live_trivial_offset with "thso") as "[thso ths_eq]"; et.
    iPoseProof (live_trivial_offset with "isofs") as "[isofs tms_eq]"; et.
    iPoseProof (live_trivial_offset with "eso") as "[eso ets_eq]"; et.
    iPoseProof (live_trivial_offset with "hso") as "[hso hds_eq]"; et.
    iPoseProof (live_trivial_offset with "tsofs") as "[tsofs tls_eq]"; et.
    iPoseProof (equiv_dup with "hhs_eq") as "[hhs_eq hhs_eq']".
    iPoseProof (equiv_point_comm with "[hhsp hhs_eq']") as "hhsp". { iFrame. }
    iPoseProof (equiv_dup with "ths_eq") as "[ths_eq ths_eq']".
    iPoseProof (equiv_point_comm with "[thsp ths_eq']") as "thsp". { iFrame. }
    iPoseProof (equiv_dup with "tms_eq") as "[tms_eq tms_eq']".
    iPoseProof (equiv_point_comm with "[isp tms_eq']") as "isp". { iFrame. }
    iPoseProof (equiv_dup with "ets_eq") as "[ets_eq ets_eq']".
    iPoseProof (equiv_point_comm with "[espt ets_eq']") as "espt". { iFrame. }
    iPoseProof (equiv_dup with "hds_eq") as "[hds_eq hds_eq']".
    iPoseProof (equiv_point_comm with "[hsp hds_eq']") as "hsp". { iFrame. }
    iPoseProof (equiv_dup with "tls_eq") as "[tls_eq tls_eq']".
    iPoseProof (equiv_point_comm with "[tsp tls_eq']") as "tsp". { iFrame. }
    iPoseProof (live_has_offset with "hhso") as "[hhso hhso_ofs]".

    iApply isim_ccallU_store;ss; oauto. iSplitL "INV hhsp hhso_ofs"; iFrame. { storezero. }
    iIntros (sts6' stt6') "[INV hhsp]". iPoseProof (live_has_offset with "thso") as "[thso thso_ofs]".
    hred_r. iApply isim_ccallU_store; ss; oauto. iSplitL "INV thsp thso_ofs"; iFrame. { storezero. }
    iIntros (sts7' stt7') "[INV thsp]". iPoseProof (live_has_offset with "isofs") as "[isofs isofs_ofs]".
    hred_r. iApply isim_ccallU_store; ss; oauto. iSplitL "INV isp isofs_ofs"; iFrame. { storezero. }
    iIntros (sts8' stt8') "[INV isp]". hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.

    (* node* entry = (node* ) malloc(sizeof(node)) start *)
    hexploit SKINCLENV; [instantiate (2:="malloc"); et|].
    i. des. ss. rewrite H0. rename H0 into malloc_loc.
    hred_r. unfold __Node, ident. des_ifs_safe.
    rewrite cast_ptrofs. hred_r.

    replace (pred _) with blk by nia. erewrite SKINCLGD; et; [|ss; et].
    hred_r. ss. rewrite co_co_sizeof.

    iApply isim_ccallU_malloc; ss; oauto. iSplitL "INV"; iFrame; [iPureIntro; ss|].
    iIntros (sts0 stt0 p_new m_new) "[INV [[% new_point] new_ofs]]".
    change (Z.to_nat _) with 16. rename H0 into m_new_size.

    hred_r. unhide. remove_tau.
    iPoseProof ((@live_cast_ptr _ _ Es) with "new_ofs") as "%".
    rewrite H0. rename H0 into new_cast_ptr.
    (* node* entry = (node* ) malloc(sizeof(node)) end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    unfold full_xorlist.
    iDestruct "PRE" as (m_hd_hdl m_tl_hdl hd tl ofs_hd_hdl ofs_tl_hdl)
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    des. clarify.
    rename H0 into hd_hdl_sz. rename H1 into tl_hdl_sz.
    rename H2 into tl_hdl_align. rename H3 into hd_hdl_align.
    hred_r. rewrite new_cast_ptr. hred_r.
    iApply isim_ccallU_store;ss; oauto. iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]".
    iSplitL "INV espt eso_ofs"; iFrame; [storezero|]. iIntros (sts9' stt9') "[INV espt]".
    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.

    (* node* hd = *hd_handler start *)
    iPoseProof (live_has_offset with "hhso") as "[hhso hhso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hhsp hhso_ofs"; iFrame; [loadzero|].
    iIntros (sts10' stt10') "[INV hhsp]". hred_r. iPoseProof (decode_encode_ptr_point with "hd_hdl_point") as "#->".

    iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%".
    rewrite H0. rename H0 into hd_hdl_ptr. hred_r.

    iPoseProof (xorlist_hd_deen with "LIST") as "%". rename H0 into hd_deen.
    iPoseProof (xorlist_hd_not_Vundef with "LIST") as "%". rename H0 into hd_notundef.
    iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame; [loadzero|].
    iIntros (sts1 stt1) "[INV hd_hdl_point]". rewrite hd_deen. hred_r.
    iPoseProof (@xorlist_hd_cast_to_ptr with "LIST") as "#->". hred_r.
    iPoseProof (live_has_offset with "hso") as "[hso hso_ofs]".
    iApply isim_ccallU_store; ss; oauto. iSplitL "INV hsp hso_ofs"; iFrame. { storezero. } iIntros (sts11' stt11') "[INV hsp]". hred_r.
    
    (* node* hd = *hd_handler end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* node* tl = *tl_handler start *)
    iPoseProof (live_has_offset with "thso") as "[thso thso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV thsp thso_ofs"; iFrame; [loadzero|].
    iIntros (sts12' stt12') "[INV thsp]". hred_r.  iPoseProof (decode_encode_ptr_point with "tl_hdl_point") as "#->".
    iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%". rewrite H0. rename H0 into tl_hdl_is_point. hred_r.

    iPoseProof (xorlist_tl_deen with "LIST") as "%". rename H0 into tl_deen.
    iPoseProof (xorlist_tl_not_Vundef with "LIST") as "%". rename H0 into tl_notundef.
    iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame; [loadzero|].
    iIntros (sts2 stt2) "[INV tl_hdl_point]". rewrite tl_deen. hred_r.
    iPoseProof (@xorlist_tl_cast_to_ptr with "LIST") as "#->". hred_r.
    iPoseProof (live_has_offset with "tsofs") as "[tsofs tsofs_ofs]". iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV tsp tsofs_ofs"; iFrame; [storezero|]. iIntros (sts13' stt13') "[INV tsp]". hred_r.

    (* node* tl = *tl_handler end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* entry->item = item start *)
    iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV espt eso_ofs"; iFrame; [loadzero|].
    iIntros (sts14' stt14') "[INV espt]". hred_r.  iPoseProof (decode_encode_ptr_point with "new_point") as "#->".
    iPoseProof (points_to_is_ptr with "new_point") as "%".
    rename H0 into new_is_point. rewrite new_is_point. hred_r. rewrite new_is_point. hred_r.

    unfold __Node, ident. rename Heq into get_co.
    rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    iPoseProof (live_has_offset with "isofs") as "[isofs isofs_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV isp isofs_ofs"; iFrame; [loadzero|].
    iIntros (sts15' stt15') "[INV isp]". hred_r. pose proof (decode_encode_val_general (Vlong item) Mint64 Mint64).
    unfold decode_encode_val in H0. rewrite H0. clear H0. rewrite cast_long. hred_r.
    replace (Coqlib.align 0 _) with 0%Z by et. replace (Ptrofs.repr 0) with Ptrofs.zero by et.
    iPoseProof (add_null_r with "new_ofs") as "%". rewrite H0. rename H0 into new_add_r. 

    replace (points_to _ _ _ _) with (points_to p_new m_new (repeat Undef 8 ++ repeat Undef 8) 1) by reflexivity.
    iPoseProof (points_to_split with "new_point") as "[new_point_item new_point_key]".
    iPoseProof (sub_null_r with "new_ofs") as "%". rename H0 into new_sub_r.
    iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".

    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV new_point_item new_ofs_ofs"; iFrame; [storezero|]. iIntros (sts3 stt3) "[INV new_point_item]".
    (* entry->item = item end *)

    hred_r. unhide. remove_tau.
    (* if (hd == NULL) start *)
    iPoseProof (live_has_offset with "hso") as "[hso hso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hsp hso_ofs"; iFrame; [loadzero|].
    iIntros (sts16' stt16') "[INV hsp]". hred_r. rewrite hd_deen.
    replace (Vlong (Int64.repr _)) with Vnullptr by et. destruct lfull.
    (* case: nil list *)
    { ss. iDestruct "LIST" as "[NULL_tl NULL_hd]".
      iPoseProof (equiv_sym with "NULL_hd") as "NULL_hd". iPoseProof (null_equiv with "NULL_hd") as "%". subst.

      iApply isim_ccallU_cmp_ptr0; ss; oauto. iSplitL "INV"; iFrame. iIntros (sts4 stt4) "INV".
      (* if (hd == NULL) end *)

      hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau.

      (* entry->link = 0 start *)
      iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV espt eso_ofs"; iFrame; [loadzero|].
      iIntros (sts17' stt17') "[INV espt]". hred_r.  iPoseProof (decode_encode_ptr_point with "new_point_item") as "#->".
      iPoseProof (points_to_is_ptr with "new_point_item") as "#->". hred_r.
      iPoseProof (points_to_is_ptr with "new_point_item") as "#->". hred_r.

      unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
      replace (Coqlib.align _ _) with 8%Z by et. replace (Vlong (Int64.repr _)) with Vnullptr by et.
      iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto. iSplitL "INV new_point_key new_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. iSplit; cycle 1.  { iApply _has_offset_slide. et. } { iPureIntro. split; ss. exists 1. ss. } }
      iIntros (sts5 stt5) "[INV new_point_key]".
      (* entry->link = 0 end *)

      hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau. unhide. remove_tau.

      (* hd_handler = *tl_handler = entry start *)
      iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV espt eso_ofs"; iFrame; [loadzero|].
      iIntros (sts18' stt18') "[INV espt]". hred_r. iPoseProof (decode_encode_ptr_point with "new_point_item") as "#->".
      rewrite new_cast_ptr. hred_r. unhide. remove_tau.
      iPoseProof (live_has_offset with "thso") as "[thso thso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV thsp thso_ofs"; iFrame; [loadzero|].
      iIntros (sts19' stt19') "[INV thsp]". hred_r. iPoseProof (decode_encode_ptr_point with "tl_hdl_point") as "#->".
      rewrite tl_hdl_is_point. hred_r. rewrite new_cast_ptr. hred_r.
      iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto. iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (sts7 stt7) "[INV tl_hdl_point]".

      hred_r. unhide. remove_tau.
      iPoseProof (live_has_offset with "hhso") as "[hhso hhso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV hhsp hhso_ofs"; iFrame; [loadzero|].
      iIntros (sts20' stt20') "[INV hhsp]". hred_r. iPoseProof (decode_encode_ptr_point with "hd_hdl_point") as "#->".
      rewrite hd_hdl_ptr. hred_r. rewrite new_cast_ptr. hred_r.
      iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto. iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame; [storezero|].
      iIntros (sts8 stt8) "[INV hd_hdl_point]".

      hred_r. remove_tau.
      (* stack free starts *)
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV tsp tsofs"; iFrame; [freezero|]. iIntros (sts21' stt21') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV hsp hso"; iFrame; [freezero|]. iIntros (sts22' stt22') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV espt eso"; iFrame; [freezero|]. iIntros (sts23' stt23') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV isp isofs"; iFrame; [freezero|]. iIntros (sts24' stt24') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV thsp thso"; iFrame; [freezero|]. iIntros (sts25' stt25') "INV". hred_r.
      iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV hhsp hhso"; iFrame; [freezero|]. iIntros (sts26' stt26') "INV". hred_r.
      hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
      iCombine "new_point_item new_point_key" as "new_point".
      iPoseProof (points_to_collect with "new_point") as "new_point".

      iExists _,_,_,_,_,_. iFrame. iSplit; ss.
      change Vnullptr with (Vptrofs Ptrofs.zero) at 3 4.
      iPoseProof (equiv_refl_live with "new_ofs") as "[new_ofs new_equiv]".
      iPoseProof (equiv_dup with "NULL_hd") as "[? ?]".
      iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame. iSplit; ss. }
    ss. destruct v; clarify.
    iDestruct "LIST" as (i_prev i_next m_hd) "[[[[% prev_addr] hd_ofs] hd_point] LIST]".
    rename H0 into m_hd_size.
    iPoseProof (sub_null_r with "hd_ofs") as "%". rename H0 into hd_sub_r.

    (* if (hd == NULL) start *)

    iApply isim_ccallU_cmp_ptr3; ss; oauto. iSplitL "INV hd_ofs".
    { rewrite hd_sub_r. iFrame. iPureIntro. red. rewrite m_hd_size. ss. }
    iIntros (sts4 stt4) "[INV hd_ofs]".
    (* if (hd == NULL) end *)

    hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau. unhide. remove_tau.

    (* entry->link = (intptr_t)hd start *)
    iPoseProof (live_has_offset with "hso") as "[hso hso_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV hsp hso_ofs"; iFrame; [loadzero|].
    iIntros (sts17' stt17') "[INV hsp]". hred_r. iPoseProof (decode_encode_ptr_point with "hd_point") as "#->".
    iPoseProof ((@live_cast_ptr_ofs _ _ Es) with "hd_ofs") as "%". rewrite H0. hred_r. rename H0 into hd_cast_ptr.

    iApply isim_ccallU_capture1; ss; oauto. iSplitL "INV hd_ofs"; iFrame.
    iIntros (sts5 stt5 i_hd) "[INV [hd_ofs hd_addr]]".

    hred_r. unhide. remove_tau.
    iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]".  iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV espt eso_ofs"; iFrame; [loadzero|]. iIntros (sts18' stt18') "[INV espt]". hred_r.
    iPoseProof (decode_encode_ptr_point with "new_point_item") as "#->".

    rewrite new_is_point. hred_r. rewrite new_is_point. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    rewrite cast_ptrofs. hred_r. replace (Coqlib.align _ _) with 8%Z by et.
    iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".

    iApply isim_ccallU_store; ss; oauto. iSplitL "INV new_point_key new_ofs_ofs"; iFrame.
    { iExists _,_. iFrame. iSplit; cycle 1; [iApply _has_offset_slide; ss|].
      { iPureIntro. split; ss. exists 1. ss. } }
    iIntros (sts6 stt6) "[INV new_point_key]".
    (* entry->link = (intptr_t)hd end *)

    hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.

    (* hd->link = hd->link ^ (intptr_t)entry start *)
    iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV espt eso_ofs"; iFrame; [loadzero|].
    iIntros (sts19' stt19') "[INV espt]". hred_r. iPoseProof (decode_encode_ptr_point with "new_point_item") as "#->".
    rewrite new_cast_ptr. hred_r. iApply isim_ccallU_capture1; ss; oauto.
    iSplitL "INV new_ofs"; iFrame. { rewrite new_sub_r. et. } iIntros (sts7 stt7 i_new) "[INV [new_ofs new_addr]]".

    hred_r. unhide. remove_tau.

    iPoseProof (live_has_offset with "hso") as "[hso hso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hsp hso_ofs"; iFrame; [loadzero|]. iIntros (sts20' stt20') "[INV hsp]". hred_r.
    iPoseProof (decode_encode_ptr_point with "hd_point") as "#->".  iPoseProof (points_to_is_ptr with "hd_point") as "%".
    
    rewrite H0. rename H0 into hd_ptr. hred_r. rewrite hd_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    iPoseProof (live_has_offset with "hso") as "[hso hso_ofs]".  iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hsp hso_ofs"; iFrame; [loadzero|]. iIntros (sts21' stt21') "[INV hsp]". hred_r.
    iPoseProof (decode_encode_ptr_point with "hd_point") as "#->".
    
    replace (Coqlib.align _ _) with 8%Z by et. rewrite hd_ptr. hred_r. rewrite hd_ptr. hred_r.
    rewrite co_co_members. ss. hred_r. replace (Coqlib.align _ _) with 8%Z by et.

    iPoseProof (points_to_split with "hd_point") as "[hd_point_item hd_point_key]".
    iPoseProof (live_has_offset_ofs with "hd_ofs") as "[hd_ofs hd_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV hd_point_key hd_ofs_ofs".
    { iFrame. iExists _. iSplit; [iApply _has_offset_slide; ss|].
      { iPureIntro. splits; ss. exists 1. ss. } }
    iIntros (sts8 stt8) "[INV hd_point_key]".

    unfold Mptr. des_ifs_safe. rewrite decode_encode_ofs. hred_r.
    rewrite cast_ptrofs. rewrite cast_ptrofs. hred_r. des_ifs_safe.

    hred_r. rewrite cast_long; et. hred_r.
    iPoseProof (live_has_offset_ofs with "hd_ofs") as "[hd_ofs hd_ofs_ofs]".
    iApply isim_ccallU_store; ss; oauto. iSplitL "INV hd_point_key hd_ofs_ofs".
    { iFrame. iExists _,_. iFrame. iSplit. 2:{ iApply _has_offset_slide. et. }
      iPureIntro. split; ss. exists 1. ss. } 
    iIntros (sts9 stt9) "[INV hd_point_key]".
    (* hd->link = hd->link ^ (intptr_t)entry end *)

    hred_r. unhide. remove_tau.

    (* *hd_handler = entry start *)
    iPoseProof (live_has_offset with "hhso") as "[hhso hhso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hhsp hhso_ofs"; iFrame; [loadzero|]. iIntros (sts22' stt22') "[INV hhsp]". hred_r.
    change Mint64 with Mptr. iPoseProof (decode_encode_ptr_point with "hd_hdl_point") as "#->".

    rewrite hd_hdl_ptr. hred_r.
    iPoseProof (live_has_offset with "eso") as "[eso eso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV espt eso_ofs"; iFrame; [loadzero|]. iIntros (sts23' stt23') "[INV espt]". hred_r.
    iPoseProof (decode_encode_ptr_point with "new_point_item") as "#->". rewrite new_cast_ptr. hred_r.

    iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".
    iApply isim_ccallU_store; ss; oauto. iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs".
    { iFrame. iExists _,_. iFrame. iPureIntro. rewrite encode_val_length. ss. }
    iIntros (sts10 stt10) "[INV hd_hdl_point]". hred_r. remove_tau.
    (* *hd_handler = entry end *)

    (* stack free start *)
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV tsp tsofs"; iFrame; [freezero|]. iIntros (sts24' stt24') "INV". hred_r.
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV hsp hso"; iFrame; [freezero|]. iIntros (sts25' stt25') "INV". hred_r.
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV espt eso"; iFrame; [freezero|]. iIntros (sts26' stt26') "INV". hred_r.
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV isp isofs"; iFrame; [freezero|]. iIntros (sts27' stt27') "INV". hred_r.
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV thsp thso"; iFrame; [freezero|]. iIntros (sts28' stt28') "INV". hred_r.
    iApply isim_ccallU_sfree; ss; oauto. iSplitL "INV hhsp hhso"; iFrame; [freezero|]. iIntros (sts29' stt29') "INV". hred_r.
    2:{ ss. }

    (* prove post condition *)
    hred_r. remove_tau. hred_l. iApply isim_choose_src.
    iExists _. iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
    iCombine "new_point_item new_point_key" as "new_point".
    iCombine "hd_point_item hd_point_key" as "hd_point".
    iPoseProof (points_to_collect with "new_point") as "new_point".
    iPoseProof (points_to_collect with "hd_point") as "hd_point".
    iPoseProof (null_equiv with "prev_addr") as "%".
    assert (i_prev = Ptrofs.zero).
    { unfold Vptrofs, Vnullptr in *. destruct Archi.ptr64 eqn:?. 2:{ clarify. }
      apply (f_equal (fun v => match v with Vlong i => i | _ => Int64.zero end)) in H0.
      apply (f_equal Ptrofs.of_int64) in H0. rewrite Ptrofs.of_int64_to_int64 in H0; et. }
    clear H0. clarify.

    iExists _,_,_,_,_,_. iFrame. iSplit; ss.
    iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. rewrite new_sub_r.
    iFrame. iSplit; ss.

    iPoseProof (equiv_dup with "hd_addr") as "[hd_addr hd_addr']".
    iCombine "hd_addr' hd_point" as "hd_point".
    iPoseProof (equiv_point_comm with "hd_point") as "hd_point".
    iPoseProof (equiv_dup with "hd_addr") as "[hd_addr hd_addr']".
    iCombine "hd_addr' hd_ofs" as "hd_ofs". rewrite hd_sub_r.
    iPoseProof (equiv_live_comm with "hd_ofs") as "hd_ofs".
    iPoseProof (equiv_sym with "hd_addr") as "hd_addr". rewrite <- Heq1.
    iExists _,_,_. iFrame. instantiate (1:=i_next).
    replace (Vptrofs (Ptrofs.xor _ _)) with (Vlong (Int64.xor i0 i1)).
    - iFrame. iSplit; ss. iApply xorlist_hd_prev_replace. iFrame. iApply equiv_sym. iFrame.
    - unfold Vptrofs in *. des_ifs. f_equal.
      rewrite int64_ptrofs_xor_comm. f_equal. rewrite Ptrofs.xor_commut.
      f_equal. rewrite Ptrofs.xor_zero_l. et.
  Qed.

  Lemma sim_delete_tl :
    sim_fnsem wf top2 ("delete_tl", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure delete_tl_spec))
                      ("delete_tl", cfunU (decomp_func sk ce f_delete_tl)).
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
    iDestruct "PRE" as (m_hd_hdl m_tl_hdl hd_old tl_old ofs_hd_hdl ofs_tl_hdl)
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    iPoseProof (rev_xorlist with "LIST") as "LIST".
    clarify. hred_r. unhide. hred_r. unhide. remove_tau. rename v into hd_handler.  rename v0 into tl_handler.
    set (rev l) as l'. replace l with (rev l') by now unfold l'; rewrite rev_involutive; et.
    clearbody l'. clear l. rename l' into linput. des. clarify. rename H0 into tl_hdl_align.
    rename H1 into hd_hdl_align. rename H2 into hd_hdl_sz. rename H3 into tl_hdl_sz.

    (* stack allocation start *)
    unhide. hred_r. iApply isim_apc. iExists (Some (50%nat : Ord.t)).
    iApply isim_ccallU_salloc; ss; oauto.  iSplitL "INV"; iFrame. { iPureIntro. ss. }
    iIntros (sts0' stt0' hhs m_hhs b_hhs) "[INV [[% hhsp] hhso]]". rename H0 into hhs_sz. des.
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
    iPoseProof (live_has_offset with "thso") as "[thso thso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV thsp thso_ofs"; iFrame; [loadzero|].
    iIntros (sts10' stt10') "[INV thsp]". hred_r.  iPoseProof (decode_encode_ptr_point with "tl_hdl_point") as "#->".
    iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%". rewrite H0. rename H0 into tl_hdl_ptr. hred_r.

    iPoseProof (xorlist_hd_deen with "LIST") as "%". rename H0 into tl_deen.
    iPoseProof (xorlist_hd_not_Vundef with "LIST") as "%". rename H0 into tl_notundef.
    iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame; [loadzero|].
    iIntros (sts0 stt0) "[INV tl_hdl_point]". rewrite tl_deen. hred_r.
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
    { ss. iDestruct "LIST" as "[NULL_hd NULL_tl]". iPoseProof (null_equiv with "NULL_hd") as "%". subst.
      iPoseProof (equiv_sym with "NULL_tl") as "H". iPoseProof (null_equiv with "H") as "%". subst.
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
    ss. destruct v; try solve [iDestruct "LIST" as "[]"]. rename i into tl_item.
    iDestruct "LIST" as (i_tl_next i_tl_prev m_tl_old) "[[[[% tl_next_equiv] tl_ofs] tl_point] LIST]".
    rename H0 into m_tl_size. iPoseProof (sub_null_r with "tl_ofs") as "%". rename H0 into tl_sub_r.

    (* node* hd_new = (node* )hd_old->link start *)
    iApply isim_ccallU_cmp_ptr4; ss; oauto. rewrite tl_sub_r. iSplitL "INV tl_ofs"; iFrame.
    { iPureIntro. red. rewrite m_tl_size. change (size_chunk Mptr) with 8%Z. change (Ptrofs.unsigned Ptrofs.zero) with 0%Z. nia. }
    iIntros (sts1 stt1) "[INV tl_ofs]". hred_r. destruct (Int.eq) eqn: ?; ss; clarify. clear Heqb.
    (* if (hd_old != NULL) end *)

    unhide. hred_r. unhide. remove_tau.

    (* item = hd_old->item start *)
    iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tospt toso_ofs"; iFrame; [loadzero|]. iIntros (sts13' stt13') "[INV tospt]". hred_r.
    iPoseProof (decode_encode_ptr_point with "tl_point") as "#->".
    iPoseProof (points_to_is_ptr with "tl_point") as "%". rewrite H0. rename H0 into tl_is_ptr.
    hred_r. rewrite tl_is_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    iPoseProof (points_to_split with "tl_point") as "[tl_point_item tl_point_key]". change Archi.ptr64 with true. hred_r.
    change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs Ptrofs.zero).
    iPoseProof (add_null_r with "tl_ofs") as "%". rewrite H0. rename H0 into tl_add_null.
    iPoseProof (live_has_offset with "tl_ofs") as "[tl_ofs tl_ofs_ofs]".

    iApply isim_ccallU_load; ss; oauto. iSplitL "INV tl_point_item tl_ofs_ofs"; iFrame; [loadzero|].
    iIntros (sts2 stt2) "[INV tl_point_item]". rewrite decode_encode_item. hred_r. change Archi.ptr64 with true. hred_r.
    iPoseProof (live_has_offset with "isofs") as "[isofs iso_ofs]".
    iApply isim_ccallU_store; ss; oauto. iSplitL "INV isp iso_ofs"; iFrame; [storezero|].
    iIntros (sts14' stt14') "[INV isp]". hred_r.

    (* item = hd_old->item end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* hd_new = (node* )hd_old->link start *)
    iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tospt toso_ofs"; iFrame; [loadzero|]. iIntros (sts15' stt15') "[INV tospt]". hred_r.
    iPoseProof (decode_encode_ptr_point with "tl_point_item") as "#->".

    rewrite tl_is_ptr. hred_r. rewrite tl_is_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. change Archi.ptr64 with true. hred_r.
    change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
    iPoseProof (live_has_offset with "tl_ofs") as "[tl_ofs tl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV tl_point_key tl_ofs_ofs"; iFrame.
    { iExists _. iSplit. { iApply _has_offset_slide. et. } iPureIntro. rewrite encode_val_length. splits; et. exists 1. ss. }
    iIntros (sts3 stt3) "[INV tl_point_key]". change Mptr with Mint64. rewrite decode_encode_ofs.
    hred_r. rewrite ptrofs_cast_ptr. hred_r. rewrite ptrofs_cast_ptr. hred_r.
    iPoseProof (live_has_offset with "tnso") as "[tnso tnso_ofs]". iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV tnsp tnso_ofs"; iFrame; [storezero|]. iIntros (sts16' stt16') "[INV tnsp]". hred_r.
    (* hd_new = (node* )hd_old->link end *)

    (* hdH* = hd_new start *)
    remove_tau. unhide. remove_tau. unhide. remove_tau. iPoseProof (live_has_offset with "thso") as "[thso thso_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV thsp thso_ofs"; iFrame; [loadzero|].
    iIntros (sts17' stt17') "[INV thsp]". hred_r. change Mint64 with Mptr.
    iPoseProof (decode_encode_ptr_point with "tl_hdl_point") as "#->". rewrite tl_hdl_ptr. hred_r.
    iPoseProof (live_has_offset with "tnso") as "[tnso tnso_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV tnsp tnso_ofs"; iFrame; [loadzero|].
    iIntros (sts18' stt18') "[INV tnsp]". hred_r. rewrite decode_encode_ofs. rewrite ptrofs_cast_ptr. hred_r.
    iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".

    iApply isim_ccallU_store; ss; oauto. iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame; [storezero'|].
    iIntros (sts4 stt4) "[INV tl_hdl_point]".
    (* hdH* = hd_new end *)

    (* if (hd_new == NULL) start *)
    hred_r. unhide. remove_tau. unhide. remove_tau. iPoseProof (live_has_offset with "tnso") as "[tnso tnso_ofs]".
    iApply isim_ccallU_load; ss; oauto. iSplitL "INV tnsp tnso_ofs"; iFrame; [loadzero|].
    iIntros (sts19' stt19') "[INV tnsp]". hred_r. rewrite decode_encode_ofs.
    replace (Vlong (Int64.repr _)) with Vnullptr by et. iPoseProof (null_equiv with "tl_next_equiv") as "%".
    assert (i_tl_next = Ptrofs.zero).
    { unfold Vptrofs, Vnullptr in *. destruct Archi.ptr64 eqn:?; [|clarify].
      apply (f_equal (fun v => match v with Vlong i => i | _ => Int64.zero end)) in H0.
      apply (f_equal Ptrofs.of_int64) in H0. rewrite Ptrofs.of_int64_to_int64 in H0; et. }
    subst. clear H0. rewrite Ptrofs.xor_zero_l. destruct lnext.
    (* case: delete from singleton list *)
    - ss. iDestruct "LIST" as "[tl_equiv NULL_next]". iPoseProof (equiv_sym with "NULL_next") as "H".
      iPoseProof (null_equiv with "H") as "%". rewrite H0. clear H0 i_tl_prev.
      iApply isim_ccallU_cmp_ptr0; ss; oauto. iSplitL "INV"; iFrame.
      iIntros (sts5 stt5) "INV". hred_r. des_ifs_safe. clear Heq. unhide. remove_tau.
      (* if (hd_new == NULL) end *)

      (* tlH* = NULL start *)
      iPoseProof (live_has_offset with "hhso") as "[hhso hhso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV hhsp hhso_ofs"; iFrame; [loadzero|]. iIntros (sts20' stt20') "[INV hhsp]". hred_r.
      iPoseProof (decode_encode_ptr_point with "hd_hdl_point") as "#->".
      iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%". rewrite H0. rename H0 into hd_hdl_ptr.

      hred_r. change Archi.ptr64 with true. hred_r.
      iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto. iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame; [storezero'|].
      iIntros (sts6 stt6) "[INV hd_hdl_point]". hred_r. unhide. remove_tau.

      (* free(hd_old) start *)
      hexploit SKINCLENV; [instantiate (2:="free"); et|]. i. des. ss. rewrite H0. rename H0 into free_loc. hred_r.
      iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV tospt toso_ofs"; iFrame; [loadzero|]. iIntros (sts21' stt21') "[INV tospt]". hred_r.
      iPoseProof (decode_encode_ptr_point with "tl_point_item") as "#->".
      iPoseProof ((@point_cast_ptr _ _ Es) with "tl_point_item") as "%".
      rewrite H0. rename H0 into tl_old_cast. hred_r. des_ifs_safe. clear e.

      replace (pred _) with blk by nia. erewrite SKINCLGD; et; [|ss; et]. hred_r.

      iCombine "tl_point_item tl_point_key" as "tl_point".
      replace (Val.addl tl_old (Vlong _))
        with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (inj_bytes (encode_int 8 (Int64.unsigned tl_item))))))) by et.
      iPoseProof (points_to_collect with "tl_point") as "tl_point". iApply isim_ccallU_mfree; ss; oauto.
      iSplitL "INV tl_point tl_ofs"; iFrame; [iExists _,_; iFrame; ss|]. iIntros (sts7 stt7) "INV". hred_r. unhide. remove_tau.
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
    - ss. destruct v; clarify. iDestruct "LIST" as (i_tl i_tl_pp m_tl_prev) "[[[[% tl_equiv] tl_prev_ofs] tl_pr_pt] LIST]".
      rename H0 into m_tl_prev_size. rename i into tl_prev_item.
      iPoseProof (sub_null_r with "tl_prev_ofs") as "%". rename H0 into tl_prev_sub_r.

      iApply isim_ccallU_cmp_ptr3; ss; oauto. rewrite tl_prev_sub_r. iSplitL "INV tl_prev_ofs"; iFrame.
      { iPureIntro. red. rewrite m_tl_prev_size. change (Ptrofs.unsigned Ptrofs.zero) with 0%Z.
        change (size_chunk Mptr) with 8%Z. nia. } iIntros (sts5 stt5) "[INV tl_prev_ofs]".

      hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau.
      (* if (hd_new == NULL) end *)

      (* link = (node* )hd_new->link start *)
      iPoseProof (live_has_offset with "tnso") as "[tnso tnso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV tnsp tnso_ofs"; iFrame; [loadzero|]. iIntros (sts20' stt20') "[INV tnsp]". hred_r. rewrite decode_encode_ofs.
      replace (is_ptr_val _) with true by ss. hred_r. replace (is_ptr_val _) with true by ss. hred_r.

      iPoseProof (points_to_split with "tl_pr_pt") as "[tl_pr_pt_item tl_pr_pt_key]".

      unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. change Archi.ptr64 with true. hred_r.
      change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
      iPoseProof (live_has_offset with "tl_prev_ofs") as "[tl_prev_ofs tl_prev_ofs_ofs]".
      iApply isim_ccallU_load; ss; oauto. iSplitL "INV tl_pr_pt_key tl_prev_ofs_ofs"; iFrame.
      { iExists _. iSplit. { iApply _has_offset_slide. et. } iPureIntro. rewrite encode_val_length. splits; et. exists 1. ss. }
      iIntros (sts6 stt6) "[INV tl_pr_pt_key]". change Mptr with Mint64. rewrite decode_encode_ofs.

      hred_r. unhide. remove_tau. unhide. remove_tau. rewrite cast_ptrofs. hred_r.
      iPoseProof (live_has_offset with "lnso") as "[lnso lnso_ofs]".
      iApply isim_ccallU_store; ss; oauto. iSplitL "INV lnsp lnso_ofs"; iFrame; [storezero|].
      iIntros (sts21' stt21') "[INV lnsp]". hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.
      (* hd_new = (node* )hd_old->link end *)

      (* hd_new->link = link ^ (intptr_t)hd_old start *)
      iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV tospt toso_ofs"; iFrame; [loadzero|]. iIntros (sts22' stt22') "[INV tospt]". hred_r.
      change Mint64 with Mptr. iPoseProof (decode_encode_ptr_point with "tl_point_item") as "#->".
      iPoseProof ((@point_cast_ptr _ _ Es) with "tl_point_item") as "%". rewrite H0. rename H0 into tl_old_cast. hred_r.

      iApply isim_ccallU_capture1; ss; oauto. iSplitL "INV tl_ofs"; iFrame; [rewrite tl_sub_r; et|].
      iIntros (sts7 stt7 i) "[INV [tl_ofs tl_equiv']]".

      iCombine "tl_equiv' tl_equiv" as "tl_equiv". iPoseProof (capture_unique with "tl_equiv") as "%". clarify.
      iDestruct "tl_equiv" as "[_ tl_equiv]". hred_r. unhide. remove_tau.

      iPoseProof (live_has_offset with "tnso") as "[tnso tnso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV tnsp tnso_ofs"; iFrame; [loadzero|]. iIntros (sts23' stt23') "[INV tnsp]". hred_r.
      rewrite decode_encode_ofs. replace (is_ptr_val _) with true by ss.
      hred_r. replace (is_ptr_val _) with true by ss. hred_r.

      unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. change Archi.ptr64 with true. hred_r.
      iPoseProof (live_has_offset with "lnso") as "[lnso lnso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV lnsp lnso_ofs"; iFrame; [loadzero|]. iIntros (sts24' stt24') "[INV lnsp]". hred_r. rewrite decode_encode_ofs.
      do 2 rewrite ptrofs_cast_ptr. hred_r. des_ifs_safe. hred_r. change Archi.ptr64 with true. hred_r.

      change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
      iPoseProof (live_has_offset with "tl_prev_ofs") as "[tl_prev_ofs tl_prev_ofs_ofs]".
      iApply isim_ccallU_store; ss; oauto. iSplitL "INV tl_pr_pt_key tl_prev_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. iSplit;[|iApply _has_offset_slide; et].
        iPureIntro. rewrite encode_val_length. split; ss. exists 1. ss. }
      iIntros (sts8 stt8) "[INV tl_pr_pt_key]". hred_r. unhide. remove_tau.
      (* hd_new->link = link ^ (intptr_t)hd_old end *)


      (* free(hd_old) start *)
      hexploit SKINCLENV; [instantiate (2:="free"); et|]. i. des. ss. rewrite H0. rename H0 into free_loc. hred_r.
      iPoseProof (live_has_offset with "toso") as "[toso toso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV tospt toso_ofs"; iFrame; [loadzero|]. iIntros (sts25' stt25') "[INV tospt]". hred_r.
      change Mint64 with Mptr. iPoseProof (decode_encode_ptr_point with "tl_point_item") as "#->".
      rewrite tl_old_cast. hred_r. destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
      replace (pred _) with blk by nia. erewrite SKINCLGD; et; [|ss; et]. hred_r.

      iCombine "tl_point_item tl_point_key" as "tl_point". iPoseProof (points_to_collect with "tl_point") as "tl_point".

      iApply isim_ccallU_mfree; ss; oauto. rewrite tl_sub_r. iSplitL "INV tl_point tl_ofs"; iFrame.
      { iExists _,_. iFrame. iPureIntro. ss. } iIntros (sts12 stt12) "INV".

      hred_r. unhide. remove_tau. change Archi.ptr64 with true. ss.
      (* free(hd_old) end *)

      iPoseProof (live_has_offset with "isofs") as "[isofs iso_ofs]". iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV isp iso_ofs"; iFrame; [loadzero|]. iIntros (sts26' stt26') "[INV isp]". hred_r.
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
      hred_l. iApply isim_choose_src. iExists _. iApply isim_ret. iFrame. iSplit; ss. rewrite last_last. iSplit; ss.
      change 8%Z with (Z.of_nat (strings.length (encode_val Mint64 (Vlong tl_prev_item)))).
      iCombine "tl_pr_pt_item tl_pr_pt_key" as "tl_pr_pt". iPoseProof (points_to_collect with "tl_pr_pt") as "tl_pr_pt".
      iExists _,_,_,_,_,_. iFrame. iSplit; ss. rewrite removelast_last. rewrite <- (rev_involutive (rev lnext ++ _)).
      iApply rev_xorlist. rewrite rev_app_distr. rewrite rev_involutive.
      change (rev [Vlong tl_prev_item]) with [Vlong tl_prev_item]. ss. iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l.
      iSplit; ss. replace (Vlong (Int64.xor i i0)) with (Vptrofs i_tl_pp); et.
      clear - Heq Heq1. unfold Vptrofs in *. des_ifs. f_equal.
      rewrite int64_ptrofs_xor_comm. rewrite Ptrofs.xor_commut.
      rewrite <- Ptrofs.xor_assoc. rewrite Ptrofs.xor_idem. rewrite Ptrofs.xor_zero_l. et.
  Qed.

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

