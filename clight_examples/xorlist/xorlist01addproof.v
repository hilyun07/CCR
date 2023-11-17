Require Import Coqlib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import SimModSem.
Require Import PCM.
Require Import HoareDef.
Require Import STB.
Require Import HTactics ProofMode.
Require Import HSim IProofMode.
Require Import ClightDmExprgen ClightDmgen.
Require Import ClightDmMem1.
Require Import CIProofMode.
Require Import xorlist.
Require Import xorlist0.
Require Import xorlist1.
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Clightdefs.

Section LEMMA.

  Lemma f_bind_ret_r E R A (s : A -> itree E R)
    : (fun a => ` x : R <- (s a);; Ret x) = s.
  Proof. apply func_ext. i. apply bind_ret_r. Qed.

  Lemma decode_encode_ofs i : decode_val Mint64 (encode_val Mint64 (Vptrofs i)) = Vptrofs i.
  Proof.
    pose proof (decode_encode_val_general (Vptrofs i) Mint64 Mint64).
    unfold Vptrofs in *. des_ifs.
  Qed.

  Lemma decode_encode_null : decode_val Mint64 (encode_val Mint64 Vnullptr) = Vnullptr.
  Proof.
    rewrite (decode_encode_val_general Vnullptr Mint64 Mint64). et.
  Qed.

  Context `{eventE -< eff}.

  Lemma cast_ptrofs i : cast_to_ptr (Vptrofs i) = Ret (Vptrofs i).
  Proof. des_ifs. Qed.

  Lemma cast_long i : Archi.ptr64 = true -> cast_to_ptr (Vlong i) = Ret (Vlong i).
  Proof. ss. Qed.

End LEMMA.

Section PROOF.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Variable GlobalStb : Sk.sem -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb xorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).


  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.


  Let ce := map (fun '(id, p) => (string_of_ident id, p)) (Maps.PTree.elements (prog_comp_env prog)).

  Section SIMFUNS.
  Variable sk: Sk.t.
  Hypothesis SKINCL : Sk.extends (xorlist0.xor.(Mod.sk)) sk.
  Hypothesis SKWF : Sk.wf (Sk.canon sk).


  Lemma sim_add :
    sim_fnsem wf top2
      ("add", fun_to_tgt "xorlist" (GlobalStb (Sk.canon sk)) (mk_pure add_spec))
      ("add", cfunU (decomp_func (Sk.canon sk) ce f_add)).
  Proof.
    (* Opaque encode_val.
    Opaque cast_to_ptr.
    econs; ss. red.

    unfold prog in ce. unfold mkprogram in ce.
    destruct (build_composite_env'). ss.
    get_composite ce e.

    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply Sk.incl_incl_env in SKINCLENV.
    unfold Sk.incl_env in SKINCLENV.
    pose proof Sk.sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_delete. i; ss.
    unfold decomp_func, function_entry_c. ss.
    let H := fresh "HIDDEN" in
    set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% PRE] %]".
    des. clarify. hred_r. unhide. hred_r. unhide.
    remove_tau. unhide. remove_tau.
    rename v into hd_hdl.
    rename v0 into tl_hdl.
    rename l into lfull.
    rename i into at_tail.
    rename i0 into item.

    hexploit SKINCLENV.
    { instantiate (2:="malloc"). ss. }
    i. des. ss. rewrite FIND. rename FIND into malloc_loc.
    hred_r. des_ifs_safe.
    rewrite cast_ptrofs.
    rename Heq1 into ptr64. rename Heq0 into get_co.
    clear Heq e. hred_r.

    replace (pred _) with blk by nia.
    erewrite SKINCLGD; et.
    hred_r. ss.
    iApply isim_apc. iExists (Some (20%nat : Ord.t)).
    rewrite co_co_sizeof.

    iApply isim_ccallU_malloc; ss; oauto.
    iSplitL "INV"; iFrame.
    { iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 p_new m_new) "[INV [[% new_point] new_ofs]]".
    set (Z.to_nat _) as si. vm_compute in si. unfold si. clear si.

    hred_r. unhide. remove_tau. 
    iPoseProof ((@offset_cast_ptr _ _ _ _ Es) with "new_ofs") as "%".
    rewrite H4. rename H4 into new_cast_ptr.
    hred_r. unhide. remove_tau. unhide.
    remove_tau.

    unfold full_xorlist.
    iDestruct "PRE" 
      as (m_hd_hdl m_tl_hdl hd tl ofs_hd_hdl ofs_tl_hdl) "PRE".
    iDestruct "PRE" as (tg_hd_hdl tg_tl_hdl) 
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    rename H4 into hd_hdl_align.
    rename H5 into tl_hdl_align.

    iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%".
    rewrite H4. rename H4 into hd_hdl_is_point. hred_r.

    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
    { rewrite encode_val_length. et. }
    iIntros (st_src1 st_tgt1) "[INV [hd_hdl_point hd_hdl_ofs]]".
    unfold Mptr. rewrite ptr64.
    replace (decode_val Mint64 (encode_val Mint64 hd)) with hd by admit "fullxor's head is pointer".

    hred_r. unhide. remove_tau. unhide. remove_tau.
    iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%".
    rewrite H4. rename H4 into tl_hdl_is_point. hred_r.

    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tl_hdl_point tl_hdl_ofs"; iFrame.
    { rewrite encode_val_length. et. }
    iIntros (st_src2 st_tgt2) "[INV [tl_hdl_point tl_hdl_ofs]]".
    unfold Mptr. rewrite ptr64. 
    replace (decode_val Mint64 (encode_val Mint64 tl)) with tl by admit "fullxor's head is pointer".

    hred_r. unhide. remove_tau. unhide. remove_tau.
    iPoseProof (points_to_is_ptr with "new_point") as "%".
    rewrite H4. rename H4 into new_is_point.
    hred_r. rewrite new_is_point. hred_r. rewrite co_co_members. ss.
    hred_r.
    replace (Coqlib.align 0 _) with 0%Z by et.
    replace (Ptrofs.repr 0) with Ptrofs.zero by et.
    iPoseProof (add_null_r with "new_ofs") as "%".
    rewrite H4. rename H4 into new_add_r.

    replace ([Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef])
    with ([Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef] ++ [Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef]) by et.
    iPoseProof (points_to_split with "new_point") as "[new_point_item new_point_key]".
    rewrite cast_long. hred_r.

    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV new_point_item new_ofs"; iFrame.
    { iExists _. iFrame. ss.
      iPureIntro. split; et. exists 0. ss. }
    iIntros (st_src3 st_tgt3) "[INV [new_point_item new_ofs]]".

    hred_r. unhide. remove_tau.
    replace (Vlong (Int64.repr _)) with Vnullptr by et.

    destruct lfull.
    (* case: nil list *)
    - unfold frag_xorlist at 1.
      iDestruct "LIST" as "[end_equiv %]". des. clarify.
      replace (Vptrofs Ptrofs.zero) with Vnullptr by et.

      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src4 st_tgt4) "INV".

      hred_r. des_ifs_safe. clear Heq.
      unhide. hred_r. unhide. remove_tau.
      rewrite new_is_point. hred_r.
      rewrite new_is_point. hred_r.
      rewrite co_co_members. ss. hred_r.
      replace (Coqlib.align _ _) with 8%Z by et.
      replace (Vlong (Int64.repr _)) with Vnullptr by et.
      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV new_point_key new_ofs"; iFrame.
      { iExists _. iFrame. iSplit; cycle 1.
        { iApply offset_slide. iFrame. }
        { iPureIntro. split; ss. exists 1. ss. } }
      iIntros (st_src5 st_tgt5) "[INV [new_point_key new_ofs]]".

      hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau. 
      unhide. remove_tau.

      iPoseProof ((offset_slide _ _ _ _ _ (Ptrofs.repr (-8)%Z)) with "new_ofs") as "new_ofs".
      replace (Val.addl (Val.addl _ _) _) with p_new.
      2:{ rewrite Val.addl_assoc. ss. }
      replace (Ptrofs.add (Ptrofs.add _ _) _) with Ptrofs.zero.
      2:{ rewrite Ptrofs.add_assoc. ss. }

      rewrite new_cast_ptr. hred_r. unhide. remove_tau.
      rewrite tl_hdl_is_point. hred_r.
      rewrite new_cast_ptr. hred_r.

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV tl_hdl_point tl_hdl_ofs"; iFrame.
      { iExists _. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (st_src7 st_tgt7) "[INV [tl_hdl_point tl_hdl_ofs]]".

      hred_r. unhide. remove_tau.
      rewrite hd_hdl_is_point. hred_r.
      rewrite new_cast_ptr. hred_r.

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
      { iExists _. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (st_src8 st_tgt8) "[INV [hd_hdl_point hd_hdl_ofs]]".


      hred_r. remove_tau. hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret.
      iFrame. iSplit; ss. iSplit; ss.
      replace (Vptrofs (Ptrofs.repr 8))
        with (Vptrofs (Ptrofs.repr (length (encode_val Mint64 (Vlong item))))) by ss.
      iCombine "new_point_item new_point_key" as "new_point".
      iPoseProof (points_to_collect with "new_point") as "new_point".
      iExists _,_,_,_,_,_,_,_. iFrame.
      iSplit.
      { iPureIntro. splits; ss. }
      unfold vlist_add.
      destruct (Val.eq _ _); ss.
      + iExists Ptrofs.zero,Ptrofs.zero,_,_.
        replace (Ptrofs.xor _ _) with Ptrofs.zero by et.
        replace (Vptrofs Ptrofs.zero) with Vnullptr by et.
        iFrame. instantiate (1:=m_new).
        iSplitL.
        { iSplit; ss. Transparent captured_to. unfold captured_to. des_ifs.
          Opaque captured_to. }
        { iSplit; ss. iLeft. ss. }
      + iExists Ptrofs.zero,Ptrofs.zero,_,_.
        replace (Ptrofs.xor _ _) with Ptrofs.zero by et.
        replace (Vptrofs Ptrofs.zero) with Vnullptr by et.
        iFrame. instantiate (1:=m_new).
        iSplitL.
        { iSplit; ss. Transparent captured_to. unfold captured_to. des_ifs.
          Opaque captured_to. }
        { iSplit; ss. iLeft. ss. }
    - ss. destruct v; try solve [iDestruct "LIST" as "%"; clarify].
      iDestruct "LIST" as (i_prev i_next m_prev m_hd) 
        "[[[[% prev_addr] hd_ofs] hd_point] LIST]".

      iApply isim_ccallU_cmp_ptr3; ss; oauto.
      iSplitL "INV hd_ofs".
      { iFrame. iPureIntro. red. rewrite H4. ss. }
      iIntros (st_src4 st_tgt4) "[INV hd_ofs]".

      hred_r. des_ifs_safe. unhide. remove_tau.
      des_ifs; cycle 1.
      (* not nil, head case *)
      + rename Heq0 into ISHEAD.
        unhide. hred_r. unhide. remove_tau. unhide. remove_tau.
        hexploit SKINCLENV.
        { instantiate (2:="encrypt"). ss. }
        i. des. ss. rewrite FIND. rename FIND into encrypt_loc.
        hred_r. rewrite cast_long; et. hred_r. des_ifs. clear e.
        rename H4 into m_hd_size.
        iPoseProof ((@offset_cast_ptr _ _ _ _ Es) with "hd_ofs") as "%".
        rewrite H4. hred_r.
        rename H4 into hd_cast_ptr.

        replace (pred _) with blk0 by nia.
        erewrite SKINCLGD; et.
        hred_r. ss.
        replace (Vlong (Int64.repr _)) with Vnullptr by et.

        iApply isim_ccallU_pure; et.
        { eapply fn_has_spec_in_stb; et.
          { eapply STBINCL. stb_tac. unfold xorStb.
            unseal "stb". ss. }
          { ss. instantiate (1:=inr (inr (inl (_,_,_,_,_)))).
            ss. oauto. }
          { ss. } }
        { instantiate (1:=14). oauto. }
        
        ss. iSplitL "INV hd_ofs".
        { iFrame. ss. }
        iIntros (st_src5 st_tgt5 ret_src ret_tgt) "[INV [POST %]]".
        iDestruct "POST" as (i_hd') "[[% hd_addr] hd_ofs]".
        iExists _. iSplit; ss. clear H4 H5 Heq.

        hred_r. unhide. remove_tau.
        rewrite new_is_point. hred_r.
        rewrite new_is_point. hred_r.
        rewrite co_co_members. ss. hred_r.
        replace (Coqlib.align _ _) with 8%Z by et.
        rewrite cast_ptrofs. hred_r.

        iApply isim_ccallU_store; ss; oauto.
        iSplitL "INV new_point_key new_ofs".
        { iFrame. iExists _. iFrame. iSplit.
          2:{ iApply offset_slide. ss. }
          iPureIntro. split; ss. exists 1. ss. }
        iIntros (st_src6 st_tgt6) "[INV [new_point_key new_ofs]]".

        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        hexploit SKINCLENV.
        { instantiate (2:="decrypt"). ss. }
        i. des. ss. rewrite FIND. rename FIND into decrypt_loc.
        hred_r.
        iPoseProof (points_to_is_ptr with "hd_point") as "%".
        rewrite H4. rename H4 into hd_is_point.
        hred_r. rewrite hd_is_point. hred_r.
        rewrite co_co_members. ss. hred_r.
        replace (Coqlib.align _ _) with 8%Z by et.

        iPoseProof (points_to_split with "hd_point") as "[hd_point_item hd_point_key]".
        iApply isim_ccallU_load; ss; oauto.
        iSplitL "INV hd_point_key hd_ofs".
        { iFrame. iSplit.
          { iApply offset_slide. ss. }
          iPureIntro. rewrite encode_val_length.
          split; ss. exists 1. ss. }
        iIntros (st_src7 st_tgt7) "[INV [hd_point_key hd_ofs]]".

        unfold Mptr. rewrite ptr64.
        rewrite decode_encode_ofs. hred_r.
        rewrite cast_long; et. hred_r.
        rewrite cast_ptrofs. hred_r.
        des_ifs_safe. clear e.

        replace (pred _) with blk1 by nia.
        erewrite SKINCLGD; et.
        hred_r. ss.
        replace (Vlong (Int64.repr _)) with Vnullptr by et.
        iApply isim_ccallU_pure; et.
        { eapply fn_has_spec_in_stb; et.
          { eapply STBINCL. stb_tac. unfold xorStb.
            unseal "stb". ss. }
          { ss. instantiate (1:=(inr _)).
            ss. oauto. }
          { ss. } }
        { instantiate (1:=11). oauto. }

        ss. iSplitL "INV".
        { iFrame. ss. }
        iIntros (st_src8 st_tgt8 ret_src0 ret_tgt0) "[INV [POST %]]".
        iDestruct "POST" as "%". clarify.
        iExists _. iSplit; ss.

        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        unhide. remove_tau.
        rewrite encrypt_loc. hred_r.
        rewrite cast_ptrofs. hred_r.
        rewrite new_cast_ptr. hred_r.
        des_ifs. clear e. hred_r.
        replace (pred _) with blk0 by nia.
        erewrite SKINCLGD; et.
        hred_r. ss.
        replace i_prev with Ptrofs.zero by admit "vnullptr capture is zero".
        rewrite Ptrofs.xor_zero_l.
        destruct lfull; ss.
        * iDestruct "LIST" as "[end_equiv %]". des. clarify.
          replace i_next with Ptrofs.zero by admit "intval is equal".
          replace (Vptrofs Ptrofs.zero) with Vnullptr by et.
          iPoseProof ((offset_slide _ _ _ _ _ (Ptrofs.repr (-8)%Z)) with "new_ofs") as "new_ofs".
          replace (Val.addl (Val.addl _ _) _) with p_new.
          2:{ rewrite Val.addl_assoc. ss. }
          replace (Ptrofs.add (Ptrofs.add _ _) _) with Ptrofs.zero.
          2:{ rewrite Ptrofs.add_assoc. ss. }

          iApply isim_ccallU_pure; et.
          { eapply fn_has_spec_in_stb; et.
            { eapply STBINCL. stb_tac. unfold xorStb.
              unseal "stb". ss. }
            { ss. instantiate (1:=(inr (inl (_,_,_,_,_)))).
              ss. oauto. }
            { ss. } }
          { instantiate (1:=10). oauto. }

          ss. iSplitL "INV new_ofs".
          { iFrame. iPureIntro. ss. }
          iIntros (st_src9 st_tgt9 ret_src0 ret_tgt0) "[INV [POST %]]".
          iDestruct "POST" as (i_l) "[[% new_addr] new_ofs]".
          rewrite H6. clear H6 H4.
          iExists _. iSplit; ss.

          hred_r. unhide. remove_tau.

          iPoseProof (points_to_is_ptr with "hd_point_item") as "%".
          rewrite H4. hred_r.
          rewrite H4. hred_r.
          rewrite co_co_members. ss. hred_r.
          replace (Coqlib.align _ _) with 8%Z by et.
          rewrite cast_ptrofs. hred_r.

          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV hd_point_key hd_ofs".
          { iFrame. iExists _. iFrame.
            iPureIntro. split; ss. exists 1. ss. }
          iIntros (st_src10 st_tgt10) "[INV [hd_point_key hd_ofs]]".

          hred_r. unhide. remove_tau.
          rewrite hd_hdl_is_point. hred_r.
          rewrite new_cast_ptr. hred_r.
          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV hd_hdl_point hd_hdl_ofs".
          { iFrame. iExists _. iFrame. iPureIntro.
            rewrite encode_val_length. ss. }
          iIntros (st_src11 st_tgt11) "[INV [hd_hdl_point hd_hdl_ofs]]".

          hred_r. remove_tau. hred_l. iApply isim_choose_src.
          iExists _. iApply isim_ret.
          iFrame. iSplit; ss. iSplit; ss.
          iCombine "new_point_item new_point_key" as "new_point".
          iCombine "hd_point_item hd_point_key" as "hd_point".
          iPoseProof (points_to_collect with "new_point") as "new_point".
          iPoseProof (points_to_collect with "hd_point") as "hd_point".

          iPoseProof ((offset_slide _ _ _ _ _ (Ptrofs.repr (-8)%Z)) with "hd_ofs") as "hd_ofs".
          replace (Val.addl (Val.addl _ _) _) with (Val.addl hd (Vptrofs Ptrofs.zero)).
          2:{ rewrite Val.addl_assoc. ss. }
          replace (Ptrofs.add (Ptrofs.add _ _) _) with Ptrofs.zero.
          2:{ rewrite Ptrofs.add_assoc. ss. }
          replace (Val.addl hd (Vptrofs Ptrofs.zero)) with hd by admit "capture should be add_null_r".

          iExists _,_,_,_,_,_,_,_. iFrame.
          iSplit; ss. unfold vlist_add.
          destruct Val.eq; ss; cycle 1.
          { destruct (Int.eq at_tail Int.zero) eqn: E; clarify.
            apply Int.same_if_eq in E. clarify. }
          { iExists Ptrofs.zero,i_hd',_,_. iFrame. rewrite Ptrofs.xor_zero_l.
            iFrame. iSplit; ss.
            unfold ptr_equiv. 
            iDestruct "end_equiv" as "[%|[B|C]]".
            { iPoseProof (capture_dup with "hd_addr") as "[hd_addr hd_addr']".
              iPoseProof (capture_dup with "hd_addr'") as "[hd_addr' hd_addr'']".
              iPoseProof (capture_pointto_comm with "hd_addr'") as "comm".
              iPoseProof (capture_offset_comm with "hd_addr''") as "comm'".
              iPoseProof ("comm" with "hd_point") as "hd_point".
              iPoseProof ("comm'" with "hd_ofs") as "hd_ofs".
              iExists _,Ptrofs.zero,_,_. iFrame.
              rewrite Ptrofs.xor_zero. iFrame. 
              clarify. iSplit; ss. iSplit; ss.
              iRight. iRight. iExists _. iSplit; ss. iExists _. iFrame. }
            { iDestruct "B" as (i0) "[% REL]".
              iDestruct "REL" as (m) "REL".
              iCombine "hd_point REL" as "hd".
              iPoseProof (replace_meta_to_alive with "hd") as "[hd_point REL]".
              iCombine "hd_addr REL" as "hd_addr".
              iPoseProof (capture_unique with "hd_addr") as "%".
              clarify.
              iDestruct "hd_addr" as "[hd_addr _]".
              iExists _,Ptrofs.zero,_,_. iFrame.
              iPoseProof (capture_dup with "hd_addr") as "[hd_addr hd_addr']".
              iPoseProof (capture_dup with "hd_addr'") as "[hd_addr' hd_addr'']".
              iPoseProof (capture_pointto_comm with "hd_addr'") as "comm".
              iPoseProof (capture_offset_comm with "hd_addr''") as "comm'".
              iPoseProof ("comm" with "hd_point") as "hd_point".
              iPoseProof ("comm'" with "hd_ofs") as "hd_ofs".
              iFrame. 
              rewrite Ptrofs.xor_zero. iFrame.
              iSplit; ss. iSplit; ss. iLeft. ss. }
            { iDestruct "C" as (i0) "[% REL]".
              iDestruct "REL" as (m) "REL". clarify.
              iPoseProof (capture_dup with "hd_addr") as "[hd_addr hd_addr']".
              iPoseProof (capture_dup with "hd_addr'") as "[hd_addr' hd_addr'']".
              iPoseProof (capture_pointto_comm with "hd_addr'") as "comm".
              iPoseProof (capture_offset_comm with "hd_addr''") as "comm'".
              iPoseProof ("comm" with "hd_point") as "hd_point".
              iPoseProof ("comm'" with "hd_ofs") as "hd_ofs".
              iExists _,Ptrofs.zero,_,_. iFrame.
              rewrite Ptrofs.xor_zero. iFrame.
              iSplit; ss. iSplit; ss. iRight. iRight. 
              assert (i0 = i_hd') by admit "capture for int".
              clarify. iExists _. iSplit; ss. iExists _. iFrame. } }
        * destruct v; try solve [iDestruct "LIST" as "%"; clarify].
          iDestruct "LIST" as (i_hd i_next_next m_hd' m_next)
            "[[[[% hd_addr'] next_ofs] next_point] LIST]".
          rename H4 into m_next_size.

          iPoseProof ((offset_slide _ _ _ _ _ (Ptrofs.repr (-8)%Z)) with "new_ofs") as "new_ofs".
          replace (Val.addl (Val.addl _ _) _) with p_new.
          2:{ rewrite Val.addl_assoc. ss. }
          replace (Ptrofs.add (Ptrofs.add _ _) _) with Ptrofs.zero.
          2:{ rewrite Ptrofs.add_assoc. ss. }

          iApply isim_ccallU_pure; et.
          { eapply fn_has_spec_in_stb; et.
            { eapply STBINCL. stb_tac. unfold xorStb.
              unseal "stb". ss. }
            { ss. instantiate (1:= (inl (_,_,_,_,_,_,_,_,_,_))).
              ss. oauto. }
            { ss. } }
          { instantiate (1:=10). oauto. }

          ss. iSplitL "INV new_ofs next_ofs".
          { iSplit; ss. iSplit; ss. iSplitR "next_ofs"; ss. iFrame. ss. }
          iIntros (st_src9 st_tgt9 ret_src0 ret_tgt0) "[INV [POST %]]".
          iDestruct "POST" as (i_new i_next') "[[[[% new_ofs] next_ofs] new_addr] next_addr]".
          rewrite H5. clear H5 H4.
          iExists _. iSplit; ss.

          hred_r. unhide. remove_tau.
          rewrite hd_is_point. hred_r.
          rewrite hd_is_point. hred_r.
          rewrite co_co_members. ss. hred_r.
          replace (Coqlib.align _ _) with 8%Z.
          rewrite cast_ptrofs. hred_r.

          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV hd_point_key hd_ofs".
          { iFrame. iExists _. iFrame. iPureIntro. split; ss. exists 1. ss. }
          iIntros (st_src10 st_tgt10) "[INV [hd_point_key hd_ofs]]".

          hred_r. unhide. remove_tau.
          rewrite hd_hdl_is_point. hred_r.
          rewrite new_cast_ptr. hred_r.

          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV hd_hdl_point hd_hdl_ofs".
          { iFrame. iExists _. iFrame. iPureIntro. split; ss.
            rewrite encode_val_length. ss. }
          iIntros (st_src11 st_tgt11) "[INV [hd_hdl_point hd_hdl_ofs]]".

          hred_r. remove_tau. 2: ss. hred_l. iApply isim_choose_src.
          iExists _. iApply isim_ret. iSplit; ss. iSplit; ss. iSplit; ss.
          iExists _,_,_,_,_,_,_,_. iFrame.
          iSplit; ss.
          unfold vlist_add.
          destruct Val.eq; cycle 1.
          { destruct (Int.eq at_tail Int.zero) eqn: E; clarify.
            apply Int.same_if_eq in E. clarify. }


          iCombine "new_point_item new_point_key" as "new_point".
          iCombine "hd_point_item hd_point_key" as "hd_point".
          iPoseProof (points_to_collect with "new_point") as "new_point".
          iPoseProof (points_to_collect with "hd_point") as "hd_point".
          iCombine "hd_point hd_addr'" as "hd".
          iPoseProof (replace_meta_to_alive with "hd") as "[hd_point hd_addr']".
          iCombine "hd_addr hd_addr'" as "hd_addr".
          iPoseProof (capture_unique with "hd_addr") as "%".
          clarify.
          iDestruct "hd_addr" as "[_ hd_addr]".
          iPoseProof ((offset_slide _ _ _ _ _ (Ptrofs.repr (-8)%Z)) with "hd_ofs") as "hd_ofs".
          replace (Val.addl (Val.addl _ _) _) with hd.
          2:{ rewrite Val.addl_assoc. admit "captured val plus null". }
          replace (Ptrofs.add (Ptrofs.add _ _) _) with Ptrofs.zero.
          2:{ rewrite Ptrofs.add_assoc. ss. }

          ss. iExists _,i_hd,_,_. iFrame.
          rewrite Ptrofs.xor_zero_l. iFrame. iSplit; ss.
          iPoseProof (capture_dup with "hd_addr") as "[hd_addr hd_addr']".
          iPoseProof (capture_dup with "hd_addr'") as "[hd_addr' hd_addr'']".
          iPoseProof (capture_pointto_comm with "hd_addr'") as "comm".
          iPoseProof (capture_offset_comm with "hd_addr''") as "comm'".
          iPoseProof ("comm" with "hd_point") as "hd_point".
          iPoseProof ("comm'" with "hd_ofs") as "hd_ofs".
          iExists _,_,_,_. iFrame. iSplit; ss.
          replace i_next' with i_next by admit "captured int is equal".
          iExists _,_,_,_. iFrame. iSplit; ss.
          iPoseProof (capture_refl with "hd_addr") as "?".
          iFrame. *)
  Admitted.

  End SIMFUNS.

End PROOF.