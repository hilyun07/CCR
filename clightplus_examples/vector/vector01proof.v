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

Section LEMMA.

  Lemma divide_iff_eqmod_0 m n : (m | n)%Z <-> Zbits.eqmod m n 0.
  Proof.
    unfold Zbits.eqmod. unfold Z.divide. split.
    - intros [k H]. exists k. lia.
    - intros [k H]. exists k. lia.
  Qed.

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

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.
  
  Definition Lens (P : iProp) {X : Type} (Q R : X -> iProp) := bi_entails P (∃ x, (Q x ∗ R x) ∗ (Q x -∗ P)).

  Arguments Lens (_)%bi_scope {_} (_ _)%bi_scope.

  Lemma lens_vector_fixed_length
    v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
    :
    Lens
      (is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)
      (fun ofsᵥ => Val.addl v (Vptrofs (Ptrofs.repr 24)) (↦_mᵥ,pᵥ) (encode_val Mint64 (Vlong (Int64.repr length)))
                  ∗ Val.addl v (Vptrofs (Ptrofs.repr 24)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)%I
      (fun ofsᵥ => ⌜ strings.length (encode_val Mint64 (Vlong (Int64.repr length))) = size_chunk_nat Mint64
                ∧ bytes_not_pure (encode_val Mint64 (Vlong (Int64.repr length))) = false
                ∧ Mint64 ≠ Many64
                ∧ (size_chunk Mint64 | Ptrofs.unsigned ofsᵥ)%Z
                ⌝)%I.
  Proof.
    Local Opaque encode_val.
    iIntros "V".
    iDestruct "V" as "[% [V1 [V2 V3]]]". des.
    iDestruct "V1" as (ofsᵥ) "[% [PT HO]]".
    iExists (Ptrofs.add ofsᵥ (Ptrofs.repr 24)).
    replace (encode_val Mptr data ++
             encode_val Mint64 (Vlong (Int64.repr esize)) ++
             encode_val Mint64 (Vlong (Int64.repr capacity)) ++
             encode_val Mint64 (Vlong (Int64.repr length)))
      with ((encode_val Mptr data ++
             encode_val Mint64 (Vlong (Int64.repr esize)) ++
             encode_val Mint64 (Vlong (Int64.repr capacity)))
              ++
              encode_val Mint64 (Vlong (Int64.repr length)))
      by (rewrite ! app_assoc; reflexivity).
    iPoseProof (points_to_split with "PT") as "[PT1 PT2]".
    replace (strings.length (encode_val Mptr data
                               ++ encode_val Mint64 (Vlong (Int64.repr esize))
                               ++ encode_val Mint64 (Vlong (Int64.repr capacity))))
      with 24
      by (rewrite ! app_length; rewrite ! encode_val_length; reflexivity).
    iPoseProof (offset_slide with "HO") as "HO".

    iSplitL "PT2 HO".
    { iSplit.
      - iFrame.
      - iPureIntro. splits; ss.
        rewrite Ptrofs.add_unsigned.
        change (Ptrofs.unsigned (Ptrofs.repr 24)) with 24%Z.
        pose proof (Ptrofs.eqm_unsigned_repr (Ptrofs.unsigned ofsᵥ + 24)).
        unfold Ptrofs.eqm in H5.
        assert (8 | Ptrofs.modulus)%Z.
        { change Ptrofs.modulus with (8 * 2305843009213693952)%Z.
          eapply Z.divide_factor_l.
        }
        pose proof (Zbits.eqmod_divides _ _ _ _ H10 H11).
        eapply divide_iff_eqmod_0.
        eapply Zbits.eqmod_trans.
        eapply Zbits.eqmod_sym. eapply H12.
        eapply divide_iff_eqmod_0.
        eapply Z.divide_add_r; ss.
        change 24%Z with (8*3)%Z. eapply Z.divide_factor_l.
    }
    iIntros "[PT2 HO]".
    iPoseProof (points_to_collect with "[PT1 PT2]") as "PT".
    { iSplitL "PT1".
      - iFrame.
      - replace (strings.length (encode_val Mptr data
                                   ++ encode_val Mint64 (Vlong (Int64.repr esize))
                                   ++ encode_val Mint64 (Vlong (Int64.repr capacity))))
          with 24
          by (rewrite ! app_length; rewrite ! encode_val_length; reflexivity).
        iFrame.
    }
    iPoseProof (offset_slide_rev with "HO") as "HO".
    iFrame.
    iSplit; ss. iExists ofsᵥ. iFrame.
    iSplit; ss. rewrite ! app_assoc. iFrame.
  Qed.

  Lemma is_vector_fixed_is_ptr_val
    v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
    : bi_entails
      (is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)
      ⌜is_ptr_val v = true⌝%I.
  Proof.
    iIntros "V".
    iDestruct "V" as "[% [V1 [V2 V3]]]".
    iDestruct "V1" as (ofsᵥ) "[% [V1.1 V1.2]]".
    iApply (points_to_is_ptr with "V1.1").
  Qed.

  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb vectorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).


  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.

  (* TODO: need to be expanded to realloc and memcpy *)
  Definition mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)); 
                      ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default));
                      ("memcpy", Gfun(Ctypes.External (EF_external "memcpy" (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil) AST.Tlong cc_default)) 
                                                    (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default));
                      ("realloc", Gfun (Ctypes.External (EF_external "realloc" (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong cc_default)) 
                                                    (Tcons (tptr tvoid) (Tcons tulong Tnil)) (tptr tvoid) cc_default))].
  Let ce := Maps.PTree.elements (prog_comp_env prog).

  Section SIMFUNS.

  Variable sk: Sk.t.
  Hypothesis SKINCL1 : Sk.le (vector_compiled.(Mod.sk)) sk.
  Hypothesis SKINCL2 : Sk.le mfsk sk.
  Hypothesis SKWF : Sk.wf sk.

  Lemma sim_vector_init :
    sim_fnsem wf top2
      ("vector_init", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_init_spec))
      ("vector_init", cfunU (decomp_func sk ce f_vector_init)).
  Proof.
    (*
    Local Opaque encode_val.
    Local Opaque cast_to_ptr.
    unfold_comp _vector VALID.
    econs; ss. red.

    (* current state: 1 *)
    unfold prog in ce. unfold mkprogram in ce.
    destruct (build_composite_env'). ss.
    get_composite ce e.

    dup SKINCL1. rename SKINCL0 into SKINCLENV1.
    apply incl_incl_env in SKINCLENV1.
    unfold incl_env in SKINCLENV1.
    dup SKINCL2. rename SKINCL0 into SKINCLENV2.
    apply incl_incl_env in SKINCLENV2.
    unfold incl_env in SKINCLENV2.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_vector_init. i; ss.
    unfold decomp_func, function_entry_c. ss.
    let H := fresh "HIDDEN" in
    set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[PRE %]".
    iDestruct "PRE" as (items usize capacity length) "[% PRE]".
    des. clarify. hred_r. 

    unhide. hred_r. unhide. remove_tau. 

    unfold is_vector_handler.
    iDestruct "PRE" as (m tag offset) "[[handler_cnt handler_ofs] %]".
    rename v into vect_handler.

    iPoseProof (points_to_is_ptr with "handler_cnt") as "%".
    rewrite H4. hred_r.
    rewrite H4. hred_r.
    unfold vector._vector.
    unfold ident. des_ifs_safe.
    rewrite get_co. hred_r.
    rewrite co_co_members. ss.
    hred_r.
    change (Coqlib.align _ _) with 16%Z.

    rewrite List.app_assoc.
    iPoseProof (points_to_split with "handler_cnt") as "[A B]".
    iPoseProof (points_to_split with "B") as "[B C]".

    hred_r.
    iApply isim_apc. iExists (Some (20%nat : Ord.t)).
    iApply isim_ccallU_store.
     *)
  Admitted.

  Lemma sim_vector_destruct :
    sim_fnsem wf top2
      ("vector_destruct", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_destruct_spec))
      ("vector_destruct", cfunU (decomp_func sk ce f_vector_destruct)).
  Proof.
  Admitted.

  Lemma sim_vector_esize :
    sim_fnsem wf top2
      ("vector_esize", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_esize_spec))
      ("vector_esize", cfunU (decomp_func sk ce f_vector_esize)).
  Proof.
  Admitted.

  Lemma sim_vector_capacity :
    sim_fnsem wf top2
      ("vector_capacity", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_capacity_spec))
      ("vector_capacity", cfunU (decomp_func sk ce f_vector_capacity)).
  Proof.
  Admitted.

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

    pose proof (incl_incl_env SKINCL1) as SKINCLENV1. unfold incl_env in SKINCLENV1.
    pose proof (incl_incl_env SKINCL2) as SKINCLENV2. unfold incl_env in SKINCLENV2.
    pose proof sk_incl_gd as SKINCLGD.

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
    iPoseProof (lens_vector_fixed_length with "V") as (ofsᵥ) "[LENGTH V_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { eapply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=0%ord). eapply OrdArith.lt_from_nat. lia. }
    iSplitL "INV LENGTH". { iSplitL "INV"; done. }
    iIntros (st_src0 st_tgt0) "[INV LENGTH]".
    iDestruct ("V_RECOVER" with "LENGTH") as "V".

    Local Transparent cast_to_ptr.
    hred_r. rewrite decode_encode_item. ss. change Archi.ptr64 with true. ss. hred_r.

    hred_l. iApply isim_choose_src. iExists (Any.upcast (Vlong (Int64.repr length))).

    iApply isim_ret.
    iSplitL "INV"; et.
  Qed.

  Lemma sim_vector_reserve :
    sim_fnsem wf top2
      ("vector_reserve", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_reserve_spec))
      ("vector_reserve", cfunU (decomp_func sk ce f_vector_reserve)).
  Proof.
  Admitted.

  Lemma sim_vector_push :
    sim_fnsem wf top2
      ("vector_push", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_push_spec))
      ("vector_push", cfunU (decomp_func sk ce f_vector_push)).
  Proof.
  Admitted.

  Lemma sim_vector_get :
    sim_fnsem wf top2
      ("vector_get", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_get_spec))
      ("vector_get", cfunU (decomp_func sk ce f_vector_get)).
  Proof.
  Admitted.

  Lemma sim_vector_set :
    sim_fnsem wf top2
      ("vector_set", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_set_spec))
      ("vector_set", cfunU (decomp_func sk ce f_vector_set)).
  Proof.
  Admitted.

  Lemma sim_vector_remove :
    sim_fnsem wf top2
      ("vector_remove", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_remove_spec))
      ("vector_remove", cfunU (decomp_func sk ce f_vector_remove)).
  Proof.
  Admitted.

  End SIMFUNS.


  Require Import ClightPlusMem01Proof.

  Variable vector0 : Mod.t.
  Hypothesis VALID : vector0._vector = Errors.OK vector0.

  Theorem correct : refines2 [vector0; (ClightPlusMem0.Mem mfsk)] [vector1.vector vector0 GlobalStb; (ClightPlusMem1.Mem mfsk)].
  Proof.
  Admitted.

End PROOF.
