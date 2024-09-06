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

  Lemma decode_encode_ptr p : is_ptr_val p -> decode_val Mptr (encode_val Mptr p) = p.
  Proof.
    intro.
    pose proof (decode_encode_val_general p Mptr Mptr).
    destruct p; ss.
  Qed.

  Lemma agree64_eq (p : ptrofs) (n : int64) : Ptrofs.agree64 p n -> Ptrofs.to_int64 p = n.
  Proof.
    unfold Ptrofs.agree64, Ptrofs.to_int64.
    i. rewrite H. apply Int64.repr_unsigned.
  Qed.

  Lemma Ptrofs_repr_Z_add x y : Ptrofs.repr (x + y) = Ptrofs.add (Ptrofs.repr x) (Ptrofs.repr y).
  Proof.
    rewrite Ptrofs.add_unsigned.
    eapply Ptrofs.eqm_samerepr.
    eapply Ptrofs.eqm_add.
    - eapply Ptrofs.eqm_unsigned_repr.
    - eapply Ptrofs.eqm_unsigned_repr.
  Qed.

  Lemma is_ptr_val_null_r
    p : is_ptr_val p -> Val.addl p (Vptrofs Ptrofs.zero) = p.
  Proof.
    i.
    change (Vptrofs Ptrofs.zero) with (Vlong Int64.zero).
    destruct p; ss.
    - rewrite Int64.add_zero. ss.
    - des_ifs. change (Ptrofs.of_int64 Int64.zero) with Ptrofs.zero.
      rewrite Ptrofs.add_zero. ss.
  Qed.

  Lemma addl_Vptrofs m n : Val.addl (Vptrofs m) (Vptrofs n) = Vptrofs (Ptrofs.add m n).
  Proof.
    unfold Vptrofs; des_ifs; ss. f_equal.
    symmetry. eapply agree64_eq.
    eapply Ptrofs.agree64_add; ss.
    - apply Ptrofs.agree64_to_int; ss.
    - apply Ptrofs.agree64_to_int; ss.
  Qed.

  Context `{eventE -< eff}.

  Lemma encode_ptr_bytes_not_pure p : is_ptr_val p -> bytes_not_pure (encode_val Mptr p) = false.
  Proof. destruct p; ss. Qed.

  Lemma cast_to_ptr_ptr p : is_ptr_val p -> cast_to_ptr p = Ret p.
  Proof. destruct p; ss. Qed.

  Lemma cast_ptrofs i : cast_to_ptr (Vptrofs i) = Ret (Vptrofs i).
  Proof. des_ifs. Qed.

  Lemma cast_long i : Archi.ptr64 = true -> cast_to_ptr (Vlong i) = Ret (Vlong i).
  Proof. ss. Qed.

  Lemma sem_add_ptr_long_c_addl ce p n
    (PTR : is_ptr_val p)
    : sem_add_ptr_long_c ce tschar p (Vlong n) = Ret (Val.addl p (Vlong n)).
  Proof.
    unfold sem_add_ptr_long_c, Val.addl.
    change Archi.ptr64 with true; ss.
    destruct p; ss; repeat f_equal.
    - rewrite Int64.mul_commut. apply Int64.mul_one.
    - rewrite Ptrofs.mul_commut. apply Ptrofs.mul_one.
  Qed.

End LEMMA.

Section PROOF.

  Import ClightPlusMem1.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition Lens (P : iProp) {X : Type} (Q R : X -> iProp) := bi_entails P (∃ x, (Q x ∗ R x) ∗ (Q x -∗ P)).
  Definition Accessor (P Q : iProp) := bi_entails P (Q ∗ (Q -∗ P)).

  Arguments Lens (_)%bi_scope {_} (_ _)%bi_scope.

  Lemma accessor_compose P Q R :
    Accessor P Q -> Accessor Q R -> Accessor P R.
  Proof.
    iIntros (AP AQ) "P".
    iPoseProof (AP with "P") as "[Q QP]".
    iPoseProof (AQ with "Q") as "[R RQ]".
    iFrame.
    iIntros "R".
    iApply "QP". iApply "RQ". iApply "R".
  Qed.

  Lemma accessor_is_vector_fixed_2
    v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
    :
    Accessor
      (is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)
      ((list_points_to data m_data cells) ** (data (⊨_m_data,Dynamic,q_data) Ptrofs.zero)).
  Proof.
    iIntros "V".
    iDestruct "V" as "(% & V1 & V2 & V3)".
    iFrame.
    iIntros "V2". iFrame.
    iPureIntro. ss.
  Qed.

  Lemma accessor_is_vector_fixed_3 cs : forall (esize : nat) p m (i : nat) c,
    is_ptr_val p ->
    Forall (fun c => cell_size c = esize) cs ->
    cs !! i = Some c ->
    Accessor (list_points_to p m cs)
             (cell_points_to (Val.addl p (Vptrofs (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.repr i)))) m c).
  Proof.
    induction cs; i.
    - ss.
    - destruct i; ss.
      + inv H5. inv H4. inv H3.
        iIntros "[CPT LPT]".
        replace (Ptrofs.mul (Ptrofs.repr (cell_size c)) (Ptrofs.repr 0)) with Ptrofs.zero.
          2: { change (Ptrofs.repr 0) with Ptrofs.zero. rewrite Ptrofs.mul_zero. ss. }
        rewrite is_ptr_val_null_r; ss.
        iSplitL "CPT". iFrame.
        iIntros "CPT". iFrame.
      + inversion H4. subst l x. rewrite H8. clear H4 H8.
        iIntros "[CPT LPT]".
        hexploit (IHcs esize (Val.addl p (Vptrofs (Ptrofs.repr esize)))).
        { destruct p; ss. }
        { ss. }
        { eapply H5. }
        i. iPoseProof (H4 with "LPT") as "[CPT_OFS LPT_RECOVER]".
        replace (Val.addl (Val.addl p (Vptrofs (Ptrofs.repr esize)))
                          (Vptrofs (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.repr i))))
          with (Val.addl p (Vptrofs (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.repr (Z.pos (Pos.of_succ_nat i)))))); cycle 1.
        { rewrite Zpos_P_of_succ_nat. rewrite Val.addl_assoc. f_equal.
          rewrite addl_Vptrofs. f_equal.
          replace (Ptrofs.repr esize)
            with (Ptrofs.mul (Ptrofs.repr esize) Ptrofs.one)
            at 2
            by eapply Ptrofs.mul_one.
          transitivity (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.add Ptrofs.one (Ptrofs.repr i))).
          - f_equal. rewrite Ptrofs.add_unsigned.
            unfold Ptrofs.one, Z.succ.
            rewrite ! Ptrofs_repr_Z_add.
            rewrite ! Ptrofs.repr_unsigned.
            apply Ptrofs.add_commut.
          - apply Ptrofs.mul_add_distr_r.
        }
        iSplitL "CPT_OFS".
        * iFrame.
        * iIntros "CPT_OFS".
          iPoseProof ("LPT_RECOVER" with "CPT_OFS") as "LPT".
          iFrame.
  Qed.

  Lemma is_vector_fixed_esize_le_max_unsigned
    v data (esize : nat) capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
      : bi_entails
        (is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)
        ⌜(Z.of_nat esize <= Int64.max_unsigned)%Z⌝%I.
  Proof.
    iIntros "V".
    iDestruct "V" as "(% & _ & _ & _)". des.
    iPureIntro.
    assert (Z.of_nat esize <= Ptrofs.max_unsigned)%Z by nia.
    ss.
  Qed.

  Lemma is_vector_fixed_cells_esize
    v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
    : bi_entails
      (is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)
      ⌜Forall (fun c => cell_size c = esize) cells⌝%I.
  Proof.
    iIntros "V".
    iDestruct "V" as "(% & _ & _ & _)". des.
    iPureIntro.
    ss.
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

  Lemma is_vector_fixed_is_ptr_data
    v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
    : bi_entails
      (is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)
      ⌜is_ptr_val data = true⌝%I.
  Proof.
    iIntros "V".
    iDestruct "V" as "[% [V1 [V2 V3]]]".
    iApply (offset_is_ptr with "V3").
  Qed.

  Lemma is_vector_is_ptr_val
    v esize capacity length cells mᵥ tgᵥ qᵥ
    : bi_entails
      (is_vector v esize capacity length cells mᵥ tgᵥ qᵥ)
      ⌜is_ptr_val v = true⌝%I.
  Proof.
    iIntros "V".
    iDestruct "V" as (data m_data unused_length unused) "[% [V1 [V2 [V3 V4]]]]".
    iDestruct "V1" as (ofsᵥ) "[% [V1.1 V1.2]]".
    iApply (points_to_is_ptr with "V1.1").
  Qed.

  Lemma lens_vector_handler_data
    v data esize capacity length mᵥ tgᵥ pᵥ qᵥ
    :
    Lens
      (is_vector_handler v data esize capacity length mᵥ tgᵥ pᵥ qᵥ)
      (fun ofsᵥ => Val.addl v (Vptrofs (Ptrofs.repr 0)) (↦_mᵥ,pᵥ) (encode_val Mptr data)
                          ∗ Val.addl v (Vptrofs (Ptrofs.repr 0)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)%I
      (fun ofsᵥ => ⌜ strings.length (encode_val Mptr data) = size_chunk_nat Mptr
                          ∧ bytes_not_pure (encode_val Mptr data) = false
                          ∧ Mptr ≠ Many64
                          ∧ (size_chunk Mptr | Ptrofs.unsigned ofsᵥ)%Z
                          ⌝)%I.
  Proof.
    Local Opaque encode_val.
    iIntros "V".
    iDestruct "V" as (ofsᵥ) "[% [PT HO]]". des.
    iExists ofsᵥ.
    iPoseProof (points_to_split with "PT") as "[PT1 PT2]".
    replace (strings.length (encode_val Mptr data))
      with 8
      by (rewrite encode_val_length; reflexivity).

    iPoseProof (add_null_r with "HO") as "%".
    iPoseProof (offset_is_ptr with "HO") as "%".
    change (Ptrofs.repr 0) with Ptrofs.zero.
    rewrite H5.
    iSplitL "PT1 HO".
    { iFrame. iPureIntro. splits; ss.
      apply encode_ptr_bytes_not_pure. ss.
    }

    iIntros "[PT1 HO]".
    iPoseProof (points_to_collect with "[PT1 PT2]") as "PT".
    { iSplitL "PT1".
      - iFrame.
      - replace (strings.length (encode_val Mptr data))
          with 8
          by (rewrite encode_val_length; reflexivity).
        iFrame.
    }

    iExists ofsᵥ. iFrame.
    iPureIntro. ss.
  Qed.

  Lemma lens_vector_fixed_data
    v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
    :
    Lens
      (is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)
      (fun ofsᵥ => Val.addl v (Vptrofs (Ptrofs.repr 0)) (↦_mᵥ,pᵥ) (encode_val Mptr data)
                  ∗ Val.addl v (Vptrofs (Ptrofs.repr 0)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)%I
      (fun ofsᵥ => ⌜ strings.length (encode_val Mptr data) = size_chunk_nat Mptr
                ∧ bytes_not_pure (encode_val Mptr data) = false
                ∧ Mptr ≠ Many64
                ∧ (size_chunk Mptr | Ptrofs.unsigned ofsᵥ)%Z
                ⌝)%I.
  Proof.
    Local Opaque encode_val.
    iIntros "V".
    iDestruct "V" as "[% [V1 [V2 V3]]]".
    iDestruct "V1" as (ofsᵥ) "[% [PT HO]]". des.
    iExists ofsᵥ.
    iPoseProof (points_to_split with "PT") as "[PT1 PT2]".
    replace (strings.length (encode_val Mptr data))
      with 8
      by (rewrite encode_val_length; reflexivity).

    iPoseProof (add_null_r with "HO") as "%".
    iPoseProof (offset_is_ptr with "HO") as "%".
    change (Ptrofs.repr 0) with Ptrofs.zero.
    rewrite H11.
    iSplitL "PT1 HO".
    { iFrame. iPureIntro. splits; ss.
      apply encode_ptr_bytes_not_pure. ss.
    }

    iIntros "[PT1 HO]".
    iPoseProof (points_to_collect with "[PT1 PT2]") as "PT".
    { iSplitL "PT1".
      - iFrame.
      - replace (strings.length (encode_val Mptr data))
          with 8
          by (rewrite encode_val_length; reflexivity).
        iFrame.
    }

    iSplit.
    iPureIntro. ss.
    iSplitL "PT HO"; iFrame.
    iExists ofsᵥ. iFrame. iPureIntro. ss.
  Qed.

  Lemma lens_vector_fixed_esize
    v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
    :
    Lens
      (is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)
      (fun ofsᵥ => Val.addl v (Vptrofs (Ptrofs.repr 8)) (↦_mᵥ,pᵥ) encode_val Mint64 (Vlong (Int64.repr esize))
                  ∗ Val.addl v (Vptrofs (Ptrofs.repr 8)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)%I
      (fun ofsᵥ => ⌜ strings.length (encode_val Mint64 (Vlong (Int64.repr esize))) = size_chunk_nat Mint64
                ∧ bytes_not_pure (encode_val Mint64 (Vlong (Int64.repr esize))) = false
                ∧ Mint64 ≠ Many64
                ∧ (size_chunk Mint64 | Ptrofs.unsigned ofsᵥ)%Z
                ⌝)%I.
  Proof.
    Local Opaque encode_val.
    iIntros "V".
    iDestruct "V" as "[% [V1 [V2 V3]]]".
    iDestruct "V1" as (ofsᵥ) "[% [PT HO]]". des.
    iExists (Ptrofs.add ofsᵥ (Ptrofs.repr 8)).
    iPoseProof (points_to_split with "PT") as "[PT1 PT2]".
    iPoseProof (points_to_split with "PT2") as "[PT2 PT3]".
    replace (strings.length (encode_val Mptr data))
      with 8
      by (rewrite encode_val_length; reflexivity).
    iPoseProof (offset_slide with "HO") as "HO".

    iSplitL "PT2 HO".
    { iSplit.
      - iFrame.
      - iPureIntro. splits; ss.
        rewrite Ptrofs.add_unsigned.
        change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8%Z.
        pose proof (Ptrofs.eqm_unsigned_repr (Ptrofs.unsigned ofsᵥ + 8)).
        unfold Ptrofs.eqm in H11.
        assert (8 | Ptrofs.modulus)%Z.
        { change Ptrofs.modulus with (8 * 2305843009213693952)%Z.
          eapply Z.divide_factor_l.
        }
        pose proof (Zbits.eqmod_divides _ _ _ _ H11 H12).
        eapply divide_iff_eqmod_0.
        eapply Zbits.eqmod_trans.
        eapply Zbits.eqmod_sym. eapply H13.
        eapply divide_iff_eqmod_0.
        eapply Z.divide_add_r; ss.
        change 8%Z with (8*1)%Z. eapply Z.divide_factor_l.
    }

    iIntros "[PT2 HO]".
    iPoseProof (points_to_collect with "[PT2 PT3]") as "PT2".
    { iSplitL "PT2"; iFrame. }
    iPoseProof (points_to_collect with "[PT1 PT2]") as "PT".
    { iSplitL "PT1".
      - iFrame.
      - replace (strings.length (encode_val Mptr data))
          with 8
          by (rewrite ! encode_val_length; reflexivity).
        iFrame.
    }

    iPoseProof (offset_slide_rev with "HO") as "HO".
    iFrame.
    iSplit; ss. iExists ofsᵥ. iFrame. ss.
  Qed.

  Lemma lens_vector_fixed_capacity
    v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
    :
    Lens
      (is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)
      (fun ofsᵥ => Val.addl v (Vptrofs (Ptrofs.repr 16)) (↦_mᵥ,pᵥ)
                                (encode_val Mint64 (Vlong (Int64.repr capacity)))
                  ∗ Val.addl v (Vptrofs (Ptrofs.repr 16)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)%I
      (fun ofsᵥ => ⌜ strings.length (encode_val Mint64 (Vlong (Int64.repr capacity))) = size_chunk_nat Mint64
                ∧ bytes_not_pure (encode_val Mint64 (Vlong (Int64.repr capacity))) = false
                ∧ Mint64 ≠ Many64
                ∧ (size_chunk Mint64 | Ptrofs.unsigned ofsᵥ)%Z
                ⌝)%I.
  Proof.
    Local Opaque encode_val.
    iIntros "V".
    iDestruct "V" as "[% [V1 [V2 V3]]]".
    iDestruct "V1" as (ofsᵥ) "[% [PT HO]]". des.
    iExists (Ptrofs.add ofsᵥ (Ptrofs.repr 16)).

    replace (encode_val Mptr data ++
             encode_val Mint64 (Vlong (Int64.repr esize)) ++
             encode_val Mint64 (Vlong (Int64.repr capacity)) ++
             encode_val Mint64 (Vlong (Int64.repr length)))
      with ((encode_val Mptr data ++
             encode_val Mint64 (Vlong (Int64.repr esize)))
             ++
             (encode_val Mint64 (Vlong (Int64.repr capacity)) ++
              encode_val Mint64 (Vlong (Int64.repr length))))
      by (rewrite ! app_assoc; reflexivity).

    iPoseProof (points_to_split with "PT") as "[PT1 PT2]".
    iPoseProof (points_to_split with "PT2") as "[PT2 PT3]".

    replace (strings.length (encode_val Mptr data
                              ++ encode_val Mint64 (Vlong (Int64.repr esize))))
      with 16
      by (rewrite ! app_length; rewrite ! encode_val_length; reflexivity).
    iPoseProof (offset_slide with "HO") as "HO".

    iSplitL "PT2 HO".
    { iSplit.
      - iFrame.
      - iPureIntro. splits; ss.
        rewrite Ptrofs.add_unsigned.
        change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16%Z.
        pose proof (Ptrofs.eqm_unsigned_repr (Ptrofs.unsigned ofsᵥ + 16)).
        unfold Ptrofs.eqm in H11.
        assert (8 | Ptrofs.modulus)%Z.
        { change Ptrofs.modulus with (8 * 2305843009213693952)%Z.
          eapply Z.divide_factor_l.
        }
        pose proof (Zbits.eqmod_divides _ _ _ _ H11 H12).
        eapply divide_iff_eqmod_0.
        eapply Zbits.eqmod_trans.
        eapply Zbits.eqmod_sym. eapply H13.
        eapply divide_iff_eqmod_0.
        eapply Z.divide_add_r; ss.
        change 16%Z with (8*2)%Z. eapply Z.divide_factor_l.
    }

    iIntros "[PT2 HO]".
    iPoseProof (points_to_collect with "[PT2 PT3]") as "PT2".
    { iSplitL "PT2"; iFrame. }
    iPoseProof (points_to_collect with "[PT1 PT2]") as "PT".
    { iSplitL "PT1".
      - iFrame.
      - replace (strings.length (encode_val Mptr data
                                  ++ encode_val Mint64 (Vlong (Int64.repr esize))))
          with 16
          by (rewrite ! app_length; rewrite ! encode_val_length; reflexivity).
        iFrame.
    }

    iPoseProof (offset_slide_rev with "HO") as "HO".
    iFrame.
    iSplit; ss. iExists ofsᵥ. iFrame.
    iSplit; ss. rewrite ! app_assoc. iFrame.
  Qed.

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
    iDestruct "V" as "[% [V1 [V2 V3]]]".
    iDestruct "V1" as (ofsᵥ) "[% [PT HO]]". des.
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
        unfold Ptrofs.eqm in H11.
        assert (8 | Ptrofs.modulus)%Z.
        { change Ptrofs.modulus with (8 * 2305843009213693952)%Z.
          eapply Z.divide_factor_l.
        }
        pose proof (Zbits.eqmod_divides _ _ _ _ H11 H12).
        eapply divide_iff_eqmod_0.
        eapply Zbits.eqmod_trans.
        eapply Zbits.eqmod_sym. eapply H13.
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

  Lemma list_points_to_collect esize p m cs
    (SIZE : Forall (fun c => cell_size c = esize) cs)
    (OWNED : Forall (fun c => exists mvs, c = owned mvs 1) cs) :
    bi_entails
      (list_points_to p m cs)
      (∃ mvs, ⌜Datatypes.length mvs = (esize * Datatypes.length cs)%nat⌝ ∗ p (↦_m, 1) mvs).
  Proof.
    revert p.
    induction cs; i; iIntros "LPT".
    - iExists []. iSplit; ss.
    - inv SIZE. inv OWNED. ss. des. clarify.
      iDestruct "LPT" as "[CPT LPT_OFS]".
      hexploit IHcs; ss. i.
      iPoseProof (H3 with "LPT_OFS") as "IH".
      iDestruct "IH" as (mvs') "[% PT]".
      iPoseProof (points_to_collect with "[CPT PT]") as "PT".
      { iSplitL "CPT"; iFrame. }
      iExists (mvs ++ mvs'). iFrame. iPureIntro.
      rewrite app_length. lia.
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
  Admitted.

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

    iApply isim_apc. iExists (Some (2: Ord.t)).
    iPoseProof (lens_vector_handler_data with "V") as (ofsᵥ) "[DATA V_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { eapply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=1%ord). eapply OrdArith.lt_from_nat. lia. }
    iSplitL "INV DATA". { iSplitL "INV"; done. }
    iIntros (st_src0 st_tgt0) "[INV DATA]".
    iPoseProof ("V_RECOVER" with "DATA") as "V".

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
    { instantiate (1:=0%ord). eapply OrdArith.lt_from_nat. lia. }
  Admitted.

  Lemma sim_vector_esize :
    sim_fnsem wf top2
      ("vector_esize", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_esize_spec))
      ("vector_esize", cfunU (decomp_func sk ce f_vector_esize)).
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
    replace (ClightPlusExprgen.field_offset ce _esize (co_members co)) with (Errors.OK 8%Z)
      by (rewrite co_co_members; reflexivity).
    hred_r.
    iApply isim_apc. iExists (Some (1 : Ord.t)).

    iPoseProof (lens_vector_fixed_esize with "V") as (ofsᵥ) "[ESIZE V_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { eapply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=0%ord). eapply OrdArith.lt_from_nat. lia. }
    iSplitL "INV ESIZE". { iSplitL "INV"; done. }
    iIntros (st_src0 st_tgt0) "[INV ESIZE]".
    iDestruct ("V_RECOVER" with "ESIZE") as "V".

    Local Transparent cast_to_ptr.
    hred_r. rewrite decode_encode_item. ss. change Archi.ptr64 with true. ss. hred_r.

    hred_l. iApply isim_choose_src. iExists (Any.upcast (Vlong (Int64.repr esize))).

    iApply isim_ret.
    iSplitL "INV"; et.
  Qed.

  Lemma sim_vector_capacity :
    sim_fnsem wf top2
      ("vector_capacity", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_capacity_spec))
      ("vector_capacity", cfunU (decomp_func sk ce f_vector_capacity)).
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
    replace (ClightPlusExprgen.field_offset ce _capacity (co_members co)) with (Errors.OK 16%Z)
      by (rewrite co_co_members; reflexivity).
    hred_r.
    iApply isim_apc. iExists (Some (1 : Ord.t)).
    iPoseProof (lens_vector_fixed_capacity with "V") as (ofsᵥ) "[CAPACITY V_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { eapply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=0%ord). eapply OrdArith.lt_from_nat. lia. }
    iSplitL "INV CAPACITY". 
    { iSplitL "INV"; done. }
    iIntros (st_src0 st_tgt0) "[INV CAPACITY]".
    iDestruct ("V_RECOVER" with "CAPACITY") as "V".

    Local Transparent cast_to_ptr.
    hred_r. rewrite decode_encode_item. ss. change Archi.ptr64 with true. ss. hred_r.

    hred_l. iApply isim_choose_src. iExists (Any.upcast (Vlong (Int64.repr capacity))).

    iApply isim_ret.
    iSplitL "INV"; et.
  Qed.

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

    iApply isim_apc. iExists (Some (4: Ord.t)).
    iPoseProof (lens_vector_fixed_data with "V") as (ofsᵥ) "[DATA V_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { apply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=3%ord). apply OrdArith.lt_from_nat. lia. }
    iSplitL "INV DATA". { iSplitL "INV"; done. }
    iIntros (st_src0 st_tgt0) "[INV DATA]".
    iDestruct ("V_RECOVER" with "DATA") as "V".

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

    iPoseProof (lens_vector_fixed_esize with "V") as (ofsᵥ') "[ESIZE V_RECOVER]".
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
    iDestruct ("V_RECOVER" with "ESIZE") as "V".

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

    replace (Val.addl data (Vlong (Int64.mul (Int64.repr esize) (Int64.repr index))))
      with (Val.addl data (Vptrofs (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.repr index)))); cycle 1.
    { f_equal. unfold Vptrofs. change Archi.ptr64 with true; ss. f_equal.
      eapply agree64_eq. eapply Ptrofs.agree64_mul.
      - ss.
      - apply Ptrofs.agree64_repr. ss.
      - apply Ptrofs.agree64_repr. ss.
    }

    iApply isim_ccallU_memcpy0.
    { ss. }
    { apply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=0%ord). apply OrdArith.lt_from_nat. lia. }

    iPoseProof (is_vector_fixed_cells_esize with "V") as "%".
    iPoseProof (is_vector_fixed_esize_le_max_unsigned with "V") as "%".
    pose proof (accessor_is_vector_fixed_2 v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data) as ACC2.
    pose proof (accessor_is_vector_fixed_3 cells esize data m_data index (owned mvs_index p_index) H4 H12 H5) as ACC3.
    iPoseProof (ACC2 with "V") as "[[LPT HO] V_RECOVER]".
    iPoseProof (ACC3 with "LPT") as "[CPT LPT_RECOVER]".
    ss.

    iSplitL "MVS OFS INV HO CPT".
    { iFrame.
      iExists mvs_dst.
      iFrame.
      iSplit.
      - iPureIntro. splits.
        + eapply Forall_lookup_1 in H12; et. ss. congruence.
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
    iIntros (st_src3 st_tgt3) "[INV [[[HO OFS] CPT] MVS]]".
    iPoseProof (offset_slide_rev with "HO") as "HO".
    iPoseProof ("LPT_RECOVER" with "CPT") as "LPT".
    iPoseProof ("V_RECOVER" with "[LPT HO]") as "V". { iFrame. }
    hred_r. remove_tau.

    hred_l.
    iApply isim_choose_src. iExists (Any.upcast Vundef).
    iApply isim_ret.
    iFrame. iPureIntro. ss.
  Qed.

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
