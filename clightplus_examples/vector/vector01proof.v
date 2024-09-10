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

  Instance eqmod_Reflexive m : Reflexive (Zbits.eqmod m).
  Proof. exact (Zbits.eqmod_refl m). Qed.

  Instance eqmod_Symmetric m : Symmetric (Zbits.eqmod m).
  Proof. exact (Zbits.eqmod_sym m). Qed.

  Instance eqmod_Transitive m : Transitive (Zbits.eqmod m).
  Proof. exact (Zbits.eqmod_trans m). Qed.

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

  Lemma offset_add_align
    align ofs x
    : (align | Ptrofs.modulus)%Z ->
      (align | Ptrofs.unsigned ofs)%Z ->
      (align | Ptrofs.unsigned x)%Z ->
      (align | Ptrofs.unsigned (Ptrofs.add ofs x))%Z.
  Proof.
    intros H0 H1 H2.
    eapply divide_iff_eqmod_0.
    unfold Ptrofs.add.
    transitivity (Ptrofs.unsigned ofs + Ptrofs.unsigned x)%Z.
    - symmetry.
      eapply (Zbits.eqmod_divides Ptrofs.modulus); et.
      eapply Ptrofs.eqm_unsigned_repr.
    - eapply divide_iff_eqmod_0.
      eapply Z.divide_add_r; et.
  Qed.

  Lemma align8_divides_modulus : (8 | Ptrofs.modulus)%Z.
  Proof.
    change Ptrofs.modulus with (8 * 2305843009213693952)%Z.
    eapply Z.divide_factor_l.
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

Section ACCESSORS.

  Import ClightPlusMem1.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  (* Slightly different variation of iris.proofmode.classes.accesor *)
  Definition accessor {X Y : Type} (P : X -> iProp) (Q R : X -> Y -> iProp) :=
    (∃ x : X, P x ∗ (∀ y : Y, Q x y -∗ R x y))%I.

  Lemma accessor_is_vector_is_vector_fixed
    v esize capacity length cells mᵥ tgᵥ qᵥ
      : bi_entails
          (is_vector v esize capacity length cells mᵥ tgᵥ qᵥ)
          (accessor
             (fun '(data, m_data) => ⌜Forall (fun c => exists mvs, c = owned mvs 1) cells⌝
                                ∗ is_vector_fixed v data esize capacity length cells mᵥ tgᵥ 1 qᵥ m_data 1)
             (fun '(data, m_data) '(qᵥ', cells') => ⌜Forall (fun c => exists mvs, c = owned mvs 1) cells'⌝
                                               ∗ is_vector_fixed v data esize capacity length cells' mᵥ tgᵥ 1 qᵥ' m_data 1)
             (fun '(data, m_data) '(qᵥ', cells') => is_vector v esize capacity length cells' mᵥ tgᵥ qᵥ'))%I.
  Proof.
    iIntros "V".
    iDestruct "V" as (data m_data unused_length unused) "[% [V1 [V2 [V3 V4]]]]"; des.
    iExists (data, m_data). iSplitL "V1 V2 V3".
    - iSplit; ss. iFrame. iPureIntro. splits; ss; lia.
    - iIntros ([qᵥ' cells']) "[% V]".
      iDestruct "V" as "[% [V1 [V2 V3]]]"; des.
      iExists data, m_data, (capacity - length), unused.
      iFrame. iPureIntro. splits; ss; lia.
  Qed.

  Lemma accessor_is_vector_fixed_is_vector_handler
    v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
      : bi_entails
          (is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)
          (accessor
             (fun '() => is_vector_handler v data esize capacity length mᵥ tgᵥ pᵥ qᵥ)
             (fun '() '() => is_vector_handler v data esize capacity length mᵥ tgᵥ pᵥ qᵥ)
             (fun '() '() => is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)).
  Proof.
    iIntros "V". iDestruct "V" as "(% & V1 & V2 & V3)".
    iExists tt. iSplitL "V1".
    - iFrame.
    - iIntros ([]) "V1". iFrame. ss.
  Qed.

  (* N.B. : You can not use this for store *)
  Lemma accessor_is_vector_is_vector_handler
    v esize capacity length cells mᵥ tgᵥ qᵥ
      : bi_entails
          (is_vector v esize capacity length cells mᵥ tgᵥ qᵥ)
          (accessor
             (fun data => is_vector_handler v data esize capacity length mᵥ tgᵥ 1 qᵥ)
             (fun data '() => is_vector_handler v data esize capacity length mᵥ tgᵥ 1 qᵥ)
             (fun data '() => is_vector v esize capacity length cells mᵥ tgᵥ qᵥ))%I.
  Proof.
    iIntros "V". iDestruct "V" as (data m_data unused_length unused) "(% & V1 & V2 & V3 & V4)".
    iExists data. iSplitL "V1".
    - iFrame.
    - iIntros ([]) "V1". iExists data, m_data, unused_length, unused. iFrame. ss.
  Qed.

  Lemma accessor_is_vector_handler_data
    v data esize capacity length mᵥ tgᵥ pᵥ qᵥ
    : bi_entails
        (is_vector_handler v data esize capacity length mᵥ tgᵥ pᵥ qᵥ)
        (accessor
           (fun ofsᵥ => ( Val.addl v (Vptrofs (Ptrofs.repr 0)) (↦_mᵥ,pᵥ) (encode_val Mptr data)
                     ∗ Val.addl v (Vptrofs (Ptrofs.repr 0)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)
                   ∗ ⌜ strings.length (encode_val Mptr data) = size_chunk_nat Mptr
                     ∧ bytes_not_pure (encode_val Mptr data) = false
                     ∧ Mptr ≠ Many64
                     ∧ (size_chunk Mptr | Ptrofs.unsigned ofsᵥ)%Z
                     ⌝)
           (fun ofsᵥ (data' : val) => ( Val.addl v (Vptrofs (Ptrofs.repr 0)) (↦_mᵥ,pᵥ) (encode_val Mptr data')
                                   ∗ Val.addl v (Vptrofs (Ptrofs.repr 0)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)
                                 ∗ ⌜is_ptr_val data'⌝)
           (fun ofsᵥ (data' : val) => is_vector_handler v data' esize capacity length mᵥ tgᵥ pᵥ qᵥ))%I.
  Proof.
    iIntros "V". iDestruct "V" as (ofsᵥ) "(% & PT1 & PT2 & PT3 & PT4 & HO)"; des.
    iPoseProof (offset_slide with "HO") as "HO".
    iExists (Ptrofs.add ofsᵥ (Ptrofs.repr 0)).
    replace (strings.length (encode_val Mptr data)) with 8
      by (rewrite encode_val_length; ss).
    iSplitL "PT1 HO".
    - iFrame. iPureIntro. splits; ss.
      + apply encode_ptr_bytes_not_pure; ss.
      + rewrite Ptrofs.add_zero; ss.
    - iIntros (data') "[[PT1 HO] %]".
      iPoseProof (offset_slide_rev with "HO") as "HO".
      iExists ofsᵥ. iFrame. ss.
  Qed.

  Lemma accessor_is_vector_handler_esize
    v data esize capacity length mᵥ tgᵥ pᵥ qᵥ
    : bi_entails
        (is_vector_handler v data esize capacity length mᵥ tgᵥ pᵥ qᵥ)
        (accessor
           (fun ofsᵥ => ( Val.addl v (Vptrofs (Ptrofs.repr 8)) (↦_mᵥ,pᵥ) encode_val Mint64 (Vlong (Int64.repr esize))
                     ∗ Val.addl v (Vptrofs (Ptrofs.repr 8)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)
                   ∗ ⌜ strings.length (encode_val Mint64 (Vlong (Int64.repr esize))) = size_chunk_nat Mint64
                     ∧ bytes_not_pure (encode_val Mint64 (Vlong (Int64.repr esize))) = false
                     ∧ Mint64 ≠ Many64
                     ∧ (size_chunk Mint64 | Ptrofs.unsigned ofsᵥ)%Z
                     ⌝)
           (fun ofsᵥ (esize' : nat) => Val.addl v (Vptrofs (Ptrofs.repr 8)) (↦_mᵥ,pᵥ) encode_val Mint64 (Vlong (Int64.repr esize'))
                                ∗ Val.addl v (Vptrofs (Ptrofs.repr 8)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)
           (fun ofsᵥ (esize' : nat) => is_vector_handler v data esize' capacity length mᵥ tgᵥ pᵥ qᵥ))%I.
  Proof.
    iIntros "V". iDestruct "V" as (ofsᵥ) "(% & PT1 & PT2 & PT3 & PT4 & HO)"; des.
    iPoseProof (offset_slide with "HO") as "HO".
    iExists (Ptrofs.add ofsᵥ (Ptrofs.repr 8)).
    replace (strings.length (encode_val Mint64 (Vlong (Int64.repr esize)))) with 8
      by (rewrite encode_val_length; ss).
    iSplitL "PT2 HO".
    - iFrame. iPureIntro. splits; ss.
      eapply offset_add_align.
      + eapply align8_divides_modulus.
      + et.
      + change (Ptrofs.unsigned (Ptrofs.repr 8)) with (8*1)%Z.
        eapply Z.divide_factor_l.
    - iIntros (esize') "[PT2 HO]".
      iPoseProof (offset_slide_rev with "HO") as "HO".
      iExists ofsᵥ. iFrame. ss.
  Qed.

  Lemma accessor_is_vector_handler_capacity
    v data esize capacity length mᵥ tgᵥ pᵥ qᵥ
    : bi_entails
        (is_vector_handler v data esize capacity length mᵥ tgᵥ pᵥ qᵥ)
        (accessor
           (fun ofsᵥ => ( Val.addl v (Vptrofs (Ptrofs.repr 16)) (↦_mᵥ,pᵥ) encode_val Mint64 (Vlong (Int64.repr capacity))
                     ∗ Val.addl v (Vptrofs (Ptrofs.repr 16)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)
                   ∗ ⌜ strings.length (encode_val Mint64 (Vlong (Int64.repr capacity))) = size_chunk_nat Mint64
                     ∧ bytes_not_pure (encode_val Mint64 (Vlong (Int64.repr capacity))) = false
                     ∧ Mint64 ≠ Many64
                     ∧ (size_chunk Mint64 | Ptrofs.unsigned ofsᵥ)%Z
                     ⌝)
           (fun ofsᵥ (capacity' : nat) => Val.addl v (Vptrofs (Ptrofs.repr 16)) (↦_mᵥ,pᵥ) encode_val Mint64 (Vlong (Int64.repr capacity'))
                                   ∗ Val.addl v (Vptrofs (Ptrofs.repr 16)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)
           (fun ofsᵥ (capacity' : nat) => is_vector_handler v data esize capacity' length mᵥ tgᵥ pᵥ qᵥ))%I.
  Proof.
    iIntros "V". iDestruct "V" as (ofsᵥ) "(% & PT1 & PT2 & PT3 & PT4 & HO)"; des.
    iPoseProof (offset_slide with "HO") as "HO".
    iExists (Ptrofs.add ofsᵥ (Ptrofs.repr 16)).
    replace (strings.length (encode_val Mint64 (Vlong (Int64.repr capacity)))) with 8
      by (rewrite encode_val_length; ss).
    iSplitL "PT3 HO".
    - iFrame. iPureIntro. splits; ss.
      eapply offset_add_align.
      + eapply align8_divides_modulus.
      + et.
      + change (Ptrofs.unsigned (Ptrofs.repr 16)) with (8*2)%Z.
        eapply Z.divide_factor_l.
    - iIntros (esize') "[PT3 HO]".
      iPoseProof (offset_slide_rev with "HO") as "HO".
      iExists ofsᵥ. iFrame. ss.
  Qed.

  Lemma accessor_is_vector_handler_length
    v data esize capacity length mᵥ tgᵥ pᵥ qᵥ
    : bi_entails
        (is_vector_handler v data esize capacity length mᵥ tgᵥ pᵥ qᵥ)
        (accessor
           (fun ofsᵥ => ( Val.addl v (Vptrofs (Ptrofs.repr 24)) (↦_mᵥ,pᵥ) encode_val Mint64 (Vlong (Int64.repr length))
                     ∗ Val.addl v (Vptrofs (Ptrofs.repr 24)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)
                   ∗ ⌜ strings.length (encode_val Mint64 (Vlong (Int64.repr length))) = size_chunk_nat Mint64
                     ∧ bytes_not_pure (encode_val Mint64 (Vlong (Int64.repr length))) = false
                     ∧ Mint64 ≠ Many64
                     ∧ (size_chunk Mint64 | Ptrofs.unsigned ofsᵥ)%Z
                     ⌝)
           (fun ofsᵥ (length' : nat) => Val.addl v (Vptrofs (Ptrofs.repr 24)) (↦_mᵥ,pᵥ) encode_val Mint64 (Vlong (Int64.repr length'))
                                 ∗ Val.addl v (Vptrofs (Ptrofs.repr 24)) (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ)
           (fun ofsᵥ (length' : nat) => is_vector_handler v data esize capacity length' mᵥ tgᵥ pᵥ qᵥ))%I.
  Proof.
    iIntros "V". iDestruct "V" as (ofsᵥ) "(% & PT1 & PT2 & PT3 & PT4 & HO)"; des.
    iPoseProof (offset_slide with "HO") as "HO".
    iExists (Ptrofs.add ofsᵥ (Ptrofs.repr 24)).
    replace (strings.length (encode_val Mint64 (Vlong (Int64.repr length)))) with 8
      by (rewrite encode_val_length; ss).
    iSplitL "PT4 HO".
    - iFrame. iPureIntro. splits; ss.
      eapply offset_add_align.
      + eapply align8_divides_modulus.
      + et.
      + change (Ptrofs.unsigned (Ptrofs.repr 24)) with (8*3)%Z.
        eapply Z.divide_factor_l.
    - iIntros (esize') "[PT4 HO]".
      iPoseProof (offset_slide_rev with "HO") as "HO".
      iExists ofsᵥ. iFrame. ss.
  Qed.

  Lemma accessor_is_vector_fixed_cells
    v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
    : bi_entails
        (is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data)
        (accessor
           (fun '() => list_points_to data m_data cells ∗ data (⊨_m_data,Dynamic,q_data) Ptrofs.zero)
           (fun '() '() => list_points_to data m_data cells ∗ data (⊨_m_data,Dynamic,q_data) Ptrofs.zero)
           (fun '() '() => is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data))%I.
  Proof.
    iIntros "V". iDestruct "V" as "(% & V1 & V2 & V3)"; des.
    iExists (). iSplitL "V2 V3".
    - iFrame.
    - iIntros ([]) "[V2 V3]". iFrame. ss.
  Qed.

  Lemma accessor_cells_cell
    esize p m cells (i : nat) cell
    : is_ptr_val p ->
      Forall (fun c => cell_size c = esize) cells ->
      cells !! i = Some cell ->
      bi_entails
        (list_points_to p m cells)
        (accessor
           (fun '() => cell_points_to (Val.addl p (Vptrofs (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.repr i)))) m cell)
           (fun '() '() => cell_points_to (Val.addl p (Vptrofs (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.repr i)))) m cell)
           (fun '() '() => list_points_to p m cells))%I.
  Proof.
    revert p cells. induction i; i.
    - destruct cells; ss. inv H5. inversion H4. subst l x. rewrite H7.
      iIntros "[CELL CELLS]".
      replace (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.repr 0)) with Ptrofs.zero
        by (rewrite Ptrofs.mul_zero; ss).
      rewrite is_ptr_val_null_r; ss.
      iExists (). iSplitL "CELL".
      + iFrame.
      + iIntros ([]) "CELL". iFrame.
    - destruct cells; ss. inversion H4. subst l x. rewrite H8.
      iIntros "[C CELLS]".
      change (Z.pos (Pos.of_succ_nat i)) with (S i : Z).
      iPoseProof (IHi with "CELLS") as ([]) "[CELL CELLS]"; et. { destruct p; ss. }
      iExists ().
      replace (Val.addl (Val.addl p (Vptrofs (Ptrofs.repr esize))) (Vptrofs (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.repr i))))
        with (Val.addl p (Vptrofs (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.repr (S i))))).
      2: {
        rewrite Nat2Z.inj_succ. rewrite Val.addl_assoc. f_equal.
        rewrite addl_Vptrofs. f_equal.
        replace (Ptrofs.repr esize) with (Ptrofs.mul (Ptrofs.repr esize) Ptrofs.one) at 2
          by eapply Ptrofs.mul_one.
        transitivity (Ptrofs.mul (Ptrofs.repr esize) (Ptrofs.add Ptrofs.one (Ptrofs.repr i))).
        - f_equal. rewrite Ptrofs.add_unsigned.
           unfold Ptrofs.one, Z.succ.
           rewrite ! Ptrofs_repr_Z_add.
           rewrite ! Ptrofs.repr_unsigned.
           apply Ptrofs.add_commut.
        - apply Ptrofs.mul_add_distr_r.
      }
      iSplitL "CELL".
      + iFrame.
      + iIntros ([]) "CELL".
        iPoseProof ("CELLS" $! () with "CELL") as "CELLS".
        iFrame.
  Qed.

End ACCESSORS.

Section PROOF.

  Import ClightPlusMem1.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

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
    iPoseProof (points_to_is_ptr with "V1.1") as "%".
    iPureIntro. destruct v; ss.
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
    iPoseProof (points_to_is_ptr with "V1.1") as "%".
    iPureIntro. destruct v; ss.
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

    iPoseProof (accessor_is_vector_handler_data with "V") as (ofsᵥ') "[DATA V_RECOVER]".
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
    iPoseProof ("V_RECOVER" with "[PT HO]") as "V"; iFrame.
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

    iPoseProof (accessor_is_vector_fixed_is_vector_handler with "V") as ([]) "[VH V_RECOVER]".
    iPoseProof (accessor_is_vector_handler_esize with "VH") as (ofsᵥ) "[ESIZE VH_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { eapply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=0%ord). eapply OrdArith.lt_from_nat. lia. }
    iSplitL "INV ESIZE". { iSplitL "INV"; done. }
    iIntros (st_src0 st_tgt0) "[INV ESIZE]".
    iPoseProof ("VH_RECOVER" with "ESIZE") as "VH".
    iPoseProof ("V_RECOVER" $! () with "VH") as "V".

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
    iPoseProof (accessor_is_vector_fixed_is_vector_handler with "V") as ([]) "[VH V_RECOVER]".
    iPoseProof (accessor_is_vector_handler_capacity with "VH") as (ofsᵥ) "[CAPACITY VH_RECOVER]".
    iApply isim_ccallU_load.
    { ss. }
    { eapply OrdArith.lt_from_nat. lia. }
    { instantiate (1:=0%ord). eapply OrdArith.lt_from_nat. lia. }
    iSplitL "INV CAPACITY". 
    { iSplitL "INV"; done. }
    iIntros (st_src0 st_tgt0) "[INV CAPACITY]".
    iPoseProof ("VH_RECOVER" with "CAPACITY") as "VH".
    iPoseProof ("V_RECOVER" $! () with "VH") as "V".

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
