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
Require Import vector1.
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Clightdefs.

Section INTEGERS.

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

  Lemma Ptrofs_repr_add_comm x y :
    Ptrofs.repr (x + y) = Ptrofs.add (Ptrofs.repr x) (Ptrofs.repr y).
  Proof.
    unfold Ptrofs.add.
    eapply Ptrofs.eqm_samerepr.
    eapply Ptrofs.eqm_add; eapply Ptrofs.eqm_unsigned_repr.
  Qed.

  Lemma Ptrofs_repr_mul_comm x y :
    Ptrofs.repr (x * y) = Ptrofs.mul (Ptrofs.repr x) (Ptrofs.repr y).
  Proof.
    unfold Ptrofs.mul.
    eapply Ptrofs.eqm_samerepr.
    eapply Ptrofs.eqm_mult; eapply Ptrofs.eqm_unsigned_repr.
  Qed.

  Lemma Ptrofs_to_int64_repr_comm n :
    Ptrofs.to_int64 (Ptrofs.repr n) = Int64.repr n.
  Proof.
    eapply Ptrofs.agree64_to_int_eq.
    eapply Ptrofs.agree64_repr; ss.
  Qed.

  Lemma Ptrofs_to_int64_add_comm m n :
    Ptrofs.to_int64 (Ptrofs.add m n) = Int64.add (Ptrofs.to_int64 m) (Ptrofs.to_int64 n).
  Proof.
    eapply Ptrofs.agree64_to_int_eq.
    eapply Ptrofs.agree64_add; ss; apply Ptrofs.agree64_to_int; ss.
  Qed.

  Lemma Ptrofs_to_int64_mul_comm m n :
    Ptrofs.to_int64 (Ptrofs.mul m n) = Int64.mul (Ptrofs.to_int64 m) (Ptrofs.to_int64 n).
  Proof.
    eapply Ptrofs.agree64_to_int_eq.
    eapply Ptrofs.agree64_mul; ss; apply Ptrofs.agree64_to_int; ss.
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

  Lemma Int64_ltu_true
    x y
    : Int64.ltu x y = true ->
      (Int64.unsigned x < Int64.unsigned y)%Z.
  Proof.
    intro H. eapply Int64.ltu_inv in H. lia.
  Qed.

  Lemma Int64_ltu_false
    x y
    : Int64.ltu x y = false ->
      (Int64.unsigned y <= Int64.unsigned x)%Z.
  Proof.
    intro H.
    apply f_equal with (f := negb) in H.
    rewrite Int64.not_ltu in H. ss.
    eapply orb_true_iff in H. destruct H.
    - eapply Int64.ltu_inv in H. lia.
    - pose proof (Int64.eq_spec y x) as E.
      rewrite H in E. subst. lia.
  Qed.

End INTEGERS.

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

  Lemma decode_encode_ptr p : is_ptr_val p -> decode_val Mptr (encode_val Mptr p) = p.
  Proof.
    intro.
    pose proof (decode_encode_val_general p Mptr Mptr).
    destruct p; ss.
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
    symmetry. eapply Ptrofs_to_int64_add_comm.
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

Section KNOWLEDGES. (* pure of persistent facts *)

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

End KNOWLEDGES.

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
           rewrite ! Ptrofs_repr_add_comm.
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

Section PARAMETERS.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb vectorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).

  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.

  Definition mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default));
                      ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default));
                      ("memcpy", Gfun(Ctypes.External (EF_external "memcpy" (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil) AST.Tlong cc_default))
                                                    (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default));
                      ("realloc", Gfun (Ctypes.External (EF_external "realloc" (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong cc_default))
                                                    (Tcons (tptr tvoid) (Tcons tulong Tnil)) (tptr tvoid) cc_default))].

End PARAMETERS.
