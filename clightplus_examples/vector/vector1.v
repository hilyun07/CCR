Require Import CoqlibCCR.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import Any.
Require Import ModSem.
Require Import ModSemE.
Require Import ClightPlusMem1.
From compcert Require Export Ctypes Values AST Memdata Integers.

Set Implicit Arguments.

Section PROP.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Inductive cell : Type :=
  | owned (mvs : list memval) (q : Qp)
  | lent (size : nat)
  .

  Definition cell_size (c : cell) : nat :=
    match c with
    | owned mvs q => Datatypes.length mvs
    | lent size => size
    end.

  Definition cell_points_to (ptr : val) (m : metadata) (c : cell) : iProp :=
    match c with
    | owned mvs q => ptr (↦_m,q) mvs
    | lent size => True%I
    end.

  Fixpoint list_points_to ptr m (cs : list cell) : iProp :=
    match cs with
    | [] => True%I
    | c :: cs' => cell_points_to ptr m c ** list_points_to (Val.addl ptr (Vptrofs (Ptrofs.repr (cell_size c)))) m cs'
    end.

  Definition is_vector_handler (v : val) (data : val) (esize capacity length: nat) mᵥ tgᵥ pᵥ qᵥ : iProp :=
    ( ∃ ofsᵥ,
      ⌜ (8 | Ptrofs.unsigned ofsᵥ)%Z ⌝
      ∗ v (↦_mᵥ,pᵥ) (encode_val Mptr data
                       ++ encode_val Mint64 (Vlong (Int64.repr esize))
                       ++ encode_val Mint64 (Vlong (Int64.repr capacity))
                       ++ encode_val Mint64 (Vlong (Int64.repr length)))
      ∗ v (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ
    )%I.

  Definition is_vector_fixed (v : val) (data : val) (esize capacity length : nat) (cells : list cell) mᵥ tgᵥ pᵥ qᵥ m_data q_data : iProp :=
    ( ⌜ esize > 0
      /\ capacity > 0
      /\ esize * capacity <= Z.to_nat Ptrofs.max_unsigned
      /\ length <= capacity
      /\ Datatypes.length cells = length
      /\ Forall (fun c => cell_size c = esize) cells
      ⌝
      ∗ is_vector_handler v data esize capacity length mᵥ tgᵥ pᵥ qᵥ
      ∗ list_points_to data m_data cells
      ∗ data (⊨_m_data,Dynamic,q_data) Ptrofs.zero
    )%I.

  Definition is_vector (v : val) (esize capacity length : nat) (cells : list cell) mᵥ tgᵥ qᵥ : iProp :=
    ( ∃ (data : val) (m_data : metadata) (unused_length : nat) (unused : list memval),
      ⌜ esize > 0
      /\ capacity > 0
      /\ esize * capacity <= Z.to_nat Ptrofs.max_unsigned
      /\ (length + unused_length)%nat = capacity
      /\ Datatypes.length cells = length
      /\ Datatypes.length unused = (esize * unused_length)%nat
      /\ Forall (fun c => cell_size c = esize) cells
      /\ Forall (fun c => exists mvs, c = owned mvs 1) cells
      ⌝
      ∗ is_vector_handler v data esize capacity length mᵥ tgᵥ 1 qᵥ
      ∗ list_points_to data m_data cells
      ∗ data (⊨_m_data,Dynamic,1) Ptrofs.zero
      ∗ (Val.addl data (Vptrofs (Ptrofs.repr (esize * length)))) (↦_m_data,1) unused
    )%I.

  Lemma is_vector_fix
    v esize capacity length cells mᵥ tgᵥ qᵥ
    : bi_entails
        (is_vector v esize capacity length cells mᵥ tgᵥ qᵥ)
        (∃ data m_data,
            ⌜ Forall (fun c => exists mvs, c = owned mvs 1) cells ⌝
            ∗ is_vector_fixed v data esize capacity length cells mᵥ tgᵥ 1 qᵥ m_data 1
            ∗ (∀ qᵥ' cells',
                ⌜ Forall (fun c => exists mvs, c = owned mvs 1) cells' ⌝
                -∗ is_vector_fixed v data esize capacity length cells' mᵥ tgᵥ 1 qᵥ' m_data 1
                -∗ is_vector v esize capacity length cells' mᵥ tgᵥ qᵥ' )).
  Proof.
    iIntros "V".
    iDestruct "V" as (data m_data unused_length unused) "[% [V1 [V2 [V3 V4]]]]". des.
    iExists data, m_data. iSplit; ss. iSplitL "V1 V2 V3".
    - iFrame. iPureIntro. splits; ss; lia.
    - iIntros (qᵥ' cells') "% V".
      iDestruct "V" as "[% [V1 [V2 V3]]]". des.
      iExists data, m_data, (capacity - length), unused.
      iFrame. iPureIntro. splits; ss; lia.
  Qed.

End PROP.

Section SPEC.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  (* TODO : Fix specs *)
  Definition vector_init_spec : fspec :=
    @mk_simple
      _
      (val * nat * nat * metadata * tag * Qp * list memval * ptrofs)
      (fun '(v, esize, capacity, mᵥ, tgᵥ, qᵥ, mvsᵥ, ofsᵥ) =>
         ( ord_pure 1%nat
         , fun varg =>
             ⌜ varg = [v; Vlong (Int64.repr esize); Vlong (Int64.repr capacity)]↑
             /\ esize > 0
             /\ capacity > 0
             /\ esize * capacity <= Z.to_nat Ptrofs.max_unsigned
             /\ Datatypes.length mvsᵥ = 24
             ⌝
             ∗ v (↦_mᵥ,1) mvsᵥ
             ∗ v (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ
         , fun vret =>
             ⌜vret = Vundef↑⌝
             ∗ is_vector v esize capacity 0 [] mᵥ tgᵥ qᵥ
         )%I
      ).

  Definition vector_destruct_spec : fspec :=
    @mk_simple
      _
      (val * nat * nat * nat * list cell * metadata * tag * Qp)
      (fun '(v, esize, capacity, length, cells, mᵥ, tgᵥ, qᵥ) =>
         ( ord_pure 1%nat
         , fun varg =>
             ⌜varg = [v]↑⌝
             ∗ is_vector v esize capacity length cells mᵥ tgᵥ qᵥ
         , fun vret =>
             ∃ mvsᵥ ofsᵥ,
             ⌜vret = Vundef↑⌝
             ∗ v (↦_mᵥ,1) mvsᵥ
             ∗ v (⊨_mᵥ,tgᵥ,qᵥ) ofsᵥ
         )%I
      ).

  Definition vector_esize_spec : fspec :=
    @mk_simple
      _
      (val * val * nat * nat * nat * list cell * metadata * tag * Qp * Qp * metadata * Qp)
      (fun '(v, data, esize, capacity, length, cells, mᵥ, tgᵥ, pᵥ, qᵥ, m_data, q_data) =>
         ( ord_pure 1%nat
         , fun varg =>
             ⌜varg = [v]↑⌝
             ∗ is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
         , fun vret =>
             ⌜vret = (Vlong (Int64.repr esize))↑⌝
             ∗ is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
         )%I
      ).

  Definition vector_capacity_spec : fspec :=
    @mk_simple
      _
      (val * val * nat * nat * nat * list cell * metadata * tag * Qp * Qp * metadata * Qp)
      (fun '(v, data, esize, capacity, length, cells, mᵥ, tgᵥ, pᵥ, qᵥ, m_data, q_data) =>
         ( ord_pure 1%nat
         , fun varg =>
             ⌜varg = [v]↑⌝
             ∗ is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
         , fun vret =>
             ⌜vret = (Vlong (Int64.repr capacity))↑⌝
             ∗ is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
         )%I
      ).

  Definition vector_length_spec : fspec :=
    @mk_simple
      _
      (val * val * nat * nat * nat * list cell * metadata * tag * Qp * Qp * metadata * Qp)
      (fun '(v, data, esize, capacity, length, cells, mᵥ, tgᵥ, pᵥ, qᵥ, m_data, q_data) =>
         ( ord_pure 1%nat
         , fun varg =>
             ⌜varg = [v]↑⌝
             ∗ is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
         , fun vret =>
             ⌜vret = (Vlong (Int64.repr length))↑⌝
             ∗ is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
         )%I
      ).

  Definition vector_reserve_spec : fspec :=
    @mk_simple
      _
      (val * nat * nat * nat * list cell * metadata * tag * Qp * nat)
      (fun '(v, esize, capacity, length, cells, mᵥ, tgᵥ, qᵥ, min_capacity) =>
         ( ord_pure 1%nat
         , fun varg =>
             ⌜varg = [v; Vlong (Int64.repr min_capacity)]↑
             /\ min_capacity > 0
             /\ esize * min_capacity < Z.to_nat Ptrofs.max_unsigned
             ⌝
             ∗ is_vector v esize capacity length cells mᵥ tgᵥ qᵥ
         , fun vret =>
             ⌜vret = Vundef↑⌝
             ∗ is_vector v esize (max capacity min_capacity) length cells mᵥ tgᵥ qᵥ
         )%I
      ).

  Definition vector_push_spec : fspec :=
    @mk_simple
      _
      (val * nat * nat * nat * list cell * metadata * tag * Qp *
         val * list memval * ptrofs * metadata * tag * Qp * Qp)
      (fun '(v, esize, capacity, length, cells, mᵥ, tgᵥ, qᵥ,
           src, mvs_src, ofs_src, m_src, tg_src, p_src, q_src) =>
         ( ord_pure 1%nat
         , fun varg =>
             ⌜varg = [v; src]↑
             /\ Datatypes.length mvs_src = esize
             ⌝
             ∗ is_vector v esize capacity length cells mᵥ tgᵥ qᵥ
             ∗ src (↦_m_src,p_src) mvs_src
             ∗ src (⊨_m_src,tg_src,q_src) ofs_src
         , fun vret =>
             ∃ capacity',
             ⌜vret = Vundef↑⌝
             ∗ is_vector v esize capacity' length (cells ++ [owned mvs_src 1]) mᵥ tgᵥ qᵥ
             ∗ src (↦_m_src,p_src) mvs_src
             ∗ src (⊨_m_src,tg_src,q_src) ofs_src
         )%I
      ).

  Definition vector_get_spec : fspec :=
    @mk_simple
      _
      (val * val * nat * nat * nat * list cell * metadata * tag * Qp * Qp * metadata * Qp *
         nat * list memval * Qp * val * list memval * ptrofs * metadata * tag * Qp)
      (fun '(v, data, esize, capacity, length, cells, mᵥ, tgᵥ, pᵥ, qᵥ, m_data, q_data,
           index, mvs_index, p_index, dst, mvs_dst, ofs_dst, m_dst, tg_dst, q_dst) =>
         ( ord_pure 1%nat
         , fun varg =>
             ⌜ varg = [v; Vlong (Int64.repr (index : nat)); dst]↑
             /\ cells !! index = Some (owned mvs_index p_index)
             /\ Datatypes.length mvs_dst = esize
             ⌝
             ∗ is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
             ∗ dst (↦_m_dst,1) mvs_dst
             ∗ dst (⊨_m_dst,tg_dst,q_dst) ofs_dst
         , fun vret =>
             ⌜vret = Vundef↑⌝
             ∗ is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
             ∗ dst (↦_m_dst,1) mvs_index
             ∗ dst (⊨_m_dst,tg_dst,q_dst) ofs_dst
         )%I
      ).

  Definition vector_set_spec : fspec :=
    @mk_simple
      _
      (val * val * nat * nat * nat * list cell * metadata * tag * Qp * Qp * metadata * Qp *
         nat * list memval * val * list memval * ptrofs * metadata * tag * Qp * Qp)
      (fun '(v, data, esize, capacity, length, cells, mᵥ, tgᵥ, pᵥ, qᵥ, m_data, q_data,
           index, mvs_index, src, mvs_src, ofs_src, m_src, tg_src, p_src, q_src) =>
         ( ord_pure 1%nat
         , fun varg =>
             ⌜ varg = [v; Vlong (Int64.repr (index : nat)); src]↑
             /\ cells !! index = Some (owned mvs_index 1)
             /\ Datatypes.length mvs_src = esize
             ⌝
             ∗ is_vector_fixed v data esize capacity length cells mᵥ tgᵥ pᵥ qᵥ m_data q_data
             ∗ src (↦_m_src,p_src) mvs_src
             ∗ src (⊨_m_src,tg_src,q_src) ofs_src
         , fun vret =>
             ⌜vret = Vundef↑⌝
             ∗ is_vector_fixed v data esize capacity length (<[index := owned mvs_src 1]> cells) mᵥ tgᵥ pᵥ qᵥ m_data q_data
             ∗ src (↦_m_src,p_src) mvs_src
             ∗ src (⊨_m_src,tg_src,q_src) ofs_src
         )%I
      ).

  Definition vector_remove_spec : fspec :=
    @mk_simple
      _
      (val * nat * nat * nat * list cell * metadata * tag * Qp * nat * list memval)
      (fun '(v, esize, capacity, length, cells, mᵥ, tgᵥ, qᵥ, index, mvs_index) =>
         ( ord_pure 1%nat
         , fun varg =>
             ⌜varg = [v; (Vlong (Int64.repr (index : nat)))]↑
             /\ cells !! index = Some (owned mvs_index 1)
             ⌝
             ∗ is_vector v esize capacity length cells mᵥ tgᵥ qᵥ
         , fun vret =>
             ⌜vret = Vundef↑⌝
             ∗ is_vector v esize capacity (length - 1) (delete index cells) mᵥ tgᵥ qᵥ
         )%I
      ).

  (* sealed *)
  Definition vectorStb : list (gname * fspec) :=
    Seal.sealing "stb" [
        ("vector_init",    vector_init_spec);
        ("vector_destruct", vector_destruct_spec);
        ("vector_esize",    vector_esize_spec);
        ("vector_capacity", vector_capacity_spec);
        ("vector_length",   vector_length_spec);
        ("vector_reserve",  vector_reserve_spec);
        ("vector_push",     vector_push_spec);
        ("vector_get",      vector_get_spec);
        ("vector_set",      vector_set_spec);
        ("vector_remove",   vector_remove_spec)
      ].

End SPEC.

Section SMOD.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition vectorSbtb: list (gname * fspecbody) :=
    [
      ("vector_init",     mk_pure vector_init_spec);
      ("vector_destruct", mk_pure vector_destruct_spec);
      ("vector_esize",    mk_pure vector_esize_spec);
      ("vector_capacity", mk_pure vector_capacity_spec);
      ("vector_length",   mk_pure vector_length_spec);
      ("vector_reserve",  mk_pure vector_reserve_spec);
      ("vector_push",     mk_pure vector_push_spec);
      ("vector_get",      mk_pure vector_get_spec);
      ("vector_set",      mk_pure vector_set_spec);
      ("vector_remove",   mk_pure vector_remove_spec)
    ].
  
  Definition SvectorSem : SModSem.t := {|
    SModSem.fnsems := vectorSbtb;
    SModSem.mn := "vector";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}.

  Variable vector0: Mod.t.

  Definition Svector : SMod.t := {|
    SMod.get_modsem := fun _ => SvectorSem;
    SMod.sk := vector0.(Mod.sk);
  |}.

  Definition vector stb : Mod.t := (SMod.to_tgt stb) Svector.

End SMOD.
