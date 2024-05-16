Require Import CoqlibCCR.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import PCM IPM.
Require Import HoareDef STB.
Require Import ClightPlusSkel.
Require Import ClightPlusExprgen.
From compcert Require Import Floats Integers Values Memory AST Ctypes Clight Clightdefs.
Require Import List.

Set Implicit Arguments.

Inductive tag :=
| Dynamic
| Local
| Unfreeable.

Record metadata := { blk : option block; sz : Z ; SZPOS: blk <> None -> 0 < sz }.

Let _pointstoRA: URA.t := (block ==> Z ==> (Consent.t memval))%ra.
Let _allocatedRA: URA.t := (block ==> (Consent.t tag))%ra.

Compute (URA.car (t:=_pointstoRA)).
Compute (URA.car (t:=_allocatedRA)).
Instance pointstoRA: URA.t := Auth.t _pointstoRA.
Instance allocatedRA: URA.t := Auth.t _allocatedRA.
Instance blocksizeRA: URA.t := (option block ==> (OneShot.t Z))%ra.
Instance blockaddressRA: URA.t := (option block ==> (OneShot.t ptrofs))%ra.

Local Open Scope Z.
Local Open Scope bi_scope.

Section POINTSTO.

  Definition __points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): _pointstoRA :=
    (fun _b _ofs => if (dec _b b) && (Coqlib.zle ofs _ofs) && (Coqlib.zlt _ofs (ofs + Z.of_nat (List.length mvs)))
                    then 
                      match List.nth_error mvs (Z.to_nat (_ofs - ofs)) with
                      | Some mv => Consent.just q mv
                      | None => ε
                      end
                    else ε)
  .

  Definition _points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): pointstoRA := Auth.white (__points_to b ofs mvs q).

End POINTSTO.

Section ALLOCATEDWITH.

  Definition __allocated_with (b: block) (tg: tag) (q: Qp) : _allocatedRA :=
    (fun _b => if dec _b b
              then Consent.just q tg
              else ε)
  .

  Definition _allocated_with (b: block) (tg: tag) (q: Qp) : allocatedRA := Auth.white (__allocated_with b tg q).

End ALLOCATEDWITH.

Section BLOCKSIZE.

  Definition _has_size (ob: option block) (sz: Z) : blocksizeRA :=
    (fun _ob => match ob, _ob with
             | Some b, Some _b => if dec _b b
                                 then OneShot.white sz
                                 else OneShot.unit
             | None, None => OneShot.white sz (* sz should be zero *)
             | _, _ => OneShot.unit
             end).

End BLOCKSIZE.

Section BLOCKADDR.

  Definition _has_base (ob: option block) (base: ptrofs) : blockaddressRA :=
    (fun _ob => match ob, _ob with
             | Some b, Some _b => if dec _b b
                                 then OneShot.white base
                                 else ε
             | None, None => OneShot.white base
             | _, _ => ε
             end).

End BLOCKADDR.

Section PROP.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition get_align (sz: nat) : Z :=
    if lt_dec sz 2 then 1
    else if le_dec sz 4 then 2
    else if lt_dec sz 8 then 4
    else 8
  .

  Definition _has_offset vaddr m ofs : iProp :=
    OwnM (_has_size m.(blk) m.(sz))
    ** match vaddr with
       | Vptr b ofs' => ⌜Some b = m.(blk) /\ ofs = ofs' /\ m.(sz) ≤ Ptrofs.max_unsigned⌝
       | Vint i =>
          if Archi.ptr64 then ⌜False⌝
          else ∃ a, OwnM (_has_base m.(blk) a) ** ⌜ofs = Ptrofs.sub (Ptrofs.of_int i) a /\ Ptrofs.unsigned a <> 0 /\ Ptrofs.unsigned a + m.(sz) ≤ Ptrofs.max_unsigned⌝
       | Vlong i =>
          if negb Archi.ptr64 then ⌜False⌝
          else ∃ a, OwnM (_has_base m.(blk) a) ** ⌜ofs = Ptrofs.sub (Ptrofs.of_int64 i) a /\ Ptrofs.unsigned a <> 0 /\ Ptrofs.unsigned a + m.(sz) ≤ Ptrofs.max_unsigned⌝
       | _ => ⌜False⌝
       end.

  Definition equiv_prov vaddr vaddr' m : iProp :=
    ∃ ofs, _has_offset vaddr m ofs ** _has_offset vaddr' m ofs.

  Definition points_to vaddr m mvs q : iProp :=
    match m.(blk) with
    | None => ⌜False⌝
    | Some blk =>
        OwnM (_has_size (Some blk) m.(sz))
        ** ∃ ofs, OwnM (_points_to blk (Ptrofs.unsigned ofs) mvs q)
        ** _has_offset vaddr m ofs
        ** ⌜Ptrofs.unsigned ofs + length mvs ≤ m.(sz)⌝
        ** match vaddr with
           | Vptr b ofs'  =>
              ⌜Ptrofs.unsigned ofs + length mvs ≤ Ptrofs.max_unsigned⌝
           | Vint i =>
              ⌜Ptrofs.unsigned ofs + length mvs ≤ Ptrofs.max_unsigned
              /\ Int.unsigned i + length mvs ≤ Ptrofs.max_unsigned⌝
           | Vlong i =>
              ⌜Ptrofs.unsigned ofs + length mvs ≤ Ptrofs.max_unsigned
              /\ Int64.unsigned i + length mvs ≤ Ptrofs.max_unsigned⌝
           | _ => ⌜False⌝
           end
    end%I.

  Definition has_offset vaddr m ofs tg q : iProp :=
    match m.(blk) with
    | None => ⌜False⌝
    | Some blk => OwnM(_allocated_with blk tg q) ** _has_offset vaddr m ofs
    end%I.

  Definition m_null : metadata.
  Proof.
    eapply Build_metadata. instantiate (1:=0). instantiate (1:=None). i. clarify.
  Defined.

  Definition disjoint (m m0: metadata) : Prop :=
    m.(blk) <> m0.(blk).
  
  Definition valid (m: metadata) (ofs: ptrofs) : Prop :=
    Ptrofs.unsigned ofs < m.(sz).

  Definition weak_valid (m: metadata) (ofs: ptrofs) : Prop :=
    Ptrofs.unsigned ofs ≤ m.(sz).

End PROP.

Notation "vaddr ⊨ m # ofs" := (_has_offset vaddr m ofs) (at level 10).
Notation "vaddr '(↦_' m , q ) mvs" := (points_to vaddr m mvs q) (at level 20).
Notation "vaddr '(⊨_' m , tg , q ) ofs" := (has_offset vaddr m ofs tg q) (at level 10).
Notation "m #^ m0" := (disjoint m m0) (at level 20).
Notation "vaddr '(≃_' m ) vaddr'" := (equiv_prov vaddr vaddr' m) (at level 20).

Section AUX.

  Lemma ptrofs_int64_neg i :
    Archi.ptr64 = true -> Ptrofs.neg (Ptrofs.of_int64 i) = Ptrofs.of_int64 (Int64.neg i).
  Proof.
    i. unfold Ptrofs.neg, Ptrofs.of_int64, Int64.neg.
    apply Ptrofs.eqm_samerepr.
    rewrite <- Ptrofs.eqm64; try apply H.
    eapply Int64.eqm_trans.
    2:{ apply Int64.eqm_unsigned_repr. }
    apply Int64.eqm_neg. apply Int64.eqm_sym.
    apply Int64.eqm_unsigned_repr.
  Qed.

  Lemma int64_ptrofs_neg p :
    Archi.ptr64 = true -> Int64.neg (Ptrofs.to_int64 p) = Ptrofs.to_int64 (Ptrofs.neg p).
  Proof.
    i. unfold Ptrofs.neg, Ptrofs.to_int64, Int64.neg.
    apply Int64.eqm_samerepr.
    apply Ptrofs.eqm64; et.
    eapply Ptrofs.eqm_trans.
    2:{ apply Ptrofs.eqm_unsigned_repr. }
    apply Ptrofs.eqm_neg. apply Ptrofs.eqm_sym.
    apply Ptrofs.eqm_unsigned_repr.
  Qed.

  Lemma ptrofs_int64_add i k :
    Archi.ptr64 = true -> Ptrofs.add (Ptrofs.of_int64 i) k = Ptrofs.of_int64 (Int64.add i (Ptrofs.to_int64 k)).
  Proof.
    i. unfold Ptrofs.of_int64, Ptrofs.to_int64, Int64.add, Ptrofs.add.
    rewrite (Int64.unsigned_repr (Ptrofs.unsigned _)).
    2:{ change Int64.max_unsigned with Ptrofs.max_unsigned.
        apply Ptrofs.unsigned_range_2. }
    rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)).
    2:{ change Ptrofs.max_unsigned with Int64.max_unsigned.
        apply Int64.unsigned_range_2. }
    apply Ptrofs.eqm_samerepr.
    rewrite <- Ptrofs.eqm64; et.
    apply Int64.eqm_unsigned_repr.
  Qed.

End AUX.

Section RULES.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Lemma _has_size_dup
      b s
    :
      OwnM (_has_size b s) ⊢ OwnM (_has_size b s) ** OwnM (_has_size b s).
  Proof.
    iIntros "A".
    set (_has_size _ _) at 1.
    replace c with ((_has_size b s) ⋅ (_has_size b s)).
    2:{ unfold c. ur. extensionalities. i. ur. des_ifs. unfold _has_size in Heq. des_ifs. }
    iDestruct "A" as "[? ?]". iFrame.
  Qed.

  Lemma _has_base_dup
      b s
    :
      OwnM (_has_base b s) ⊢ OwnM (_has_base b s) ** OwnM (_has_base b s).
  Proof.
    iIntros "A".
    set (_has_base _ _) at 1.
    replace c with ((_has_base b s) ⋅ (_has_base b s)).
    2:{ unfold c. ur. extensionalities. i. ur. des_ifs. unfold _has_base in Heq. des_ifs. }
    iDestruct "A" as "[? ?]". iFrame.
  Qed.

  Lemma _has_base_unique
      b s0 s1
    :
      OwnM (_has_base b s0 ⋅ _has_base b s1) ⊢ ⌜s0 = s1⌝.
  Proof.
    iIntros "C".
    iOwnWf "C" as wfc. iPureIntro.
    ur in wfc. specialize (wfc b).
    ur in wfc. unfold _has_base in wfc. des_ifs.
  Qed.

  Lemma _has_offset_slide
      vaddr m ofs k
    :
      vaddr ⊨ m # ofs ⊢ Val.addl vaddr (Vptrofs k) ⊨ m # (Ptrofs.add ofs k).
  Proof.
    destruct m. destruct blk0; cycle 1.
    - unfold _has_offset. ss. des_ifs.
      + iIntros "[A B]".
        iDestruct "B" as (a) "[B %]".
        iFrame. iExists a. iFrame.
        iPureIntro.
        des. split; clarify. rewrite <- Ptrofs.sub_add_l. f_equal.
        unfold Val.addl, Vptrofs in *.
        des_ifs. rewrite ptrofs_int64_add; et.
      + iIntros "[A %]". des; clarify.
    - iIntros "A".
      unfold _has_offset.
      des_ifs; try solve [iDestruct "A" as "[A %]"; clarify].
      + iDestruct "A" as "[? A]". iFrame.
        iDestruct "A" as (a) "[? %]". iExists _. iFrame.
        iPureIntro. des. clarify. split; clarify.
        rewrite <- Ptrofs.sub_add_l. f_equal.
        unfold Val.addl, Vptrofs in *.
        des_ifs. rewrite ptrofs_int64_add; et.
      + iDestruct "A" as "[A %]".
        iFrame. iPureIntro. des. clarify.
        ss. des_ifs. unfold Vptrofs in *. des_ifs.
        split; et. rewrite Ptrofs.of_int64_to_int64; et.
  Qed.

  Lemma _has_offset_slide_rev
      vaddr m ofs k
    :
      Val.addl vaddr (Vptrofs k) ⊨ m # (Ptrofs.add ofs k) ⊢ vaddr ⊨ m # ofs.
  Proof.
    destruct m. destruct blk0; cycle 1.
    - unfold _has_offset. ss. des_ifs.
      + iIntros "[A B]".
        iDestruct "B" as (a) "[B %]".
        iFrame. iExists a. iFrame.
        iPureIntro.
        des. split; clarify.
        unfold Val.addl, Vptrofs in *.
        des_ifs. rewrite <- ptrofs_int64_add in H3; et.
        rewrite Ptrofs.sub_add_l in H3.
        apply (f_equal (fun x => Ptrofs.add x (Ptrofs.neg k))) in H3.
        rewrite Ptrofs.add_assoc in H3.
        rewrite Ptrofs.add_assoc in H3.
        rewrite Ptrofs.add_neg_zero in H3.
        rewrite Ptrofs.add_zero in H3.
        rewrite Ptrofs.add_zero in H3.
        et.
      + iIntros "[A %]". des; clarify.
    - iIntros "A".
      unfold _has_offset.
      des_ifs; try solve [iDestruct "A" as "[A %]"; clarify].
      + iDestruct "A" as "[? A]". iFrame.
        iDestruct "A" as (a) "[? %]". iExists _. iFrame.
        iPureIntro. des. clarify. split; clarify.
        unfold Val.addl, Vptrofs in *.
        des_ifs. rewrite <- ptrofs_int64_add in H3; et.
        rewrite Ptrofs.sub_add_l in H3.
        apply (f_equal (fun x => Ptrofs.add x (Ptrofs.neg k))) in H3.
        rewrite Ptrofs.add_assoc in H3.
        rewrite Ptrofs.add_assoc in H3.
        rewrite Ptrofs.add_neg_zero in H3.
        rewrite Ptrofs.add_zero in H3.
        rewrite Ptrofs.add_zero in H3.
        et.
      + iDestruct "A" as "[A %]".
        iFrame. iPureIntro. des. clarify.
        ss. unfold Vptrofs in Heq. dup Heq.
        apply (f_equal (fun v => match v with Vptr _ ofs => ofs | _ => Ptrofs.zero end)) in Heq.
        destruct Archi.ptr64 eqn:?. 2:{ clarify. }
        inversion Heq0. subst. split; et. rewrite Ptrofs.of_int64_to_int64 in Heq; et.
        apply (f_equal (fun x => Ptrofs.add x (Ptrofs.neg k))) in Heq.
        rewrite Ptrofs.add_assoc in Heq.
        rewrite Ptrofs.add_assoc in Heq.
        rewrite Ptrofs.add_neg_zero in Heq.
        rewrite Ptrofs.add_zero in Heq.
        rewrite Ptrofs.add_zero in Heq.
        et.
  Qed.

  Lemma _has_offset_unique
      vaddr m ofs0 ofs1
    :
      vaddr ⊨ m # ofs0 ** vaddr ⊨ m # ofs1 ⊢ ⌜ofs0 = ofs1⌝.
  Proof.
    iIntros "[A B]".
    unfold _has_offset.
    des_ifs; try solve [iDestruct "A" as "[A %]"; clarify]. 
    - iDestruct "A" as "[_ A]".
      iDestruct "B" as "[_ B]".
      iDestruct "A" as (a) "[A1 %]".
      iDestruct "B" as (a0) "[B1 %]".
      des. clarify.
      iCombine "A1 B1" as "C".
      iOwnWf "C" as wfc. iPureIntro.
      ur in wfc. specialize (wfc (blk m)).
      ur in wfc. unfold _has_base in wfc. des_ifs.
    - iDestruct "A" as "[A %]".
      iDestruct "B" as "[B %]".
      des. clarify.
  Qed.

  Lemma _has_offset_dup
      vaddr m ofs
    :
      vaddr ⊨m# ofs ⊢ vaddr ⊨m# ofs ** vaddr ⊨m# ofs.
  Proof.
    iIntros "[A' A]".
    unfold _has_offset.
    iPoseProof (_has_size_dup with "A'") as "[? ?]".
    des_ifs; try solve [iDestruct "A" as "%"; clarify].
    - iDestruct "A" as (a) "[A %]".
      iPoseProof (_has_base_dup with "A") as "[A B]".
      iFrame. iSplitL "A"; iExists _; iFrame; clarify.
    - iDestruct "A" as "%". iFrame. ss.
  Qed.

  Lemma offset_slide
      vaddr m tg q ofs k
    :
       vaddr (⊨_ m, tg, q) ofs ⊢ (Val.addl vaddr (Vptrofs k)) (⊨_ m,tg,q) (Ptrofs.add ofs k).
  Proof.
    iIntros "A".
    destruct m. destruct blk0; ss. unfold has_offset. ss. 
    iDestruct "A" as "[? A]". iFrame. iApply _has_offset_slide. et.
  Qed.

  Lemma offset_slide_rev
      vaddr m tg q ofs k
    :
       (Val.addl vaddr (Vptrofs k)) (⊨_ m,tg,q) (Ptrofs.add ofs k) ⊢ vaddr (⊨_ m, tg, q) ofs.
  Proof.
    iIntros "A".
    destruct m. destruct blk0; ss. unfold has_offset. ss. 
    iDestruct "A" as "[? A]". iFrame. 
    iApply _has_offset_slide_rev. et.
  Qed.

  Lemma offset_unique
      vaddr m tg q0 q1 ofs0 ofs1
    :
      vaddr (⊨_ m, tg, q0) ofs0 ** vaddr (⊨_ m, tg, q1) ofs1 ⊢ ⌜ofs0 = ofs1⌝.
  Proof.
    destruct m. destruct blk0; cycle 1.
    { unfold has_offset. ss. iIntros "%". des; clarify. }
    iIntros "[A B]".
    iDestruct "A" as "[_ A]".
    iDestruct "B" as "[_ B]".
    iCombine "A B" as "C".
    iApply _has_offset_unique; et.
  Qed.

  Lemma offset_trivial
      b m tg q ofs0 ofs1
    :
      Vptr b ofs0 (⊨_ m, tg, q) ofs1 ⊢ ⌜m.(blk) = Some b /\ ofs0 = ofs1⌝.
  Proof.
    destruct m. destruct blk0; cycle 1.
    { unfold has_offset. ss. iIntros "%". des; clarify. }
    iIntros "[A B]".
    iDestruct "B" as "[_ %]". des. et. 
  Qed.

  Lemma _points_to_ownership
      b ofs mvs q0 q1
    :
      _points_to b ofs mvs (q0 + q1) = (_points_to b ofs mvs q0) ⋅ (_points_to b ofs mvs q1).
  Proof.
    unfold _points_to. unfold Auth.white. ur. ur. ur.
    f_equal. ss. extensionalities. i. extensionalities. i. ur.
    unfold __points_to. des_ifs.
  Qed.

  Lemma points_to_ownership
      vaddr mvs m q0 q1
    : 
      ⊢ vaddr (↦_ m, q0 + q1) mvs ∗-∗ (vaddr (↦_ m, q0) mvs ** vaddr (↦_ m, q1) mvs).
  Proof.
    iIntros. iSplit.
    - iIntros "A". unfold points_to.
      destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
      iDestruct "A" as "[B A]".
      iPoseProof (_has_size_dup with "B") as "[? ?]". iFrame.
      des_ifs; iDestruct "A" as (ofs) "[[[B A] %] %]"; des; clarify.
      + unfold _has_offset. des_ifs. iDestruct "A" as "[? %]"; clarify.
      + iPoseProof (_has_offset_dup with "A") as "[C D]".
        rewrite _points_to_ownership.
        iDestruct "B" as "[A B]".
        iSplitL "A C"; iExists _; iFrame; et.
      + iPoseProof (_has_offset_dup with "A") as "[C D]".
        rewrite _points_to_ownership.
        iDestruct "B" as "[A B]".
        iSplitL "A C"; iExists _; iFrame; et.
    - iIntros "A". unfold points_to.
      iDestruct "A" as "[B A]".
      destruct (blk m); try solve [iDestruct "A" as "%"; clarify]. 
      iDestruct "A" as "[? A]". iDestruct "B" as "[? B]". iFrame.
      des_ifs; iDestruct "A" as (ofs0) "[[[A A'] %] %]"; des; clarify.
      + unfold _has_offset. des_ifs. iDestruct "A'" as "[_ %]". clarify.
      + iDestruct "B" as (ofs1) "[[[B B'] %] %]"; des; clarify.
        iCombine "B' A'" as "C".
        iPoseProof (_has_offset_unique with "C") as "%". iDestruct "C" as "[_ C]". clarify.
        iCombine "B A" as "?".
        rewrite <- _points_to_ownership.
        iExists _. iFrame. iPureIntro. nia.
      + iDestruct "B" as (ofs1) "[[[B B'] %] %]"; des; clarify.
        iCombine "B' A'" as "C".
        iPoseProof (_has_offset_unique with "C") as "%". iDestruct "C" as "[_ C]". clarify.
        iCombine "B A" as "?".
        rewrite <- _points_to_ownership.
        iExists _. iFrame. iPureIntro. nia.
  Qed.

  Lemma _allocated_with_ownership
      b tg q0 q1
    :
      _allocated_with b tg (q0 + q1) = (_allocated_with b tg q0) ⋅ (_allocated_with b tg q1).
  Proof.
    unfold _allocated_with. unfold Auth.white. ur. ur. ur.
    f_equal. ss. extensionalities. i.
    unfold __allocated_with. des_ifs.
  Qed.

  Lemma offset_ownership
      vaddr m tg q0 q1 ofs
    :
      ⊢ vaddr (⊨_ m, tg, (q0 + q1)%Qp) ofs  ∗-∗ (vaddr (⊨_ m, tg, q0) ofs ** vaddr (⊨_ m, tg, q1) ofs).
  Proof.
    iIntros. iSplit.
    - iIntros "A". unfold has_offset.
      destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
      rewrite _allocated_with_ownership.
      iDestruct "A" as "[[? ?] A]".
      iPoseProof (_has_offset_dup with "A") as "[? ?]".
      iFrame.
    - iIntros "A". unfold has_offset.
      iDestruct "A" as "[A B]".
      destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
      iDestruct "A" as "[A ?]".
      iDestruct "B" as "[B ?]".
      iCombine "A B" as "?".
      rewrite _allocated_with_ownership. iFrame.
  Qed.

  Lemma _points_to_nil : forall blk ofs q _b _ofs, __points_to blk ofs [] q _b _ofs = ε.
  Proof.
    intros. unfold __points_to. destruct dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss. 
    edestruct nth_error_None. rewrite H4; et. ss. nia.
  Qed.

  Lemma points_to_nil : forall blk ofs q, __points_to blk ofs [] q = ε.
  Proof.
    i. replace (__points_to blk0 ofs [] q) with ((λ (_ : block) (_ : Z), @URA.unit (Consent.t memval))).
    2:{ extensionalities. rewrite _points_to_nil. et. }
    et.
  Qed.     

  Lemma _points_to_content
      b ofs mvs0 mvs1 q
    :
      _points_to b ofs (mvs0 ++ mvs1) q = (_points_to b ofs mvs0 q) ⋅ (_points_to b (ofs + length mvs0) mvs1 q).
  Proof.
    unfold _points_to. unfold Auth.white. ur. ur. ur.
    f_equal. ss. extensionalities. ur. rename H4 into x0.
    unfold __points_to.
    destruct dec; ss;
    destruct Coqlib.zle; ss;
    destruct Coqlib.zlt; ss;
    try destruct Coqlib.zle; ss;
    try destruct Coqlib.zlt; ss;
    try destruct Coqlib.zlt; ss;
    des_ifs; try rewrite app_length in *; try nia;
    try solve [rewrite nth_error_app1 in *; try nia; clarify
              |rewrite nth_error_app2 in *; try nia;
               replace (Z.to_nat _) with ((Z.to_nat (x0 - ofs)) - length mvs0)%nat in * by nia;
               clarify].
  Qed.

  Lemma points_to_split
      vaddr mvs0 mvs1 m q
    : 
      vaddr (↦_m,q) (mvs0 ++ mvs1)
      ⊢ vaddr (↦_m,q) mvs0 ** (Val.addl vaddr (Vptrofs (Ptrofs.repr (length mvs0))) (↦_m,q) mvs1).
  Proof.
    iIntros "A". unfold points_to.
    destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
    iDestruct "A" as "[B A]".
    iPoseProof (_has_size_dup with "B") as "[? ?]". iFrame.
    des_ifs; iDestruct "A" as (ofs) "[[[B A] %] %]"; des; clarify.
    - unfold _has_offset. des_ifs. iDestruct "A" as "[? %]"; clarify.
    - rewrite _points_to_content.
      iPoseProof (_has_offset_dup with "A") as "[? A]".
      iDestruct "B" as "[? B]".
      rewrite <- Heq.
      iSplitR "A B"; iExists _; iFrame.
      + iPureIntro. rewrite app_length in *. nia.
      + rewrite app_length in *.
        assert (X: Ptrofs.unsigned ofs + length mvs0 = Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (length mvs0)))).
        { unfold Ptrofs.add. destruct ofs. ss.
          rewrite (Ptrofs.unsigned_repr (length _)); try nia.
          rewrite (Ptrofs.unsigned_repr); et. nia. }
        rewrite X. iFrame. iSplit; iSplit.
        { iApply _has_offset_slide. et. }
        all: iPureIntro; try nia.
        unfold Val.addl, Vptrofs in *. des_ifs.
        assert (X0: Int64.unsigned i + length mvs0 = Int64.unsigned (Int64.add i (Ptrofs.to_int64 (Ptrofs.repr (length mvs0))))).
        { unfold Int64.add, Ptrofs.to_int64. destruct i. ss.
          rewrite (Ptrofs.unsigned_repr (length _)); try nia.
          change Ptrofs.max_unsigned with Int64.max_unsigned in *.
          rewrite (Int64.unsigned_repr (length _)); try nia.
          rewrite (Int64.unsigned_repr); et. nia. }
        rewrite <- X0. nia.
    - rewrite _points_to_content.
      iPoseProof (_has_offset_dup with "A") as "[? A]".
      iDestruct "B" as "[? B]".
      rewrite <- Heq.
      iSplitR "A B"; iExists _; iFrame.
      + iPureIntro. rewrite app_length in *. nia.
      + rewrite app_length in *.
        assert (X: Ptrofs.unsigned ofs + length mvs0 = Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (length mvs0)))).
        { unfold Ptrofs.add. destruct ofs. ss.
          rewrite (Ptrofs.unsigned_repr (length _)); try nia.
          rewrite (Ptrofs.unsigned_repr); et. nia. }
        rewrite X. iFrame. iSplit; try iSplit.
        { iApply _has_offset_slide. et. }
        all: iPureIntro; try nia.
  Qed.

  Lemma points_to_collect
      vaddr mvs0 mvs1 m q
    : 
      vaddr (↦_m,q) mvs0 ** (Val.addl vaddr (Vptrofs (Ptrofs.repr (Z.of_nat (List.length mvs0)))) (↦_m,q) mvs1)
      ⊢ vaddr (↦_m,q) (mvs0 ++ mvs1).
  Proof.
    iIntros "[A B]". unfold points_to.
    destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
    iDestruct "A" as "[? A]". iDestruct "B" as "[? B]". iFrame.
    des_ifs; iDestruct "A" as (ofs) "[[[C A] %] %]"; des; clarify.
    - unfold _has_offset. des_ifs. iDestruct "A" as "[? %]"; clarify.
    - iDestruct "B" as (ofs0) "[[[D B] %] %]"; des; clarify.
      rewrite <- Heq.
      iPoseProof (_has_offset_dup with "A") as "[? A]".
      iPoseProof (_has_offset_slide with "A") as "A".
      iCombine "A B" as "A".
      iPoseProof (_has_offset_unique with "A") as "%".
      iClear "A". rewrite <- H9.
      assert (X: Ptrofs.unsigned ofs + length mvs0 = Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (length mvs0)))).
      { unfold Ptrofs.add. destruct ofs. ss.
        rewrite (Ptrofs.unsigned_repr (length _)); try nia.
        rewrite (Ptrofs.unsigned_repr); et. nia. }
      iCombine "C D" as "?". rewrite <- X. rewrite <- _points_to_content.
      iExists _. iFrame. iPureIntro. rewrite app_length.
      rewrite <- H9 in *. rewrite <- X in *.
      splits; try nia.
      unfold Val.addl, Vptrofs in *. des_ifs.
      assert (X0: Int64.unsigned i + length mvs0 = Int64.unsigned (Int64.add i (Ptrofs.to_int64 (Ptrofs.repr (length mvs0))))).
      { unfold Int64.add, Ptrofs.to_int64. destruct i. ss.
        rewrite (Ptrofs.unsigned_repr (length _)); try nia.
        change Ptrofs.max_unsigned with Int64.max_unsigned in *.
        rewrite (Int64.unsigned_repr (length _)); try nia.
        rewrite (Int64.unsigned_repr); et. nia. }
      rewrite <- X0 in *. nia.
    - iDestruct "B" as (ofs0) "[[[D B] %] %]"; des; clarify.
      rewrite <- Heq.
      iPoseProof (_has_offset_dup with "A") as "[? A]".
      iPoseProof (_has_offset_slide with "A") as "A".
      iCombine "A B" as "A".
      iPoseProof (_has_offset_unique with "A") as "%".
      iClear "A". rewrite <- H7.
      assert (X: Ptrofs.unsigned ofs + length mvs0 = Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (length mvs0)))).
      { unfold Ptrofs.add. destruct ofs. ss.
        rewrite (Ptrofs.unsigned_repr (length _)); try nia.
        rewrite (Ptrofs.unsigned_repr); et. nia. }
      iCombine "C D" as "?". rewrite <- X. rewrite <- _points_to_content.
      iExists _. iFrame. iPureIntro. rewrite app_length.
      rewrite <- H7 in *. rewrite <- X in *.
      splits; try nia.
  Qed.

  Lemma equiv_refl_point m p q mvs
    : p (↦_m,q) mvs  ⊢  p (↦_m,q) mvs ** p (≃_m) p.
  Proof.
    iIntros "A". unfold points_to.
    destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
    iDestruct "A" as "[? A]".
    des_ifs; iDestruct "A" as (ofs) "[[[C A] %] %]"; des; clarify.
    - unfold _has_offset. des_ifs. iDestruct "A" as "[? %]"; clarify.
    - iFrame. iPoseProof (_has_offset_dup with "A") as "[? A]".
      iPoseProof (_has_offset_dup with "A") as "A".
      iSplitR "A".
      + iExists _. iFrame. iPureIntro. nia.
      + iExists _. et.
    - iFrame. iPoseProof (_has_offset_dup with "A") as "[? A]".
      iPoseProof (_has_offset_dup with "A") as "A".
      iSplitR "A".
      + iExists _. iFrame. iPureIntro. nia.
      + iExists _. et.
  Qed.

  Lemma equiv_refl_offset m p tg q ofs
    : p (⊨_m,tg,q) ofs  ⊢  p (⊨_m,tg,q) ofs ** p (≃_m) p.
  Proof.
    iIntros "A". unfold has_offset.
    destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
    iDestruct "A" as "[? A]".
    iPoseProof (_has_offset_dup with "A") as "[? A]".
    iPoseProof (_has_offset_dup with "A") as "A".
    iSplitR "A"; iFrame. iExists _. et.
  Qed.

  Lemma equiv_trivial_offset m p tg q ofs b
      (BLK: blk m = Some b)
    : 
      p (⊨_m,tg,q) ofs  ⊢ (Vptr b ofs) (⊨_m,tg,q) ofs ** p (≃_m) (Vptr b ofs).
  Proof.
    iIntros "A". unfold has_offset.
    destruct (blk m) eqn:?; try solve [iDestruct "A" as "%"; clarify]. clarify.
    iDestruct "A" as "[? A]". iFrame.
    unfold equiv_prov.
    iPoseProof (_has_offset_dup with "A") as "[A B]".
    iPoseProof (_has_offset_dup with "B") as "[B C]".
    iSplitL "A".
    - unfold _has_offset. iDestruct "A" as "[A B]".
      des_ifs; clarify.
      + iDestruct "B" as (a) "[B %]". des. clarify. iFrame. iPureIntro. splits; et.
        destruct a; ss; nia.
      + iFrame. rewrite Heqo. iDestruct "B" as "%". des. et.
    - iExists _. iFrame.
      unfold _has_offset. iDestruct "B" as "[A B]".
      des_ifs; clarify.
      + iDestruct "B" as (a) "[B %]". des. clarify. iFrame. iPureIntro. splits; et.
        destruct a; ss; nia.
      + iFrame. rewrite Heqo. iDestruct "B" as "%". des. et.
  Qed.

  Lemma equiv_refl_equiv m p q
    : p (≃_m) q ⊢ p (≃_m) p.
  Proof.
    iIntros "A". unfold equiv_prov.
    iDestruct "A" as (ofs) "[A _]".
    iPoseProof (_has_offset_dup with "A") as "[? ?]".
    iExists _. iFrame.
  Qed.

  Lemma equiv_sym p q m
    : p (≃_m) q ⊢ q (≃_m) p.
  Proof.
    iIntros "A". unfold equiv_prov.
    iDestruct "A" as (ofs) "[A B]".
    iExists ofs. iFrame.
  Qed.

  Lemma equiv_trans p q r m
    : p (≃_m) q ** q (≃_m) r 
    ⊢ p (≃_m) r.
  Proof.
    iIntros "A". unfold equiv_prov.
    iDestruct "A" as "[A B]".
    iDestruct "A" as (ofs1) "[A A']". iDestruct "B" as (ofs2) "[B B']".
    iCombine "A' B" as "A'". iPoseProof (_has_offset_unique with "A'") as "%". subst.
    iExists ofs2. iFrame.
  Qed.

  Lemma equiv_dup p q m
    : p (≃_m) q
    ⊢ p (≃_m) q ** p (≃_m) q.
  Proof.
    unfold equiv_prov.
    iIntros "A".
    iDestruct "A" as (ofs) "[A B]".
    iPoseProof (_has_offset_dup with "A") as "[A ?]".
    iPoseProof (_has_offset_dup with "B") as "[B ?]".
    iSplitL "A B"; iExists _; iFrame.
  Qed.

  Lemma equiv_slide
      p q m k
    :
       p (≃_m) q ⊢ (Val.addl p (Vptrofs k)) (≃_m) (Val.addl q (Vptrofs k)).
  Proof.
    iIntros "A". iDestruct "A" as (ofs) "[A A']". 
    iExists _. iSplitL "A"; iApply _has_offset_slide; et.
  Qed.

  Lemma equiv_slide_rev
      p q m k
    :
      (Val.addl p (Vptrofs k)) (≃_m) (Val.addl q (Vptrofs k)) ⊢ p (≃_m) q.
  Proof.
    iIntros "A". iDestruct "A" as (ofs) "[A A']". 
    replace ofs with (Ptrofs.add (Ptrofs.add ofs (Ptrofs.neg k)) k).
    2:{ rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_commut (Ptrofs.neg _)).
        rewrite Ptrofs.add_neg_zero. rewrite Ptrofs.add_zero. et. }
    iExists _. iSplitL "A"; iApply _has_offset_slide_rev; et.
  Qed.

  Lemma capture_unique
      p m i j
    :
      p (≃_m) (Vptrofs i) ** p (≃_m) (Vptrofs j) ⊢ ⌜i = j⌝.
  Proof.
    iIntros "[A B]".
    iDestruct "A" as (ofs0) "[A' A]".
    iDestruct "B" as (ofs1) "[B' B]".
    iCombine "A' B'" as "C".
    iPoseProof (_has_offset_unique with "C") as "%". clarify. iClear "C".
    unfold _has_offset. des_ifs.
    iDestruct "A" as "[_ A]".
    iDestruct "B" as "[_ B]".
    iDestruct "A" as (a0) "[A %]".
    iDestruct "B" as (a1) "[B %]".
    iCombine "A B" as "C".
    iPoseProof (_has_base_unique with "C") as "%". clarify.
    iPureIntro.
    assert (i0 = i1).
    { des. rewrite H4 in H3. clear - H3.
      assert (Ptrofs.eq (Ptrofs.sub (Ptrofs.of_int64 i0) a1) (Ptrofs.sub (Ptrofs.of_int64 i1) a1) = true).
      { rewrite H3. apply Ptrofs.eq_true. }
      do 2 rewrite Ptrofs.sub_add_opp in H.
      rewrite Ptrofs.translate_eq in H.
      apply Ptrofs.same_if_eq in H.
      apply (f_equal Ptrofs.to_int64) in H.
      rewrite Ptrofs.to_int64_of_int64 in H; et.
      rewrite Ptrofs.to_int64_of_int64 in H; et. }
    subst. rewrite <- Heq in Heq1.
    clear -Heq1. unfold Vptrofs in *. destruct Archi.ptr64 eqn:?. 2:{ clarify. }
    apply (f_equal (fun v => match v with Vlong i => i | _ => Int64.zero end)) in Heq1.
    apply (f_equal Ptrofs.of_int64) in Heq1.
    rewrite Ptrofs.of_int64_to_int64 in Heq1; et.
    rewrite Ptrofs.of_int64_to_int64 in Heq1; et.
  Qed.

  Lemma _ii_offset_eq i j ofs m :
    Vptrofs i ⊨ m # ofs ** Vptrofs j ⊨ m # ofs ⊢ ⌜i = j⌝.
  Proof.
    iIntros "[A B]".
    unfold _has_offset. des_ifs.
    iDestruct "A" as "[_ A]".
    iDestruct "B" as "[_ B]".
    iDestruct "A" as (a) "[A %]".
    iDestruct "B" as (a') "[B %]".
    iCombine "A B" as "C". iOwnWf "C" as wfc.
    iPureIntro. ur in wfc. specialize (wfc (blk m)).
    ur in wfc. unfold _has_base in *. 
    des_ifs; unfold Vptrofs in *; des_ifs; rewrite Ptrofs.of_int64_to_int64 in *; et; des; subst.
    all: match goal with
         | H : Ptrofs.sub ?i ?x = Ptrofs.sub ?j ?x |- _ =>
           clear -H;
           rewrite <- (Ptrofs.add_zero_l x) in H;
           apply (f_equal ((flip Ptrofs.add) x)) in H
         end; ss;
         rewrite <-! Ptrofs.sub_add_l in *;
         rewrite ! Ptrofs.sub_shifted in *;
         rewrite ! Ptrofs.sub_zero_l in *; et.
  Qed.

  Lemma equiv_ii_eq i j m :
    Vptrofs i (≃_m) Vptrofs j ⊢ ⌜i = j⌝.
  Proof.
    iIntros "A".
    iDestruct "A" as (ofs) "A".
    iApply _ii_offset_eq. et.
  Qed.
  
  Lemma equiv_point_comm p q f m mvs :
    p (≃_m) q ** p (↦_m,f) mvs ⊢ q (↦_m,f) mvs.
  Proof.
    iIntros "[A B]". unfold equiv_prov. iDestruct "A" as (ofs) "[A A']".
    unfold points_to.
    destruct (blk m); try solve [iDestruct "B" as "[]"].
    iDestruct "B" as "[? B]". iFrame.
    iDestruct "B" as (ofs0) "[[[B B'] %] C]".
    iCombine "A B'" as "D".
    iPoseProof (_has_offset_unique with "D") as "%". subst.
    iPoseProof (_has_offset_dup with "A'") as "[A' A''']".
    iDestruct "D" as "[_ A]".
    iExists _. iFrame. iSplit; ss. 
    destruct p; try solve [iDestruct "C" as "[]"].
    - unfold _has_offset.
      des_ifs; try solve [iDestruct "A" as "[A []]"].
    - destruct q; try solve [iDestruct "A'" as "[? []]"].
      + iCombine "A A'" as "A".
        replace (Vlong i) with (Vptrofs (Ptrofs.of_int64 i)).
        2:{ unfold Vptrofs. des_ifs. rewrite Ptrofs.to_int64_of_int64; et. }
        replace (Vlong i0) with (Vptrofs (Ptrofs.of_int64 i0)).
        2:{ unfold Vptrofs. des_ifs. rewrite Ptrofs.to_int64_of_int64; et. }
        iPoseProof (_ii_offset_eq with "A") as "%". 
        apply (f_equal Ptrofs.to_int64) in H4.
        rewrite Ptrofs.to_int64_of_int64 in H4; et.
        rewrite Ptrofs.to_int64_of_int64 in H4; et.
        subst. et.
      + iDestruct "C" as "%". des. clarify.
    - iDestruct "C" as "%".
      destruct q; try solve [iDestruct "A'" as "[? []]"]; ss.
      unfold _has_offset. des_ifs.
      iDestruct "A'" as "[_ A']".
      iDestruct "A'" as (a) "[_ %]".
      iPureIntro. split; et.
      des. clarify.
      assert (Ptrofs.unsigned (Ptrofs.sub (Ptrofs.of_int64 i0) a) + Ptrofs.unsigned a + strings.length mvs ≤ Ptrofs.max_unsigned)%Z by nia.
      clear -H5.
      assert (Ptrofs.add (Ptrofs.sub (Ptrofs.of_int64 i0) a) a = Ptrofs.of_int64 i0).
      { rewrite Ptrofs.sub_add_opp. rewrite Ptrofs.add_assoc.
        rewrite (Ptrofs.add_commut _ a). rewrite Ptrofs.add_neg_zero.
        rewrite Ptrofs.add_zero. et. }
      unfold Ptrofs.add in H.
      apply (f_equal Ptrofs.unsigned) in H.
      replace (Ptrofs.unsigned (Ptrofs.of_int64 i0)) with (Int64.unsigned i0) in H.
      2:{ clear. unfold Ptrofs.of_int64. rewrite Ptrofs.unsigned_repr; et.
          change Ptrofs.max_unsigned with Int64.max_unsigned.
          apply Int64.unsigned_range_2. }
      rewrite <- H.
      rewrite Ptrofs.unsigned_repr_eq.
      set (Ptrofs.unsigned _ + _) as x in *.
      hexploit (Z.mod_le x Ptrofs.modulus); ss; try nia.
      unfold x. clear.
      destruct (Ptrofs.sub _ _); destruct a; ss.
      nia.
  Qed.

  Lemma equiv_offset_comm p q tg f m ofs :
    p (≃_m) q ** p (⊨_m,tg,f) ofs ⊢ q (⊨_m,tg,f) ofs.
  Proof.
    iIntros "[A B]".
    unfold equiv_prov.
    iDestruct "A" as (ofs0) "[A A']".
    unfold has_offset. des_ifs.
    iDestruct "B" as "[? B]".
    iFrame. iCombine "A B" as "C".
    iPoseProof (_has_offset_unique with "C") as "%".
    clarify.
  Qed.

  Lemma null_equiv p
    : 
      Vnullptr (≃_m_null) p ⊢ ⌜p = Vnullptr⌝.
  Proof.
    iIntros "A". 
    destruct p;
      try solve [iDestruct "A" as (ofs) "[_ A]"; iDestruct "A" as "[? []]"].
    - change Vnullptr with (Vptrofs Ptrofs.zero).
      replace (Vlong i) with (Vptrofs (Ptrofs.of_int64 i)).
      2:{ unfold Vptrofs. des_ifs. f_equal. apply Ptrofs.to_int64_of_int64; et. }
      iPoseProof (equiv_ii_eq with "A") as "%".
      rewrite H3. et.
    - iDestruct "A" as (ofs) "[_ [_ %]]". des. clarify.
  Qed.

  Lemma equiv_notundef p q m
    : 
      p (≃_m) q ⊢ ⌜p <> Vundef⌝.
  Proof.
    iIntros "A". 
    destruct p;
      try solve [iDestruct "A" as (ofs) "[A _]"; iDestruct "A" as "[? []]"].
    all : iPureIntro; ss.
  Qed.

  Lemma point_notnull 
      vaddr m q mvs
    : 
      vaddr (↦_m,q) mvs ⊢ ⌜vaddr <> Vnullptr⌝.
  Proof.
    iIntros "A". unfold points_to. des_ifs.
    iDestruct "A" as "[_ A]".
    iDestruct "A" as (ofs) "[[[_ A] %] [% %]]".
    unfold _has_offset. des_ifs.
    iDestruct "A" as "[_ A]".
    iDestruct "A" as (a) "[A %]".
    iPureIntro. des. clarify.
    assert (X: i <> Int64.zero); try solve [red; intro X'; apply X; inv X'; ss].
    red. i. subst. change (Int64.unsigned Int64.zero) with 0 in *.
    rewrite Z.add_0_l in H5. apply H7. clear H7.
    i. unfold Ptrofs.sub, Ptrofs.of_int64 in *.
    change (Int64.unsigned Int64.zero) with 0 in *.
    change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0 in *.
    rewrite Ptrofs.unsigned_repr_eq in *.
    destruct (Coqlib.zeq 0 (Ptrofs.unsigned a)); et. exfalso.
    rewrite Z_mod_nz_opp_full in H3.
    2: rewrite Z.mod_small; et; apply Ptrofs.unsigned_range.
    rewrite Z_mod_nz_opp_full in H4.
    2: rewrite Z.mod_small; et; apply Ptrofs.unsigned_range.
    rewrite Z.mod_small in *.
    all: try apply Ptrofs.unsigned_range.
    change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *.
    nia.
  Qed.

  Lemma point_notundef p q m mvs
    : 
      p (↦_m, q) mvs ⊢ ⌜p <> Vundef⌝.
  Proof.
    iIntros "A". unfold points_to.
    des_ifs; try solve [iDestruct "A" as "[_ A]"; iDestruct "A" as (ofs) "[? []]"].
  Qed.

  Lemma offset_notundef
      p m tg q ofs
    : 
      p (⊨_m,tg,q) ofs ⊢ ⌜p <> Vundef⌝.
  Proof.
    iIntros "A". unfold has_offset, _has_offset.
    des_ifs. iDestruct "A" as "[_ [_ []]]".
  Qed.

  Lemma _offset_ptr {eff} {K:eventE -< eff} v m ofs
    : 
      v ⊨m# ofs ⊢ ⌜@cast_to_ptr eff K v = Ret v⌝.
  Proof.
    iIntros "A". unfold has_offset.
    destruct v; ss; des_ifs_safe;
    iDestruct "A" as "[A %]"; clarify.
  Qed.

  Lemma offset_cast_ptr {eff} {K:eventE -< eff} v m tg q ofs
    : 
      v (⊨_m,tg,q) ofs ⊢ ⌜@cast_to_ptr eff K v = Ret v⌝.
  Proof.
    iIntros "A". unfold has_offset. des_ifs.
    unfold _has_offset.
    des_ifs; iDestruct "A" as "[_ [_ %]]"; clarify.
  Qed.

  Lemma point_cast_ptr {eff} {K:eventE -< eff} v m q mvs
    : 
      v (↦_m,q) mvs ⊢ ⌜@cast_to_ptr eff K v = Ret v⌝.
  Proof.
    iIntros "A". unfold points_to.
    destruct (blk m); clarify.
    iDestruct "A" as "[_ A]".
    iDestruct "A" as (ofs) "[[[_ ?] _] _]".
    iApply _offset_ptr. et.
  Qed.

  Lemma ptrofs_cast_ptr {eff} {K:eventE -< eff} i
    : 
      @cast_to_ptr eff K (Vptrofs i) = Ret (Vptrofs i).
  Proof. unfold cast_to_ptr. des_ifs. Qed.

  Lemma points_to_is_ptr v m q mvs
    : 
      v (↦_m,q) mvs ⊢ ⌜is_ptr_val v = true⌝.
  Proof.
    iIntros "A". unfold points_to, _has_offset.
    destruct v; ss; des_ifs_safe;
    iDestruct "A" as "[A B]"; clarify;
    iDestruct "B" as (ofs) "[[[B C] %] %]"; clarify.
    iDestruct "C" as "[_ %]". clarify.
  Qed.

  Lemma decode_encode_ptr_ofs v m tg q ofs 
    : 
      v (⊨_m,tg,q) ofs ⊢ ⌜decode_val Mptr (encode_val Mptr v) = v⌝.
  Proof.
    unfold Mptr. des_ifs.
    pose proof (decode_encode_val_general v Mint64 Mint64).
    unfold decode_encode_val in H3.
    iIntros "A". unfold has_offset, _has_offset.
    destruct v; try solve [iDestruct "A" as "[A [A' %]]"; clarify];
      des_ifs; rewrite H3; et.
    all: iDestruct "A" as "[_ [_ %]]"; clarify.
  Qed.

  Lemma decode_encode_ptr_equiv p m q
    : 
      p (≃_m) q ⊢ ⌜decode_val Mptr (encode_val Mptr p) = p⌝.
  Proof.
    unfold Mptr. des_ifs.
    pose proof (decode_encode_val_general p Mint64 Mint64).
    unfold decode_encode_val in H3.
    iIntros "A". iDestruct "A" as (ofs) "[A _]".
    destruct p; try solve [iDestruct "A" as "[? []]"].
    - rewrite H3. et.
    - des_ifs.
  Qed.

  Lemma add_null_r v m tg q ofs: 
      v (⊨_m,tg,q) ofs ⊢ ⌜Val.addl v (Vptrofs Ptrofs.zero) = v⌝.
  Proof.
    iIntros "A". unfold has_offset, _has_offset.
    des_ifs; try solve [iDestruct "A" as "[A [A' %]]"; clarify].
    - iPureIntro. ss. unfold Vptrofs. des_ifs.
      change (Ptrofs.to_int64 _) with Int64.zero. 
      rewrite Int64.add_zero. et.
    - iPureIntro. ss. unfold Vptrofs. des_ifs.
      rewrite Ptrofs.of_int64_to_int64; et.
      rewrite Ptrofs.add_zero. et.
  Qed.

End RULES.

Section SPEC.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  (* input: Z, output: block *)
  Definition salloc_spec: fspec :=
    (mk_simple (fun n => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = n↑ /\ 0 < n ≤ Ptrofs.max_unsigned⌝),
                    (fun vret => ∃ m vaddr b,
                                 ⌜vret = b↑ /\ m.(blk) = Some b /\ m.(sz) = n ⌝
                                 ** vaddr (↦_m,1) List.repeat Undef (Z.to_nat n)
                                 ** vaddr (⊨_m,Local, 1) Ptrofs.zero)
    )))%I.

  (* input: option block * Z, output: unit *)
  Definition sfree_spec: fspec :=
    (mk_simple (fun '() => (
                  (ord_pure 0%nat),
                  (fun varg => ∃ m mvs vaddr,
                                ⌜varg = (m.(blk), m.(sz))↑
                                /\ Z.of_nat (List.length mvs) = m.(sz)⌝
                                ** vaddr (↦_m,1) mvs
                                ** vaddr (⊨_m,Local,1) Ptrofs.zero),
                  (fun vret => ⌜vret = tt↑⌝)
    )))%I.

  (* input: chunk * val, output: val *)
  Definition load_spec: fspec :=
    (mk_simple (fun '(chunk, vaddr, m, tg, q0, ofs, q1, mvs) => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (chunk, vaddr)↑
                                 /\ List.length mvs = size_chunk_nat chunk
                                 /\ bytes_not_pure mvs = false
                                 /\ chunk <> Many64
                                 /\ ((size_chunk chunk) | Ptrofs.unsigned ofs)⌝
                                 ** vaddr (⊨_m,tg,q0) ofs
                                 ** vaddr (↦_m,q1) mvs),
                    (fun vret => ∃ v, ⌜vret = v↑ /\ decode_val chunk mvs = v⌝
                                 ** vaddr (⊨_m,tg,q0) ofs
                                 ** vaddr (↦_m,q1) mvs)
    )))%I.

  (* deprecated, maybe revive in bitfield at v3.11? *)
  (* Definition loadbytes_spec: fspec :=
    (mk_simple (fun '(vaddr, sz, q, mvs) => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (vaddr, sz)↑ /\ Z.of_nat (List.length mvs) = sz⌝ 
                                ** vaddr ⊢q#> mvs),
                    (fun vret => ⌜vret = mvs↑⌝ ** vaddr ⊢q#> mvs)
    ))). *)

  (* input: chunk * val * val, output: unit *)
  Definition store_spec: fspec :=
    (mk_simple
      (fun '(chunk, vaddr, m, ofs, tg, q, v_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ mvs_old, ⌜varg = (chunk, vaddr, v_new)↑
                         /\ List.length mvs_old = size_chunk_nat chunk
                         /\ ((size_chunk chunk) | Ptrofs.unsigned ofs)⌝
                         ** vaddr (⊨_m,tg,q) ofs
                         ** vaddr (↦_m,1) mvs_old),
            (fun vret => ∃ mvs_new, ⌜vret = tt↑
                         /\ encode_val chunk v_new = mvs_new⌝
                         ** vaddr (⊨_m,tg,q) ofs
                         ** vaddr (↦_m,1) mvs_new)
    )))%I.

  (* deprecated, maybe revive in bitfield at v3.11? *)
  (* Definition storebytes_spec: fspec :=
    (mk_simple
      (fun '(vaddr, mvs_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ mvs_old, ⌜varg = (vaddr, mvs_new)↑
                                    /\ List.length mvs_old = List.length mvs_new⌝
                                    ** vaddr ⊢1#> mvs_old),
            (fun vret => ⌜vret = tt↑⌝ ** vaddr ⊢1#> mvs_new)
    )))%I. *)

  (* group of cmp_ptr rules *)
  (* input: comparison * val * val, output: bool *)

  Definition cmp_ofs (c: comparison) (ofs0 ofs1: Z) :=
    match c with
    | Ceq => ofs0 =? ofs1
    | Cne => negb (ofs0 =? ofs1)
    | Clt => ofs0 <? ofs1
    | Cle => ofs0 <=? ofs1
    | Cgt => ofs0 >? ofs1
    | Cge => ofs0 >=? ofs1
    end.

  Definition cmp_ptr_hoare0 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(c) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (c, Vnullptr, Vnullptr)↑⌝),
            (fun vret => ⌜vret = match c with
                                 | Ceq | Cle | Cge => true↑
                                 | _ => false↑
                                 end⌝)
          )%I.

  Definition cmp_ptr_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Ceq, Vnullptr, vaddr)↑ /\ weak_valid m ofs⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ⌜vret = false↑⌝ 
                         ** vaddr (⊨_m,tg,q) ofs)
          )%I.

  Definition cmp_ptr_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Cne, Vnullptr, vaddr)↑ /\ weak_valid m ofs⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ⌜vret = true↑⌝ 
                         ** vaddr (⊨_m,tg,q) ofs)
          )%I.

  Definition cmp_ptr_hoare3 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Ceq, vaddr, Vnullptr)↑ /\ weak_valid m ofs⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ⌜vret = false↑⌝ 
                         ** vaddr (⊨_m,tg,q) ofs)
          )%I.

  Definition cmp_ptr_hoare4 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Cne, vaddr, Vnullptr)↑ /\ weak_valid m ofs⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ⌜vret = true↑⌝ 
                         ** vaddr (⊨_m,tg,q) ofs)
          )%I.

  Definition cmp_ptr_hoare5 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(c, vaddr0, vaddr1, m, ofs0, ofs1, q0, q1, tg) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (c, vaddr0, vaddr1)↑ /\ weak_valid m ofs0 /\ weak_valid m ofs1⌝
                         ** vaddr0 (⊨_m,tg,q0) ofs0
                         ** vaddr1 (⊨_m,tg,q1) ofs1),
            (fun vret => ⌜vret = (cmp_ofs c (Ptrofs.unsigned ofs0) (Ptrofs.unsigned ofs1))↑⌝
                         ** vaddr0 (⊨_m,tg,q0) ofs0
                         ** vaddr1 (⊨_m,tg,q1) ofs1)
          )%I.

  Definition cmp_ptr_hoare6 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr0, vaddr1, m0, m1, ofs0, ofs1, q0, q1, tg0, tg1) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Ceq, vaddr0, vaddr1)↑ /\ m0 #^ m1
                         /\ valid m0 ofs0 /\ valid m1 ofs1⌝
                         ** vaddr0 (⊨_m0,tg0,q0) ofs0
                         ** vaddr1 (⊨_m1,tg1,q1) ofs1),
            (fun vret => ⌜vret = false↑⌝ 
                         ** vaddr0 (⊨_m0,tg0,q0) ofs0
                         ** vaddr1 (⊨_m1,tg1,q1) ofs1)
          )%I.

  Definition cmp_ptr_hoare7 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr0, vaddr1, m0, m1, ofs0, ofs1, q0, q1, tg0, tg1) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Cne, vaddr0, vaddr1)↑ /\ m0 #^ m1
                         /\ valid m0 ofs0 /\ valid m1 ofs1⌝
                         ** vaddr0 (⊨_m0,tg0,q0) ofs0
                         ** vaddr1 (⊨_m1,tg1,q1) ofs1),
            (fun vret => ⌜vret = true↑⌝ 
                         ** vaddr0 (⊨_m0,tg0,q0) ofs0
                         ** vaddr1 (⊨_m1,tg1,q1) ofs1)
          )%I.

  Definition cmp_ptr_spec: fspec :=
    mk_simple (
      cmp_ptr_hoare0
      @ cmp_ptr_hoare1
      @ cmp_ptr_hoare2
      @ cmp_ptr_hoare3
      @ cmp_ptr_hoare4
      @ cmp_ptr_hoare5
      @ cmp_ptr_hoare6
      @ cmp_ptr_hoare7
    ).

  (* input: Z * val * val, output: val *)
  Definition sub_ptr_spec : fspec :=
    (mk_simple
      (fun '(size, vaddr0, vaddr1, m, ofs0, ofs1, q0, q1, tg) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (size, vaddr0, vaddr1)↑ /\ 0 < size ≤ Ptrofs.max_signed
                         /\ Ptrofs.min_signed ≤ Ptrofs.unsigned ofs0 - Ptrofs.unsigned ofs1 ≤ Ptrofs.max_signed
                         /\ weak_valid m ofs0 /\ weak_valid m ofs1⌝
                         ** vaddr0 (⊨_m,tg,q0) ofs0
                         ** vaddr1 (⊨_m,tg,q1) ofs1),
            (fun vret => ⌜vret = (Vptrofs (Ptrofs.repr (Z.quot (Ptrofs.unsigned ofs0 - Ptrofs.unsigned ofs1) size)))↑⌝
                         ** vaddr0 (⊨_m,tg,q0) ofs0
                         ** vaddr1 (⊨_m,tg,q1) ofs1)
    )))%I.

  (* input: val, output: bool *)
  Definition non_null_spec: fspec :=
    (mk_simple
      (fun '(vaddr, m, q, tg, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = vaddr↑ /\ weak_valid m ofs⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ⌜vret = true↑⌝
                         ** vaddr (⊨_m,tg,q) ofs)
    )))%I.

  (* builtin-like functions of clight *)
  (* input: list val, output: val *)

  (* heap malloc free *)
  Definition malloc_spec: fspec :=
    (mk_simple (fun n => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = [Vptrofs n]↑ /\ Ptrofs.unsigned n > 0⌝),
                    (fun vret => ∃ m vaddr, ⌜vret = vaddr↑ /\ m.(sz) = Ptrofs.unsigned n⌝
                                 ** vaddr (↦_m,1) List.repeat Undef (Z.to_nat (Ptrofs.unsigned n))
                                 ** vaddr (⊨_m,Dynamic,1) Ptrofs.zero)
    )))%I.

  Definition mfree_spec: fspec :=
    (mk_simple (fun '() => (
                    (ord_pure 0%nat),
                    (fun varg => ∃ m mvs vaddr,
                                 ⌜varg = [vaddr]↑ /\ Z.of_nat (List.length mvs) = m.(sz)⌝
                                 ** vaddr (↦_m,1) mvs
                                 ** vaddr (⊨_m,Dynamic,1) Ptrofs.zero),
                    (fun vret => ⌜vret = Vundef↑⌝)
    )))%I.

  (* memcpy *)
  Definition memcpy_hoare0 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, vaddr', tg, tg', qp, q, q', ofs_src, ofs_dst, m_src, m_dst, mvs_src) => (
            (ord_pure 0%nat),
            (fun varg => ∃ al sz mvs_dst,
                         ⌜varg = (al, sz, [vaddr; vaddr'])↑
                         /\ List.length mvs_src = List.length mvs_dst
                         /\ List.length mvs_dst = Z.to_nat sz
                         /\ (al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
                         /\ (al | Ptrofs.unsigned ofs_src)
                         /\ (al | Ptrofs.unsigned ofs_dst)
                         /\ 0 ≤ sz /\ (al | sz)⌝
                         ** vaddr' (⊨_m_src,tg',q') ofs_src
                         ** vaddr (⊨_m_dst,tg,q) ofs_dst
                         ** vaddr' (↦_m_src,qp) mvs_src
                         ** vaddr (↦_m_dst,1) mvs_dst),
            (fun vret => ⌜vret = Vundef↑⌝
                         ** vaddr' (⊨_m_src,tg',q') ofs_src
                         ** vaddr (⊨_m_dst,tg,q) ofs_dst
                         ** vaddr' (↦_m_src,qp) mvs_src
                         ** vaddr (↦_m_dst,1) mvs_src)
          )%I.

  Definition memcpy_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m_dst, tg, q, ofs_dst, mvs_dst) => (
            (ord_pure 0%nat),
            (fun varg => ∃ al sz,
                         ⌜varg = (al, sz, [vaddr; vaddr])↑
                         /\ List.length mvs_dst = Z.to_nat sz
                         /\ (al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
                         /\ (al | Ptrofs.unsigned ofs_dst)
                         /\ 0 ≤ sz /\ (al | sz)⌝
                         ** vaddr (⊨_m_dst,tg,q) ofs_dst
                         ** vaddr (↦_m_dst,1) mvs_dst),
            (fun vret => ⌜vret = Vundef↑⌝
                         ** vaddr (⊨_m_dst,tg,q) ofs_dst
                         ** vaddr (↦_m_dst,1) mvs_dst)
          )%I.

  Definition memcpy_spec: fspec :=
    mk_simple (memcpy_hoare0 @ memcpy_hoare1).

  (* capture *)
  Definition capture_hoare0 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '() => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = [Vnullptr]↑⌝),
            (fun vret => ⌜vret = (Vnullptr)↑⌝ )
          )%I.

  Definition capture_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, q, ofs, tg) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = [vaddr]↑⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ∃ i, ⌜vret = (Vptrofs i)↑⌝
                         ** vaddr (⊨_m,tg,q) ofs
                         ** vaddr (≃_m) (Vptrofs i))
          )%I.

  Definition capture_spec: fspec :=
    mk_simple (capture_hoare0 @ capture_hoare1).

  (* sealed *)
  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("salloc", salloc_spec); ("sfree", sfree_spec); 
           ("load", load_spec);
           (* ("loadbytes", loadbytes_spec);  *)
           ("store", store_spec);
           (* ("storebytes", storebytes_spec); *)
           ("sub_ptr", sub_ptr_spec); ("cmp_ptr", cmp_ptr_spec);
           ("non_null?", non_null_spec);
           ("malloc", malloc_spec); ("free", mfree_spec);
           ("memcpy", memcpy_spec);
           ("capture", capture_spec)
           ].
    Defined.

End SPEC.

Section MRS.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Variable sk: Sk.t.
  Let skenv: SkEnv.t := load_skenv sk.

  Definition store_init_data (res : _pointstoRA) (b : block) (p : Z) (optq : option Qp) (id : init_data) : option _pointstoRA :=
    match id with
    | Init_int8 n => 
      if Zdivide_dec (align_chunk Mint8unsigned) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint8unsigned (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int16 n =>
      if Zdivide_dec (align_chunk Mint16unsigned) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint16unsigned (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int32 n =>
      if Zdivide_dec (align_chunk Mint32) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint32 (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int64 n =>
      if Zdivide_dec (align_chunk Mint64) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint64 (Vlong n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_float32 n =>
      if Zdivide_dec (align_chunk Mfloat32) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mfloat32 (Vsingle n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_float64 n =>
      if Zdivide_dec (align_chunk Mfloat64) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mfloat64 (Vfloat n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_space z => 
      match optq with
      | Some q => Some (__points_to b p (repeat (Byte Byte.zero) (Z.to_nat z)) q ⋅ res)
      | None => Some res
      end
    | Init_addrof symb ofs =>
      match SkEnv.id2blk skenv (string_of_ident symb) with
      | Some b' =>
        if Zdivide_dec (align_chunk Mptr) p
        then
          match optq with
          | Some q => Some (__points_to b p (encode_val Mptr (Vptr (Pos.of_succ_nat b') ofs)) q ⋅ res)
          | None => Some res
          end
        else None
      | None => None
      end
    end.

  Fixpoint store_init_data_list (res : _pointstoRA) (b : block) (p : Z) (optq: option Qp) (idl : list init_data) {struct idl} : option _pointstoRA :=
    match idl with
    | [] => Some res
    | id :: idl' =>
        match store_init_data res b p optq id with
        | Some res' => store_init_data_list res' b (p + init_data_size id)%Z optq idl'
        | None => None
        end
    end.

  Definition alloc_global (res : _pointstoRA * _allocatedRA * blocksizeRA) (b: block) (gd : globdef fundef type) : option (_pointstoRA * _allocatedRA * blocksizeRA) :=
    let '(p, a, s) := res in
    match gd with
    | Gfun _ => Some (p, a ⋅ (__allocated_with b Unfreeable (1/2)%Qp), s ⋅ (_has_size (Some b) 1)) 
    | Gvar v =>
      let optq := match Globalenvs.Genv.perm_globvar v with
                  | Freeable | Writable => Some 1%Qp
                  | Readable => Some (1/2)%Qp
                  | Nonempty => None
                  end
      in
      match store_init_data_list ε b 0 optq (gvar_init v) with
      | Some res' => Some (p ⋅ res', a ⋅ (__allocated_with b  Unfreeable (1/2)%Qp), s ⋅ (_has_size (Some b) (init_data_list_size (gvar_init v))))
      | None => None
      end
    end.

  Fixpoint alloc_globals (res: _pointstoRA * _allocatedRA * blocksizeRA) (b: block) (sk: Sk.t) : option (_pointstoRA * _allocatedRA * blocksizeRA) :=
    match sk with
    | nil => Some res
    | g :: gl' => 
      let (_, gd) := g in
      match alloc_global res b gd with
      | Some res' => alloc_globals res' (Pos.succ b) gl'
      | None => None
      end
    end.

  Definition res_init : Σ :=
    match alloc_globals (ε, ε, ε) xH sk with
    | Some (p, a, s) => GRA.embed (Auth.black p) ⋅ GRA.embed (Auth.black a) ⋅ GRA.embed s
    | None => GRA.embed (Auth.black ε : pointstoRA) ⋅ GRA.embed (Auth.black ε : allocatedRA)
    end.

End MRS.

Section SMOD.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("salloc", mk_pure salloc_spec);
    ("sfree",   mk_pure sfree_spec);
    ("load",   mk_pure load_spec);
    (* ("loadbytes",   mk_pure loadbytes_spec); *)
    ("store",  mk_pure store_spec);
    (* ("storebytes",   mk_pure storebytes_spec); *)
    ("sub_ptr", mk_pure sub_ptr_spec);
    ("cmp_ptr", mk_pure cmp_ptr_spec);
    ("non_null?",   mk_pure non_null_spec);
    ("malloc",   mk_pure malloc_spec);
    ("free",   mk_pure mfree_spec);
    ("memcpy", mk_pure memcpy_spec);
    ("capture", mk_pure capture_spec)
    ]
  .

  Definition SMemSem sk : SModSem.t := 
    {|
      SModSem.fnsems := MemSbtb;
      SModSem.mn := "Mem";
      SModSem.initial_mr := (res_init sk)
                            ⋅ GRA.embed ((fun ob => match ob with
                                                   | Some _ => OneShot.black
                                                   | None => OneShot.white Ptrofs.zero
                                                   end) : blockaddressRA)
                            ⋅ GRA.embed ((fun ob => match  ob with
                                                   | Some b => if Coqlib.plt b (Pos.of_succ_nat (List.length sk)) then OneShot.unit else OneShot.black
                                                   | None => OneShot.white 0
                                                   end) : blocksizeRA);
      SModSem.initial_st := tt↑;
    |} .

  Definition SMem sk: SMod.t := {|
    SMod.get_modsem := SMemSem;
    SMod.sk := sk;
  |}
  .

  Definition Mem sk: Mod.t := (SMod.to_tgt (fun _ => to_stb [])) (SMem sk).

End SMOD.

Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
Global Opaque _allocated_with.
Global Opaque _has_size.
Global Opaque _has_base.
Global Opaque equiv_prov.
