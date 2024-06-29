Require Import AList.
Require Import CoqlibCCR PCM IPM.
From compcert Require Import Floats Integers Values Memory AST Ctypes Clight Clightdefs.

Inductive tag :=
| Dynamic
| Local
| Unfreeable.

Let __pointstoRA: URA.t := (block ==> Z ==> (Consent.t memval))%ra.
Let __allocatedRA: URA.t := (block ==> (Consent.t tag))%ra.
Let _pointstoRA: URA.t := Auth.t __pointstoRA.
Let _allocatedRA: URA.t := Auth.t __allocatedRA.
Let _blocksizeRA: URA.t := (option block ==> (OneShot.t Z))%ra.
Let _blockaddressRA: URA.t := (option block ==> (OneShot.t ptrofs))%ra.

Module Mem.
Section MEM.
  Local Obligation Tactic := i; unseal "ra"; ss; des_ifs_safe.

  Definition car : Type := _pointstoRA * _allocatedRA * _blocksizeRA * _blockaddressRA.

  Let _add : car -> car -> car :=
    fun '(a0, b0, c0, d0) '(a1, b1, c1, d1) =>
      (URA.add a0 a1, URA.add b0 b1, URA.add c0 c1, URA.add d0 d1).

  Let _wf : car -> Prop :=
    fun '(_p, _a, _s, _c) =>
      URA.wf _p /\ URA.wf _a /\ URA.wf _s /\ URA.wf _c /\
      match _a with
      | Auth.frag al | Auth.excl _ al =>
        forall b0 b1 q0 q1 tg0 tg1 sz0 sz1 a0 a1 (DIF: b0 <> b1),
          al b0 = Consent.just q0 tg0 ->
          _s (Some b0) = OneShot.white sz0 ->
          _c (Some b0) = OneShot.white a0 ->
          al b1 = Consent.just q1 tg1 ->
          _s (Some b1) = OneShot.white sz1 ->
          _c (Some b1) = OneShot.white a1 ->
          sz1 < Ptrofs.unsigned a0 - Ptrofs.unsigned a1 \/
          sz0 < Ptrofs.unsigned a1 - Ptrofs.unsigned a0
      | _ => True
      end /\
      match _p with
      | Auth.frag p | Auth.excl _ p =>
        forall b0 b1 q0 q1 mv0 mv1 sz0 sz1 a0 a1 (DIF: b0 <> b1),
          (exists z, p b0 z = Consent.just q0 mv0) ->
          _s (Some b0) = OneShot.white sz0 ->
          _c (Some b0) = OneShot.white a0 ->
          (exists z, p b1 z = Consent.just q1 mv1) ->
          _s (Some b1) = OneShot.white sz1 ->
          _c (Some b1) = OneShot.white a1 ->
          sz1 < Ptrofs.unsigned a0 - Ptrofs.unsigned a1 \/
          sz0 < Ptrofs.unsigned a1 - Ptrofs.unsigned a0
      | _ => True
      end.

  Let _unit : car := (URA.unit, URA.unit, URA.unit, URA.unit).

  Let _core : car -> car :=
    fun '(a, b, c, d) =>
      (URA.core a, URA.core b, URA.core c, URA.core d).

  Program Instance t: URA.t := {
    URA.car := car;
    URA._add := _add;
    URA._wf := _wf;
    URA.unit := _unit;
    URA.core := _core;
  }.

  Next Obligation. subst _add. ss. des_ifs; et. rewrite (URA.add_comm c1). rewrite (URA.add_comm c2). rewrite (URA.add_comm c0). rewrite (URA.add_comm c). et. Qed.
  Next Obligation. subst _add. ss. des_ifs. rewrite URA.add_assoc. rewrite URA.add_assoc. rewrite URA.add_assoc. rewrite URA.add_assoc. et. Qed.
  Next Obligation. subst _add. ss. des_ifs. unfold _unit in Heq. clarify. rewrite URA.unit_id. rewrite URA.unit_id. rewrite URA.unit_id. rewrite URA.unit_id. et. Qed.
  Next Obligation.
  Local Transparent URA.unit.
    unfold "ε" in Heq. ss. clarify. ur. ur. ur. ur. splits; et; i; clarify.
  Qed.
  Next Obligation.
    unfold _wf, _add in *. des_ifs_safe. des.
    splits. all: try eapply URA.wf_mon; et.
    - clear H4. ur in H1. ur in H2. ur in H3.
      destruct c2; et; i.
      all: pose proof (H1 (Some b0)); pose proof (H1 (Some b1)).
      all: pose proof (H2 (Some b0)); pose proof (H2 (Some b1)).
      all: rewrite URA.add_comm in H10; rewrite URA.add_comm in H11.
      all: rewrite URA.add_comm in H12; rewrite URA.add_comm in H13.
      all: rewrite H5 in *; rewrite H6 in *.
      all: rewrite H8 in *; rewrite H9 in *.
      all: apply OneShot.oneshot_initialized in H10, H11, H12, H13.
      + des_ifs. 3:{ ur in H0. clarify. }
        * ur in H0. ur in H0. pose proof (H0 b0). pose proof (H0 b1).
          rewrite H4 in *. rewrite H7 in *.
          rewrite URA.add_comm in H14. rewrite URA.add_comm in H15.
          apply Consent.consent_wf in H14, H15.
          des; eapply (H3 b0 b1); ur; des_ifs; clarify.
          all: try rewrite H4; try rewrite H7; try rewrite H14; try rewrite H15; ur; des_ifs.
        * ur in H0. destruct H0 as [H0 X]. eapply URA.wf_extends in H0; et.
          ur in H0. pose proof (H0 b0). pose proof (H0 b1).
          rewrite H4 in *. rewrite H7 in *.
          rewrite URA.add_comm in H14. rewrite URA.add_comm in H15.
          apply Consent.consent_wf in H14, H15.
          des; eapply (H3 b0 b1); ur; des_ifs; clarify.
          all: try rewrite H4; try rewrite H7; try rewrite H14; try rewrite H15; ur; des_ifs.
      + des_ifs. 2,3: ur in H0; clarify.
        ur in H0. destruct H0 as [H0 X]. eapply URA.wf_extends in H0; et.
        ur in H0. pose proof (H0 b0). pose proof (H0 b1).
        rewrite H4 in *. rewrite H7 in *.
        rewrite URA.add_comm in H14. rewrite URA.add_comm in H15.
        apply Consent.consent_wf in H14, H15.
        des; eapply (H3 b0 b1); ur; des_ifs; clarify.
        all: try rewrite H4; try rewrite H7; try rewrite H14; try rewrite H15; ur; des_ifs.
    - clear H3. ur in H1. ur in H2. ur in H4.
      des_ifs; i; des. all: try solve [ur in H; clarify].
      all: pose proof (H1 (Some b0)); pose proof (H1 (Some b1)).
      all: pose proof (H2 (Some b0)); pose proof (H2 (Some b1)).
      all: rewrite URA.add_comm in H10; rewrite URA.add_comm in H11.
      all: rewrite URA.add_comm in H12; rewrite URA.add_comm in H13.
      all: rewrite H5 in *; rewrite H6 in *.
      all: rewrite H8 in *; rewrite H9 in *.
      all: apply OneShot.oneshot_initialized in H10, H11, H12, H13.
      all: ur in H. 2,3: destruct H as [H X]; eapply URA.wf_extends in H; et.
      all: do 2 ur in H.
      all: pose proof (H b0 z0); pose proof (H b1 z).
      all: rewrite H3 in *; rewrite H7 in *.
      all: rewrite URA.add_comm in H14; rewrite URA.add_comm in H15.
      all: apply Consent.consent_wf in H14, H15.
      all: des; eapply (H4 b0 b1); ur; des_ifs; clarify.
      all: eexists; ur; try rewrite H3; try rewrite H7; try rewrite H14; try rewrite H15; ur; des_ifs.
  Qed.
  Next Obligation.
    subst _core _add. ss. des_ifs_safe.
    repeat f_equal; des_ifs; do 4 ur; f_equal; extensionalities; des_ifs.
  Qed.
  Next Obligation.
    subst _core. ss. des_ifs_safe.
    repeat f_equal; des_ifs; extensionalities; des_ifs.
  Qed.
  Next Obligation.
    destruct a as [[[p a] s] c]. destruct b as [[[p' a'] s'] c'].
    simpl _add. hexploit (URA.core_mono p p').
    hexploit (URA.core_mono a a').
    hexploit (URA.core_mono s s').
    hexploit (URA.core_mono c c'). i. des.
    exists (c0, c1, c2, c3). ss. rewrite H. rewrite H0. rewrite H1. rewrite H2. et.
  Qed.

End MEM.
End Mem.

Local Open Scope Z.
Local Open Scope bi_scope.

Lemma update_same_blk K `{Dec K} V
    m k (v: V) :
  update m k v k = v
.
Proof. unfold update. des_ifs. Qed.

Lemma update_diff_blk K `{Dec K} V
    m k k' (v: V)
    (NEQ: k <> k'):
  update m k v k' = m k'
.
Proof. unfold update. des_ifs. Qed.

Section POINTSTO.

  Definition __points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): __pointstoRA :=
    fun _b _ofs =>
      if (Pos.eq_dec _b b) && (Coqlib.zle ofs _ofs) && (Coqlib.zlt _ofs (ofs + Z.of_nat (List.length mvs)))
      then
        match List.nth_error mvs (Z.to_nat (_ofs - ofs)) with
        | Some mv => Consent.just q mv
        | None => Consent.unit
        end
      else Consent.unit
  .

  Definition _points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): Mem.t := (Auth.white (__points_to b ofs mvs q), ε, ε, ε).

End POINTSTO.

Section ALLOCATEDWITH.

  Definition __allocated_with (b: block) (tg: tag) (q: Qp) : __allocatedRA :=
    fun _b =>
      if Pos.eq_dec _b b
      then Consent.just q tg
      else Consent.unit
  .

  Definition _allocated_with (b: block) (tg: tag) (q: Qp) : Mem.t := (ε, Auth.white (__allocated_with b tg q), ε, ε).

End ALLOCATEDWITH.

Section BLOCKSIZE.

  Definition __has_size (ob: option block) (sz: Z) : _blocksizeRA :=
    fun _ob =>
      match ob, _ob with
      | Some b, Some _b =>
        if Pos.eq_dec _b b then OneShot.white sz
        else OneShot.unit
      | None, None => OneShot.white sz (* sz should be zero *)
      | _, _ => OneShot.unit
      end
  .

  Definition _has_size (ob: option block) (sz: Z) : Mem.t := (ε, ε, __has_size ob sz, ε).

End BLOCKSIZE.

Section BLOCKADDR.

  Definition __has_base (ob: option block) (base: ptrofs) : _blockaddressRA :=
    fun _ob =>
      match ob, _ob with
      | Some b, Some _b =>
        if Pos.eq_dec _b b then OneShot.white base
        else OneShot.unit
      | None, None => OneShot.white base
      | _, _ => OneShot.unit
      end
  .

  Definition _has_base (ob: option block) (base: ptrofs) : Mem.t := (ε, ε, ε, __has_base ob base).

End BLOCKADDR.

Section PROPS.

  Lemma points_to_outbound
      blk z mvl q ofs
      (RANGE: ~(z ≤ ofs < z + length mvl)) :
    __points_to blk z mvl q blk ofs = ε
  .
  Proof.
    unfold __points_to. destruct Pos.eq_dec; ss; clarify.
    destruct Coqlib.zle; destruct Coqlib.zlt; ss. nia.
  Qed.

  Lemma points_to_diff_blk
      blk blk' z mvl q ofs
      (NEQ: blk <> blk') :
    __points_to blk z mvl q blk' ofs = ε
  .
  Proof. unfold __points_to. destruct Pos.eq_dec; ss; clarify. Qed.

  Lemma points_to_wf
      (p: __pointstoRA) blk z mvl q
      (WF: URA.wf p)
      (Qrange: (q ≤ 1)%Qp)
      (UP: forall (ofs: Z) (RANGE: z ≤ ofs < z + length mvl), p blk ofs = ε) :
    URA.wf (p ⋅ __points_to blk z mvl q)
  .
  Proof.
    do 2 ur. i. do 2 ur in WF. destruct (Pos.eq_dec k blk); cycle 1.
    { rewrite points_to_diff_blk; et. rewrite URA.unit_id. et. }
    clarify. destruct (Coqlib.zle z k0); destruct (Coqlib.zlt k0 (z + length mvl)); try solve [rewrite points_to_outbound; [rewrite URA.unit_id| nia]; et].
    rewrite UP; try nia. rewrite URA.unit_idl. ur. unfold __points_to. des_ifs.
  Qed.

  Lemma allocated_with_diff_blk
      blk blk' tg q
      (NEQ: blk <> blk') :
    __allocated_with blk tg q blk' = ε
  .
  Proof. unfold __allocated_with. des_ifs. Qed.

  Lemma allocated_with_wf
      (a: __allocatedRA) blk tg q
      (WF: URA.wf a)
      (Qrange: (q ≤ 1)%Qp)
      (UA: a blk = ε) :
    URA.wf (a ⋅ __allocated_with blk tg q)
  .
  Proof.
    ur. i. ur in WF. destruct (Pos.eq_dec blk k); cycle 1.
    { rewrite allocated_with_diff_blk; et. rewrite URA.unit_id. et. }
    clarify. rewrite UA. rewrite URA.unit_idl. ur. unfold __allocated_with. des_ifs.
  Qed.

  Lemma alloc_update
      (p: __pointstoRA) (a: __allocatedRA) (s: _blocksizeRA) (c: _blockaddressRA)
      (blk: block) (z: Z) (mvl: list memval) (tg: tag) (qp qa: Qp) (sz: Z)
      (Qprange: (qp ≤ 1)%Qp)
      (Qarange: (qa ≤ 1)%Qp)
      (UP: forall (ofs: Z) (RANGE: z ≤ ofs < z + length mvl), p blk ofs = Consent.unit)
      (UA: a blk = Consent.unit)
      (BS: s (Some blk) = OneShot.black)
      (BC: c (Some blk) = OneShot.black) :
    URA.updatable (t:=Mem.t) (Auth.black p, Auth.black a, s, c)
      (Auth.black (p ⋅ __points_to blk z mvl qp) ⋅ Auth.white (__points_to blk z mvl qp),
        Auth.black (a ⋅ __allocated_with blk tg qa) ⋅ Auth.white (__allocated_with blk tg qa),
          update s (Some blk) (OneShot.white sz), c)
  .
  Proof.
    ii. destruct ctx as [[[p' a'] s'] c']. ur in H. des. ur. splits; eauto.
    - rewrite URA.unit_idl. pose proof @Auth.auth_alloc2. move Qprange at bottom.
      hexploit points_to_wf; et. { eapply URA.wf_mon in H. ur in H. des. et. }
      i. apply H5 in H6. unfold URA.updatable in H6. red in H6. hexploit H6; et.
      i. clear - H7. set (Auth.excl _ _). eassert (c = _); cycle 1. { rewrite H. apply H7. }
      unfold c. clear. ur. rewrite URA.unit_idl. f_equal. extensionalities. ur. ur. et.
    - rewrite URA.unit_idl. pose proof @Auth.auth_alloc2.
      hexploit allocated_with_wf; et. { eapply URA.wf_mon in H0. ur in H0. des. et. }
      instantiate (1:=tg). i. apply H5 in H6. unfold URA.updatable in H6. red in H6. hexploit H6; et.
      i. clear - H7. set (Auth.excl _ _). eassert (c = _); cycle 1. { rewrite H. apply H7. }
      unfold c. clear. ur. rewrite URA.unit_idl. f_equal. extensionalities. ur. ur. et.
    - clear - BS H1. ur. ur in H1. i. destruct (AList.dec (Some blk) k); cycle 1. { rewrite update_diff_blk; et. }
      clarify. rewrite update_same_blk. specialize (H1 (Some blk)). rewrite BS in *. ur in H1. ur. des_ifs.
    - rewrite URA.unit_idl. clear H4. ur in H3. ur. destruct a'; et.
      i. destruct (AList.dec blk b0); clarify. { rewrite BC in *. ur in H6. des_ifs. }
      destruct (AList.dec blk b1); clarify. { rewrite BC in *. ur in H9. des_ifs. }
      rewrite update_diff_blk in H8. 2:{ ii. apply n0. clarify. }
      rewrite update_diff_blk in H5. 2:{ ii. apply n0. clarify. }
      ur in H4. ur in H7. rewrite allocated_with_diff_blk in H4; et. rewrite allocated_with_diff_blk in H7; et.
      rewrite URA.unit_idl in H4. rewrite URA.unit_idl in H7. rewrite URA.unit_idl in H3. et.
    - rewrite URA.unit_idl. clear H3. ur in H4. ur. destruct p'; et.
      i. des. destruct (AList.dec blk b0); clarify. { rewrite BC in *. ur in H6. des_ifs. }
      destruct (AList.dec blk b1); clarify. { rewrite BC in *. ur in H9. des_ifs. }
      rewrite update_diff_blk in H8. 2:{ ii. apply n0. clarify. }
      rewrite update_diff_blk in H5. 2:{ ii. apply n0. clarify. }
      do 2 ur in H3. do 2 ur in H7. rewrite points_to_diff_blk in H3; et. rewrite points_to_diff_blk in H7; et.
      rewrite URA.unit_idl in H3. rewrite URA.unit_idl in H7. rewrite URA.unit_idl in H4. et.
  Qed.

  Lemma free_update
      (p: __pointstoRA) (a: __allocatedRA) (s: _blocksizeRA) (c: _blockaddressRA)
      (blk: block) (z: Z) (mvl: list memval) (tg: tag) (qp qa: Qp)
      (UP: forall (ofs: Z) (RANGE: z ≤ ofs < z + length mvl), p blk ofs = __points_to blk z mvl qp blk ofs)
      (UA: a blk = Consent.just qa tg) :
    URA.updatable (t:=Mem.t)
      (Auth.black p ⋅ Auth.white (__points_to blk z mvl qp),
        Auth.black a ⋅ Auth.white (__allocated_with blk tg qa), s, c)
      (Auth.black (update p blk (fun _ofs => if Coqlib.zle z _ofs && Coqlib.zlt _ofs (z + length mvl) then Consent.unit else p blk _ofs) : __pointstoRA),
        (Auth.black (update a blk Consent.unit : __allocatedRA)), s, c)
  .
  Proof.
    ii. destruct ctx as [[[p' a'] s'] c']. ur in H. des. ur. splits; eauto.
    - clear - H UP. pose proof (@Auth.auth_dealloc __pointstoRA). hexploit H0; cycle 1.
      { i. do 2 red in H1. apply H1. instantiate (1:= __points_to blk z mvl qp). instantiate (1:= p).
        set (_ ⋅ _). eassert (c = _); cycle 1. rewrite H2; et. unfold c. ur. des_ifs. do 2 f_equal. extensionalities. ur. ur. ur. et. }
      clear -UP. rr. i. des. red in H, H0. clarify. rewrite URA.unit_idl. split.
      + ur. ur. i. ur in H. ur in H. destruct (AList.dec blk k); cycle 1. { rewrite update_diff_blk; et. }
        clarify. rewrite update_same_blk. des_ifs. ur. et.
      + rr. extensionalities. destruct (AList.dec blk H0); cycle 1. { rewrite update_diff_blk; et. ur. ur. rewrite points_to_diff_blk; et. ur. des_ifs. }
        clarify. rewrite update_same_blk. des_ifs.
        * do 2 ur in UP. hexploit (UP H1); [destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; nia|].
          i. unfold __points_to in H2. destruct Pos.eq_dec; ss; clarify.
          destruct (nth_error_Some mvl (Z.to_nat (H1 - z))).
          hexploit H4; [destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; nia|]. i. des_ifs.
          ur in H2. des_ifs. apply Qp_add_id_free in H2. clarify.
        * do 2 ur. rewrite points_to_outbound; [|destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; nia].
          rewrite URA.unit_idl. et.
    - clear - H0 UA. pose proof (@Auth.auth_dealloc __allocatedRA). hexploit H; cycle 1.
      { i. do 2 red in H1. apply H1. instantiate (1:= __allocated_with blk tg qa). instantiate (1:= a).
        set (_ ⋅ _). eassert (c = _); cycle 1. rewrite H2; et. unfold c. ur. des_ifs. do 2 f_equal. extensionalities. ur. ur. et. }
      clear -UA. rr. i. des. red in H, H0. clarify. rewrite URA.unit_idl. split.
      + ur. i. destruct (AList.dec blk k); clarify. { rewrite update_same_blk. ur. et. }
        rewrite update_diff_blk; et. ur in H. et.
      + rr. ur in UA. unfold __allocated_with in UA. des_ifs.
        extensionalities. destruct (AList.dec blk H0); clarify.
        { rewrite update_same_blk. ur in UA. des_ifs. apply Qp_add_id_free in H2. clarify. }
        rewrite update_diff_blk; et. ur. rewrite allocated_with_diff_blk; et. rewrite URA.unit_idl. et.
    - clear -H0 H3. ur in H3. ur. des_ifs. i. rewrite (@URA.unit_idl __allocatedRA) in *.
      ur in H0. des. eapply URA.wf_extends in H0; et. ur in H0.
      destruct (AList.dec blk b0); destruct (AList.dec blk b1); clarify.
      + eapply H3; et.
        * ur. specialize (H0 b0). unfold __allocated_with. unfold __allocated_with in H0.
          des_ifs. rewrite H in *. ur. ur in H0. des_ifs.
        * ur. specialize (H0 b1). unfold __allocated_with. unfold __allocated_with in H0.
          des_ifs. rewrite H4 in *. ur. ur in H0. des_ifs.
      + clear n. eapply H3; et.
        * ur. specialize (H0 b0). unfold __allocated_with. unfold __allocated_with in H0.
          des_ifs. rewrite H in *. ur. ur in H0. des_ifs.
        * ur. specialize (H0 b1). unfold __allocated_with. unfold __allocated_with in H0.
          des_ifs. rewrite H4 in *. ur. ur in H0. des_ifs.
      + eapply H3. apply DIF. all: et.
        * ur. specialize (H0 b0). unfold __allocated_with. unfold __allocated_with in H0.
          des_ifs. rewrite H in *. ur. ur in H0. des_ifs.
        * ur. specialize (H0 b1). unfold __allocated_with. unfold __allocated_with in H0.
          des_ifs. rewrite H4 in *. ur. ur in H0. des_ifs.
    - clear -H H4. ur in H4. ur. des_ifs. i. rewrite (@URA.unit_idl __pointstoRA) in *.
      ur in H. des. eapply URA.wf_extends in H; et. do 2 ur in H.
      destruct (__points_to blk z mvl qp b0 z1) eqn:?;
        destruct (__points_to blk z mvl qp b1 z0) eqn:?;
          try solve [hexploit H; match goal with H: _ = Consent.boom |- _ => rewrite H end; intro X; ur in X; des_ifs].
      + eapply H4; et.
        * do 2 ur. specialize (H b0 z1). eexists. rewrite H0 in *. rewrite Heqc0 in *. des_ifs. ur. ur in H. des_ifs.
        * do 2 ur. specialize (H b1 z0). eexists. rewrite H3 in *. rewrite Heqc1 in *. des_ifs. ur. ur in H. des_ifs.
      + eapply H4; et.
        * do 2 ur. specialize (H b0 z1). eexists. rewrite H0 in *. rewrite Heqc0 in *. des_ifs. ur. ur in H. des_ifs.
        * do 2 ur. specialize (H b1 z0). eexists. rewrite H3 in *. rewrite Heqc1 in *. des_ifs. ur. ur in H. des_ifs.
      + eapply H4; et.
        * do 2 ur. specialize (H b0 z1). eexists. rewrite H0 in *. rewrite Heqc0 in *. des_ifs. ur. ur in H. des_ifs.
        * do 2 ur. specialize (H b1 z0). eexists. rewrite H3 in *. rewrite Heqc1 in *. des_ifs. ur. ur in H. des_ifs.
      + eapply H4; et.
        * do 2 ur. specialize (H b0 z1). eexists. rewrite H0 in *. rewrite Heqc0 in *. des_ifs. ur. ur in H. des_ifs.
        * do 2 ur. specialize (H b1 z0). eexists. rewrite H3 in *. rewrite Heqc1 in *. des_ifs. ur. ur in H. des_ifs.
  Qed.

  Lemma store_update
      (p: __pointstoRA) (a: _allocatedRA) (s: _blocksizeRA) (c: _blockaddressRA)
      (blk: block) (z: Z) (mvl mvl': list memval) (qp: Qp)
      (EQ: length mvl = length mvl')
      (UP: forall (ofs: Z) (RANGE: z ≤ ofs < z + length mvl), p blk ofs = __points_to blk z mvl qp blk ofs) :
    URA.updatable (t:=Mem.t)
      (Auth.black p ⋅ Auth.white (__points_to blk z mvl qp), a, s, c)
      (Auth.black
        (update p blk
          (fun _ofs =>
            if Coqlib.zle z _ofs && Coqlib.zlt _ofs (z + length mvl')
            then
              match nth_error mvl' (Z.to_nat (_ofs - z)) with
              | Some mv => Consent.just qp mv
              | None => Consent.unit
              end
            else p blk _ofs) : __pointstoRA) ⋅ Auth.white (__points_to blk z mvl' qp), a, s, c)
  .
  Proof.
    ii. destruct ctx as [[[p' a'] s'] c']. ur in H. des. ur. splits; eauto.
    - clear - H UP EQ. pose proof (@Auth.auth_update __pointstoRA). hexploit H0; cycle 1.
      + i. do 2 red in H1. specialize (H1 p').
        set (_ ⋅ _). eassert (c = _); cycle 1. rewrite H2. apply H1.
        2:{ unfold c. ur. des_ifs. f_equal. extensionalities. do 3 ur. et. }
        set (_ ⋅ _). eassert (c0 = _); cycle 1. rewrite H3. apply H.
        unfold c0. ur. des_ifs. f_equal. extensionalities. do 3 ur. et.
      + clear -UP EQ. rr. i. des. red in H, H0. clarify. split.
        * ur. ur. i. ur in H. ur in H. destruct (AList.dec blk k); cycle 1. { rewrite update_diff_blk; et. }
          clarify. rewrite update_same_blk. des_ifs; ur; et.
          specialize (H k k0). unfold __points_to in H. destruct Pos.eq_dec; clarify. ss.
          rewrite EQ in H. rewrite Heq in *.
          destruct (nth_error_Some mvl (Z.to_nat (k0 - z))).
          hexploit H1; [destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; nia|]. i. des_ifs.
          apply URA.wf_mon in H. ur in H. et.
        * rr. extensionalities. destruct (AList.dec blk H0); cycle 1. { rewrite update_diff_blk; et. ur. ur. rewrite !points_to_diff_blk; et. }
          clarify. rewrite update_same_blk.
          destruct (_ && _) eqn:?; cycle 1. { unfold __points_to. ur. ur. destruct Pos.eq_dec; clarify. ss. rewrite EQ in *. rewrite Heqb. et. }
          do 2 ur in UP. specialize (UP H1).
          hexploit UP; [destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; nia|]. i.
          unfold __points_to in H2. destruct Pos.eq_dec; clarify. ss. rewrite EQ in *. rewrite Heqb in H2.
          destruct (nth_error_Some mvl (Z.to_nat (H1 - z))).
          ur. ur. unfold __points_to. destruct Pos.eq_dec; clarify. ss. rewrite Heqb.
          replace (ctx H0 H1) with (ε : Consent.t memval). rewrite URA.unit_id; et.
          des_ifs; ur in H2; des_ifs. apply Qp_add_id_free in H2. clarify.
    - clear -H H4 EQ UP. rewrite (@URA.unit_idl __pointstoRA) in *.
      ur in H4. ur. des_ifs. i. des. do 2 ur in H0. do 2 ur in H3. ur in H. des. eapply URA.wf_extends in H; et. do 2 ur in H.
      assert (exists q mv, (__points_to blk z mvl qp ⋅ f0) b0 z1 = Consent.just q mv); cycle 1.
      assert (exists q mv, (__points_to blk z mvl qp ⋅ f0) b1 z0 = Consent.just q mv); cycle 1.
      { des. eapply H4. 1,2,3,5,6: et. all: et. }
      + clear - H H3 EQ UP. do 2 ur in H3. do 2 ur. specialize (H b1 z0). des_ifs; try solve [unfold __points_to in *; des_ifs].
        * unfold __points_to in Heq. des_ifs. unfold __points_to. unfold __points_to in H.
          rewrite EQ in *. rewrite Heq1 in *. des_ifs; ur; et. ur in H. des_ifs. et.
        * unfold __points_to in Heq. unfold __points_to. rewrite EQ in *.
          des_ifs; ur; et. rewrite nth_error_None in Heq2. rewrite EQ in Heq2.
          rewrite <- nth_error_None in Heq2. clarify.
        * unfold __points_to. unfold __points_to in H.
          rewrite EQ in *. des_ifs; ur; et. ur in H. des_ifs. et.
      + clear - H H0 EQ UP. do 2 ur in H0. do 2 ur. specialize (H b0 z1). des_ifs; try solve [unfold __points_to in *; des_ifs].
        * unfold __points_to in Heq. des_ifs. unfold __points_to. unfold __points_to in H.
          rewrite EQ in *. rewrite Heq1 in *. des_ifs; ur; et. ur in H. des_ifs. et.
        * unfold __points_to in Heq. unfold __points_to. rewrite EQ in *.
          des_ifs; ur; et. rewrite nth_error_None in Heq2. rewrite EQ in Heq2.
          rewrite <- nth_error_None in Heq2. clarify.
        * unfold __points_to. unfold __points_to in H.
          rewrite EQ in *. des_ifs; ur; et. ur in H. des_ifs. et.
  Qed.

  Lemma capture_update
      (p: __pointstoRA) (a: __allocatedRA) (s: _blocksizeRA) (c: _blockaddressRA)
      (blk: block) (tg: tag) (qa: Qp) (addr: ptrofs) (sz: Z)
      (BS: s (Some blk) = OneShot.white sz)
      (BC: c (Some blk) = OneShot.black)
      (Gp: forall b' q' mv' sz' addr',
            b' <> blk ->
            (exists z', p b' z' = Consent.just q' mv') ->
            s (Some b') = OneShot.white sz' ->
            c (Some b') = OneShot.white addr' ->
            sz < Ptrofs.unsigned addr' - Ptrofs.unsigned addr \/ sz' < Ptrofs.unsigned addr - Ptrofs.unsigned addr')
      (Ga: forall b' q' tg' sz' addr',
            b' <> blk ->
            a b' = Consent.just q' tg' ->
            s (Some b') = OneShot.white sz' ->
            c (Some b') = OneShot.white addr' ->
            sz < Ptrofs.unsigned addr' - Ptrofs.unsigned addr \/ sz' < Ptrofs.unsigned addr - Ptrofs.unsigned addr')
      (Gs: forall k, s k <> OneShot.unit)
      (Gc: forall k, c k <> OneShot.unit) :
    URA.updatable (t:=Mem.t)
      (Auth.black p, Auth.black a ⋅ Auth.white (__allocated_with blk tg qa), s, c)
      (Auth.black p, Auth.black a ⋅ Auth.white (__allocated_with blk tg qa), s, update c (Some blk) (OneShot.white addr))
  .
  Proof.
    ii. destruct ctx as [[[p' a'] s'] c']. ur in H. des. ur. splits; eauto.
    - ur. i. ur in H2. destruct (AList.dec (Some blk) k); cycle 1. { rewrite update_diff_blk; et. }
      clarify. rewrite update_same_blk. specialize (H2 (Some blk)). rewrite BC in H2.
      clear - H2. ur in H2. des_ifs. ur. et.
    - rewrite (@URA.unit_idl __allocatedRA) in *. clear - H0 H2 H3 BS BC Ga Gc Gs. ur in H3. ur. des_ifs.
      i. ur in H0. des. destruct (AList.dec blk b0); destruct (AList.dec blk b1); clarify.
      + rewrite update_diff_blk in H7. 2:{ ii. apply n. clarify. }
        rewrite update_same_blk in H4. ur in H2. specialize (H2 (Some b0)).
        rewrite BC in H2. ur in H2. des_ifs. ur in H4. clarify.
        rewrite BS in H1. assert (sz = sz0); clarify. { ur in H1. des_ifs. }
        apply URA.pw_extends in H0. ur in H8. red in H0. specialize (H0 b1). specialize (H8 b1).
        rewrite H5 in H0. red in H0. des. ur in H0.
        specialize (Gs (Some b1)). specialize (Gc (Some b1)).
        des_ifs; rewrite <- H0 in *; ur in H8; clarify.
        * ur in H6. ur in H7. apply or_comm. des_ifs; eapply Ga; et.
        * ur in H6. ur in H7. apply or_comm. des_ifs; eapply Ga; et.
      + rewrite update_same_blk in H7. ur in H2. specialize (H2 (Some b1)).
        rewrite update_diff_blk in H4. 2:{ ii. apply n. clarify. }
        rewrite BC in H2. ur in H2. des_ifs. ur in H7. clarify.
        rewrite BS in H6. assert (sz = sz1); clarify. { ur in H6. des_ifs. }
        apply URA.pw_extends in H0. ur in H8. red in H0. specialize (H0 b0). specialize (H8 b0).
        rewrite H in H0. red in H0. des. ur in H0.
        specialize (Gs (Some b0)). specialize (Gc (Some b0)).
        des_ifs; rewrite <- H0 in *; ur in H8; clarify.
        * ur in H1. ur in H4. des_ifs; eapply Ga; et.
        * ur in H1. ur in H4. des_ifs; eapply Ga; et.
      + rewrite update_diff_blk in H4. 2:{ ii. apply n. clarify. }
        rewrite update_diff_blk in H7. 2:{ ii. apply n0. clarify. }
        eapply H3. apply DIF. all: et.
    - clear - H H2 H4 BS BC Gp Gc Gs. ur in H4. ur. des_ifs.
      i. rewrite URA.unit_idl in H0. rewrite URA.unit_idl in H5.
      des. ur in H. des. rewrite URA.unit_idl in H.
      destruct (AList.dec blk b0); destruct (AList.dec blk b1); clarify.
      + rewrite update_diff_blk in H7. 2:{ ii. apply n. clarify. }
        rewrite update_same_blk in H3. ur in H2. specialize (H2 (Some b0)).
        rewrite BC in H2. ur in H2. des_ifs. ur in H3. clarify.
        rewrite BS in H1. assert (sz = sz0); clarify. { ur in H1. des_ifs. }
        apply URA.pw_extends in H. do 2 ur in H8. red in H. specialize (H b1). specialize (H8 b1 z).
        apply URA.pw_extends in H. red in H. specialize (H z).
        rewrite H5 in H. red in H. des. ur in H.
        specialize (Gs (Some b1)). specialize (Gc (Some b1)).
        des_ifs; rewrite <- H in *; ur in H8; clarify.
        * ur in H6. ur in H7. apply or_comm. des_ifs; eapply Gp; et.
        * ur in H6. ur in H7. apply or_comm. des_ifs; eapply Gp; et.
      + rewrite update_same_blk in H7. ur in H2. specialize (H2 (Some b1)).
        rewrite update_diff_blk in H3. 2:{ ii. apply n. clarify. }
        rewrite BC in H2. ur in H2. des_ifs. ur in H7. clarify.
        rewrite BS in H6. assert (sz = sz1); clarify. { ur in H6. des_ifs. }
        apply URA.pw_extends in H. do 2 ur in H8. red in H. specialize (H b0). specialize (H8 b0 z0).
        apply URA.pw_extends in H. red in H. specialize (H z0).
        rewrite H0 in H. red in H. des. ur in H.
        specialize (Gs (Some b0)). specialize (Gc (Some b0)).
        des_ifs; rewrite <- H in *; ur in H8; clarify.
        * ur in H1. ur in H3. des_ifs; eapply Gp; et.
        * ur in H1. ur in H3. des_ifs; eapply Gp; et.
      + rewrite update_diff_blk in H3. 2:{ ii. apply n. clarify. }
        rewrite update_diff_blk in H7. 2:{ ii. apply n0. clarify. }
        rewrite URA.unit_idl in H4.
        eapply H4. apply DIF. all: et.
  Qed.

End PROPS.