From compcert Require Import
     AST Maps Globalenvs Memory Values Linking Integers.
From compcert Require Import
     Ctypes Clight Clightdefs.

Require Import CoqlibCCR.
Require Export ZArith.
Require Import String.
Require Import Orders.
Require Export AList.
Require Export Skeleton.

(* TODO: skeleton should be pair of def and type def *)
Set Implicit Arguments.

Local Open Scope nat_scope.

Fixpoint _find_idx {A} (f: A -> bool) (l: list A) (acc: nat): option (nat * A) :=
  match l with
  | [] => None
  | hd :: tl => if (f hd) then Some (acc, hd) else _find_idx f tl (S acc)
  end
.

Definition find_idx {A} (f: A -> bool) (l: list A): option (nat * A) := _find_idx f l 0.

Notation "'do' ' X <- A ; B" := (o_bind A (fun _x => match _x with | X => B end))
                                  (at level 200, X pattern, A at level 100, B at level 200)
                                : o_monad_scope.

Lemma find_idx_red {A} (f: A -> bool) (l: list A):
  find_idx f l =
  match l with
  | [] => None
  | hd :: tl =>
    if (f hd)
    then Some (0%nat, hd)
    else
      do (n, a) <- find_idx f tl;
      Some (S n, a)
  end.
Proof.
  unfold find_idx. generalize 0. induction l; ss.
  i. des_ifs; ss.
  - rewrite Heq0. ss.
  - rewrite Heq0. specialize (IHl (S n)). rewrite Heq0 in IHl. ss.
Qed.

Definition gdef := globdef fundef type.

Module GDef <: Typ. Definition t := gdef. End GDef.

Module SkGSort := AListSort GDef.

Definition gsort: alist gname gdef -> alist gname gdef := SkGSort.sort.

Definition cdef := composite.

Module CDef <: Typ. Definition t := cdef. End CDef.

Module SkCSort := AIListSort CDef.

Definition csort: alist positive cdef -> alist positive cdef := SkCSort.sort.

Definition incl (sk0 sk1: (alist gname gdef) * (alist positive cdef)): Prop :=
  (forall gn gd (IN: List.In (gn, gd) (fst sk0)), List.In (gn, gd) (fst sk1))
  /\ (forall id co (IN: List.In (id, co) (snd sk0)), List.In (id, co) (snd sk1)).

Definition struct_or_union_dec : forall x y: struct_or_union, {x = y} + {x <> y}.
Proof.
  i. destruct x, y.
  - left. et.
  - right. ss.
  - right. ss.
  - left. et.
Defined.

Definition members_dec : forall x y: members, {x = y} + {x <> y}.
Proof.
  i. revert y. induction x. 
  - i. destruct y.
    + left. et.
    + right. ss.
  - i. destruct y.
    + right. ss.
    + destruct a, p. destruct (dec i i0); cycle 1. { right. ii. apply n. clarify. }
      subst. destruct (type_eq t t0); cycle 1. { right. ii. apply n. clarify. }
      subst. destruct (IHx y). subst. left. et.
      right. ii. apply n. clarify.
Defined.

Definition attr_dec : forall x y: attr, {x = y} + {x <> y}.
Proof.
  i. destruct x, y.
  destruct attr_volatile; destruct attr_volatile0.
  2,3: right; ii; clarify.
  all: destruct attr_alignas; destruct attr_alignas0.
  2,3,6,7: right; ii; clarify.
  2,4: left; et.
  all: destruct (N.eq_dec n n0); subst.
  1,3: left; et.
  all: right; ii; clarify.
Defined.

Definition composite_eq_dec : forall x y: composite, {x = y} + {x <> y}.
Proof.
  i. destruct x, y.
  destruct (struct_or_union_dec co_su co_su0);
  destruct (members_dec co_members co_members0);
  destruct (attr_dec co_attr co_attr0);
  destruct (Z.eq_dec co_sizeof co_sizeof0);
  destruct (Z.eq_dec co_alignof co_alignof0);
  destruct (Nat.eq_dec co_rank co_rank0).
  { subst.
    assert (co_sizeof_pos = co_sizeof_pos0) by apply proof_irr.
    assert (co_alignof_two_p = co_alignof_two_p0) by apply proof_irr.
    assert (co_sizeof_alignof = co_sizeof_alignof0) by apply proof_irr.
    subst. left. et. }
  all: right; ii; inv H; et.
Defined.

Definition check_compat_composite (l: alist ident composite) (cd: ident * composite) : bool :=
  List.forallb
    (fun cd' =>
      if ident_eq (fst cd') (fst cd) then composite_eq_dec (snd cd) (snd cd') else true)
    l.

Definition filter_redefs (l1 l2: alist ident composite) :=
  let names1 := map fst l1 in
  List.filter (fun cd => negb (In_dec ident_eq (fst cd) names1)) l2.

Definition _link_composite_defs (l1 l2: alist ident composite): option (alist ident composite) :=
  if List.forallb (check_compat_composite l2) l1
  then Some (l1 ++ filter_redefs l1 l2)
  else None.

Definition default_composite : composite.
Proof.
  econs.
  - exact Struct.
  - exact [].
  - econs. { exact true. } { exact None. }
  - exact 0.
  - instantiate (1:=0%Z). nia.
  - exists 0. ss.
  - exists 0%Z. ss.
Qed.

Definition link_composite_defs (l1 l2: alist ident composite): alist ident composite :=
  match _link_composite_defs l1 l2 with
  | Some l => l
  | None => [(xH, default_composite); (xH, default_composite)]
  end.

Definition add (sk0 sk1: (alist gname gdef) * (alist positive cdef)): (alist gname gdef) * (alist positive cdef) :=
  let (g0, c0) := sk0 in
  let (g1, c1) := sk1 in
  (List.app g0 g1, link_composite_defs c0 c1).

Definition sort (sk : (alist gname gdef) * (alist positive cdef)): (alist gname gdef) * (alist positive cdef) :=
  let (g, c) := sk in
  (gsort g, csort c).

Definition wf (sk: (alist gname gdef) * (alist positive cdef)): Prop :=
  let (g, c) := sk in
  List.NoDup (List.map fst g) /\ List.NoDup (List.map fst c).

Definition wf_dec (sk: (alist gname gdef) * (alist positive cdef)): {wf sk} + {~wf sk}.
Proof.
  destruct sk.
  destruct (ListDec.NoDup_dec string_dec (map fst a));
  destruct (ListDec.NoDup_dec Pos.eq_dec (map fst a0)).
  - left. red. et.
  - right. red. i. red in H. apply n0. des. et.
  - right. red. i. red in H. apply n. des. et.
  - right. red. i. red in H. apply n0. des. et.
Defined.

Program Definition gdefs: Sk.ld := 
  @Sk.mk ((alist gname gdef) * (alist positive cdef)) (nil, nil) add sort wf wf_dec incl
  _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation.
  econs.
  - ii. ss.
  - ii. unfold incl in *. des. split.
    + i. eapply H0. eapply H. ss.
    + i. eapply H1. eapply H2. ss.
Qed.
Next Obligation.
  split.
  - ii. eapply Permutation.Permutation_in; [|apply IN].
    eapply SkGSort.sort_permutation.
  - ii. eapply Permutation.Permutation_in; [|apply IN].
    eapply SkCSort.sort_permutation.
Qed.
Next Obligation.
  split.
  - ii. eapply Permutation.Permutation_in; [|apply IN].
    symmetry. eapply SkGSort.sort_permutation.
  - ii. eapply Permutation.Permutation_in; [|apply IN].
    symmetry. eapply SkCSort.sort_permutation.
Qed.
Next Obligation.
  unfold sort, add, wf in *. des. f_equal.
  - eapply SkGSort.sort_add_comm. auto.
  - admit "sort_comm".
Qed.
Next Obligation.
  unfold add. f_equal.
  - eapply List.app_assoc.
  - admit "assoc".
Qed.
Next Obligation.
  unfold link_composite_defs. ss. unfold filter_redefs. ss.
  f_equal. induction a0; ss. f_equal. et.
Qed.
Next Obligation.
  unfold add. rewrite List.app_nil_r. f_equal.
  unfold link_composite_defs. unfold _link_composite_defs. ss. unfold check_compat_composite.
  ss. rewrite List.app_nil_r.
  replace (if (forallb _ _) then _ else _) with (Some a0); et.
  induction a0; ss. destruct forallb; ss.
Qed.
Next Obligation.
  red. split; ss.
  - induction a0; ss. i. ss. des; subst; et.
  - admit "le_add".
Qed.
Next Obligation.
  red. unfold add. ss. split; ss.
  - induction a; ss. i. ss. des; subst; et.
  - admit "le_add".
Qed.
Next Obligation.
  red. unfold incl, add in *. ss. des. split; ss.
  - induction a0; ss. i. ss. des; subst; et.
  - admit "siran".
Qed.
Next Obligation.
  unfold wf in *. des_ifs. ss. clarify. des. split.
  - eapply Permutation.Permutation_NoDup; [|et].
    eapply Permutation.Permutation_map.
    apply Permutation.Permutation_app_comm.
  - eapply Permutation.Permutation_NoDup; [|et].
    eapply Permutation.Permutation_map.
    admit "comm_perm".
Qed.
Next Obligation.
  unfold wf in *. des_ifs. ss. clarify. des. split.
  - eapply Permutation.Permutation_NoDup; [|et].
    eapply Permutation.Permutation_map.
    eapply SkGSort.sort_permutation.
  - eapply Permutation.Permutation_NoDup; [|et].
    eapply Permutation.Permutation_map.
    eapply SkCSort.sort_permutation.
Qed.
Next Obligation.
  split; econs.
Qed.
Next Obligation.
  unfold wf in *. des_ifs. ss. clarify. des. split.
  - cut (NoDup (map fst a)).
    { i. eapply Permutation.Permutation_NoDup; [|et].
        eapply Permutation.Permutation_map.
        eapply SkGSort.sort_permutation. }
    cut (NoDup (map fst (a ++ a0))).
    { i. rewrite map_app in H1.
        eapply nodup_app_l. et. }
    i. eapply Permutation.Permutation_NoDup; [|et].
    eapply Permutation.Permutation_map.
    symmetry. eapply SkGSort.sort_permutation.
  - cut (NoDup (map fst a2)).
    { i. eapply Permutation.Permutation_NoDup; [|et].
        eapply Permutation.Permutation_map.
        eapply SkCSort.sort_permutation. }
    (* cut (NoDup (map fst (a2 ++ a1))).
    { i. rewrite map_app in H1.
        eapply nodup_app_l. et. }
    i. eapply Permutation.Permutation_NoDup; [|et].
    eapply Permutation.Permutation_map.
    symmetry. eapply SkCSort.sort_permutation. *)
    admit "add no dup".
Qed.

Local Existing Instance gdefs.

Definition load_skenv (sk: Sk.t): (SkEnv.t) :=
  let n := List.length (fst sk) in
  {|
      SkEnv.blk2id := fun blk => do '(gn, _) <- (List.nth_error (fst sk) blk); Some gn;
      SkEnv.id2blk := fun id => do '(blk, _) <- find_idx (fun '(id', _) => string_dec id id') (fst sk); Some blk
  |}
  .

Lemma load_skenv_wf sk
    (WF: Sk.wf sk)
:
    <<WF: SkEnv.wf (load_skenv sk)>>
.
Proof.
  r in WF. ss. unfold wf in WF. des_ifs. des. 
  rr. split; i; ss.
  - uo; des_ifs.
    + f_equal. ginduction a; ss. i. inv WF.
      rewrite find_idx_red in Heq1. des_ifs; ss.
      { destruct string_dec in Heq; clarify. }
      des_sumbool. uo. des_ifs. destruct p. ss.
      hexploit IHa; et.
    + exfalso. ginduction a; ss. i. inv WF.
      rewrite find_idx_red in Heq2. des_ifs; ss.
      des_sumbool. uo. des_ifs. destruct p. ss.
      hexploit IHa; et.
  - ginduction a; ss.
    { i. uo. ss. destruct blk; ss. }
    i. destruct a. inv WF. uo. destruct blk; ss; clarify.
    { rewrite find_idx_red. uo. des_ifs; destruct string_dec in *; ss. }
    hexploit IHa; et. i.
    rewrite find_idx_red. uo. des_ifs; des_sumbool; ss. exfalso.
    subst. clear - Heq1 H2. ginduction a0; ss. i.
    rewrite find_idx_red in Heq1.
    des_ifs; destruct string_dec; ss; et.
    uo. des_ifs. destruct p. eapply IHa0; et.
Qed.

Definition incl_env (sk0: Sk.t) (skenv: SkEnv.t): Prop :=
  forall gn gd (IN: List.In (gn, gd) (fst sk0)),
  exists blk, <<FIND: skenv.(SkEnv.id2blk) gn = Some blk>>.

Lemma incl_incl_env sk0 sk1
    (INCL: incl sk0 sk1)
:
    incl_env sk0 (load_skenv sk1).
Proof.
  unfold incl in *. des.
  ii. exploit INCL; et. i. ss. uo. des_ifs; et.
  exfalso. clear - x0 Heq0. destruct sk1. ss. ginduction a; et.
  i. ss. rewrite find_idx_red in Heq0. des_ifs.
  des_sumbool. uo.  des_ifs. des; clarify.
  eapply IHa; et.
Qed.

Lemma in_env_in_sk :
  forall sk blk symb
        (FIND: SkEnv.blk2id (load_skenv sk) blk = Some symb),
  exists def, In (symb, def) (fst sk).
Proof.
  i. unfold SkEnv.blk2id. ss.
  uo. des_ifs. des; clarify.
  eapply nth_error_In in Heq0. et.
Qed.

Lemma in_sk_in_env :
  forall sk def symb
        (IN: In (symb, def) (fst sk)),
  exists blk, SkEnv.blk2id (load_skenv sk) blk = Some symb.
Proof.
  i. unfold SkEnv.blk2id. ss.
  uo. eapply In_nth_error in IN. des.
  exists n. unfold alist in *. rewrite IN. et.
Qed.

Lemma env_range_some :
  forall sk blk
        (BLKRANGE : blk < Datatypes.length (fst sk)),
  <<FOUND : exists symb, SkEnv.blk2id (load_skenv sk) blk = Some symb>>.
Proof.
  i. destruct sk. ss. depgen l. induction blk; i; ss; clarify.
  - destruct l; ss; clarify. { lia. }
    uo. destruct p. exists s. ss.
  - destruct l; ss; clarify. { lia. }
    apply lt_S_n in BLKRANGE. eapply IHblk; eauto.
Qed.

Lemma env_found_range :
  forall sk symb blk
        (FOUND : SkEnv.id2blk (load_skenv sk) symb = Some blk),
  <<BLKRANGE : blk < Datatypes.length (fst sk)>>.
Proof.
  intros sk. destruct sk. ss.
  induction a; i; ss; clarify.
  uo; des_ifs. destruct p0. rewrite find_idx_red in Heq0. des_ifs.
  { apply Nat.lt_0_succ. }
  destruct blk.
  { apply Nat.lt_0_succ. }
  uo. des_ifs. destruct p. ss. clarify. apply lt_n_S. eapply IHa; eauto.
  instantiate (1:=symb). rewrite Heq0. ss.
Qed.

Lemma sk_incl_gd sk0 sk1 gn blk gd: 
  Sk.wf sk1 ->
  Sk.le sk0 sk1 ->
  SkEnv.id2blk (load_skenv sk1) gn = Some blk ->
  In (gn, gd) (fst sk0) ->
  nth_error (fst sk1) blk = Some (gn, gd).
Proof.
  ss. i. destruct sk0. destruct sk1. unfold incl in H0. ss. des. hexploit H0; et. i.
  clear - H H1 H5. ginduction a1; i; ss.
  destruct blk; ss.
  - des; clarify. uo. des_ifs. rewrite find_idx_red in Heq0. exfalso.
    des_ifs; des_sumbool; subst.
    + ss. inv H. eapply in_map with (f:=fst) in H5. et.
    + uo. des_ifs.
  - des; clarify. uo. des_ifs. rewrite find_idx_red in Heq0.
    des_ifs; des_sumbool; subst.
    { exfalso. et. }
    eapply IHa1; et.
    + inv H. et.
    + uo. rewrite find_idx_red in H1. des_ifs.
      uo. unfold curry2 in *. clarify.
Qed.

Global Existing Instance gdefs.
Arguments Sk.unit: simpl never.
Arguments Sk.add: simpl never.
Arguments Sk.wf: simpl never.
Coercion load_skenv: Sk.t >-> SkEnv.t.
Global Opaque load_skenv.