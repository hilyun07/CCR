Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import ProofMode.

Set Implicit Arguments.



Let _memRA: URA.t := (mblock ==> Z ==> (Excl.t val))%ra.
Compute (URA.car (t:=_memRA)).
Instance memRA: URA.t := Auth.t _memRA.
Compute (URA.car).


Let _memRACAP: URA.t := (mblock ==> (OneShot.t Z))%ra.
Compute (URA.car (t:=_memRACAP)).
Instance memRACAP: URA.t := Auth.t _memRACAP.
Compute (URA.car).

Let _memRASZ: URA.t := (mblock ==> (Excl.t Z))%ra.
Compute (URA.car (t:=_memRASZ)).
Instance memRASZ: URA.t := Auth.t _memRASZ.
Compute (URA.car).

Local Arguments Z.of_nat: simpl nomatch.


Section POINTSTO.
  Context `{@GRA.inG memRA Σ}.

  Definition _points_to (loc: mblock * Z) (vs: list val): _memRA :=
    let (b, ofs) := loc in
    (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length vs))))%Z
                    then (List.nth_error vs (Z.to_nat (_ofs - ofs))) else ε)
  .

  (* Opaque _points_to. *)
  Lemma unfold_points_to loc vs:
    _points_to loc vs =
    let (b, ofs) := loc in
    (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length vs))))%Z
                    then (List.nth_error vs (Z.to_nat (_ofs - ofs))) else ε)
  .
  Proof. refl. Qed.

  Definition points_to (loc: mblock * Z) (vs: list val): memRA := Auth.white (_points_to loc vs).

  (* Definition var_points_to (skenv: SkEnv.t) (var: gname) (v: val): memRA := *)
  (*   match (skenv.(SkEnv.id2blk) var) with *)
  (*   | Some  blk => points_to (blk, 0%Z) [v] *)
  (*   | None => ε *)
  (*   end. *)

  (* Lemma points_to_split *)
  (*       blk ofs hd tl *)
  (*   : *)
  (*     (points_to (blk, ofs) (hd :: tl)) = (points_to (blk, ofs) [hd]) ⋅ (points_to (blk, (ofs + 1)%Z) tl) *)
  (* . *)
  (* Proof. *)
  (*   ss. unfold points_to. unfold Auth.white. repeat (rewrite URA.unfold_add; ss). *)
  (*   f_equal. *)
  (*   repeat (apply func_ext; i). *)
  (*   des_ifs; bsimpl; des; des_sumbool; subst; ss; *)
  (*     try rewrite Z.leb_gt in *; try rewrite Z.leb_le in *; try rewrite Z.ltb_ge in *; try rewrite Z.ltb_lt in *; try lia. *)
  (*   - clear_tac. subst. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *. *)
  (*     assert(x0 = ofs). { lia. } subst. *)
  (*     rewrite Z.sub_diag in *. ss. *)
  (*   - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *. *)
  (*     destruct (Z.to_nat (x0 - ofs)) eqn:T; ss. *)
  (*     { exfalso. lia. } *)
  (*     rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss. *)
  (*   - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *. *)
  (*     destruct (Z.to_nat (x0 - ofs)) eqn:T; ss. *)
  (*     { exfalso. lia. } *)
  (*     rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss. *)
  (*   - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *. *)
  (*     assert(x0 = ofs). { lia. } subst. *)
  (*     rewrite Z.sub_diag in *. ss. *)
  (*   - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *. *)
  (*     destruct (Z.to_nat (x0 - ofs)) eqn:T; ss. *)
  (*     { exfalso. lia. } *)
  (*     rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss. *)
  (*   - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *. *)
  (*     assert(x0 = ofs). { lia. } subst. *)
  (*     rewrite Z.sub_diag in *. ss. *)
  (* Qed. *)

  (* Definition initial_mem_mr (csl: gname -> bool) (sk: Sk.t): _memRA := *)
  (*   fun blk ofs => *)
  (*     match List.nth_error sk blk with *)
  (*     | Some (g, gd) => *)
  (*       match gd with *)
  (*       | Sk.Gfun => ε *)
  (*       | Sk.Gvar gv => if csl g then if (dec ofs 0%Z) then Some (Vint gv) else ε else ε *)
  (*       end *)
  (*     | _ => ε *)
  (*     end. *)


(* Lemma points_tos_points_to *)
(*       loc v *)
(*   : *)
(*     (points_to loc v) = (points_tos loc [v]) *)
(* . *)
(* Proof. *)
(*   apply func_ext. i. *)
(*   apply prop_ext. *)
(*   ss. split; i; r. *)
(*   - des_ifs. ss. eapply Own_extends; et. rp; try refl. repeat f_equal. repeat (apply func_ext; i). *)
(*     des_ifs; bsimpl; des; des_sumbool; ss; clarify. *)
(*     + rewrite Z.sub_diag; ss. *)
(*     + rewrite Z.leb_refl in *; ss. *)
(*     + rewrite Z.ltb_ge in *. lia. *)
(*     + rewrite Z.ltb_lt in *. lia. *)
(*   - des_ifs. ss. eapply Own_extends; et. rp; try refl. repeat f_equal. repeat (apply func_ext; i). *)
(*     des_ifs; bsimpl; des; des_sumbool; ss; clarify. *)
(*     + rewrite Z.sub_diag; ss. *)
(*     + rewrite Z.ltb_lt in *. lia. *)
(*     + rewrite Z.leb_refl in *; ss. *)
(*     + rewrite Z.ltb_ge in *. lia. *)
(* Qed. *)

End POINTSTO.

Section RELTO.

  Context `{@GRA.inG memRACAP Σ}.

  Local Open Scope Z.

  Definition _relates_to (laddr: mblock * Z) (paddr: Z): _memRACAP :=
    let (b, ofs) := laddr in
    (fun _b => if (dec _b b) then OneShot.white (paddr - ofs) else ε).

  Lemma unfold_relates_to laddr paddr:
    _relates_to laddr paddr =
    let (b, ofs) := laddr in
    (fun _b => if (dec _b b) then OneShot.white (paddr - ofs) else ε).
  Proof. refl. Qed.

  Definition relates_to (laddr: mblock * Z) (paddr: Z) : memRACAP := Auth.white (_relates_to laddr paddr).

  Lemma dup_relates_to (laddr: mblock * Z) (paddr: Z) : (_relates_to laddr paddr) = (_relates_to laddr paddr) ⋅ (_relates_to laddr paddr).
  Proof.
    unfold _relates_to. destruct laddr. unfold _relates_to. repeat ur.
    apply func_ext. intros. des_ifs.
  Qed.
  
End RELTO.

Section SZOF.

  Context `{@GRA.inG memRASZ Σ}.

  Definition _size_of (loc: block * Z) (sz: Z) : _memRASZ :=
    let (b, ofs) := loc in
    (fun _b _ofs => if (dec _b b) && (dec _ofs ofs)
                 then Excl.just sz
                 else ε)
  .

  Lemma unfold_size_of laddr paddr:
    _size_of laddr paddr =
    let (b, ofs) := laddr in
    (fun _b => if (dec _b b) then OneShot.white (paddr - ofs) else ε).
  Proof. refl. Qed.

  Definition sz_of (loc: block * Z) (sz: Z) : iProp := OwnM (_sz_of loc sz).

End SZOF.

Notation "loc |-> vs" := (points_to loc vs) (at level 20).
Notation "loc ~~ z" := (relates_to loc z) (at level 25).
Notation "loc :== z" := (sz_of loc z) (at level 30).

Section AUX.
  Context `{@GRA.inG memRA Σ}.

  Lemma points_to_disj
        ptr x0 x1
    :
      (OwnM (ptr |-> [x0]) -∗ OwnM (ptr |-> [x1]) -* ⌜False⌝)
  .
  Proof.
    destruct ptr as [blk ofs].
    iIntros "A B". iCombine "A B" as "A". iOwnWf "A" as WF0.
    unfold points_to in WF0. rewrite ! unfold_points_to in *. repeat (ur in WF0); ss.
    specialize (WF0 blk ofs). des_ifs; bsimpl; des; des_sumbool; zsimpl; ss; try lia.
  Qed.

  Fixpoint is_list (ll: val) (xs: list val): iProp :=
    match xs with
    | [] => (⌜ll = Vnullptr⌝: iProp)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl]))
                             ** is_list ltl xtl: iProp)%I
    end
  .

  Lemma unfold_is_list: forall ll xs,
      is_list ll xs =
      match xs with
      | [] => (⌜ll = Vnullptr⌝: iProp)%I
      | xhd :: xtl =>
        (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl]))
                               ** is_list ltl xtl: iProp)%I
      end
  .
  Proof.
    i. destruct xs; auto.
  Qed.

  Lemma unfold_is_list_cons: forall ll xhd xtl,
      is_list ll (xhd :: xtl) =
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl]))
                             ** is_list ltl xtl: iProp)%I.
  Proof.
    i. eapply unfold_is_list.
  Qed.

  Lemma is_list_wf
        ll xs
    :
      (is_list ll xs) -∗ (⌜(ll = Vnullptr) \/ (match ll with | Vptr _ 0 => True | _ => False end)⌝)
  .
  Proof.
    iIntros "H0". destruct xs; ss; et.
    { iPure "H0" as H0. iPureIntro. left. et. }
    iDestruct "H0" as (lhd ltl) "[[H0 H1] H2]".
    iPure "H0" as H0. iPureIntro. right. subst. et.
  Qed.

  (* Global Opaque is_list. *)

  Context `{@GRA.inG memRACAP Σ}.

  (* Lemma dup_relates_to : forall loc addr, ((loc ~~ addr) -∗ ((loc ~~ addr) ** (loc ~~ addr))). *)
  (* Proof. *)
  (*   intros. unfold relates_to. unfold Auth.white.  *)
  (*   set (_relates_to _ _) at 2 3. *)
  (*   rewrite dup__relates_to. unfold c. *)
  (*   replace (Auth.frag (_relates_to loc addr ⋅ _relates_to loc addr)) with ((Auth.frag (_relates_to loc addr)) ⋅ (Auth.frag (_relates_to loc addr))) by repeat (ur;auto). *)
  (*   iIntros "A". iDestruct "A" as "[B C]". *)
  (*   iSplitL "B";iFrame. *)
  (* Qed. *)

  Lemma slide_relates_to : forall b ofs delta addr, (OwnM ((b, ofs) ~~ addr) -∗ OwnM((b, (ofs + delta)%Z) ~~ (addr + delta))).
  Proof.
    intros. unfold relates_to. unfold _relates_to.
    replace (addr + delta - (ofs + delta))%Z with (Z.sub addr ofs) by nia.
    auto.
  Qed.

End AUX.




Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition alloc_spec: fspec :=
    (mk_simple (fun sz => (
                    (ord_pure 0),
                    (fun varg => (⌜varg = [Vint (Z.of_nat sz)]↑ /\ (8 * (Z.of_nat sz) < modulus_64)%Z⌝: iProp)%I),
                    (fun vret => (∃ b, (⌜vret = (Vptr b 0)↑⌝)
                                         ** OwnM ((b, 0%Z) |-> (List.repeat Vundef sz))): iProp)%I
    ))).

  Definition free_spec: fspec :=
    (mk_simple (fun '(b, ofs) => (
                    (ord_pure 0),
                    (fun varg => (∃ v, (⌜varg = ([Vptr b ofs])↑⌝) ** OwnM ((b, ofs) |-> [v]))%I),
                    fun vret => ⌜vret = (Vint 0)↑⌝%I
    ))).

  Definition load_spec: fspec :=
    (mk_simple (fun '(b, ofs, v) => (
                    (ord_pure 0),
                    (fun varg => (⌜varg = ([Vptr b ofs])↑⌝) ** OwnM(((b, ofs) |-> [v]))),
                    (fun vret => OwnM((b, ofs) |-> [v]) ** ⌜vret = v↑⌝)
    ))).

  Definition store_spec: fspec :=
    (mk_simple
       (fun '(b, ofs, v_new) => (
            (ord_pure 0),
            (fun varg => (∃ v_old, (⌜varg = ([Vptr b ofs ; v_new])↑⌝) ** OwnM((b, ofs) |-> [v_old]))%I),
            (fun vret => OwnM((b, ofs) |-> [v_new]) ** ⌜vret = (Vint 0)↑⌝
    )))).

  Definition cmp_spec: fspec :=
    (mk_simple
       (fun '(result, resource) => (
            (ord_pure 0),
            (fun varg =>
               ((∃ b ofs v, ⌜varg = [Vptr b ofs; Vnullptr]↑⌝ ** ⌜resource = ((b, ofs) |-> [v])⌝ ** ⌜result = false⌝) ∨
                (∃ b ofs v, ⌜varg = [Vnullptr; Vptr b ofs]↑⌝ ** ⌜resource = ((b, ofs) |-> [v])⌝ ** ⌜result = false⌝) ∨
                (∃ b0 ofs0 v0 b1 ofs1 v1, ⌜varg = [Vptr b0 ofs0; Vptr b1 ofs1]↑⌝ ** ⌜resource = (((b0, ofs0) |-> [v0])) ⋅ ((b1, ofs1) |-> [v1])⌝ ** ⌜result = false⌝) ∨
                (∃ b ofs v, ⌜varg = [Vptr b ofs; Vptr b  ofs]↑⌝ ** ⌜resource = ((b, ofs) |-> [v])⌝ ** ⌜result = true⌝) ∨
                (⌜varg = [Vnullptr; Vnullptr]↑ /\ result = true⌝))
                 ** OwnM(resource)
            ),
            (fun vret => OwnM(resource) ** ⌜vret = (if result then Vint 1 else Vint 0)↑⌝)
    ))).

  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("alloc", alloc_spec) ; ("free", free_spec) ; ("load", load_spec) ; ("store", store_spec) ; ("cmp", cmp_spec)].
  Defined.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("alloc", mk_specbody alloc_spec (fun _ => trigger (Choose _)));
    ("free",   mk_specbody free_spec (fun _ => trigger (Choose _)));
    ("load",   mk_specbody load_spec (fun _ => trigger (Choose _)));
    ("store",  mk_specbody store_spec (fun _ => trigger (Choose _)));
    ("cmp",    mk_specbody cmp_spec (fun _ => trigger (Choose _)))
    ]
  .

  Variable csl: gname -> bool.

  Definition SMemSem (sk: Sk.t): SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    SModSem.initial_mr := (GRA.embed (Auth.black (initial_mem_mr csl sk)));
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SMem: SMod.t := {|
    SMod.get_modsem := SMemSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Mem: Mod.t := (SMod.to_tgt (fun _ => to_stb [])) SMem.

End PROOF.
Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
