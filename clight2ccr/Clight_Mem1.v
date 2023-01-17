 
Require Import Coqlib.
Require Import ITreelib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import ProofMode.
Require Import Any.
From compcert Require Import Ctypes Floats Integers Values Memory AST.
(* Require Import Any. *)
(* Require Import ModSem. *)
(* Require Import AList. *)

(*      AST Maps Globalenvs Memory Values Linking Integers. *)
(* From compcert Require Import *)
(*      Ctypes Clight. *)

Set Implicit Arguments.


Let _memRA: URA.t := (block ==> Z ==> (Excl.t memval))%ra.
Compute (URA.car (t:=_memRA)).
Instance memRA: URA.t := Auth.t _memRA.
Compute (URA.car).

Local Arguments Z.of_nat: simpl nomatch.

Section PROOF.
  Context `{@GRA.inG memRA Σ}.
  
 
  Definition _points_to (loc: block * Z) (vs: list memval): _memRA :=
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

  Definition points_to (loc: block * Z) (vs: list memval): memRA := Auth.white (_points_to loc vs).

  (** TODO-var **)
  (* Definition var_points_to (skenv: SkEnv.t) (var: gname) (v: val): memRA := *)
  (*   match (skenv.(SkEnv.id2blk) var) with *)
  (*   | Some  blk => points_to (Pos.of_nat blk, 0%Z) [v] *)
  (*   | None => ε *)
  (*   end. *)

  Lemma points_to_split
        blk ofs hd tl
    :
      (points_to (blk, ofs) (hd :: tl)) = (points_to (blk, ofs) [hd]) ⋅ (points_to (blk, (ofs + 1)%Z) tl)
  .
  Proof.
    ss. unfold points_to. unfold Auth.white. repeat (rewrite URA.unfold_add; ss).
    f_equal.
    repeat (apply func_ext; i).
    des_ifs; bsimpl; des; des_sumbool; subst; ss;
      try rewrite Z.leb_gt in *; try rewrite Z.leb_le in *; try rewrite Z.ltb_ge in *; try rewrite Z.ltb_lt in *; try lia.
    - clear_tac. subst. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss.
  Qed.
  
  Lemma _points_to_nil : forall blk ofs _b _ofs, _points_to (blk, ofs) [] _b _ofs = ε.
  Proof.
    intros. simpl. destruct ((ofs <=? _ofs) && (_ofs <? ofs + 0)) eqn : E; try nia.
    rewrite andb_false_r. auto.   
  Qed.

  Lemma points_to_nil : forall blk ofs, (points_to (blk, ofs) []) = ε.
  Proof.
    intros. unfold points_to. unfold _points_to.
    unfold Auth.white.
    assert (@eq (block -> Z -> @URA.car (Excl.t memval)) (λ (_b : block) (_ofs : Z),
                if dec _b blk && ((ofs <=? _ofs) && (_ofs <? ofs + @strings.length memval []))
                then @Excl.option_coercion memval (nth_error [] (Z.to_nat (_ofs - ofs)))
                else @URA.unit (Excl.t memval)) (λ (_ : block) (_ : Z), @URA.unit (Excl.t memval))).
    { apply func_ext. intros. apply func_ext. intros. simpl.
      replace ((ofs <=? x0) && (x0 <? ofs + 0)) with false by nia. rewrite andb_false_r. auto. }
    rewrite H0. auto.
  Qed.                                                            

  (** TODO-var **)
  (* Definition initial_mem_mr (csl: gname -> bool) (sk: Sk.t): _memRA := *)
  (*   fun blk ofs => *)
  (*     match List.nth_error sk (Pos.to_nat blk) with *)
  (*     | Some (g, gd) => *)
  (*       match gd with *)
  (*       | Sk.Gfun => ε *)
  (*       | Sk.Gvar gv => if csl g then if (dec ofs 0%Z) then Some (Vint (Int.repr gv)) else ε else ε *)
  (*       end *)
  (*     | _ => ε *)
  (*     end. *)

End PROOF.

Notation "loc |-> vs" := (points_to loc vs) (at level 20).


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

  (** TODO-is_list **)
  (* Fixpoint is_list (ll: val) (xs: list val): iProp := *)
  (*   match xs with *)
  (*   | [] => (⌜ll = Vnullptr⌝: iProp)%I *)
  (*   | xhd :: xtl => *)
  (*     (∃ lhd ltl, ⌜ll = Vptr lhd (Ptrofs.repr 0)⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                            ** is_list ltl xtl: iProp)%I *)
  (*   end *)
  (* . *)

  (* Lemma unfold_is_list: forall ll xs, *)
  (*     is_list ll xs = *)
  (*     match xs with *)
  (*     | [] => (⌜ll = Vnullptr⌝: iProp)%I *)
  (*     | xhd :: xtl => *)
  (*       (∃ lhd ltl, ⌜ll = Vptr lhd (Ptrofs.repr 0)⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                              ** is_list ltl xtl: iProp)%I *)
  (*     end *)
  (* . *)
  (* Proof. *)
  (*   i. destruct xs; auto. *)
  (* Qed. *)

  (* Lemma unfold_is_list_cons: forall ll xhd xtl, *)
  (*     is_list ll (xhd :: xtl) = *)
  (*     (∃ lhd ltl, ⌜ll = Vptr lhd (Ptrofs.repr 0)⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                            ** is_list ltl xtl: iProp)%I. *)
  (* Proof. *)
  (*   i. eapply unfold_is_list. *)
  (* Qed. *)

  (* Lemma is_list_wf *)
  (*       ll xs *)
  (*   : *)
  (*     (is_list ll xs) -∗ (⌜(ll = Vnullptr) \/ (match ll with | Vptr _ ofs => Ptrofs.eq ofs (Ptrofs.repr 0) | _ => False end)⌝) *)
  (* . *)
  (* Proof. *)
  (*   iIntros "H0". destruct xs; ss; et. *)
  (*   { iPure "H0" as H0. iPureIntro. left. et. } *)
  (*   iDestruct "H0" as (lhd ltl) "[[H0 H1] H2]". *)
  (*   iPure "H0" as H0. iPureIntro. right. subst. et. *)
  (* Qed. *)

  (* Global Opaque is_list. *)
  Definition encode_list chunk vlist : list memval := flat_map (encode_val chunk) vlist. 
  
  Definition is_arr (chunk : memory_chunk) (ll : val) (xs : list val) :=
    (∃ (b :block) (ofs : ptrofs),
        ⌜ll = Vptr b ofs⌝ ** OwnM ((b, Ptrofs.intval ofs) |-> (encode_list chunk xs)))%I.
End AUX.

Definition wordsize_64 := 64%nat.
Definition modulus_64 := two_power_nat wordsize_64.
Definition modulus_64_half := (modulus_64 / 2)%Z.
Definition max_64 := (modulus_64_half - 1)%Z.
Definition min_64 := (- modulus_64_half)%Z.

(* Definition intrange_64 : Z -> Prop := fun z => (min_64 <= z <= max_64)%Z. *)
(* Definition modrange_64 : Z -> Prop := fun z => (- 1 < z < modulus_64)%Z. *)
Definition intrange_64 : Z -> bool := fun z => (Z_le_gt_dec min_64 z) && (Z_le_gt_dec z max_64).
Definition modrange_64 : Z -> bool := fun z => (Z_le_gt_dec 0 z) && (Z_lt_ge_dec z modulus_64).


Ltac unfold_intrange_64 := unfold intrange_64, min_64, max_64 in *; unfold modulus_64_half, modulus_64, wordsize_64 in *.
Ltac unfold_modrange_64 := unfold modrange_64, modulus_64, wordsize_64 in *.

Section PROOF.
  Context `{@GRA.inG memRA Σ}.

 Definition alloc_spec: fspec :=
    (mk_simple (fun '(lo, hi) => (
                    (ord_pure 0%nat),
                    (fun varg => (⌜varg = (lo, hi)↑ /\ (lo <= hi)%Z⌝)%I),
                    (fun vret => (∃ b, (⌜vret = b↑⌝
                                      ** OwnM((b, lo) |-> (List.repeat Undef (Z.to_nat (hi - lo))))))%I
    )))).

  Definition free_spec: fspec :=
    (mk_simple (fun '() => (
                   (ord_pure 0%nat),
                   (fun varg => (∃ l b lo hi, (⌜varg = (b, lo, hi)↑ /\ Z.of_nat (List.length l) = hi - lo⌝) ** OwnM ((b, lo) |-> l))%I),
                    fun vret => ⌜vret = tt↑⌝%I
    ))).

  Definition load_spec: fspec :=
    (mk_simple (fun '(chunk, b, ofs, l) => (
                    (ord_pure 0%nat),
                    (fun varg => (⌜varg = (chunk, b, Ptrofs.repr ofs)↑⌝) ** OwnM((b, ofs) |-> l)%I),
                    (fun vret => (∃ v, OwnM((b, ofs) |-> l) ** ⌜vret = v↑ /\ decode_val chunk l = v⌝)%I)
    ))).

  Definition loadbytes_spec: fspec :=
    (mk_simple (fun '(b, ofs, n, l) => (
                    (ord_pure 0%nat),
                    (fun varg => (⌜varg = (b, Ptrofs.repr ofs, n)↑ /\ (Z.of_nat (List.length l) = n)⌝) ** OwnM(((b, ofs) |-> l))),
                    (fun vret => OwnM((b, ofs) |-> l) ** ⌜vret = l↑⌝)
    ))).

  Definition store_spec: fspec :=
    (mk_simple
       (fun '(chunk, b, ofs, v_new) => (
            (ord_pure 0%nat),
            (fun varg => (∃ l_old, (⌜varg = (chunk, b, Ptrofs.repr ofs, v_new)↑ /\ List.length l_old = size_chunk_nat chunk⌝) ** OwnM((b, ofs) |-> l_old))%I),
            (fun vret => (∃ l_new, OwnM((b, ofs) |-> l_new) ** ⌜vret = tt↑ /\ encode_val chunk v_new = l_new⌝)%I)
    ))).

  Definition storebytes_spec: fspec :=
    (mk_simple
       (fun '(b, ofs, l_new) => (
            (ord_pure 0%nat),
            (fun varg => (∃ l_old, (⌜varg = (b, ofs, l_new)↑ /\ List.length l_old = List.length l_new⌝) ** OwnM((b, ofs) |-> l_old))%I),
            (fun vret => OwnM((b, ofs) |-> l_new) ** ⌜vret = tt↑⌝)
    ))).

  Definition valid_pointer_spec: fspec :=
    (mk_simple
       (fun '(result, resource) => (
            (ord_pure 0%nat),
            (fun varg =>
               ((∃ b ofs v, ⌜varg = (b, ofs)↑⌝ ** ⌜resource = ((b, ofs) |-> [v])⌝ ** ⌜result = true⌝) ∨
                (∃ b ofs v, ⌜varg = (b, ofs)↑⌝ ** ⌜resource <> ((b, ofs) |-> [v])⌝ ** ⌜result = false⌝))
                 ** OwnM(resource)
            ),
            (fun vret => OwnM(resource) ** ⌜vret = result↑⌝)
    ))).

  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("alloc", alloc_spec); ("free", free_spec); ("load", load_spec);
           ("loadbytes", loadbytes_spec); ("store", store_spec); ("storebytes", storebytes_spec);
           ("valid_pointer", valid_pointer_spec)].
  Defined.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("alloc", mk_specbody alloc_spec (fun _ => trigger (Choose _)));
    ("free",   mk_specbody free_spec (fun _ => trigger (Choose _)));
    ("load",   mk_specbody load_spec (fun _ => trigger (Choose _)));
    ("loadbytes",   mk_specbody loadbytes_spec (fun _ => trigger (Choose _)));
    ("store",  mk_specbody store_spec (fun _ => trigger (Choose _)));
    ("storebytes",   mk_specbody storebytes_spec (fun _ => trigger (Choose _)));
    ("valid_pointer",   mk_specbody valid_pointer_spec (fun _ => trigger (Choose _)))
    ]
  .

  Variable csl: gname -> bool.

  Definition SMemSem (sk: Sk.t): SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    (* SModSem.initial_mr := (GRA.embed (Auth.black (initial_mem_mr csl sk))); *)
    SModSem.initial_mr := (GRA.embed (Auth.black ε));
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
