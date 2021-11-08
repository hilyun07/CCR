Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ProofMode.
Require Import Mem1.

Set Implicit Arguments.


Module AppRA.
Section AppRA.

Variant car: Type :=
| half (usable: bool)
| full
| boom
| unit
.

Let add := fun a0 a1 => match a0, a1 with
                                    | half true, half true => full
                                    | half false, half false => full
                                    | _, unit => a0
                                    | unit, _ => a1
                                    | _, _ => boom
                                    end.
Let wf := fun a => match a with | boom => False | _ => True end.

Program Instance t: URA.t := {
  car := car;
  unit := unit;
  _add := add;
  _wf := wf;
}
.
Next Obligation. subst add wf. i. destruct a, b; ss; des_ifs; ss. Qed.
Next Obligation. subst add wf. i. destruct a, b; ss; des_ifs; ss. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.
Next Obligation. subst add wf. i. unseal "ra". ss. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.

End AppRA.
End AppRA.

Definition Init: AppRA.t := AppRA.half false.
Definition InitX: AppRA.t := AppRA.half false.
Definition Run: AppRA.t := AppRA.half true.
Definition RunX: AppRA.t := AppRA.half true.


(*** simpl RA ***)
Instance spRA: URA.t := Auth.t (Excl.t unit).
Definition sp_white: spRA := @Auth.white (Excl.t unit) (Some tt).
Definition sp_black: spRA := @Auth.black (Excl.t unit) (Some tt).



(*** MW RA ***)
(* Instance _mwRA: URA.t := (Z ==> (Excl.t Z))%ra. *)
Instance _mwRA: URA.t := Excl.t (Z -> option Z)%ra.
Instance mwRA: URA.t := Auth.t _mwRA%ra.
Definition mw_state (f: Z -> option Z): mwRA := @Auth.white _mwRA (Some f).
Definition mw_stateX (f: Z -> option Z): mwRA := @Auth.black _mwRA (Some f).

Lemma _mw_state_false: forall f g, ~ URA.wf (mw_state f ⋅ mw_state g).
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *.
  rr in H. ur in H. rewrite Seal.sealing_eq in *. rr in H. ss.
Qed.

Lemma _mw_stateX_false: forall f g, ~ URA.wf (mw_stateX f ⋅ mw_stateX g).
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *. ss.
Qed.

Lemma _mw_state_eq: forall f g, URA.wf (mw_state f ⋅ mw_stateX g) -> f = g.
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *. des. rr in H. des. ur in H. des_ifs.
Qed.

Lemma _mw_state_upd: forall f g h, URA.updatable (mw_state f ⋅ mw_stateX g) (mw_state h ⋅ mw_stateX h).
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *. des_ifs.
  rr. ur. rewrite Seal.sealing_eq in *. des; ss. rr in H. ur in H. des. des_ifs.
  esplits; ss.
  { rr. esplits; et. ur. instantiate (1:=Excl.unit). ss. }
  { ur. ss. }
Qed.

Section PROOF.
  Context `{@GRA.inG mwRA Σ}.
  Lemma mw_state_false: forall f g, (OwnM (mw_state f) ⊢ OwnM (mw_state g) -* ⌜False⌝)%I.
  Proof.
    i. iIntros "A B". iCombine "A B" as "A". iOwnWf "A". exfalso. eapply _mw_state_false; et.
  Qed.
  Lemma mw_stateX_false: forall f g, (OwnM (mw_stateX f) ⊢ OwnM (mw_stateX g) -* ⌜False⌝)%I.
  Proof.
    i. iIntros "A B". iCombine "A B" as "A". iOwnWf "A". exfalso. eapply _mw_stateX_false; et.
  Qed.
  Lemma mw_state_eq: forall f g, (OwnM (mw_state f) ⊢ OwnM (mw_stateX g) -* ⌜f = g⌝)%I.
  Proof.
    i. iIntros "A B". iCombine "A B" as "A". iOwnWf "A". iPureIntro. eapply _mw_state_eq; et.
  Qed.
  Lemma mw_state_upd: forall f g h, (OwnM (mw_state f) ⊢ OwnM (mw_stateX g) -* #=> (OwnM (mw_state h) ** OwnM (mw_stateX h)))%I.
  Proof.
    i. iIntros "A B". iCombine "A B" as "A". iPoseProof (OwnM_Upd with "A") as "B".
    { eapply _mw_state_upd; et. }
    iMod "B". iModIntro. iDestruct "B" as "[A B]". iFrame.
  Qed.
End PROOF.



(* Definition _mapRA: URA.t := (mblock ==> (Excl.t (list (Z * Z))))%ra. *)
Definition _mapRA: URA.t := (mblock ==> (Excl.t (Z -> option Z)))%ra.
Instance mapRA: URA.t := Auth.t _mapRA.
Definition _is_map (h: mblock) (map: (Z -> option Z)): _mapRA :=
  (fun _h => if (dec _h h) then Some map else ε)
.
Definition is_map (h: mblock) (map: (Z -> option Z)): mapRA := Auth.white (_is_map h map).







Section PROOF.
  Context `{@GRA.inG AppRA.t Σ}.
  Context `{@GRA.inG mwRA Σ}.
  Context `{@GRA.inG spRA Σ}.

  Definition mk_simple_frame {X: Type} (PQ: X -> ((Any.t -> ord -> iProp) * (Any.t -> iProp))): fspec :=
    mk_simple (fun '(FRAME, x) => let '(P, Q) := (PQ x) in
                                  (fun varg ord => FRAME ** P varg ord, fun vret => FRAME ** Q vret))
  .

  (******************************* MW ****************************)
  Definition main_spec: fspec :=
    mk_simple (fun (_: unit) =>
                 ((fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Init
                                   ** OwnM (mw_stateX Maps.empty) ** OwnM sp_white),
                  (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run ** OwnM sp_white))).

  Definition loop_spec: fspec :=
    mk_simple (fun f =>
                 ((fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Run
                                        ** OwnM (mw_state f) ** OwnM sp_white ∧ ⌜f 0 = Some 42%Z⌝),
                  (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run ** OwnM (mw_state f) ** OwnM sp_white))).

  Definition put_spec: fspec :=
    mk_simple (fun '(f, k, v) =>
                 ((fun varg o => ⌜varg = [Vint k; Vint v]↑ ∧ intrange_64 k ∧ intrange_64 v ∧ o = ord_top⌝ ** OwnM (mw_state f) ** OwnM sp_white),
                  (fun vret => OwnM (mw_state (add k v f)) ** OwnM sp_white)))
  .

  Definition get_spec: fspec :=
    mk_simple (fun '(f, k, v) =>
                 ((fun varg o => ⌜varg = [Vint k]↑ ∧ intrange_64 k ∧ f k = Some v ∧ o = ord_top⌝ ** OwnM (mw_state f) ** OwnM sp_white),
                  (fun vret => ⌜vret = (Vint v)↑⌝ ** OwnM (mw_state f) ** OwnM sp_white)))
  .

  Definition MWStb: alist gname fspec.
    eapply (Seal.sealing "stb").
    eapply [("main",main_spec); ("loop",loop_spec); ("put",put_spec); ("get",get_spec)].
  Defined.




  (******************************* App ****************************)
  (* Definition init_spec0: fspec := *)
  (*   mk_simple (fun (_: unit) => ( *)
  (*                  (fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Init), *)
  (*                  (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run))). *)

  (* Definition run_spec0: fspec := *)
  (*   mk_simple (fun (_: unit) => ( *)
  (*                  (fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Run), *)
  (*                  (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run))). *)

  Definition init_spec1: fspec :=
    mk_simple (fun f => ((fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Init ** OwnM (mw_state f)),
                         (fun vret => OwnM Run ** OwnM (mw_state (add 0%Z 42%Z f))))).

  Definition run_spec1: fspec :=
    mk_simple (fun f => ((fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Run ** OwnM (mw_state f) ∧ ⌜f 0 = Some 42%Z⌝),
                         (fun vret => OwnM Run ** OwnM (mw_state f) ∧ ⌜f 0 = Some 42%Z⌝))).

  Definition AppStb: alist gname fspec.
    eapply (Seal.sealing "stb").
    eapply [("init",init_spec1); ("run",run_spec1)].
  Defined.



  (******************************* Map ****************************)
  Context `{@GRA.inG mapRA Σ}.

  Definition new_spec: fspec :=
    (mk_simple (fun (_: unit) => (
                    (fun varg o => (⌜varg = ([]: list val)↑ ∧ o = ord_pure 0⌝: iProp)%I),
                    (fun vret => (∃ h, ⌜vret = (Vptr h 0)↑⌝ ** OwnM(is_map h (fun _ => None)): iProp)%I)
    )))
  .

  Definition update_spec: fspec :=
    mk_simple (fun '(h, k, v, m) =>
                 ((fun varg o => (⌜varg = ([Vptr h 0%Z; Vint k; Vint v]: list val)↑ ∧ o = ord_pure 1⌝ **
                                   OwnM (is_map h m))%I),
                  (fun vret => ⌜vret = Vundef↑⌝ **  OwnM (is_map h (Maps.add k v m))))).

  Definition access_spec: fspec :=
    mk_simple (fun '(h, k, v, m) =>
                 ((fun varg o => ⌜varg = ([Vptr h 0%Z; Vint k]: list val)↑ ∧ o = ord_pure 1 ∧ m k = Some v⌝ **
                                  OwnM (is_map h m)),
                  (fun vret => ⌜vret = (Vint v)↑⌝ ** (OwnM (is_map h m))))).

  Definition MapStb: alist gname fspec.
    eapply (Seal.sealing "stb").
    eapply [("new",new_spec); ("update",update_spec); ("access",access_spec)].
  Defined.





  Definition fspec_mw1: fspec :=
    mk_fspec (meta:=unit) (fun _ _ argh argl o => (⌜argh = argl ∧ o = ord_top⌝ ** OwnM (sp_white))%I)
             (fun _ _ reth retl => (⌜reth = retl⌝ ** OwnM (sp_white))%I)
  .

  (******************************* Dedicated STB for MW1 ****************************)
  Context `{@GRA.inG memRA Σ}.

  Definition MW1Stb: alist gname fspec.
    eapply (Seal.sealing "stb").
    eapply [("main", fspec_mw1); ("loop", fspec_mw1); ("put", fspec_mw1); ("get", fspec_mw1);
            ("init", fspec_trivial); ("run", fspec_trivial);
            ("new", fspec_trivial); ("access", fspec_trivial); ("update", fspec_trivial);
            ("alloc", alloc_spec); ("free", free_spec); ("load", load_spec); ("store", store_spec); ("cmp", cmp_spec)].
   Defined.

End PROOF.
Global Hint Unfold MWStb MW1Stb AppStb MapStb: stb.



Definition set `{Dec K} V (k: K) (v: V) (f: K -> V): K -> V := fun k0 => if dec k k0 then v else f k0.



Section PROOF.
  Context `{Σ: GRA.t}.
  
  Lemma Own_unit
    :
      bi_entails True%I (Own ε)
  .
  Proof.
    red. uipropall. ii. rr. esplits; et. rewrite URA.unit_idl. refl.
  Qed.

  Context `{@GRA.inG M Σ}.

  Lemma embed_unit
    :
      (GRA.embed ε) = ε
  .
  Proof.
    unfold GRA.embed.
    Local Transparent GRA.to_URA. unfold GRA.to_URA. Local Opaque GRA.to_URA.
    Local Transparent URA.unit. unfold URA.unit. Local Opaque URA.unit.
    cbn.
    apply func_ext_dep. i.
    dependent destruction H. ss. rewrite inG_prf. cbn. des_ifs.
  Qed.

End PROOF.

Section PROOF.
  Context `{@GRA.inG M Σ}.

  Lemma OwnM_unit
    :
      bi_entails True%I (OwnM ε)
  .
  Proof.
    unfold OwnM. r. uipropall. ii. rr. esplits; et. rewrite embed_unit. rewrite URA.unit_idl. refl.
  Qed.
End PROOF.


Ltac get_fresh_string :=
  match goal with
  | |- context["A"] =>
    match goal with
    | |- context["A0"] =>
      match goal with
      | |- context["A1"] =>
        match goal with
        | |- context["A2"] =>
          match goal with
          | |- context["A3"] =>
            match goal with
            | |- context["A4"] =>
              match goal with
              | |- context["A5"] => fail 5
              | _ => constr:("A5")
              end
            | _ => constr:("A4")
            end
          | _ => constr:("A3")
          end
        | _ => constr:("A2")
        end
      | _ => constr:("A1")
      end
    | _ => constr:("A0")
    end
  | _ => constr:("A")
  end
.
Ltac iDes :=
  repeat multimatch goal with
         | |- context[@environments.Esnoc _ _ (INamed ?namm) ?ip] =>
           match ip with
           | @bi_or _ _ _ =>
             let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ "|" +:+ namm +:+ "]")) in
             iDestruct namm as pat
           | @bi_pure _ _ => iDestruct namm as "%"
           | @iNW _ ?newnamm _ => iEval (unfold iNW) in namm; iRename namm into newnamm
           | @bi_sep _ _ _ =>
             let f := get_fresh_string in
             let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ " " +:+ f +:+ "]")) in
             iDestruct namm as pat
           | @bi_exist _ _ (fun x => _) =>
             let x := fresh x in
             iDestruct namm as (x) namm
           end
         end
.
Ltac iCombineAll :=
  repeat multimatch goal with
         | |- context[@environments.Esnoc _ (@environments.Esnoc _ _ (INamed ?nam1) _) (INamed ?nam2) _] =>
           iCombine nam1 nam2 as nam1
         end
.
Ltac xtra := iCombineAll; iAssumption.

(*** TODO: MOVE TO ImpPrelude ***)
Definition add_ofs (ptr: val) (d: Z): val :=
  match ptr with
  | Vptr b ofs => Vptr b (ofs + d)
  | _ => Vundef
  end
.

Lemma scale_int_8 n: scale_int (8 * n) = Some n.
Proof.
  unfold scale_int. des_ifs.
  - rewrite Z.mul_comm. rewrite Z.div_mul; ss.
  - contradict n0. eapply Z.divide_factor_l.
Qed.
