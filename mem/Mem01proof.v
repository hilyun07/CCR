Require Import Mem0 Mem1 SimModSem HoareDef.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



(*** black + delta --> new_black ***)
Definition add_delta_to_black `{M: URA.t} (b: URA.auth_t) (w: URA.auth_t): URA.auth_t :=
  match b, w with
  | URA.excl e _, URA.frag f1 => URA.excl (URA.add e f1) URA.unit
  | _, _ => URA.boom
  end
.


(* Notation "wf n *)
(* '------------------------------------------------------------------' *)
(* src0 tgt0 *)
(* '------------------------------------------------------------------' *)
(* src1 tgt1 *)
(* '------------------------------------------------------------------' *)
(* src2 tgt2" := *)
(*   (sim_itree wf n (([(_, src0)], src1), src2) (([(_, tgt0)], tgt1), tgt2)) *)
(*     (at level 60, *)
(*      format "wf  n '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src0 '//' *)
(* tgt0 '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src1 '//' *)
(* tgt1 '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src2 '//' '//' '//' *)
(* tgt2 '//' *)
(* "). *)
(******** TODO: it works in emacs but fails in coqc -- try coq 8.13 and uncomment it ***********)

Notation "wf n
'------------------------------------------------------------------'
src0 tgt0
'------------------------------------------------------------------'
src1 tgt1
'------------------------------------------------------------------'
src2 tgt2" :=
  (gpaco3 (_sim_itree wf) _ _ _ n (([(_, src0)], src1), src2) (([(_, tgt0)], tgt1), tgt2))
    (at level 60,
     format "wf  n '//'
'------------------------------------------------------------------' '//'
src0 '//'
tgt0 '//'
'------------------------------------------------------------------' '//'
src1 '//'
tgt1 '//'
'------------------------------------------------------------------' '//'
src2 '//' '//' '//'
tgt2 '//'
").



Ltac go := try first[pfold; econs; [..|M]; (Mskip ss); et; check_safe; ii; left|
                     pfold; econsr; [..|M]; (Mskip ss); et; check_safe; ii; left].
Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau;
                    try rewrite interp_vis;
                    try rewrite interp_ret;
                    try rewrite interp_tau;
                    try rewrite interp_trigger
                   ).
Ltac force_l := pfold; econs; [..|M]; Mskip ss; et.
Ltac force_r := pfold; econsr; [..|M]; Mskip ss; et.
Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ} `{@GRA.inG (RA.excl Mem.t) Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  (* Eval compute in (@RA.car (RA.excl Mem.t)). *)
  Eval compute in (@RA.car Mem1._memRA).
  Inductive sim_loc: option val -> (option val + unit) -> Prop :=
  | sim_loc_present v: sim_loc (Some v) (inl (Some v))
  | sim_loc_absent: sim_loc None (inr tt)
  .

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists mem_src (mem_tgt: Mem.t),
        (<<SRC: mrps_src0 = Maps.add "Mem" ((GRA.padding ((URA.black mem_src): URA.car (t:=Mem1.memRA))), tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "Mem" (ε, mem_tgt↑) Maps.empty>>) /\
        (<<SIM: forall b ofs, sim_loc ((mem_tgt.(Mem.cnts)) b ofs) (mem_src b ofs)>>) /\
        (<<NULLPTR: mem_src 0%nat 0%Z = inl (Some Vundef)>>)
  .

  Local Opaque points_to.
  
  Hint Resolve sim_itree_mon: paco.

  Theorem correct: ModSemPair.sim Mem1.MemSem Mem0.MemSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. esplits; ss; et. ii.
      destruct (classic (b = 0%nat /\ ofs = 0%Z)).
      - des. subst. ss. unfold update. des_ifs. econs.
      - des_ifs; bsimpl; des; des_sumbool; ss; try rewrite Nat.eqb_neq in *; try rewrite Z.eqb_neq in *;
          apply_all_once Nat.eqb_eq; apply_all_once Z.eqb_eq; subst; try lia.
        + unfold update. des_ifs; econs; et.
        + unfold update. des_ifs; econs; et.
    }
    econs; ss.
    { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      ginit. { eapply cpn3_wcompat; eauto with paco. } unfold alist_add, alist_remove; ss.
      unfold Mem0.allocF.
      unfold fun_to_tgt, cfun, HoareFun. ss.
      Set Printing All.
      TTTTTTTTTTTTTTTTTTTTTTTTTTTT
      gstep.
      Ltac _step :=
        gstep; econs.
      gstep. eapply sim_itree_mon. econs; eauto. i.
      gstep.
      _step.
      match goal with
      | [ |- (gpaco3 (_sim_itree wf) _ _ _ _ (_, ?itr_src) (_, ?itr_tgt))] =>
        idtac
      end.
      (* Opaque MemStb. *)
      (* Opaque mapi. *)
      Local Opaque URA.add.
      pfold. econs; eauto. ii. ss. left.
      match goal with
      | [ |- paco3 (_sim_itree ?wf) bot3 _ _ _ ] =>
        replace (paco3 (_sim_itree wf) bot3) with (sim_itree wf) by ss
      end
   .
      fold.
      replace (paco3 (_sim_itree wf) bot3) with (sim_itree wf) by ss.

      go. ss. rename x into sz.
      unfold assume.
      igo.
      go. clarify. unfold HoareFun. go. rename x into rarg_src.
      unfold assume.
      igo.
      repeat go. clear_tac.
      Opaque URA.add.
      unfold unpadding, assume.
      igo.
      pfold. econsr; et. esplits; et. left.
      igo. des_ifs.
      unfold unwrapU. des_ifs. igo. des_ifs. unfold MPut. igo. repeat go.
      ss. clarify.
      force_r. esplits; ss. left.
      go. igo.
      go. igo.
      Hint Unfold alist_add.
      u.
      Hint Unfold body_to_tgt interp_hCallE_tgt.
      u. igo.
      Local Opaque MemStb.
      cbn.
      set (blk := (Mem.nb mem_tgt)) in *.
      force_l. exists (Vptr (Mem.nb mem_tgt) 0). left.
      igo. go.
      force_l.
      set (mem_src_new := add_delta_to_black
                            (* (URA.excl (mem_src: URA.car (t:=Mem1._memRA)) frag) *)
                            (URA.black (mem_src: URA.car (t:=Mem1._memRA)))
                            (points_tos (blk, 0%Z) (repeat (Vint 0) sz))).
      eexists (GRA.padding (mem_src_new: URA.car (t:=Mem1.memRA)),
               GRA.padding (points_tos (blk, 0%Z) (repeat (Vint 0) sz))). left.
      igo. force_l.
      {
        replace (fun k => URA.unit) with (URA.unit (t:=Σ)) by ss.
        rewrite URA.unit_idl.
        rewrite GRA.padding_add.
        rewrite <- URA.unit_id.
        apply URA.updatable_add; cycle 1.
        { apply URA.updatable_unit. }
        eapply GRA.padding_updatable.
        subst mem_src_new. des_ifs.
        ss. clarify.
        rewrite <- Heq.
        Local Transparent points_tos.
        replace ((fun _ _ => @inr (option val) unit tt)) with (URA.unit (t:=Mem1._memRA)) by ss.
        replace (URA.excl ((mem_src: URA.car (t:=Mem1._memRA)) ⋅ f) URA.unit) with
            (URA.black ((mem_src: URA.car (t:=Mem1._memRA)) ⋅ f)) by ss.
        rewrite Heq.
        eapply URA.auth_alloc2.

        clear - WF Heq SIM.
        { ss. intros b ofs. des_ifs. ss.

          assert(WF0: URA.wf ((GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA))))
                                ⋅ (URA.unit ⋅ (rarg_src: URA.car (t:=GRA.to_URA Σ))))).
          { ss. }
          eapply URA.wf_mon in WF0.
          eapply GRA.padding_wf in WF0.

          unfold URA.white in *. clarify.
          subst blk.
          Local Transparent URA.add.
          ss. des_ifs.
          - bsimpl; des; des_sumbool; clarify.
            admit "ez: Heq is wrong. Add mem tgt is wf (nb is actually nb); use sim_loc.".
          - des. specialize (WF1 b ofs). bsimpl; des; des_sumbool; clarify; des_ifs.
          - des. specialize (WF1 b ofs). bsimpl; des; des_sumbool; clarify; des_ifs.
            apply_all_once Z.leb_le. apply_all_once Z.ltb_lt.
            intro A. apply nth_error_None in A. rewrite repeat_length in *.
            apply inj_le in A. rewrite Z2Nat.id in A; cycle 1.
            { lia. }
            lia.
        }
      }
      left.
      force_l. eexists. left.
      unfold guarantee. igo.
      force_l. esplits; et. left.
      Local Opaque add_delta_to_black.
      pfold; econs; try (by ss).
      { instantiate (1:= GRA.padding _). rewrite GRA.padding_add. rewrite URA.unit_idl. f_equal. }
      left.
      pfold; econs; ss; et.
      {
        rr. unfold alist_add. ss. esplits; ss; et.
        { unfold mem_src_new.
          Local Transparent add_delta_to_black.
          ss.
        }
        ii. ss.
        subst mem_src_new.
        assert(b <> blk).
        {admit "should be ez". }
        hexploit (SIM b ofs); et. intro A. inv A.
        {
          des_ifs; bsimpl; des; des_sumbool; clarify.
          - unfold update. des_ifs. rewrite <- H3. econs.
          - unfold update. des_ifs. rewrite <- H3. econs.
          - unfold update. des_ifs. rewrite <- H3. econs.
        }
        {
          des_ifs; bsimpl; des; des_sumbool; clarify.
          - unfold update. des_ifs. rewrite <- H3. econs.
          - unfold update. des_ifs. rewrite <- H3. econs.
          - unfold update. des_ifs. rewrite <- H3. econs.
        }
      }
    }
    econs.
    { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      u.
      unfold Mem0.freeF.
      Local Opaque URA.add.
      go. ss. destruct x as [b ofs].
      unfold assume.
      igo.
      repeat (go; igo). des; clarify.
      replace ((fun k => URA.unit): URA.car (t:=Σ))  with (URA.unit: URA.car (t:=Σ)) in WF by ss.
      rewrite URA.unit_idl in WF.
      rewrite GRA.padding_add in WF. apply GRA.padding_wf in WF. des.
      Local Opaque URA.wf.
      Hint Unfold handle_hCallE_tgt.
      u. igo. ss.
      force_l. eexists (Vint 0). left.
      repeat (go; igo).
      force_r. eexists. left.
      repeat (go; igo).
      force_r. esplits; et. left.
      assert(A: mem_src b ofs = inl (Some v)).
      {
        Local Transparent URA.wf.
        ss. des_ifs. des. specialize (WF0 b ofs).
        Local Transparent URA.add.
        clear SIM.
        ss. clarify. rr in WF. des. clarify. ss. des_ifs.
        - bsimpl; des; des_sumbool; ss.
        - bsimpl; des; des_sumbool; ss.
      }
      Local Opaque URA.wf.
      Local Opaque URA.add.
      hexploit (SIM b ofs); et. intro B. rewrite A in *. inv B.
      unfold unwrapU. des_ifs; cycle 1.
      {exfalso. unfold Mem.free in *. des_ifs. }
      repeat (igo; go).
      unfold MPut.
      repeat (igo; go).
      u.
      set (mem_src' := fun _b _ofs => if dec _b b && dec _ofs ofs then inr () else mem_src _b _ofs).
      assert(WF': URA.wf (mem_src': URA.car (t:=Mem1._memRA))).
      { Local Transparent URA.wf.
        Local Transparent URA.add.
        ss. ii. des_ifs.
        ss. clarify.
        subst mem_src'. ss. des_ifs. des. specialize (WF0 k k0). bsimpl. des; des_sumbool; des_ifs.
        Local Opaque URA.wf.
        Local Opaque URA.add.
      }
      rename t into mem_tgt'.
      assert(SIM': forall b ofs, sim_loc (Mem.cnts mem_tgt' b ofs) (mem_src' b ofs)).
      { i.
        unfold Mem.free in Heq. des_ifs. ss.
        subst mem_src'. ss.
        destruct (classic (b = b0 /\ ofs = ofs0)); des; clarify.
        - unfold update. des_ifs. econs.
        - des_ifs.
          { Psimpl. bsimpl; des; des_sumbool; ss; clarify. }
          replace (update (Mem.cnts mem_tgt) b (update (Mem.cnts mem_tgt b) ofs None) b0 ofs0) with
              (Mem.cnts mem_tgt b0 ofs0); cycle 1.
          { unfold update. des_ifs. Psimpl. des_ifs; bsimpl; des; des_sumbool; ss; clarify. }
          et.
      }
      force_l.
      eexists ((GRA.padding (URA.black (mem_src': URA.car (t:=Mem1._memRA)))), URA.unit: URA.car (t:=Σ)). left.
      force_l.
      { replace (fun k => URA.unit) with (URA.unit: URA.car (t:=Σ)) by ss.
        rewrite URA.unit_id. rewrite URA.unit_idl.
        rewrite GRA.padding_add. apply GRA.padding_updatable.
        apply URA.auth_dealloc.
        clear - WF' WF.
        r. i. rewrite URA.unit_idl.
        ss. destruct H; clear H. (*** coq bug; des infloops ***) des. clarify.
        esplits; et.
        apply func_ext. intro _b. apply func_ext. intro _ofs.
        destruct (classic (b = _b /\ ofs = _ofs)).
        - destruct H; clear H. clarify.
          subst mem_src'. ss. des_ifs; bsimpl; des; des_sumbool; clarify.
          clear - H0.
          Local Transparent URA.wf.
          Local Transparent URA.add.
          specialize (H0 _b _ofs). ss. des_ifs; bsimpl; des; des_sumbool; clarify. des_u. ss.
        - Psimpl.
          subst mem_src'. s. des_ifs; bsimpl; des; des_sumbool; clarify.
          destruct H; clear H; des; clarify.
          Local Opaque URA.wf.
          Local Opaque URA.add.
      }
      left. u.
      force_l. exists (URA.unit: URA.car (t:=Σ)). left.
      unfold guarantee.
      igo. force_l. esplits; et. left.
      force_l.
      { rewrite URA.unit_idl. ss. }
      left.
      pfold; econs; et.
      ss.
      esplits; ss; et.
    }
    Local Opaque GRA.to_URA.
    Local Opaque points_to.
    Local Opaque URA.add.
    Local Opaque URA.wf.
    econs.
    { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      u.
      unfold Mem0.loadF.
      go. ss. destruct x as [[b ofs] v].
      unfold assume.
      igo.
      repeat (go; igo). des_ifs. des; clarify. ss. rewrite URA.unit_idl in *.
      rewrite GRA.padding_add in WF. apply GRA.padding_wf in WF. des.
      Hint Unfold handle_hCallE_tgt.
      u. igo. ss.
      force_l. eexists _. left.
      repeat (go; igo).
      force_r. eexists. left.
      repeat (go; igo).
      force_r. esplits; et. left.
      force_l. eexists (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA))),
                        GRA.padding ((b, ofs) |-> v)). left.
      force_l. esplits; et. left.
      force_l. esplits; et. left.
      unfold guarantee.
      repeat (go; igo).
      force_l. esplits; et. left.
      force_l. { rewrite URA.unit_idl; refl. } left.
      Local Transparent URA.wf.
      Local Transparent URA.add.
      Local Transparent GRA.to_URA.
      Local Transparent points_to.
      ss. des_ifs. des; ss. do 2 spc WF0. des_ifs; cycle 1.
      { exfalso. rr in WF. des. ss. des_ifs. do 2 spc SIM. des_ifs. bsimpl; des; des_sumbool; ss. }
      destruct o; ss.
      assert(v0 = v).
      { rr in WF. des. ss. des_ifs. do 2 spc SIM. des_ifs. bsimpl; des; des_sumbool; ss. }
      clarify.
      unfold unwrapU. unfold Mem.load. exploit SIM; et. intro T. rewrite Heq in *. inv T.
      pfold. econs; et.
      rr. esplits; ss; et.
    }
    Local Opaque GRA.to_URA.
    Local Opaque points_to.
    Local Opaque URA.add.
    Local Opaque URA.wf.
    econs; et.
    { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      u.
      unfold Mem0.storeF.
      go. ss. destruct x as [[b ofs] v].
      set (mem_src' := fun _b _ofs => if dec _b b && dec _ofs ofs then inl (Some v) else mem_src _b _ofs).
      unfold assume.
      igo.
      repeat (go; igo). des_ifs. des; clarify. ss. rewrite URA.unit_idl in *.
      rewrite GRA.padding_add in WF. apply GRA.padding_wf in WF. des.
      Hint Unfold handle_hCallE_tgt.
      u. igo. ss.
      force_l. eexists _. left.
      repeat (go; igo).
      force_r. eexists. left.
      repeat (go; igo).
      force_r. esplits; et. left.
      force_l. eexists (GRA.padding (URA.black (mem_src': URA.car (t:=Mem1._memRA))),
                        GRA.padding ((b, ofs) |-> v)). left.
      assert(WF0: URA.wf (mem_src': URA.car (t:=Mem1._memRA))).
      { Local Transparent URA.wf.
        clear - WF. apply URA.wf_mon in WF. ss. des.
        ii. specialize (WF0 k k0). des_ifs_safe. unfold mem_src' in *. des_ifs.
        Local Opaque URA.wf.
      }
      force_l.
      { rewrite ! GRA.padding_add. eapply GRA.padding_updatable.
        clear - WF WF0. clear WF.
        Local Transparent URA.add GRA.to_URA points_to URA.wf.
        eapply URA.auth_update; et.
        rr. ii. destruct H; clear H. (*** FIXME: des runs infloop ***)
        des. subst. esplits; et.
        subst mem_src'. do 2 (apply func_ext; i). specialize (H0 x x0). specialize (WF0 x x0).
        ss. des_ifs.
        Local Opaque URA.add GRA.to_URA points_to URA.wf.
      }
      left.
      force_l. esplits; et. left.
      unfold guarantee.
      repeat (go; igo).
      force_l. esplits; et. left.
      force_l. { rewrite URA.unit_idl; refl. } left.
      assert(U: mem_src b ofs = inl (Some v_old)).
      { Local Transparent URA.add GRA.to_URA points_to URA.wf.
        clear - WF. ss. des. specialize (WF0 b ofs). r in WF. des; clarify. ss. des_ifs; ss.
        - bsimpl; des; des_sumbool; ss.
        - bsimpl; des; des_sumbool; ss.
        Local Opaque URA.add GRA.to_URA points_to URA.wf.
      }
      hexploit SIM; et. intro T. rewrite U in *. inv T.
      unfold unwrapU. unfold Mem.store.
      assert(exists _perm_some, Mem.cnts mem_tgt b 0 = Some _perm_some).
      { admit "this is simple hack to mimic permission (to give UB properly);
               should handle it better later". }
      des. des_ifs.
      repeat (go; igo). unfold MPut. repeat (go; igo).
      pfold. econs; ss; et.
      { esplits; ss; et. ii. ss. unfold mem_src'. des_ifs; bsimpl; des; des_sumbool; des_ifs.
        econs; et. }
    }
  Unshelve.
    all: ss.
    all: try (by repeat econs; et).
  Unshelve.
    all: try (by repeat econs; et).
  Qed.
  (* Theorem correct: ModSemPair.sim Mem1.MemSem Mem0.MemSem. *)
  (* Proof. *)
  (*   econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3. *)
  (*   { typeclasses eauto. } *)
  (*   { ss. esplits; ss; et. ii. econs 2. } *)
  (*   econs; ss. *)
  (*   { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify. *)
  (*     unfold alist_add, alist_remove; ss. *)
  (*     unfold Mem0.allocF. *)
  (*     (* Opaque MemStb. *) *)
  (*     (* Opaque mapi. *) *)
  (*     Local Opaque URA.add. *)
  (*     go. ss. rename x into sz. *)
  (*     unfold assume. *)
  (*     igo. *)
  (*     go. clarify. unfold HoareFun. go. rename x into rarg_src. *)
  (*     unfold assume. *)
  (*     igo. *)
  (*     repeat go. clear_tac. *)
  (*     Opaque URA.add. *)
  (*     unfold unpadding, assume. *)
  (*     igo. *)
  (*     pfold. econsr; et. esplits; et. left. *)
  (*     igo. des_ifs. *)
  (*     unfold unwrapU. des_ifs. igo. des_ifs. unfold MPut. igo. repeat go. *)
  (*     ss. clarify. *)
  (*     force_r. esplits; ss. left. *)
  (*     go. igo. *)
  (*     go. igo. *)
  (*     Hint Unfold alist_add. *)
  (*     u. *)
  (*     Hint Unfold body_to_tgt interp_hCallE_tgt. *)
  (*     u. igo. *)
  (*     Local Opaque MemStb. *)
  (*     cbn. *)
  (*     set (blk := (Mem.nb mem_tgt)) in *. *)
  (*     force_l. exists (Vptr (Mem.nb mem_tgt) 0). left. *)
  (*     igo. go. *)
  (*     force_l. *)
  (*     set (mem_src_new := add_delta_to_black *)
  (*                           (* (URA.excl (mem_src: URA.car (t:=Mem1._memRA)) frag) *) *)
  (*                           (URA.black (mem_src: URA.car (t:=Mem1._memRA))) *)
  (*                           (points_tos (blk, 0%Z) (repeat (Vint 0) sz))). *)
  (*     eexists (GRA.padding (mem_src_new: URA.car (t:=Mem1.memRA)), *)
  (*              GRA.padding (points_tos (blk, 0%Z) (repeat (Vint 0) sz))). left. *)
  (*     igo. force_l. *)
  (*     { *)
  (*       replace (fun k => URA.unit) with (URA.unit (t:=Σ)) by ss. *)
  (*       rewrite URA.unit_idl. *)
  (*       rewrite GRA.padding_add. *)
  (*       rewrite <- URA.unit_id. *)
  (*       apply URA.updatable_add; cycle 1. *)
  (*       { apply URA.updatable_unit. } *)
  (*       eapply GRA.padding_updatable. *)
  (*       subst mem_src_new. des_ifs. *)
  (*       ss. clarify. *)
  (*       rewrite <- Heq. *)
  (*       Local Transparent points_tos. *)
  (*       replace ((fun _ _ => @inr (option val) unit tt)) with (URA.unit (t:=Mem1._memRA)) by ss. *)
  (*       replace (URA.excl ((mem_src: URA.car (t:=Mem1._memRA)) ⋅ f) URA.unit) with *)
  (*           (URA.black ((mem_src: URA.car (t:=Mem1._memRA)) ⋅ f)) by ss. *)
  (*       rewrite Heq. *)
  (*       eapply URA.auth_alloc2. *)

  (*       clear - WF Heq SIM. *)
  (*       { ss. intros b ofs. des_ifs. ss. *)

  (*         assert(WF0: URA.wf ((GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) *)
  (*                               ⋅ (URA.unit ⋅ (rarg_src: URA.car (t:=GRA.to_URA Σ))))). *)
  (*         { ss. } *)
  (*         eapply URA.wf_mon in WF0. *)
  (*         eapply GRA.padding_wf in WF0. *)

  (*         unfold URA.white in *. clarify. *)
  (*         subst blk. *)
  (*         Local Transparent URA.add. *)
  (*         ss. des_ifs. *)
  (*         - bsimpl; des; des_sumbool; clarify. *)
  (*           admit "ez: Heq is wrong. Add mem tgt is wf (nb is actually nb); use sim_loc.". *)
  (*         - des. specialize (WF1 b ofs). bsimpl; des; des_sumbool; clarify; des_ifs. *)
  (*         - des. specialize (WF1 b ofs). bsimpl; des; des_sumbool; clarify; des_ifs. *)
  (*           apply_all_once Z.leb_le. apply_all_once Z.ltb_lt. *)
  (*           intro A. apply nth_error_None in A. rewrite repeat_length in *. *)
  (*           apply inj_le in A. rewrite Z2Nat.id in A; cycle 1. *)
  (*           { lia. } *)
  (*           lia. *)
  (*       } *)
  (*     } *)
  (*     left. *)
  (*     force_l. eexists. left. *)
  (*     unfold guarantee. igo. *)
  (*     force_l. esplits; et. left. *)
  (*     Local Opaque add_delta_to_black. *)
  (*     pfold; econs; try (by ss). *)
  (*     { instantiate (1:= GRA.padding _). rewrite GRA.padding_add. rewrite URA.unit_idl. f_equal. } *)
  (*     left. *)
  (*     pfold; econs; ss; et. *)
  (*     { *)
  (*       rr. unfold alist_add. ss. esplits; ss; et. *)
  (*       { unfold mem_src_new. *)
  (*         Local Transparent add_delta_to_black. *)
  (*         ss. *)
  (*       } *)
  (*       ii. ss. *)
  (*       subst mem_src_new. *)
  (*       assert(b <> blk). *)
  (*       {admit "should be ez". } *)
  (*       hexploit (SIM b ofs); et. intro A. inv A. *)
  (*       { *)
  (*         des_ifs; bsimpl; des; des_sumbool; clarify. *)
  (*         - unfold update. des_ifs. rewrite <- H3. econs. *)
  (*         - unfold update. des_ifs. rewrite <- H3. econs. *)
  (*         - unfold update. des_ifs. rewrite <- H3. econs. *)
  (*       } *)
  (*       { *)
  (*         des_ifs; bsimpl; des; des_sumbool; clarify. *)
  (*         - unfold update. des_ifs. rewrite <- H3. econs. *)
  (*         - unfold update. des_ifs. rewrite <- H3. econs. *)
  (*         - unfold update. des_ifs. rewrite <- H3. econs. *)
  (*       } *)
  (*     } *)
  (*   } *)
  (*   econs. *)
  (*   { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify. *)
  (*     u. *)
  (*     unfold Mem0.freeF. *)
  (*     Local Opaque URA.add. *)
  (*     go. ss. destruct x as [b ofs]. *)
  (*     unfold assume. *)
  (*     igo. *)
  (*     repeat (go; igo). des; clarify. *)
  (*     replace ((fun k => URA.unit): URA.car (t:=Σ))  with (URA.unit: URA.car (t:=Σ)) in WF by ss. *)
  (*     rewrite URA.unit_idl in WF. *)
  (*     rewrite GRA.padding_add in WF. apply GRA.padding_wf in WF. des. *)
  (*     Local Opaque URA.wf. *)
  (*     Hint Unfold handle_hCallE_tgt. *)
  (*     u. igo. ss. *)
  (*     force_l. eexists (Vint 0). left. *)
  (*     repeat (go; igo). *)
  (*     force_r. eexists. left. *)
  (*     repeat (go; igo). *)
  (*     force_r. esplits; et. left. *)
  (*     assert(A: mem_src b ofs = inl (Some v)). *)
  (*     { *)
  (*       Local Transparent URA.wf. *)
  (*       ss. des_ifs. des. specialize (WF0 b ofs). *)
  (*       Local Transparent URA.add. *)
  (*       clear SIM. *)
  (*       ss. clarify. rr in WF. des. clarify. ss. des_ifs. *)
  (*       - bsimpl; des; des_sumbool; ss. *)
  (*       - bsimpl; des; des_sumbool; ss. *)
  (*     } *)
  (*     Local Opaque URA.wf. *)
  (*     Local Opaque URA.add. *)
  (*     hexploit (SIM b ofs); et. intro B. rewrite A in *. inv B. *)
  (*     unfold unwrapU. des_ifs; cycle 1. *)
  (*     {exfalso. unfold Mem.free in *. des_ifs. } *)
  (*     repeat (igo; go). *)
  (*     unfold MPut. *)
  (*     repeat (igo; go). *)
  (*     u. *)
  (*     set (mem_src' := fun _b _ofs => if dec _b b && dec _ofs ofs then inr () else mem_src _b _ofs). *)
  (*     assert(WF': URA.wf (mem_src': URA.car (t:=Mem1._memRA))). *)
  (*     { Local Transparent URA.wf. *)
  (*       Local Transparent URA.add. *)
  (*       ss. ii. des_ifs. *)
  (*       ss. clarify. *)
  (*       subst mem_src'. ss. des_ifs. des. specialize (WF0 k k0). bsimpl. des; des_sumbool; des_ifs. *)
  (*       Local Opaque URA.wf. *)
  (*       Local Opaque URA.add. *)
  (*     } *)
  (*     rename t into mem_tgt'. *)
  (*     assert(SIM': forall b ofs, sim_loc (Mem.cnts mem_tgt' b ofs) (mem_src' b ofs)). *)
  (*     { i. *)
  (*       unfold Mem.free in Heq. des_ifs. ss. *)
  (*       subst mem_src'. ss. *)
  (*       destruct (classic (b = b0 /\ ofs = ofs0)); des; clarify. *)
  (*       - unfold update. des_ifs. econs. *)
  (*       - des_ifs. *)
  (*         { Psimpl. bsimpl; des; des_sumbool; ss; clarify. } *)
  (*         replace (update (Mem.cnts mem_tgt) b (update (Mem.cnts mem_tgt b) ofs None) b0 ofs0) with *)
  (*             (Mem.cnts mem_tgt b0 ofs0); cycle 1. *)
  (*         { unfold update. des_ifs. Psimpl. des_ifs; bsimpl; des; des_sumbool; ss; clarify. } *)
  (*         et. *)
  (*     } *)
  (*     force_l. *)
  (*     eexists ((GRA.padding (URA.black (mem_src': URA.car (t:=Mem1._memRA)))), URA.unit: URA.car (t:=Σ)). left. *)
  (*     force_l. *)
  (*     { replace (fun k => URA.unit) with (URA.unit: URA.car (t:=Σ)) by ss. *)
  (*       rewrite URA.unit_id. rewrite URA.unit_idl. *)
  (*       rewrite GRA.padding_add. apply GRA.padding_updatable. *)
  (*       apply URA.auth_dealloc. *)
  (*       clear - WF' WF. *)
  (*       r. i. rewrite URA.unit_idl. *)
  (*       ss. destruct H; clear H. (*** coq bug; des infloops ***) des. clarify. *)
  (*       esplits; et. *)
  (*       apply func_ext. intro _b. apply func_ext. intro _ofs. *)
  (*       destruct (classic (b = _b /\ ofs = _ofs)). *)
  (*       - destruct H; clear H. clarify. *)
  (*         subst mem_src'. ss. des_ifs; bsimpl; des; des_sumbool; clarify. *)
  (*         clear - H0. *)
  (*         Local Transparent URA.wf. *)
  (*         Local Transparent URA.add. *)
  (*         specialize (H0 _b _ofs). ss. des_ifs; bsimpl; des; des_sumbool; clarify. des_u. ss. *)
  (*       - Psimpl. *)
  (*         subst mem_src'. s. des_ifs; bsimpl; des; des_sumbool; clarify. *)
  (*         destruct H; clear H; des; clarify. *)
  (*         Local Opaque URA.wf. *)
  (*         Local Opaque URA.add. *)
  (*     } *)
  (*     left. u. *)
  (*     force_l. exists (URA.unit: URA.car (t:=Σ)). left. *)
  (*     unfold guarantee. *)
  (*     igo. force_l. esplits; et. left. *)
  (*     force_l. *)
  (*     { rewrite URA.unit_idl. ss. } *)
  (*     left. *)
  (*     pfold; econs; et. *)
  (*     ss. *)
  (*     esplits; ss; et. *)
  (*   } *)
  (*   Local Opaque GRA.to_URA. *)
  (*   Local Opaque points_to. *)
  (*   Local Opaque URA.add. *)
  (*   Local Opaque URA.wf. *)
  (*   econs. *)
  (*   { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify. *)
  (*     u. *)
  (*     unfold Mem0.loadF. *)
  (*     go. ss. destruct x as [[b ofs] v]. *)
  (*     unfold assume. *)
  (*     igo. *)
  (*     repeat (go; igo). des_ifs. des; clarify. ss. rewrite URA.unit_idl in *. *)
  (*     rewrite GRA.padding_add in WF. apply GRA.padding_wf in WF. des. *)
  (*     Hint Unfold handle_hCallE_tgt. *)
  (*     u. igo. ss. *)
  (*     force_l. eexists _. left. *)
  (*     repeat (go; igo). *)
  (*     force_r. eexists. left. *)
  (*     repeat (go; igo). *)
  (*     force_r. esplits; et. left. *)
  (*     force_l. eexists (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA))), *)
  (*                       GRA.padding ((b, ofs) |-> v)). left. *)
  (*     force_l. esplits; et. left. *)
  (*     force_l. esplits; et. left. *)
  (*     unfold guarantee. *)
  (*     repeat (go; igo). *)
  (*     force_l. esplits; et. left. *)
  (*     force_l. { rewrite URA.unit_idl; refl. } left. *)
  (*     Local Transparent URA.wf. *)
  (*     Local Transparent URA.add. *)
  (*     Local Transparent GRA.to_URA. *)
  (*     Local Transparent points_to. *)
  (*     ss. des_ifs. des; ss. do 2 spc WF0. des_ifs; cycle 1. *)
  (*     { exfalso. rr in WF. des. ss. des_ifs. do 2 spc SIM. des_ifs. bsimpl; des; des_sumbool; ss. } *)
  (*     destruct o; ss. *)
  (*     assert(v0 = v). *)
  (*     { rr in WF. des. ss. des_ifs. do 2 spc SIM. des_ifs. bsimpl; des; des_sumbool; ss. } *)
  (*     clarify. *)
  (*     unfold unwrapU. unfold Mem.load. exploit SIM; et. intro T. rewrite Heq in *. inv T. *)
  (*     pfold. econs; et. *)
  (*     rr. esplits; ss; et. *)
  (*   } *)
  (*   Local Opaque GRA.to_URA. *)
  (*   Local Opaque points_to. *)
  (*   Local Opaque URA.add. *)
  (*   Local Opaque URA.wf. *)
  (*   econs; et. *)
  (*   { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify. *)
  (*     u. *)
  (*     unfold Mem0.storeF. *)
  (*     go. ss. destruct x as [[b ofs] v]. *)
  (*     set (mem_src' := fun _b _ofs => if dec _b b && dec _ofs ofs then inl (Some v) else mem_src _b _ofs). *)
  (*     unfold assume. *)
  (*     igo. *)
  (*     repeat (go; igo). des_ifs. des; clarify. ss. rewrite URA.unit_idl in *. *)
  (*     rewrite GRA.padding_add in WF. apply GRA.padding_wf in WF. des. *)
  (*     Hint Unfold handle_hCallE_tgt. *)
  (*     u. igo. ss. *)
  (*     force_l. eexists _. left. *)
  (*     repeat (go; igo). *)
  (*     force_r. eexists. left. *)
  (*     repeat (go; igo). *)
  (*     force_r. esplits; et. left. *)
  (*     force_l. eexists (GRA.padding (URA.black (mem_src': URA.car (t:=Mem1._memRA))), *)
  (*                       GRA.padding ((b, ofs) |-> v)). left. *)
  (*     assert(WF0: URA.wf (mem_src': URA.car (t:=Mem1._memRA))). *)
  (*     { Local Transparent URA.wf. *)
  (*       clear - WF. apply URA.wf_mon in WF. ss. des. *)
  (*       ii. specialize (WF0 k k0). des_ifs_safe. unfold mem_src' in *. des_ifs. *)
  (*       Local Opaque URA.wf. *)
  (*     } *)
  (*     force_l. *)
  (*     { rewrite ! GRA.padding_add. eapply GRA.padding_updatable. *)
  (*       clear - WF WF0. clear WF. *)
  (*       Local Transparent URA.add GRA.to_URA points_to URA.wf. *)
  (*       eapply URA.auth_update; et. *)
  (*       rr. ii. destruct H; clear H. (*** FIXME: des runs infloop ***) *)
  (*       des. subst. esplits; et. *)
  (*       subst mem_src'. do 2 (apply func_ext; i). specialize (H0 x x0). specialize (WF0 x x0). *)
  (*       ss. des_ifs. *)
  (*       Local Opaque URA.add GRA.to_URA points_to URA.wf. *)
  (*     } *)
  (*     left. *)
  (*     force_l. esplits; et. left. *)
  (*     unfold guarantee. *)
  (*     repeat (go; igo). *)
  (*     force_l. esplits; et. left. *)
  (*     force_l. { rewrite URA.unit_idl; refl. } left. *)
  (*     assert(U: mem_src b ofs = inl (Some v_old)). *)
  (*     { Local Transparent URA.add GRA.to_URA points_to URA.wf. *)
  (*       clear - WF. ss. des. specialize (WF0 b ofs). r in WF. des; clarify. ss. des_ifs; ss. *)
  (*       - bsimpl; des; des_sumbool; ss. *)
  (*       - bsimpl; des; des_sumbool; ss. *)
  (*       Local Opaque URA.add GRA.to_URA points_to URA.wf. *)
  (*     } *)
  (*     hexploit SIM; et. intro T. rewrite U in *. inv T. *)
  (*     unfold unwrapU. unfold Mem.store. *)
  (*     assert(exists _perm_some, Mem.cnts mem_tgt b 0 = Some _perm_some). *)
  (*     { admit "this is simple hack to mimic permission (to give UB properly); *)
  (*              should handle it better later". } *)
  (*     des. des_ifs. *)
  (*     repeat (go; igo). unfold MPut. repeat (go; igo). *)
  (*     pfold. econs; ss; et. *)
  (*     { esplits; ss; et. ii. ss. unfold mem_src'. des_ifs; bsimpl; des; des_sumbool; des_ifs. *)
  (*       econs; et. } *)
  (*   } *)
  (* Unshelve. *)
  (*   all: ss. *)
  (*   all: try (by repeat econs; et). *)
  (* Unshelve. *)
  (*   all: try (by repeat econs; et). *)
  (* Qed. *)

End SIMMODSEM.


