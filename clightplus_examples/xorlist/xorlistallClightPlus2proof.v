Require Import CoqlibCCR.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import SimModSem.
Require Import PCM.
Require Import HoareDef.
Require Import STB.
Require Import STS2SmallStep.
Require Import ClightPlusSkel ClightPlusExprgen ClightPlusgen.
Require Import ClightPlusMem0 ClightPlusMem1 ClightPlusMemAux.
Require Import CProofMode CIProofMode.
Require Import xorlist.
Require Import xorlistall0.
Require Import xorlistall1.
Require Import xorlist1.
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Clightdefs.

Require Import Hoare.
Require Import ClightPlus2ClightSepComp.
Require Import xorlistall01proof.

Theorem refine_improve_trans mdl1 mdl2 clight_prog: refines_closed mdl1 mdl2 -> improves2_program (ModL.compile mdl1) (Clight.semantics2 clight_prog) -> improves2_program (ModL.compile mdl2) (Clight.semantics2 clight_prog).
Proof.
  i. unfold refines_closed, improves2_program in *. i. hexploit H0. { apply BEH. }
  i. des. unfold Beh.of_program in H. hexploit H. { apply BEH0. }
  i. esplits. { apply H1. } apply SIM.
Qed.

Section PROOF.
  Let Σ := GRA.of_list [pointstoRA; allocatedRA; blocksizeRA; blockaddressRA].
  Local Existing Instance Σ.

  Let pointstoRA_inG: @GRA.inG pointstoRA Σ.
  Proof. exists 0. ss. Defined.
  Local Existing Instance pointstoRA_inG.

  Let allocatedRA_inG: @GRA.inG allocatedRA Σ.
  Proof. exists 1. ss. Defined.
  Local Existing Instance allocatedRA_inG.

  Let blocksizeRA_inG: @GRA.inG blocksizeRA Σ.
  Proof. exists 2. ss. Defined.
  Local Existing Instance blocksizeRA_inG.

  Let blockaddressRA_inG: @GRA.inG blockaddressRA Σ.
  Proof. exists 3. ss. Defined.
  Local Existing Instance blockaddressRA_inG.

  Let mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)); ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))].

  Let mds := [SMem mfsk; SxorAll].

  Let GlobalStb : Sk.t -> string -> option fspec := fun sk => to_stb (SMod.get_stb mds sk).
  Hint Unfold GlobalStb: stb.

  Theorem final_thm prog (LINK: xorlistall0._xor = Some prog) :
    improves2_program (ModL.compile (Mod.add_list (map SMod.to_src mds))) (Clight.semantics2 prog).
  Proof.
    destruct xorlistall0.valid_xor.
    destruct xorlistall0.msk_xor.
    unfold xor in H. rewrite LINK in H.
    unfold _msk in H0. rewrite LINK in H0.
    eapply refine_improve_trans; cycle 1.
    { eapply single_compile_program_improves; et. }
    etrans.
    - eapply refines_close. hexploit (correct GlobalStb); et.
      { clear H H0 LINK. stb_incl_tac; tauto. }
      { clear H H0 LINK. unfold xorStb. stb_incl_tac; tauto. }
      i.
      eassert (x0 = mfsk).
      { unfold _xor in LINK. vm_compute (Linking.link _ _) in LINK. 
        destruct Ctypes.link_build_composite_env. destruct a. inversion LINK.
        clear LINK. subst. vm_compute (mem_skel _) in H0. inversion H0. refl. }
      clear LINK H H0. ii. eapply H1. ss.
      unfold Mod.add_list at 2. ss. rewrite ModL.add_empty_r.
      rewrite H2 in PR. apply PR.
    - etrans.
      { apply refines_close. rewrite <- refines2_eq.
        apply refines2_cons; [|refl]. eapply Weakening.adequacy_weaken. ss. }
      set (_ :: _).
      assert (l = map (SMod.to_tgt GlobalStb) mds).
      { unfold l, mds. clear LINK H H0. ss. }
      rewrite H1. eapply adequacy_type.
      + instantiate (1:= GRA.embed (_has_size None 0%Z : blocksizeRA) ⋅ GRA.embed (_has_base None Ptrofs.zero : blockaddressRA)).
        (* instantiate (1:= GRA.embed ((fun ob => match ob with
                                                   | Some _ => OneShot.unit
                                                   | None => OneShot.white Ptrofs.zero
                                                   end) : blockaddressRA)
                          ⋅ GRA.embed ((fun ob => match  ob with
                                                   | Some b => OneShot.unit
                                                   | None => OneShot.white 0%Z
                                                   end) : blocksizeRA)). *)
        admit.
        (* clear. ss. unfold SMod.get_initial_mrs. ss. rewrite URA.unit_idl.
        rewrite URA.unit_id. rewrite URA.add_comm.
        rewrite <- URA.add_assoc.
        unfold c. rewrite (URA.add_comm (@GRA.embed blockaddressRA _ _ _) (@GRA.embed blocksizeRA _ _ _)).
        rewrite (URA.add_assoc _ (@GRA.embed blocksizeRA _ _ _) (@GRA.embed blockaddressRA _ _ _)).
        rewrite GRA.embed_add. ur.
        rewrite (URA.add_comm (@GRA.embed blockaddressRA _ _ _) (@GRA.embed blocksizeRA _ _ _)).
        rewrite URA.add_assoc.
        ur. ur. unfold URA._add. unfold GRA.to_URA.
        set (GRA.embed _ ⋅ GRA.embed _). *)
      + i. simpl in MAIN. inv MAIN. exists tt.
        clear. splits; et.
        2:{ i. ss. iIntros "%"; des; clarify. }
        iIntros "[A B]". ss. iSplit; et. iSplit; et.
        iExists Ptrofs.zero. unfold _has_offset.
        des_ifs. ss.
        iPoseProof (_has_size_dup with "A") as "[$ $]".
        iPoseProof (_has_base_dup with "B") as "[B ?]".
        unfold Vnullptr in Heq. des_ifs.
        iSplitL "B"; iExists _; iFrame; iPureIntro; splits; et; ss.
  Admitted.

End PROOF.