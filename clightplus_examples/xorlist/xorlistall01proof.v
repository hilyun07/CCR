Require Import CoqlibCCR.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import SimModSem.
Require Import PCM.
Require Import HoareDef.
Require Import STB.
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

Require Import ClightPlusMem01Proof.
Require Import xorlist01proof.
Require Import main01proof.

Section PROOF.

  Import ClightPlusMem1.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.
  
  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).
  Hypothesis STBINCL : forall sk, stb_incl (to_stb xorStb) (GlobalStb sk).

  Variable xorlink : Clight.program.
  Variable xormod : Mod.t.
  Hypothesis VALID_link : xorlistall0._xor = Some xorlink.
  Hypothesis VALID_comp : compile xorlink "xorlist" = Errors.OK xormod.
  Let mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)); ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))].

  (* Variable xor0 : Mod.t.
  Hypothesis VALID : xorlist0._xor = Errors.OK xor0. *)

  Theorem correct : refines2 [xormod; ClightPlusMem0.Mem mfsk] [xorlistall1.xorAllWrapped GlobalStb; ClightPlusMem1.Mem mfsk].
  Proof.
    eapply adequacy_local_strong_l. econs; cycle 1.
    { simpl map. econs; [|econs; refl].
      unfold xor_sk, xor. rewrite VALID_link. rewrite VALID_comp. et. }
    i. econs; cycle 1.
    { econs; [|ss]. apply correct_mod; et. inv SKINCL. inv H6. ss. }
    hexploit sim_delete_tl; et. { inv SKINCL. inv H6. et. } i. rename H3 into sim_delete_tl.
    hexploit sim_delete_hd; et. { inv SKINCL. inv H6. et. } i. rename H3 into sim_delete_hd.
    hexploit sim_add_hd; et. { inv SKINCL. inv H6. et. } i. rename H3 into sim_add_hd.
    hexploit sim_add_tl; et. { inv SKINCL. inv H6. et. } i. rename H3 into sim_add_tl.
    hexploit sim_main; et. { inv SKINCL. et. } { inv SKINCL. inv H6. et. } i. rename H3 into sim_main.
    eassert (_xor = _).
    { unfold _xor. vm_compute (Linking.link _ _). reflexivity. }
    rewrite H3 in *. clear H3. destruct Ctypes.link_build_composite_env. destruct a.
    inversion VALID_link. clear VALID_link. subst.
    clear a.
    set (compile _ _) in VALID_comp.
    eassert (r = Errors.OK _).
    { reflexivity. }
    rewrite H3 in *. clear r H3.
    inversion VALID_comp. clear VALID_comp. subst. ss.
    econstructor 1 with (wf := xorlist01proof.wf) (le := top2); et; ss; cycle 1.
    { eexists. econs. apply to_semantic. iIntros. et. }
    (* each functions has simulation relation *)
    unfold get_ce. simpl prog_comp_env.
    econs. { apply sim_add_hd. }
    econs. { apply sim_add_tl. }
    econs. { apply sim_main. }
    econs. { apply sim_delete_hd. }
    econs. { apply sim_delete_tl. }
    econs.
    Unshelve. exact tt.
  Qed.

End PROOF.