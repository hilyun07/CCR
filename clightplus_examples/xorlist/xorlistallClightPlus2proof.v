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
Require Import ClightPlusMem01Proof.
Require Import ClightPlusInitProof.
Require Import ClightPlusgenCorrect.
Require Import xorlistall01proof.

Theorem refine_improve_trans L mdl1 mdl2 : refines_closed mdl1 mdl2 -> improves2_program (ModL.compile mdl1) L -> improves2_program (ModL.compile mdl2) L.
Proof.
  i. unfold refines_closed, improves2_program in *. i. apply H0 in BEH. des_ifs.
  des. unfold Beh.of_program in H. hexploit H. { apply BEH0. }
  i. esplits. { apply H1. } apply SIM.
Qed.

Section Lemma.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Lemma valid_point sk' sk p a s
    (SUCC: alloc_globals sk' (ε, ε, ε) xH sk = Some (p, a, s))
    : URA.wf p.
  Proof.
    set ε as p0 in SUCC.
    set ε as a0 in SUCC.
    set ε as s0 in SUCC.
    set xH as b0 in SUCC.
    assert (forall b, (b0 ≤ b)%positive -> p0 b = ε).
    { i. unfold p0. ss. }
    assert (URA.wf p0).
    { ur. i. unfold p0. ur. i. ur. ss. }
    clearbody p0 a0 s0 b0.
    revert p a s sk' p0 a0 s0 b0 SUCC H3 H4.
    induction sk; i; ss; clarify. des_ifs.
    - hexploit IHsk; et. i. apply H3. nia.
    - hexploit IHsk; et.
      + i. ur. rewrite H3; try nia. r_solve. clear -Heq0 H5.
        set 0%Z in Heq0.
        set ε in Heq0.
        set (gvar_init v) in Heq0.
        assert (c0 b = ε) by ss.
        clearbody z c0 l.
        ginduction l; i; ss; clarify.
        des_ifs. hexploit IHl; et. extensionalities.
        unfold store_init_data in Heq. des_ifs.
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
      + ur in H4. ur in H4. ur. ur. i. destruct (Pos.eq_dec k b0); subst; cycle 1.
        * replace (c k k0) with (ε : Consent.t memval); r_solve; et.
          clear -Heq0 n.
          set 0%Z in Heq0.
          set ε in Heq0.
          set (gvar_init v) in Heq0.
          assert (c0 k = ε) by ss.
          clearbody z c0 l.
          ginduction l; i; ss; clarify. { rewrite H. ss. }
          des_ifs. hexploit IHl; et. extensionalities.
          unfold store_init_data in Heq. des_ifs.
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        * rewrite H3; try nia. set (_ k0). assert (y = ε) by ss. rewrite H5. r_solve.
          clear -Heq0.
          set 0%Z in Heq0.
          set ε in Heq0.
          set (gvar_init v) in Heq0.
          assert (forall i, (z ≤ i)%Z -> c0 b0 i = ε).
          { i. unfold c0. ss. }
          assert (forall i, (i < z)%Z -> URA.wf (c0 b0 i)).
          { i. unfold c0. ur. ss. }
          clearbody z c0 l.
          ginduction l; i; ss; clarify.
          { destruct (Coqlib.zlt k0 z); unfold Coqlib.Plt in *; [apply H0|rewrite H]; try nia; ur; ss. }
          des_ifs. unfold store_init_data in Heq. des_ifs.
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite repeat_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite repeat_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. des_ifs. nia. }
            { i. unfold __points_to.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
    - hexploit IHsk; et.
      + i. ur. rewrite H3; try nia. r_solve. clear -Heq0 H5.
        set 0%Z in Heq0.
        set ε in Heq0.
        set (gvar_init v) in Heq0.
        assert (c0 b = ε) by ss.
        clearbody z c0 l.
        ginduction l; i; ss; clarify.
        des_ifs. hexploit IHl; et. extensionalities.
        unfold store_init_data in Heq. des_ifs.
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
      + ur in H4. ur in H4. ur. ur. i. destruct (Pos.eq_dec k b0); subst; cycle 1.
        * replace (c k k0) with (ε : Consent.t memval); r_solve; et.
          clear -Heq0 n.
          set 0%Z in Heq0.
          set ε in Heq0.
          set (gvar_init v) in Heq0.
          assert (c0 k = ε) by ss.
          clearbody z c0 l.
          ginduction l; i; ss; clarify. { rewrite H. ss. }
          des_ifs. hexploit IHl; et. extensionalities.
          unfold store_init_data in Heq. des_ifs.
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        * rewrite H3; try nia. set (_ k0). assert (y = ε) by ss. rewrite H5. r_solve.
          clear -Heq0.
          set 0%Z in Heq0.
          set ε in Heq0.
          set (gvar_init v) in Heq0.
          assert (forall i, (z ≤ i)%Z -> c0 b0 i = ε).
          { i. unfold c0. ss. }
          assert (forall i, (i < z)%Z -> URA.wf (c0 b0 i)).
          { i. unfold c0. ur. ss. }
          clearbody z c0 l.
          ginduction l; i; ss; clarify.
          { destruct (Coqlib.zlt k0 z); unfold Coqlib.Plt in *; [apply H0|rewrite H]; try nia; ur; ss. }
          des_ifs. unfold store_init_data in Heq. des_ifs.
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite repeat_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite repeat_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. des_ifs. nia. }
            { i. unfold __points_to.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
    - hexploit IHsk; et.
      + i. ur. rewrite H3; try nia. r_solve. clear -Heq0 H5.
        set 0%Z in Heq0.
        set ε in Heq0.
        set (gvar_init v) in Heq0.
        assert (c0 b = ε) by ss.
        clearbody z c0 l.
        ginduction l; i; ss; clarify.
        des_ifs. hexploit IHl; et. extensionalities.
        unfold store_init_data in Heq. des_ifs.
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
      + ur in H4. ur in H4. ur. ur. i. destruct (Pos.eq_dec k b0); subst; cycle 1.
        * replace (c k k0) with (ε : Consent.t memval); r_solve; et.
          clear -Heq0 n.
          set 0%Z in Heq0.
          set ε in Heq0.
          set (gvar_init v) in Heq0.
          assert (c0 k = ε) by ss.
          clearbody z c0 l.
          ginduction l; i; ss; clarify. { rewrite H. ss. }
          des_ifs. hexploit IHl; et. extensionalities.
          unfold store_init_data in Heq. des_ifs.
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
          { ur. ur. rewrite H. unfold __points_to. destruct AList.dec; ss; clarify; try nia. r_solve. }
        * rewrite H3; try nia. set (_ k0). assert (y = ε) by ss. rewrite H5. r_solve.
          clear -Heq0.
          set 0%Z in Heq0.
          set ε in Heq0.
          set (gvar_init v) in Heq0.
          assert (forall i, (z ≤ i)%Z -> c0 b0 i = ε).
          { i. unfold c0. ss. }
          assert (forall i, (i < z)%Z -> URA.wf (c0 b0 i)).
          { i. unfold c0. ur. ss. }
          clearbody z c0 l.
          ginduction l; i; ss; clarify.
          { destruct (Coqlib.zlt k0 z); unfold Coqlib.Plt in *; [apply H0|rewrite H]; try nia; ur; ss. }
          des_ifs. unfold store_init_data in Heq. des_ifs.
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite length_inj_bytes. rewrite encode_int_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to. rewrite repeat_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. }
            { i. unfold __points_to. rewrite repeat_length.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
          { hexploit IHl; et; ss; ur; ur. 
            { i. rewrite H; try nia. unfold __points_to.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia. r_solve. des_ifs. nia. }
            { i. unfold __points_to.
              destruct AList.dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; clarify; try nia.
              { rewrite H; try nia. r_solve. des_ifs. }
              r_solve. ur in H0. eapply H0. nia. } }
    - hexploit IHsk; et.
      + i. ur. rewrite H3; try nia. r_solve. clear -Heq0 H5.
        set 0%Z in Heq0.
        set ε in Heq0.
        set (gvar_init v) in Heq0.
        assert (c0 b = ε) by ss.
        clearbody z c0 l.
        ginduction l; i; ss; clarify.
        des_ifs. hexploit IHl; et. extensionalities.
        unfold store_init_data in Heq. des_ifs; rewrite H; et.
      + ur in H4. ur in H4. ur. ur. i. destruct (Pos.eq_dec k b0); subst; cycle 1.
        * replace (c k k0) with (ε : Consent.t memval); r_solve; et.
          clear -Heq0 n.
          set 0%Z in Heq0.
          set ε in Heq0.
          set (gvar_init v) in Heq0.
          assert (c0 k = ε) by ss.
          clearbody z c0 l.
          ginduction l; i; ss; clarify. { rewrite H. ss. }
          des_ifs. hexploit IHl; et. extensionalities.
          unfold store_init_data in Heq. des_ifs; rewrite H; et.
        * rewrite H3; try nia. set (_ k0). assert (y = ε) by ss. rewrite H5. r_solve.
          clear -Heq0.
          set 0%Z in Heq0.
          set ε in Heq0.
          set (gvar_init v) in Heq0.
          assert (forall i, (z ≤ i)%Z -> c0 b0 i = ε).
          { i. unfold c0. ss. }
          assert (forall i, (i < z)%Z -> URA.wf (c0 b0 i)).
          { i. unfold c0. ur. ss. }
          clearbody z c0 l.
          ginduction l; i; ss; clarify.
          { destruct (Coqlib.zlt k0 z); unfold Coqlib.Plt in *; [apply H0|rewrite H]; try nia; ur; ss. }
          des_ifs. unfold store_init_data in Heq. des_ifs.
          { hexploit IHl; et; ss; ur; ur.
            { i. apply H; nia. }
            { i. ur in H0. destruct (Coqlib.zlt i0 z). { apply H0. et. } rewrite H; ss. nia. } }
          { hexploit IHl; et; ss; ur; ur.
            { i. apply H; nia. }
            { i. ur in H0. destruct (Coqlib.zlt i0 z). { apply H0. et. } rewrite H; ss. nia. } }
          { hexploit IHl; et; ss; ur; ur.
            { i. apply H; nia. }
            { i. ur in H0. destruct (Coqlib.zlt i0 z). { apply H0. et. } rewrite H; ss. nia. } }
          { hexploit IHl; et; ss; ur; ur.
            { i. apply H; nia. }
            { i. ur in H0. destruct (Coqlib.zlt i0 z). { apply H0. et. } rewrite H; ss. nia. } }
          { hexploit IHl; et; ss; ur; ur.
            { i. apply H; nia. }
            { i. ur in H0. destruct (Coqlib.zlt i z). { apply H0. et. } rewrite H; ss. nia. } }
          { hexploit IHl; et; ss; ur; ur.
            { i. apply H; nia. }
            { i. ur in H0. destruct (Coqlib.zlt i z). { apply H0. et. } rewrite H; ss. nia. } }
          { hexploit IHl; et; ss; ur; ur.
            { i. apply H; nia. }
            { i. ur in H0. destruct (Coqlib.zlt i z). { apply H0. et. } rewrite H; ss. nia. } }
          { hexploit IHl; et; ss; ur; ur.
            { i. des_ifs. apply H; nia. }
            { i. ur in H0. destruct Archi.ptr64 eqn:?; clarify. destruct (Coqlib.zlt i1 z). { apply H0. et. } rewrite H; ss. nia. } }
  Qed.

  Lemma valid_alloc sk' sk p a s
    (SUCC: alloc_globals sk' (ε, ε, ε) xH sk = Some (p, a, s))
    : URA.wf a.
  Proof.
    set ε as p0 in SUCC.
    set ε as a0 in SUCC.
    set ε as s0 in SUCC.
    set xH as b0 in SUCC.
    assert (forall b, (b0 ≤ b)%positive -> a0 b = ε).
    { i. unfold a0. ss. }
    assert (URA.wf a0).
    { ur. i. unfold a0. ur. ss. }
    clearbody p0 a0 s0 b0.
    revert p a s sk' p0 a0 s0 b0 SUCC H3 H4.
    induction sk; i; ss; clarify. des_ifs.
    - hexploit IHsk; et.
      + i. ur. rewrite H3; try nia. r_solve. unfold __allocated_with. des_ifs. nia.
      + ur in H4. ur. i. destruct (Pos.eq_dec k b0); subst; cycle 1.
        * unfold __allocated_with. des_ifs. r_solve. et.
        * rewrite H3; try nia. r_solve. unfold __allocated_with. des_ifs. ur. ss.
    - hexploit IHsk; et.
      + i. ur. rewrite H3; try nia. r_solve. unfold __allocated_with. des_ifs. nia.
      + ur in H4. ur. i. destruct (Pos.eq_dec k b0); subst; cycle 1.
        * unfold __allocated_with. des_ifs. r_solve. et.
        * rewrite H3; try nia. r_solve. unfold __allocated_with. des_ifs. ur. ss.
    - hexploit IHsk; et.
      + i. ur. rewrite H3; try nia. r_solve. unfold __allocated_with. des_ifs. nia.
      + ur in H4. ur. i. destruct (Pos.eq_dec k b0); subst; cycle 1.
        * unfold __allocated_with. des_ifs. r_solve. et.
        * rewrite H3; try nia. r_solve. unfold __allocated_with. des_ifs. ur. ss.
    - hexploit IHsk; et.
      + i. ur. rewrite H3; try nia. r_solve. unfold __allocated_with. des_ifs. nia.
      + ur in H4. ur. i. destruct (Pos.eq_dec k b0); subst; cycle 1.
        * unfold __allocated_with. des_ifs. r_solve. et.
        * rewrite H3; try nia. r_solve. unfold __allocated_with. des_ifs. ur. ss.
    - hexploit IHsk; et.
      + i. ur. rewrite H3; try nia. r_solve. unfold __allocated_with. des_ifs. nia.
      + ur in H4. ur. i. destruct (Pos.eq_dec k b0); subst; cycle 1.
        * unfold __allocated_with. des_ifs. r_solve. et.
        * rewrite H3; try nia. r_solve. unfold __allocated_with. des_ifs. ur. ss.
  Qed.

  Lemma valid_size sk' sk p a (s : blocksizeRA)
    (SUCC: alloc_globals sk' (ε, ε, ε) xH sk = Some (p, a, s))
    : URA.wf (s ⋅ (fun k => match k with
                            | Some b => if Coqlib.plt b (Pos.of_succ_nat (List.length sk)) then OneShot.unit else OneShot.black
                            | None => OneShot.white 0%Z
                            end)).
  Proof. 
    set ε as p0 in SUCC.
    set ε as a0 in SUCC.
    set ε as s0 in SUCC.
    set xH as b0 in SUCC.
    assert (s0 None = ε).
    { ss. }
    replace (Pos.of_succ_nat (strings.length sk)) with (Pos.of_nat (Pos.to_nat b0 + (strings.length sk))) by nia.
    assert (forall b, (b0 ≤ b)%positive -> s0 (Some b) = ε).
    { i. unfold s0. ss. }
    assert (forall b, (b < b0)%positive -> URA.wf (s0 (Some b))).
    { i. unfold s0. ur. ss. }
    clearbody p0 a0 s0 b0.
    revert p a s sk' p0 a0 s0 b0 SUCC H3 H4 H5.
    induction sk; i; ss; clarify.
    - ur. i. des_ifs.
      { unfold Coqlib.Plt in p0. hexploit (H5 b); try nia. i. ur. des_ifs. ur in H6. clarify. }
      { unfold Coqlib.Plt in n. hexploit (H4 b); try nia. i. ur. unfold Values.block. rewrite H6. ss. }
      { unfold Values.block in *. rewrite H3. ur. ss. }
    - des_ifs.
      + hexploit IHsk; et. 
        * ur. rewrite H3. r_solve.
        * i. ur. rewrite H4; try nia. r_solve.
          Local Transparent _has_size.
          unfold _has_size. des_ifs. nia.
        * i. ur. des_ifs. { rewrite H4; try nia. r_solve. et. } hexploit (H5 b); try nia. i. ur in H7. ur. des_ifs.
        * i. set (Pos.of_nat _). set (Pos.of_nat _) in H6. replace p1 with p2; et. nia.
      + hexploit IHsk; et.
        * ur. rewrite H3. r_solve.
        * i. ur. rewrite H4; try nia. r_solve. unfold _has_size. des_ifs. nia.
        * i. ur. des_ifs. { rewrite H4; try nia. r_solve. et. } hexploit (H5 b); try nia. i. ur in H7. ur. des_ifs.
        * i. set (Pos.of_nat _). set (Pos.of_nat _) in H6. replace p1 with p2; et. nia.
      + hexploit IHsk; et.
        * ur. rewrite H3. r_solve.
        * i. ur. rewrite H4; try nia. r_solve. unfold _has_size. des_ifs. nia.
        * i. ur. des_ifs. { rewrite H4; try nia. r_solve. et. } hexploit (H5 b); try nia. i. ur in H7. ur. des_ifs.
        * i. set (Pos.of_nat _). set (Pos.of_nat _) in H6. replace p1 with p2; et. nia.
      + hexploit IHsk; et.
        * ur. rewrite H3. r_solve.
        * i. ur. rewrite H4; try nia. r_solve. unfold _has_size. des_ifs. nia.
        * i. ur. des_ifs. { rewrite H4; try nia. r_solve. et. } hexploit (H5 b); try nia. i. ur in H7. ur. des_ifs.
        * i. set (Pos.of_nat _). set (Pos.of_nat _) in H6. replace p1 with p2; et. nia.
      + hexploit IHsk; et.
        * ur. rewrite H3. r_solve.
        * i. ur. rewrite H4; try nia. r_solve. unfold _has_size. des_ifs. nia.
        * i. ur. des_ifs. { rewrite H4; try nia. r_solve. et. } hexploit (H5 b); try nia. i. ur in H7. ur. des_ifs.
        * i. set (Pos.of_nat _). set (Pos.of_nat _) in H6. replace p1 with p2; et. nia.
  Qed.

End Lemma.


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

  Lemma wf_sk : match mem_init_cond_dec (sort (Sk.add mfsk (Sk.add xor_sk Sk.unit))) (sort (Sk.add mfsk (Sk.add xor_sk Sk.unit))) with in_left => True | in_right => False end.
  Proof.
    unfold mfsk. clear. unfold xor_sk, xor, _xor.
    eassert (Linking.link main.prog prog = _).
    { vm_compute (Linking.link _ _). eauto. }
    rewrite H. clear H. destruct Ctypes.link_build_composite_env. destruct a.
    clear.
    set (compile _ _).
    eassert (r = Errors.OK _).
    { unfold r. clear. eauto. }
    rewrite H. clear r H. simpl (Mod.sk _).
    clear. apply Logic.I.
  Qed.

  Lemma _wf_sk : load_mem (sort (Sk.add mfsk (Sk.add xor_sk Sk.unit))) <> None.
  Proof.
    pose proof wf_sk.
    destruct mem_init_cond_dec. 2:{ inversion H. }
    unfold mem_init_cond in m.
    hexploit load_mem_exists. { apply m. }
    i. des. rewrite H0. et.
  Qed.

  Theorem final_thm prog (LINK: xorlistall0._xor = Some prog) :
    improves2_program (ModL.compile (Mod.add_list (map SMod.to_src mds))) (semantics3 prog).
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
        clear. ss. unfold SMod.get_initial_mrs. ss. rewrite URA.unit_idl.
        rewrite URA.unit_id.
        unfold res_init. 
        destruct alloc_globals eqn:?.
        2:{ rewrite wf_iff in Heqo. pose proof _wf_sk. rewrite Heqo in H. exfalso. apply H. et. }
        destruct p as [[p a] s].
        apply GRA.point_wise_wf_lift.
        simpl. splits.
        { repeat rewrite GRA.point_add. unfold GRA.embed. simpl.
          clear. r_solve.
          Local Transparent _has_base.
          unfold _has_base. ur. i. des_ifs; r_solve; ur; et.
          des_ifs. }
        { repeat rewrite GRA.point_add. unfold GRA.embed. simpl.
          hexploit valid_size. et. i.
          clear - H. r_solve. rewrite (URA.add_comm _ s). rewrite <- URA.add_assoc.
          set (_ ⋅ _) at 2.
          eassert (c = _).
          { Local Transparent _has_size.
            unfold c. unfold _has_size. ur.
            instantiate (1:= fun k => match k with Some b => if Coqlib.plt b (Pos.of_succ_nat (length (sort (Sk.add mfsk (Sk.add xor_sk Sk.unit))))) then OneShot.unit else OneShot.black | None => OneShot.white 0%Z end).
            extensionalities. destruct H0.
            { ur. des_ifs. } ur. des_ifs. }
          rewrite H0. clear c H0. apply H. }
        { repeat rewrite GRA.point_add. unfold GRA.embed. simpl.
          apply valid_alloc in Heqo.
          clear -Heqo. r_solve. ur. split; [|eapply Heqo]. exists a. r_solve. }
        { repeat rewrite GRA.point_add. unfold GRA.embed. simpl.
          apply valid_point in Heqo.
          clear -Heqo. r_solve. ur. split; [|eapply Heqo]. exists p. r_solve. }
        et.
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
  Qed.

  Require Import Clight2Asm ClightPlus2AsmProof ClightPlus2ClightProof.
  From compcert Require Import Behaviors.

  Theorem final_thm_asm prog asm (LINK: xorlistall0._xor = Some prog) (COMP: transf_clight_program prog = Errors.OK asm) :
    improves2_program (ModL.compile (Mod.add_list (map SMod.to_src mds))) (Asm.semantics asm).
  Proof.
    eapply improves2_program_observe_trans. apply final_thm; et.
    eapply transf_clight_program_preservation in COMP.
    unfold Complements.improves in *. i. hexploit COMP; et.
    i. des. hexploit semantics2to3; et. i. des.
    esplits; et. eapply observation_improves_trans; et.
  Qed.

End PROOF.