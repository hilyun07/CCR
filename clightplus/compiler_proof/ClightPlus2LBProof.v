(** Libraries. *)
Require Import String.
From compcert Require Import
     Coqlib Errors AST Linking Smallstep Behaviors
     (** Languages (syntax and semantics). *)
     Ctypes Csyntax Csem Cstrategy Cexec
     Clight Csharpminor Cminor CminorSel RTL LTL Linear Mach Asm
     (** Translation passes. *)
     Initializers SimplExpr SimplLocals
     Cshmgen Cminorgen Selection RTLgen
     Tailcall Inlining Renumber Constprop
     CSE Deadcode Unusedglob Allocation
     Tunneling Linearize CleanupLabels Debugvar
     Stacking Asmgen
     (** Proofs of semantic preservation. *)
     SimplExprproof SimplLocalsproof Cshmgenproof
     Cminorgenproof Selectionproof RTLgenproof
     Tailcallproof Inliningproof Renumberproof
     Constpropproof CSEproof Deadcodeproof
     Unusedglobproof Allocproof Tunnelingproof
     Linearizeproof CleanupLabelsproof Debugvarproof
     Stackingproof Asmgenproof
     (** Command-line flags. *)
     Compopts
     (** Sum up *)
     Compiler Complements CoqlibC
.

Require Import Clight2Asm.

Set Implicit Arguments.


Section CLIGHTPROOF.

  Local Open Scope string_scope.
  Local Open Scope linking_scope.

  Definition Clight_to_Asm :=
  mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  ::: mkpass Inliningproof.match_prog
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass Unusedglobproof.match_prog
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

  Definition match_prog_clight: Clight.program -> Asm.program -> Prop :=
    pass_match (compose_passes Clight_to_Asm).

  Theorem transf_clight_program_match
      p tp
      (T: transf_clight_program p = Errors.OK tp) :
    match_prog_clight p tp.
  Proof.
    unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
    rename p into p2.
    destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
    destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
    unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
    destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
    destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
    unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
    set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
    destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
    set (p9 := Renumber.transf_program p8) in *.
    set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
    set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
    destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
    destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
    destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
    destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
    set (p16 := Tunneling.tunnel_program p15) in *.
    destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
    set (p18 := CleanupLabels.transf_program p17) in *.
    destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
    destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
    unfold match_prog_clight; simpl.
    exists p3; split. apply Cshmgenproof.transf_program_match; auto.
    exists p4; split. apply Cminorgenproof.transf_program_match; auto.
    exists p5; split. apply Selectionproof.transf_program_match; auto.
    exists p6; split. apply RTLgenproof.transf_program_match; auto.
    exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
    exists p8; split. apply Inliningproof.transf_program_match; auto.
    exists p9; split. apply Renumberproof.transf_program_match; auto.
    exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
    exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
    exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
    exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
    exists p14; split. apply Unusedglobproof.transf_program_match; auto.
    exists p15; split. apply Allocproof.transf_program_match; auto.
    exists p16; split. apply Tunnelingproof.transf_program_match.
    exists p17; split. apply Linearizeproof.transf_program_match; auto.
    exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
    exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
    exists p20; split. apply Stackingproof.transf_program_match; auto.
    exists tp; split. apply Asmgenproof.transf_program_match; auto.
    reflexivity.
  Qed.

  Lemma match_prog_clight_preservation
      p tp
      (TRANSF: match_prog_clight p tp) :
    improves (Clight.semantics2 p) (Asm.semantics tp).
  Proof.
    unfold match_prog_clight, pass_match in TRANSF; simpl in TRANSF.
    Ltac DestructM :=
        match goal with
        [ H: exists p, _ /\ _ |- _ ] =>
        let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
        destruct H as (p & M & MM); clear H
    end.
    repeat DestructM. subst tp.

    etrans. eapply Cshmgen_correct; eauto.
    etrans. eapply Cminorgen_correct; eauto.
    etrans. eapply Selection_correct; eauto.
    etrans. eapply RTLgen_correct; eauto.
    etrans. exploit Tailcall_correct; eauto. intros REL. eapply rtc_improves; eauto.
    etrans. eapply Inlining_correct; eauto.
    etrans. eapply Renumber0_correct; eauto.
    etrans. exploit Constprop_correct; eauto. intros REL. eapply rtc_improves; eauto.
    etrans. exploit Renumber1_correct; eauto. intros REL. eapply rtc_improves; eauto.
    etrans. exploit CSE_correct; eauto. intros REL. eapply rtc_improves; eauto.
    etrans. exploit Deadcode_correct; eauto. intros REL. eapply rtc_improves; eauto.
    etrans. eapply Unusedglob_correct; eauto.
    etrans. eapply Allocation_correct; eauto.
    etrans. eapply Tunneling_correct; eauto.
    etrans. eapply Linearize_correct; eauto.
    etrans. eapply CleanupLabels_correct; eauto.
    etrans. exploit Debugvar_correct; eauto. intros REL. eapply rtc_improves; eauto.
    etrans. eapply Stacking_correct; eauto.
    etrans. eapply Asmgen_correct; eauto. refl.
  Qed.

  Theorem transf_clight_program_preservation_lbd
      p tp
      (T: transf_clight_program p = Errors.OK tp) :
    improves (Clight.semantics2 p) (Lowerbound.semantics tp).
  Proof.
    etrans. apply match_prog_clight_preservation.
    apply transf_clight_program_match. et.
    eapply Lowerbound_correct; eauto.
  Qed.

End CLIGHTPROOF.

Require Import Skeleton ModSem.
Require Import ClightPlusgen.
Require Import STS2SmallStep.
Require Import ClightPlusgenCorrect.
Require Import ClightPlus2ClightProof.

Theorem compile_behavior_improves_lbd
    (clight_prog : Clight.program) (asm : Asm.program)
    (mn: string) (md: Mod.t) (sk_mem: Sk.t)
    (COMP: compile clight_prog mn = Errors.OK md)
    (MEMSKEL: mem_skel clight_prog = Errors.OK sk_mem)
    (COMP': transf_clight_program clight_prog = Errors.OK asm)
:
    (improves2_program (clightp_sem sk_mem md) (Lowerbound.semantics asm)).
Proof.
  eapply improves2_program_observe_trans.
  eapply single_compile_program_improves; et.
  eapply transf_clight_program_preservation_lbd in COMP'.
  unfold Complements.improves in *. i. hexploit COMP'; et.
  i. des. hexploit semantics2to3; et. i. des.
  esplits; et. eapply observation_improves_trans; et.
Qed.