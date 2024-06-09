From compcert Require Import Globalenvs Smallstep Simulation AST Integers Events Behaviors Errors Memory Values Maps.
From compcert Require Import Ctypes Clight Clightdefs Globalenvs.
Require Import ClightPlus2ClightMatchEnv.
Require Import String.

Definition match_temps le le' := forall id, CoqlibCCR.option_rel (Val.inject inject_id) (le ! id) (le' ! id).

Inductive match_cont : cont -> cont -> Prop :=
  | match_Kstop : match_cont Kstop Kstop
  | match_Kseq s k k' (NEXT: match_cont k k') : match_cont (Kseq s k) (Kseq s k')
  | match_Kloop1 s1 s2 k k' (NEXT: match_cont k k') : match_cont (Kloop1 s1 s2 k) (Kloop1 s1 s2 k')
  | match_Kloop2 s1 s2 k k' (NEXT: match_cont k k') : match_cont (Kloop2 s1 s2 k) (Kloop2 s1 s2 k')
  | match_Kswitch k k' (NEXT: match_cont k k') : match_cont (Kswitch k) (Kswitch k')
  | match_Kcall id f e le le' k k' 
      (LEINJ: match_temps le le') 
      (NEXT: match_cont k k') 
    : match_cont (Kcall id f e le k) (Kcall id f e le' k').

Variant match_states : state -> state -> Prop :=
  | match_state f s k k' e le le' m m' 
      (EXT: Mem.extends m m')
      (LEINJ: match_temps le le')
      (NEXT: match_cont k k')
    : match_states (State f s k e le m) (State f s k' e le' m')
  | match_callstate fd args args' k k' m m' 
      (EXT: Mem.extends m m')
      (VALINJ: List.Forall2 (Val.inject inject_id) args args')
      (NEXT: match_cont k k')
    : match_states (Callstate fd args k m) (Callstate fd args' k' m')
  | match_returnstate res res' k k' m m' 
      (EXT: Mem.extends m m')
      (VALINJ: Val.inject inject_id res res')
      (NEXT: match_cont k k')
    : match_states (Returnstate res k m) (Returnstate res' k' m').

Lemma match_states_bsim p gmtgt st_src st_tgt
  (M: match_states st_src st_tgt)
:
  NOSTUTTER.bsim (semantics3 p) (semantics2 p) gmtgt
  (* (concrete_snapshot (Genv.globalenv p) (Callstate f [] Kstop m'))  *)
  lt 0%nat st_src st_tgt.
Proof.
Admitted.

Lemma semantics2to3 p:
  forall obs1, program_observes (Clight.semantics2 p) obs1 ->
  exists obs0, program_observes (semantics3 p) obs0 /\ observation_improves obs0 obs1.
Proof.
  apply backward_simulation_observation_improves.
  econs. econs.
  { apply Arith.Wf_nat.lt_wf. }
  { i. inversion INITSRC. eexists. econs; eauto. }
  i. inv INITSRC. inv INITTGT. inv TGTCAP.
  replace ge0 with ge in * by auto. clear ge0. clarify.
  esplits; ss.
  { econs; eauto. }
  { eauto. admit "asd". }
  { eapply match_states_bsim. econs; eauto. 2:econs. admit "". }
Admitted.