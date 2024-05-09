
  Section SIMFUNS.
  Variable xorlink : Clight.program.
  Variable xormod : Mod.t.
  Hypothesis VALID_link : xorlist0._xor = Some xorlink.
  Hypothesis VALID_comp : compile xorlink "xorlist" = Errors.OK xormod.
  Let mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)); ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))].
  (* Require Import ClightPlusMem01Proof. *)

  Variable xor0 : Mod.t.
  Hypothesis VALID : xorlist0._xor = Errors.OK xor0.

  Theorem correct : refines2 [xormod; ClightPlusMem0.Mem mfsk] [xorlist1.xor xormod GlobalStb; main GlobalStb; ClightPlusMem1.Mem mfsk].
  Proof.
    eapply adequacy_local_strong_l. econs; cycle 1.
    { econs; [ss|]. econs; ss. }
    i. econs; cycle 1.
    { econs; [|ss]. apply correct_mod; et. inv SKINCL. inv H6. ss. }
    unfold _xor, compile, get_sk in VALID.
    destruct Pos.eq_dec; [|clarify].
    destruct Coqlib.list_norepet_dec; ss. des_ifs_safe.
    econstructor 1 with (wf := wf) (le := top2); et; ss; cycle 1.
    { eexists. econs. apply to_semantic. iIntros. et. }
    (* each functions has simulation relation *)
    econs; cycle 1.
    econs; cycle 1.
    econs; cycle 1.
    econs; cycle 1.
    econs; et.
    all: des_ifs; inv SKINCL; inv H6; ss.
    - eapply sim_delete_tl; et.
    - eapply sim_delete_hd; et.
    - eapply sim_add_tl; et.
    - eapply sim_add_hd; et.
    Unshelve. exact tt.
  Qed.