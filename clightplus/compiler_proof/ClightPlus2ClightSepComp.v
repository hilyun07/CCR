From compcert Require Import Coqlib Behaviors Integers Floats Values AST Globalenvs Ctypes Cop Clight Clightdefs.

Require Import CoqlibCCR.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import STS2SmallStep.
Require Import ClightPlusMem0.
Require Import IRed.
Require Import ClightPlusExprgen.
Require Import ClightPlusgen.

Require Import ClightPlus2ClightMatchEnv.
Require Import ClightPlus2ClightArith.
Require Import ClightPlus2ClightGenv.
Require Import ClightPlus2ClightLenv.
Require Import ClightPlus2ClightMem.
Require Import ClightPlus2ClightSim.
Require Import ClightPlus2ClightMatchStmt.
Require Import ClightPlus2ClightSimAll.


Section PROOFSINGLE.

  Ltac solve_mkprogram := unfold mkprogram, build_composite_env' in *; des_ifs; eauto.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0. (* these are itree normalization tactic *)
  Ltac sim_tau := (try sim_red); try pfold; econs 3; ss; clarify; eexists; exists (ModSemL.step_tau _).
  (* Ltac sim_triggerUB := unfold triggerUB; (try sim_red); econs 5; i; ss; auto; *)
  (*                       dependent destruction STEP; try (irw in x; clarify; fail). *)
  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB := 
    (try rename H into HH); ss; unfold triggerUB; try sim_red; try pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Ltac to_oeq :=
    match goal with
| |- ?A = ?B => change (oeq A B)
    end.

  Ltac from_oeq :=
    match goal with
    | |- oeq ?A ?B => change (A = B)
    end.

  Ltac sim_redE :=
    to_oeq; cbn; repeat (Red.prw ltac:(_red_gen) 1 0); repeat (Red.prw ltac:(_red_gen) 2 0); from_oeq.

  Ltac tgt_step := try pfold; econs 4; eexists; eexists.

  Ltac wrap_up := try pfold; econs 7; et; right.

  Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss.

(*
  Definition imp_sem (src : Imp.programL) := compile_val (ModL.add (Mod.lift (Mem (fun _ => false))) (ImpMod.get_modL src)).

  Definition imp_initial_state (src : Imp.programL) := (imp_sem src).(initial_state).
 *)

(** Why does final value determines sort of state? *)
(** The reason why Vint is special is just "int main(void)"? *)

  Definition compile_val md := @ModL.compile _ EMSConfigC md. 

  Definition clightligt_sem prog mn := compile_val (ModL.add (Mod.lift Mem) (Mod.lift (get_mod prog mn))).

  Definition clightlight_initial_state prog mn := (clightligt_sem prog mn).(STS.initial_state).

  Opaque ident_of_string.

  Lemma NoDup_norepeat :
    forall A (l : list A), Coqlib.list_norepet l <-> NoDup l.
  Proof.
    split; induction l; i; ss; eauto.
    - econs.
    - inv H. econs; eauto.
    - econs.
    - inv H. econs; eauto.
  Qed.

  Arguments Es_to_eventE /.
  Arguments itree_of_stmt /. 
  Arguments sloop_iter_body_two /. 
  Arguments ktree_of_cont_itree /. 

  Theorem single_compile_behavior_improves
          mn clight_prog
          left_st right_st
          (MAIN: clight_prog.(prog_main) = ident_of_string "main")
          (WFDEF2: NoDup (List.map fst clight_prog.(prog_defs)))
          (SINIT: left_st = clightlight_initial_state clight_prog mn)
          (TINIT: Clight.initial_state clight_prog right_st)
        :
          <<IMPROVES: @improves2 _ (Clight.semantics2 clight_prog) left_st right_st>>.
  Proof.
    Local Opaque type_eq.
    eapply adequacy; eauto.
    { apply Csharpminor_wf_semantics. }
    red. rewrite SINIT. unfold clightlight_initial_state in *. ss; clarify. inv TINIT.
    unfold ModSemL.initial_itr.
    rename ge into tge, H into INIT_TMEM, H0 into MAIN_TBLOCK, H1 into FIND_TMAINF, H2 into MAIN_TYPE, f into tmain.
    (* set (Build_genv tge (let (ce, _) := build_composite_env' types WF_TYPES in ce)) as ge. *)
    unfold ModL.wf_bool. destruct ModL.wf_dec; ss. 2:{ sim_triggerUB. }
    grind. unfold ITree.map. sim_red.

    destruct (alist_find "main" _) eqn:FOUNDMAIN;[|sim_triggerUB]. ss.
    rewrite alist_find_find_some in FOUNDMAIN. rewrite find_map in FOUNDMAIN. uo; des_ifs; ss.
    destruct p. inv H0.
    

    sim_red. rewrite alist_find_map_snd in FOUNDMAIN. uo. des_ifs.
    (* simpl ModL.enclose in wf_fnsems. set (ClightPlusSkel.sort _) as sk_canon in *.
    replace (ModSemL.fnsems _) with ((ModSemL.fnsems (MemSem sk_canon)) ++ (ModSemL.fnsems (modsem clight_prog mn sk_canon))) in wf_fnsems by ss.
    rewrite map_app in wf_fnsems. hexploit nodup_app_r; et. *)
    rewrite <- NoDup_norepeat in WFDEF2.
    apply alist_find_find_some in 
    apply alist_find_some in Heq.
    set (fun f => cfunU (E:=Es) (fun vl => if type_eq (type_of_function f) (Tfunction Ctypes.Tnil type_int32s cc_default)
                                           then v <- decomp_func (get_sk (clight_prog.(prog_defs))) (get_ce clight_prog) f vl;; 
                                              match v with
                                              | Vint _ => Ret v
                                              | _ => triggerUB
                                              end
                                           else triggerUB)) as main_form.
    assert (exists f, In (prog_main clight_prog, Gfun (Internal f)) (prog_defs clight_prog) /\ main_form f = i0).
    { admit "". }
    des. unfold Genv.find_funct_ptr in FIND_TMAINF. des_ifs. hexploit tgt_genv_match_symb_def; et.
    i. clarify. unfold main_form. des_ifs; try sim_triggerUB. ss. sim_red. unfold decomp_func. sim_red. unfold hide.
    pfold_reverse. 
    eapply step_function_entry with (ge := ge) (sk := sge_init); et; ss.
    { unfold sge_init, tge, mkprogram, Globalenvs.Genv.globalenv. des_ifs_safe. ss.
      clear -WFDEF_NODUP WFDEF_EXT SK wf_fnsems.
      admit "This can be proved from these hypothesis". }
    { instantiate (1 := m0). clear -INIT_TMEM. admit "This can be proved from these hypothesis". }
    i. tgt_step.
    { econs. unfold ge in H. unfold tge in H. ss. unfold mkprogram in *. des_ifs; et. }
    econs 7; et. left. 

    eapply match_states_sim; eauto.
    { i. ss. clear - H5. depgen s. revert fd. induction defs; i; ss.
      des_ifs; et.
      { ss. des; et. clarify. apply Any.upcast_inj in H0. des.
        apply JMeq_eq in EQ0. clarify. et. }
      { ss. des; et. clarify. apply Any.upcast_inj in H0. des.
        apply JMeq_eq in EQ0. clarify. } }
    { set (update _ _ _) as init_pstate. econs; et. 
      { admit "global proof". }
      { instantiate (1:= init_pstate). unfold init_pstate. unfold update. ss. }
      { unfold fnsem_has_internal. i. apply Sk.sort_incl_rev in H5. ss. des; clarify.
        { apply Any.upcast_inj in H5. des. apply JMeq_eq in EQ0. clarify. }
        { apply Any.upcast_inj in H5. des. apply JMeq_eq in EQ0. clarify. }
        exists mn.
        admit "relation between decomp_fundef and get_sk". }
      { econs; et. }
      instantiate (1 := mn).
      ss. unfold itree_stop, kstop_itree, itree_of_cont_pop. ss. sim_redE.
      unfold sge_init. ss.
      set (EventsL.interp_Es _ _ _) as s. 
      set (EventsL.interp_Es _ _ _) as s'.
      assert (s = s').
      { unfold s, s'. sim_redE. unfold prog_comp_env, mkprogram. des_ifs. } 
      rewrite H5. apply bind_extk. i. sim_redE. des_ifs_safe. sim_redE.
      clear FIND_ITREE.
      destruct o.
      { sim_redE. unfold mkprogram.  des_ifs_safe. ss. apply bind_extk. i. des_ifs_safe. sim_redE.


        apply bind_extk. i. des_ifs_safe. sim_redE. et. }
      { destruct o0.
        { des_ifs_safe. sim_redE. apply bind_extk. i. des_ifs_safe. sim_redE. apply bind_extk.
          i. des_ifs_safe. sim_redE. apply bind_extk.
          i. des_ifs_safe. sim_redE. et. }
        { sim_redE. do 2 f_equal. des_ifs_safe. sim_redE.
          unfold mkprogram. des_ifs. ss. apply bind_extk.
          i. des_ifs_safe. sim_redE. apply bind_extk.
          i. des_ifs_safe. sim_redE. et. } } }
  Qed.

  (* Theorem single_compile_program_improves
          (types: list Ctypes.composite_definition)
          (defs: list (AST.ident * AST.globdef Clight.fundef Ctypes.type))
          (public: list AST.ident)
          (WF_TYPES: Clightdefs.wf_composites types)
          mn clight_prog
          (WFDEF_NODUP: NoDup (List.map fst defs))
          (WFDEF_EXT: forall a, In a Mem.(Mod.sk) -> In a (List.map (fun '(p, gd) => (string_of_ident p, gd↑)) defs))
          (COMP: clight_prog = mkprogram types defs public (ident_of_string "main") WF_TYPES)
    :
      <<IMPROVES: improves2_program (clightligt_sem types defs WF_TYPES mn) (Clight.semantics2 clight_prog)>>.
  Proof.
    red. unfold improves2_program. i. inv BEH.
    { hexploit single_compile_behavior_improves.
      1,2,3: et. 1: refl. 1: ss; et. unfold improves2, clightlight_initial_state. i.
      eapply H1; et. }
    (* initiall wrong case, for us only when main is not found *)
    exists (Tr.ub). split; red; eauto.
    2:{ pfold. econs 4; eauto.
        - ss.
        - unfold Behaviors.behavior_prefix. exists (Behaviors.Goes_wrong Events.E0). ss.
    }
    Print Clight.initial_state.
    ss. unfold ModSemL.initial_itr.
    pfold. econs 6; ss; eauto.
    unfold Beh.inter. ss. unfold assume. grind.
    apply ModSemL.step_trigger_take_iff in STEP. des. clarify. split; eauto.
    red. unfold ITree.map; ss.
    unfold unwrapU. des_ifs.
    (* main do not exists, ub *)
    2:{ sim_red. unfold triggerUB. grind. econs 6; ss. grind. ss. apply ModSemL.step_trigger_take_iff in STEP. des. clarify. }

    (* found main, contradiction *)
    exfalso.
    rename Heq into FSEM.
    grind. rewrite alist_find_find_some in FSEM. rewrite find_map in FSEM.
    match goal with
    | [ FSEM: o_map (?a) _ = _ |- _ ] => destruct a eqn:FOUND; ss; clarify
    end.
    destruct p as [? ?]; ss; clarify. rewrite find_map in FOUND.
    uo. des_ifs_safe.
    eapply found_itree_clight_function in Heq. des; clarify.
    assert (exists f, In (p0, Gfun (Internal f)) defs).
    { clear -Heq0 Heq. set (Sk.sort _) as sk in *. clearbody sk.
      revert_until defs. induction defs; et.
      i. ss. destruct a. destruct g.
      - destruct f.
        + ss. destruct Heq0.
          * clarify. et. 
          * eapply IHdefs in H; et. des. et.
        + eapply IHdefs in Heq0; et. des. et.
      - eapply IHdefs in Heq0; et. des. et. }
    des. replace defs with (mkprogram types defs public (ident_of_string "main") WF_TYPES).(AST.prog_defs) in H0 by solve_mkprogram.
    hexploit Globalenvs.Genv.find_symbol_exists; et. i. des.
    hexploit tgt_genv_find_def_by_blk; eauto. 1:{ admit "provable". }
    i. assert (exists m, Genv.init_mem (mkprogram types defs public (ident_of_string "main") WF_TYPES) = Some m) by admit "hypothesis".
    des. 
    specialize H with (Callstate (Internal f) [] Kstop m).
    eapply H.
    econs; ss; eauto.
    { solve_mkprogram. ss. replace (ident_of_string "main") with p0 by admit "provable". et. }
    { unfold Genv.find_funct_ptr. rewrite H3. et. }
    admit "hypothesis".
    Unshelve. inv Heq0.
  Qed. *)

End PROOFSINGLE.


(* 

  Definition init_data_list_aligned_dec p il :{Genv.init_data_list_aligned p il} + {~ Genv.init_data_list_aligned p il}.
  Proof.
    revert p. induction il.
    - i. left. ss.
    - i. destruct (Zdivide_dec (Genv.init_data_alignment a) p).
      + destruct (IHil (p + init_data_size a)). { left. ss. }
        right. ii. apply n. ss. des. et.
      + right. ii. apply n. ss. des. et.
  Defined.

  

  Fixpoint mem_init_condition sk l :=
    match l with
    | [] => true
    | (Gvar v) :: l' => if init_data_list_aligned_dec 0 (gvar_init v) 
                        then match l with
                        else false
    | _ :: l' => mem_init_condition sk l'
    end *)
