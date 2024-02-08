From compcert Require Import Maps Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
From ExtLib Require Import Data.List.
Require Import CoqlibCCR.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import AList.

Require Import ClightPlusgen.
Require Import ClightPlus2ClightMatchEnv.

From compcert Require Import Ctypes Clight Clightdefs.

Import Permutation.

Set Implicit Arguments.

Section GENV.

  Lemma cenv_match_some sk ge co i
      (MGCE: match_gce sk ge)
    :
      alist_find i (snd sk) = Some co -> ge.(genv_cenv) ! i = Some co.
  Proof.
    i. apply PTree.elements_complete. inv MGCE. rewrite MCE. et.
  Qed.

  Lemma cenv_match_none sk ge i
      (MGCE: match_gce sk ge)
    :
      alist_find i (snd sk) = None -> ge.(genv_cenv) ! i = None.
  Proof.
    i. destruct (ge.(genv_cenv) ! i) eqn:?; et. apply PTree.elements_correct in Heqo. 
    inv MGCE. rewrite MCE in Heqo. clarify.
  Qed.

  Lemma match_sizeof ty sk ge
      (MCE: match_gce sk ge)
    :
      Ctypes.sizeof ge ty = ClightPlusExprgen.sizeof (snd sk) ty.
  Proof.
    induction ty; ss.
    - rewrite IHty. et.
    - destruct (ge.(genv_cenv) ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
    - destruct (ge.(genv_cenv) ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
  Qed.

  Lemma match_alignof_blockcopy ty sk ge
      (MCE: match_gce sk ge)
    :
      Ctypes.alignof_blockcopy ge ty = ClightPlusExprgen.alignof_blockcopy (snd sk) ty.
  Proof.
    induction ty; ss.
    - destruct (ge.(genv_cenv) ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
    - destruct (ge.(genv_cenv) ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
  Qed.

  Lemma match_alignof ty sk ge
      (MCE: match_gce sk ge)
    :
      Ctypes.alignof ge ty = ClightPlusExprgen.alignof (snd sk) ty.
  Proof.
    induction ty; ss.
    - rewrite IHty. et.
    - destruct (ge.(genv_cenv) ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
    - destruct (ge.(genv_cenv) ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
  Qed.

  Variable prog : program.
  Variable sk : Sk.t.
  Let types : list composite_definition := prog.(prog_types).
  Let defs : list (ident * globdef fundef type) := prog.(prog_defs).
  Let public : list ident := prog.(prog_public).
  Let _main : ident := prog.(prog_main).
  Let ce := List.map (map_fst string_of_ident) (PTree.elements prog.(prog_comp_env)).

  (* Lemma found_itree_clight_function
        (fn: string) 
        (i: list Values.val -> itree Es Values.val) 
        (mn: string) (p: ident)
        (FOUND : find
                    ((fun '(k2, _) => fn ?[ eq ] k2) <*>
                     map_snd
                      (fun sem => transl_all mn (T:=Any.t) ∘ sem) <*>
                     (fun '(fn, f) => (fn, cfunU f)))
                    (decomp_fundefs prog sk defs) = 
                 Some (p, i))
    :
      string_of_ident p = fn /\ In (p, i) (decomp_fundefs prog sk defs).
  Proof.
    apply find_some in FOUND. des. split; et.
    unfold "<*>" in FOUND0. ss. rewrite eq_rel_dec_correct in FOUND0.
    des_ifs.
  Qed. *)

  (* Lemma decomp_fundefs_decomp_func i p
        (INLEFT: In (p, i) (decomp_fundefs prog sk defs)) 
    :
        exists f, 
          (i = fun vl => 
                v <- decomp_func sk ce f vl;; 
                (if Pos.eq_dec p (ident_of_string "main")
                 then (match v with Values.Vint _ => Ret v | _ => triggerUB end)
                 else Ret v)) /\ In (p, Gfun (Internal f)) defs.
  Proof.
    induction defs.
    { inv INLEFT. }
    destruct a as [? [[|]|]].
    2, 3: apply IHl in INLEFT; des; simpl; eauto.
    simpl in INLEFT. des.
    2: apply IHl in INLEFT; des; simpl; eauto.
    inv INLEFT. simpl. eexists; split; eauto.
  Qed.   *)
  
  Lemma in_def_gdefs a clight_prog
        (INDEFS_FUN: In a defs)
    :
        In a clight_prog.(prog_defs).
  Proof.
  Admitted.


  Lemma tgt_genv_match_symb_def
        ident b gd1 gd2
        (NO_REP: Coqlib.list_norepet (List.map fst defs))
        (GFSYM: Genv.find_symbol (Genv.globalenv prog) ident = Some b)
        (GFDEF: Genv.find_def (Genv.globalenv prog) b = Some gd1)
        (INTGT: In (ident, gd2) (prog_defs prog))
    :
      gd1 = gd2.
  Proof.
    (* assert (AST.prog_defs clight_prog = defs) by now
      unfold mkprogram, build_composite_env' in *; des_ifs.
    assert (prog_defs clight_prog = defs) by now
      unfold mkprogram, build_composite_env' in *; des_ifs.
    hexploit prog_defmap_norepet.
    { unfold prog_defs_names. rewrite H. auto. }
    { eauto. }
    i. apply Genv.find_def_symbol in H1. des. clarify.
  Qed. *)
  Admitted.

  Lemma tgt_genv_find_def_by_blk
        ident b gd 
        (NO_REP: Coqlib.list_norepet (List.map fst defs))
        (GFSYM: Genv.find_symbol (Genv.globalenv prog) ident = Some b)
        (INTGT: In (ident, gd) (prog_defs prog))
    :
      Genv.find_def (Genv.globalenv prog) b = Some gd.
  Proof.
    (* assert (AST.prog_defs clight_prog = defs) by now
      unfold mkprogram, build_composite_env' in *; des_ifs.
    assert (prog_defs clight_prog = defs) by now
      unfold mkprogram, build_composite_env' in *; des_ifs.
    hexploit prog_defmap_norepet.
    { unfold prog_defs_names. rewrite H. auto. }
    { eauto. }
    i. apply Genv.find_def_symbol in H1. des. clarify.
  Qed. *)
  Admitted.

End GENV.