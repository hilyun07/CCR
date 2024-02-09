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

Require Import ClightPlusExprgen.
Require Import ClightPlusgen.
Require Import ClightPlus2ClightMatchEnv.

From compcert Require Import Ctypes Clight Clightdefs.


Set Implicit Arguments.

Section GENV.

  Context `{Σ: GRA.t}.

  Variable prog : program.
  Variable sk : Sk.t.
  Variable defs : list (ident * globdef fundef type).
  (* Let types : list composite_definition := prog.(prog_types).
  Let public : list ident := prog.(prog_public).
  Let _main : ident := prog.(prog_main).
  Let ce := List.map (map_fst string_of_ident) (PTree.elements prog.(prog_comp_env)). *)

  Lemma found_itree_clight_function s i
        (mn: string) 
        (FOUND : find
                    ((fun '(k2, _) => s ?[ eq ] k2) <*>
                     map_snd
                      (fun sem => transl_all mn (T:= Any.t) ∘ sem))
                    (decomp_fundefs prog sk defs) = Some (s, i))
    :
     exists p, p2s p = s /\ In (s, i) (decomp_fundefs prog sk defs).
  Proof.
  Admitted.

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
  

  Lemma tgt_genv_match_symb_def
        ident b gd1 gd2
        (NO_REP: Coqlib.list_norepet (List.map fst defs))
        (GFSYM: Genv.find_symbol (Genv.globalenv prog) ident = Some b)
        (GFDEF: Genv.find_def (Genv.globalenv prog) b = Some gd1)
        (INTGT: In (ident, gd2) (prog_defs prog))
    :
      gd1 = gd2.
  Proof.
    (* assert (AST.prog_defs prog = defs) by now
      unfold mkprogram, build_composite_env' in *; des_ifs.
    assert (prog_defs prog = defs) by now
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
    (* assert (AST.prog_defs prog = defs) by now
      unfold mkprogram, build_composite_env' in *; des_ifs.
    assert (prog_defs prog = defs) by now
      unfold mkprogram, build_composite_env' in *; des_ifs.
    hexploit prog_defmap_norepet.
    { unfold prog_defs_names. rewrite H. auto. }
    { eauto. }
    i. apply Genv.find_def_symbol in H1. des. clarify.
  Qed. *)
  Admitted.

End GENV.