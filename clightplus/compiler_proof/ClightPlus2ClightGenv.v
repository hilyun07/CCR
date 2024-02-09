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
    remember ((fun '(k2, _) => s ?[ eq ] k2) <*>
             map_snd
               (fun sem : option string * Any.t -> itree Es Any.t =>
                transl_all mn (T:=Any.t) ∘ sem)) as cond.
    revert FOUND. induction defs.
    { ss. }
    clear Heqcond.
    i. destruct a. destruct g.
    2:{ simpl. eapply IHl. simpl in FOUND. eauto. }
    unfold decomp_fundefs in FOUND. destruct f.
    (* INTERNAL *)
    { destruct (cond (p2s i0,
             cfunU
               (fun vl : list Values.val =>
                if Pos.eq_dec i0 (prog_main prog)
                then
                 if
                  type_eq (type_of_function f)
                    (Tfunction Tnil type_int32s cc_default)
                 then
                  ` v : Values.val <- decomp_func sk (get_ce prog) f vl;;
                  match v with
                  | Values.Vint _ => Ret v
                  | _ => triggerUB
                  end
                 else triggerUB
                else decomp_func sk (get_ce prog) f vl))) eqn:COND.
      2:{ simpl in *. rewrite COND in FOUND. ss. exploit IHl; eauto. i. des.
          esplits; eauto. }
      simpl in *. rewrite COND in FOUND. inv FOUND. esplits; eauto. }
    (* EXTERNAL *)
    { simpl. eapply IHl; eauto. }
  Qed.

  Lemma decomp_fundefs_decomp_func i str p
        (P2S: p2s p = str)
        (INLEFT: In (str, i) (decomp_fundefs prog sk defs)) 
    :
        exists f, 
          (i = cfunU (fun vl =>
                        if Pos.eq_dec p prog.(prog_main)
                        then if type_eq (type_of_function f) (Tfunction Tnil type_int32s cc_default)
                            then v <- decomp_func sk (get_ce prog) f vl;; 
                                  match v with
                                  | Values.Vint _ => Ret v
                                  | _ => triggerUB
                                  end
                            else triggerUB
                        else decomp_func sk (get_ce prog) f vl)) /\ In (p, Gfun (Internal f)) defs.
  Proof.
    ginduction defs; i.
    { ss. }
    destruct a. destruct g.
    2:{ simpl in INLEFT. exploit IHl; eauto. i. des.
        esplits; eauto. clear - x1. simpl. auto. }
    destruct f.
    2:{ simpl in INLEFT. exploit IHl; eauto. i. des.
        esplits; eauto. clear - x1. simpl. auto. }
    Opaque type_eq. simpl in *. inv INLEFT.
    - inv H. eapply p2s_inj in H1. subst. eauto.
    - exploit IHl. eauto. eauto. i. des. esplits; eauto.
  Qed.

  Lemma tgt_genv_match_symb_def
        ident b gd1 gd2
        (NO_REP: Coqlib.list_norepet (List.map fst (prog_defs prog)))
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
        (NO_REP: Coqlib.list_norepet (List.map fst (prog_defs prog)))
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