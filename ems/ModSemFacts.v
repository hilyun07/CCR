Require Import CoqlibCCR.
Require Export sflibCCR.
Require Export ITreelib.
Require Import STS Behavior.
Require Import ModSem.
Require Import SimGlobal.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Red IRed.
Require Import SimModSem.

Require Import Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault
     TranslateFacts.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Any.


Set Implicit Arguments.


Module ModSemFacts.
Import ModSem.
Section COMM.

  Inductive comm_emb : IFun Es Es -> IFun Es Es -> Prop := 
    |comm_emb_1 : comm_emb emb_l emb_r
    |comm_emb_2 : comm_emb emb_r emb_l
  .

  Inductive comm_ems : itree Es Any.t -> itree Es Any.t -> Prop := 
    | comm_ems_intro emb_l emb_r it (EMB: comm_emb emb_l emb_r) :
        comm_ems (translate emb_l it) (translate emb_r it).

  Definition comm_st (stp: Any.t * Any.t) : Prop :=
    exists a b, fst stp = Any.pair a b /\
    snd stp = Any.pair b a.

  Lemma add_comm_aux
        itl itr stl str (w: unit)
        (COMM: comm_ems itl itr)
        (STATE: comm_st (stl, str))

  :
      sim_itree (fun _ => comm_st) top2 false false w (stl, itl) (str, itr).
  Proof.   
    destruct COMM, STATE. des. ss.
    (* unfold assoc_st. *)
    ginit.
    generalize it as itr.
    clarify.
    generalize x as a0.
    generalize b as b0.
    gcofix CIH. i.
    rewrite (itree_eta_ itr).
    destruct (observe itr).
    - erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
      gstep. apply sim_itree_ret.
      unfold lift_rel.
      eexists; et. splits; et.
      unfold comm_st. exists a0, b0; et.
    - erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
      gstep. 
      apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH; et.
    - erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
      rewrite <- ! bind_trigger.
      destruct e as [c|[s|e]].
      + (* callE *)
        gstep. destruct c, EMB.
        (* SIMPLIFY BELOW *)
        * apply sim_itree_call; clarify.
          -- exists a0, b0; et.
          -- i. unfold comm_st in WF. des. ss. clarify.
             gstep. econs; et.
            gfinal. left. eapply CIH.
        * apply sim_itree_call; clarify.
          -- eexists a0, b0; et.
          -- i. unfold comm_st in WF. des. ss. clarify.
            gstep. econs; et.
             gfinal. left. eapply CIH.

      + (* sE *)
        gstep. destruct s, EMB.
        * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
          eapply sim_itree_progress; et.
          unfold run_l, run_r. rewrite ! Any.pair_split.
          gfinal. left. destruct (run a0). eapply CIH.
        * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
          eapply sim_itree_progress; et.
          unfold run_l, run_r. rewrite ! Any.pair_split.
          gfinal. left. destruct (run b0). eapply CIH.
      + (* eventE *)
        gstep. destruct e, EMB.
        (* Choose *)
        * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH.
        * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH.
        (* Take *)
        * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH.
        * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
          eapply sim_itree_progress; et.
          gfinal. left. eapply CIH.
        (* Syscall *)
        * apply sim_itree_syscall. i.
          eapply sim_itree_flag_down.
          gfinal. left. eapply CIH.
        * apply sim_itree_syscall. i.
          eapply sim_itree_flag_down.
          gfinal. left. eapply CIH.
  Qed. 


  (* Move to somewhere else *)
  Lemma fst_trans_l : forall x, fst (trans_l x) = fst x.
  Proof. i. destruct x. ss. Qed.

  Lemma fst_trans_r : forall x, fst (trans_r x) = fst x.
  Proof. i. destruct x. ss. Qed.

  Lemma fun_fst_trans_l : 
    (fun x : string * (Any.t -> itree Es Any.t) => fst (trans_l x)) = (fun x : string * (Any.t -> itree Es Any.t) => fst x).
  Proof.
    extensionality x. rewrite fst_trans_l. et.
  Qed.

  Lemma fun_fst_trans_r : 
    (fun x : string * (Any.t -> itree Es Any.t) => fst (trans_r x)) = (fun x : string * (Any.t -> itree Es Any.t) => fst x).
  Proof.
    extensionality x. rewrite fst_trans_r. et.
  Qed.

  Lemma fun_fst_trans_l_l :
    (fun x : string * (Any.t -> itree Es Any.t) => fst (trans_l (trans_l x))) = (fun x : string * (Any.t -> itree Es Any.t) => fst x).
  Proof.
    extensionality x. rewrite ! fst_trans_l. et.
  Qed.

  Lemma fun_fst_trans_l_r :
    (fun x : string * (Any.t -> itree Es Any.t) => fst (trans_l (trans_r x))) = (fun x : string * (Any.t -> itree Es Any.t) => fst x).
  Proof.
    extensionality x. rewrite fst_trans_l. rewrite fst_trans_r. et.
  Qed.

  Lemma fun_fst_trans_r_l:
    (fun x : string * (Any.t -> itree Es Any.t) => fst (trans_r (trans_l x))) = (fun x : string * (Any.t -> itree Es Any.t) => fst x).
  Proof.
    extensionality x. rewrite fst_trans_r. rewrite fst_trans_l. et.
  Qed.

  Lemma fun_fst_trans_r_r:
    (fun x : string * (Any.t -> itree Es Any.t) => fst (trans_r (trans_r x))) = (fun x : string * (Any.t -> itree Es Any.t) => fst x).
  Proof.
    extensionality x. rewrite ! fst_trans_r. et.
  Qed.


  Context {CONF: EMSConfig}.

  Theorem add_comm
    ms0 ms1
    (P0 P1: bool) (IMPL: P1 = true -> P0 = true)
    (WF: wf (add ms1 ms0))
  :
  <<COMM: Beh.of_program (compile (add ms0 ms1) (Some P0)) <1= Beh.of_program (compile (add ms1 ms0) (Some P1))>>
  .
  Proof.
    destruct P1; cycle 1.
    { ii. eapply initial_itr_not_wf;et. }
    rewrite IMPL; et.
    unfold compile. red. eapply adequacy_local_aux; et.
    - i. s.
      unfold add_fnsems. rewrite ! alist_find_app_o.
      destruct (alist_find fn (fnsems ms1)) eqn:MS1; destruct (alist_find fn (fnsems ms0)) eqn: MS0.
      + right. unfold trans_l.
        exists (fun args => translate emb_l (i args)).
        exists (fun args => translate emb_r (i args)).
        rewrite ! alist_find_map.
        esplits; et.
        * rewrite MS1. et.
        * inv WF. ss. unfold add_fnsems in wf_fnsems0.
          rewrite ! List.map_app in *. rewrite ! List.map_map in *.
          apply NoDup_app_disjoint with (a:=fn) in wf_fnsems0.
          -- clarify.
          -- replace fn with (fst (fn, i)); et.
             rewrite fun_fst_trans_l.
             apply in_map. apply alist_find_some in MS1. et.
          -- replace fn with (fst (fn, i0)); et.
             rewrite fun_fst_trans_r.
             apply in_map. apply alist_find_some in MS0. et.
        * instantiate (1:= top2). instantiate (1:= unit). instantiate (1:=(fun _ => comm_st)).
          unfold sim_fsem, "==>". i. eapply add_comm_aux; et.
          rewrite H. econs. econs.
      + right. unfold trans_l.
        exists (fun args => translate emb_l (i args)).
        exists (fun args => translate emb_r (i args)).
        rewrite ! alist_find_map.
        esplits; et.
        * rewrite MS1. et.
        * rewrite MS0. s. unfold trans_r. rewrite alist_find_map.
          unfold o_map. rewrite MS1. et.
        * unfold sim_fsem, "==>". i. eapply add_comm_aux; et.
          rewrite H. econs. econs.

      + right. unfold trans_l.
        exists (fun args => translate emb_r (i args)).
        exists (fun args => translate emb_l (i args)).
        rewrite ! alist_find_map.
        esplits; et.
        * rewrite MS1. s. unfold trans_r. rewrite alist_find_map.
          unfold o_map. rewrite MS0. et.
        * rewrite MS0. et.
        * unfold sim_fsem, "==>". i. eapply add_comm_aux; et.
          rewrite H. econs. econs.
      + left. unfold trans_l, trans_r.
        rewrite ! alist_find_map. rewrite MS1, MS0. et.
    - exists tt. econs; et; clarify.
      unfold comm_st. ss. exists (initial_mrs ms1), (initial_mrs ms0). et.
Qed.

End COMM.
Section ASSOC.

Inductive assoc_emb : IFun Es Es -> IFun Es Es -> Prop :=
  |assoc_emb_1 : assoc_emb emb_l (emb_l >>> emb_l)
  |assoc_emb_2 : assoc_emb (emb_l >>> emb_r ) (emb_r >>> emb_l)
  |assoc_emb_3 : assoc_emb (emb_r >>> emb_r) emb_r
.

Inductive assoc_ems : itree Es Any.t -> itree Es Any.t -> Prop :=
  | assoc_ems_intro emb_l emb_r it (EMB: assoc_emb emb_l emb_r) :
      assoc_ems (translate emb_l it) (translate emb_r it).
     
Definition assoc_st (stp: Any.t * Any.t) : Prop :=
  exists a b c, fst stp = Any.pair a (Any.pair b c) /\
  snd stp = Any.pair (Any.pair a b) c
.

Definition assoc_rev_st (stp: Any.t * Any.t) : Prop :=
  exists a b c, fst stp = Any.pair (Any.pair a b) c /\
  snd stp = Any.pair a (Any.pair b c)
.

Lemma add_assoc_aux
        itl itr stl str (w: unit)
        (ASSOC: assoc_ems itl itr)
        (STATE: assoc_st (stl, str))
  :
      sim_itree (fun _ => assoc_st) top2 false false w (stl, itl) (str, itr).
Proof.
  destruct ASSOC, STATE. des. ss.
  (* unfold assoc_st. *)
  ginit.
  generalize it as itr.
  clarify.
  generalize x as a0.
  generalize b as b0.
  generalize c as c0.
  gcofix CIH. i.
  rewrite (itree_eta_ itr).
  destruct (observe itr).
  - erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    gstep. apply sim_itree_ret.
    unfold lift_rel.
    exists tt. splits; et.
    unfold assoc_st. exists a0, b0, c0; et.
  - erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    gstep. 
    apply sim_itree_tau_src. apply sim_itree_tau_tgt.
    eapply sim_itree_progress; et.
    gfinal. left. eapply CIH; et.
  - erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    rewrite <- ! bind_trigger.
    destruct e as [c'|[s|e]].
    + (* callE *)
      gstep. destruct c', EMB.
      (* SIMPLIFY BELOW *)
      * apply sim_itree_call; clarify.
        -- exists a0, b0, c0; et.
        -- i. destruct WF, H, H, H. ss. clarify.
        gstep. econs; et. 
         gfinal. left. eapply CIH.
      * apply sim_itree_call; clarify.
        -- eexists a0, b0, c0; et.
        -- i. unfold assoc_st in WF. des. ss. clarify.
        gstep. econs; et.
           gfinal. left. eapply CIH.
      * apply sim_itree_call; clarify.
        -- eexists a0, b0, c0; et.
        -- i. unfold assoc_st in WF. des. ss. clarify.
        gstep. econs; et.
           gfinal. left. eapply CIH.
    + (* sE *)
      gstep. destruct s, EMB.
      * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
        eapply sim_itree_progress; et.
        unfold run_l, run_r. rewrite ! Any.pair_split.
        gfinal. left. destruct (run a0). eapply CIH.
      * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
        eapply sim_itree_progress; et.
        unfold run_l, run_r. rewrite ! Any.pair_split.
        gfinal. left. destruct (run b0). eapply CIH.
      * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
        eapply sim_itree_progress; et.
        unfold run_l, run_r. rewrite ! Any.pair_split.
        gfinal. left. destruct (run c0). eapply CIH.
    + (* eventE *)
      gstep. destruct e, EMB.
      (* Choose *)
      * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      (* Take *)
      * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      (* Syscall *)
      * apply sim_itree_syscall. i.
        eapply sim_itree_flag_down.
        gfinal. left. eapply CIH.
      * apply sim_itree_syscall. i.
        eapply sim_itree_flag_down.
        gfinal. left. eapply CIH.
      * apply sim_itree_syscall. i.
        eapply sim_itree_flag_down.
        gfinal. left. eapply CIH.
Qed. 

Lemma add_assoc_rev_aux
        itl itr stl str (w: unit)
        (ASSOC: assoc_ems itr itl)
        (STATE: assoc_rev_st (stl, str))

  :
      sim_itree (fun _ => assoc_rev_st) top2 false false w (stl, itl) (str, itr)
.
Proof.
destruct ASSOC, STATE. des. ss.
(* unfold assoc_st. *)
ginit. 
generalize it as itr.
clarify.
generalize x as a0.
generalize b as b0.
generalize c as c0.
gcofix CIH. i.
rewrite (itree_eta_ itr).
destruct (observe itr).
- erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
  gstep. apply sim_itree_ret.
  unfold lift_rel. 
  exists tt. splits; et.
  unfold assoc_st. exists a0, b0, c0; et.
- erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
  gstep. 
  apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
  eapply sim_itree_progress; et.
  gfinal. left. eapply CIH; et.
- erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
  rewrite <- ! bind_trigger.
  destruct e as [c'|[s|e]].
  + (* callE *)
    gstep. destruct c', EMB.
    (* SIMPLIFY BELOW *)
    * apply sim_itree_call; clarify.
      -- exists a0, b0, c0; et.
      -- i. destruct WF, H, H, H. ss. clarify.
      gstep. econs; et. 
       gfinal. left. eapply CIH.
    * apply sim_itree_call; clarify.
      -- eexists a0, b0, c0; et.
      -- i. unfold assoc_rev_st in WF. des. ss. clarify.
      gstep. econs; et.
         gfinal. left. eapply CIH.
    * apply sim_itree_call; clarify.
      -- eexists a0, b0, c0; et.
      -- i. unfold assoc_rev_st in WF. des. ss. clarify.
      gstep. econs; et.
         gfinal. left. eapply CIH.
  + (* sE *)
    gstep. destruct s, EMB.
    * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
      eapply sim_itree_progress; et.
      unfold run_l, run_r. rewrite ! Any.pair_split.
      gfinal. left. destruct (run a0). eapply CIH.
    * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
      eapply sim_itree_progress; et.
      unfold run_l, run_r. rewrite ! Any.pair_split.
      gfinal. left. destruct (run b0). eapply CIH.
    * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
      eapply sim_itree_progress; et.
      unfold run_l, run_r. rewrite ! Any.pair_split.
      gfinal. left. destruct (run c0). eapply CIH.
  + (* eventE *)
    gstep. destruct e, EMB.
    (* Choose *)
    * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH.
    * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH.
    * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH.
    (* Take *)
    * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH.
    * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH.
    * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
      eapply sim_itree_progress; et.
      gfinal. left. eapply CIH.
    (* Syscall *)
    * apply sim_itree_syscall. i.
      eapply sim_itree_flag_down.
      gfinal. left. eapply CIH.
    * apply sim_itree_syscall. i.
      eapply sim_itree_flag_down.
      gfinal. left. eapply CIH.
    * apply sim_itree_syscall. i.
      eapply sim_itree_flag_down.
      gfinal. left. eapply CIH.
Qed.

Context {CONF: EMSConfig}.


Theorem add_assoc
        ms0 ms1 ms2
        (P0 P1: bool) (IMPL: P1 = true -> P0 = true)
  :
    <<COMM: Beh.of_program (compile (add (add ms0 ms1) ms2) (Some P0)) <1=
            Beh.of_program (compile (add ms0 (add ms1 ms2)) (Some P1))>>
.
Proof.
  destruct P1; cycle 1.
  { ii. eapply initial_itr_not_wf;et. }
  rewrite IMPL; et.
  unfold compile. red. 
  eapply adequacy_local_aux; et.
  2: { exists tt. instantiate (1:= top2). instantiate (1:=(fun _ => assoc_st)).  econs; et; clarify.
       unfold assoc_st. ss. exists (initial_mrs ms0), (initial_mrs ms1), (initial_mrs ms2). splits; et. }
  i. s.
  unfold add_fnsems, trans_l, trans_r. s. unfold add_fnsems, trans_l, trans_r.
  rewrite ! alist_find_app_o. rewrite ! alist_find_map.
  rewrite ! alist_find_app_o. rewrite ! alist_find_map.
  destruct (alist_find fn (fnsems ms0)) eqn: MS0; destruct (alist_find fn (fnsems ms1)) eqn:MS1; destruct (alist_find fn (fnsems ms2)) eqn: MS2.
  - right. ss. esplits; et.
    unfold sim_fsem, "==>". i. eapply add_assoc_aux; et. rewrite H.
    unfold translate_l.
    erewrite <- (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    econs. econs.
  - right. ss. esplits; et.
    unfold sim_fsem, "==>". i. eapply add_assoc_aux; et. rewrite H.
    unfold translate_l.
    erewrite <- (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    econs. econs.
  - right. ss. esplits; et.
    unfold sim_fsem, "==>". i. eapply add_assoc_aux; et. rewrite H.
    unfold translate_l.
    erewrite <- (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    econs. econs.
  - right. ss. esplits; et.
    unfold sim_fsem, "==>". i. eapply add_assoc_aux; et. rewrite H.
    unfold translate_l.
    erewrite <- (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    econs. econs.
  - right. esplits; et; s; et.
    unfold sim_fsem, "==>". i. eapply add_assoc_aux; et.
    rewrite H. 
    unfold translate_l, translate_r.
    erewrite <- (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    erewrite <- (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    econs. econs.
  - right. esplits; et; s; et.
    unfold sim_fsem, "==>". i. eapply add_assoc_aux; et.
    rewrite H. 
    unfold translate_l, translate_r.
    erewrite <- (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    erewrite <- (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    econs. econs.
  - right. esplits; et; s; et.
    unfold sim_fsem, "==>". i. eapply add_assoc_aux; et.
    rewrite H.
    unfold translate_l, translate_r.
    erewrite <- ! (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)).
    econs. econs.
  - s. et.
Qed.

Theorem add_assoc_rev
        ms0 ms1 ms2
        (P0 P1: bool) (IMPL: P1 = true -> P0 = true)
  :
    <<COMM: Beh.of_program (compile (add ms0 (add ms1 ms2)) (Some P0)) <1=
            Beh.of_program (compile (add (add ms0 ms1) ms2) (Some P1))>>
.
Proof.
  destruct P1; cycle 1.
  { ii. eapply initial_itr_not_wf;et. }
  rewrite IMPL; et.
  unfold compile. red.
  eapply adequacy_local_aux; et.
  2: { exists tt. instantiate (1:= top2). instantiate (1:=(fun _ => assoc_rev_st)).  econs; et; clarify.
       unfold assoc_rev_st. ss. exists (initial_mrs ms0), (initial_mrs ms1), (initial_mrs ms2). splits; et. }
  i. s.
  unfold add_fnsems, translate_l, translate_r, trans_l, trans_r. s. unfold add_fnsems, translate_l, translate_r, trans_l, trans_r.
  rewrite ! alist_find_app_o. rewrite ! alist_find_map.
  rewrite ! alist_find_app_o. rewrite ! alist_find_map.

  destruct (alist_find fn (fnsems ms0)) eqn: MS0;
  destruct (alist_find fn (fnsems ms1)) eqn:MS1;
  destruct (alist_find fn (fnsems ms2)) eqn: MS2;
  ( ss; et; right; esplits; et; s; et; unfold sim_fsem, "==>"; i; eapply add_assoc_rev_aux; et; rewrite H; unfold translate_l, translate_r;
    erewrite <- ! (@bisimulation_is_eq _ _ _ _ (@translate_cmpE _ _ _ _ _ _ _)); econs; econs).
Qed.

End ASSOC.

Section EMPTY.

Inductive empty_emb : IFun Es Es -> Prop := 
  | empty_emb_intro : empty_emb emb_l
.

Inductive empty_ems : itree Es Any.t -> itree Es Any.t -> Prop := 
  | empty_ems_intro emb_l it (EMB: empty_emb emb_l) :
      empty_ems it (translate emb_l it).

Definition empty_st (stp: Any.t * Any.t) : Prop :=
  exists a, fst stp = a /\ 
  snd stp = Any.pair a tt↑
.

Definition empty_rev_st (stp: Any.t * Any.t) : Prop :=
  exists a, fst stp = Any.pair a tt↑ /\
  snd stp = a
.


Lemma add_empty_aux
        itl itr stl str (w: unit)
        (EMPTY: empty_ems itl itr)
        (STATE: empty_st (stl, str))

  :
      sim_itree (fun _ => empty_st) top2 false false w (stl, itl) (str, itr)
.
Proof.
  destruct EMPTY, STATE. des. ss.
  unfold empty_st.
  ginit. 
  generalize it as itr. 
  clarify.
  generalize x as a.
  gcofix CIH. i.
  rewrite (itree_eta_ itr).
  destruct (observe itr).
  - (* Ret *)
    erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    gstep. apply sim_itree_ret.
    unfold lift_rel. 
    exists tt. splits; et.
  - (* Tau *)
    erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    gstep. 
    apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
    eapply sim_itree_progress; et.
    gfinal. left. eapply CIH; et.
  - (* Vis *)
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    rewrite <- ! bind_trigger.
    destruct e as [c|[s|e]].
    + (* callE *)
      gstep. destruct c, EMB. 
      apply sim_itree_call; clarify.
      -- exists a; et.
      -- i. destruct WF, H. ss. clarify.
        gstep. econs; et. 
         gfinal. left. eapply CIH.
    + (* sE *)
      gstep. destruct s, EMB.
      apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
      eapply sim_itree_progress; et.
      unfold run_l, run_r. rewrite ! Any.pair_split.
      gfinal. left. destruct (run a). eapply CIH.
      
    + (* eventE *)
      gstep. destruct e, EMB.
      (* Choose *)
      * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      (* Take *)
        * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH. 
      (* Syscall *)
        * apply sim_itree_syscall. i.
        eapply sim_itree_flag_down.
        gfinal. left. eapply CIH. 

Qed.

Lemma add_empty_rev_aux
        itl itr stl str (w: unit)
        (EMPTY: empty_ems itr itl)
        (STATE: empty_rev_st (stl, str))

  :
      sim_itree (fun _ => empty_rev_st) top2 false false w (stl, itl) (str, itr)
.
Proof.
  destruct EMPTY, STATE. des. ss.
  unfold empty_rev_st.
  ginit. 
  generalize it as itr. 
  clarify.
  generalize x as a.
  gcofix CIH. i.
  ides itr.
  - (* Ret *)
    erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    gstep. apply sim_itree_ret.
    unfold lift_rel. 
    exists tt. splits; et.
  - (* Tau *)
    erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    gstep. 
    apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
    eapply sim_itree_progress; et.
    gfinal. left. eapply CIH; et.
  - (* Vis *)
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    rewrite <- ! bind_trigger.
    destruct e as [c|[s|e]].
    + (* callE *)
      gstep. destruct c, EMB. 
      apply sim_itree_call; clarify.
      -- exists a; et.
      -- i. destruct WF, H. ss. clarify.
        gstep. econs; et. 
         gfinal. left. eapply CIH.
    + (* sE *)
      gstep. destruct s, EMB.
      apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
      eapply sim_itree_progress; et.
      unfold run_l, run_r. rewrite ! Any.pair_split.
      gfinal. left. destruct (run a). eapply CIH.
      
    + (* eventE *)
      gstep. destruct e, EMB.
      (* Choose *)
      * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      (* Take *)
        * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH. 
      (* Syscall *)
        * apply sim_itree_syscall. i.
        eapply sim_itree_flag_down.
        gfinal. left. eapply CIH. 

Qed.


Context {CONF: EMSConfig}.

Theorem add_empty
      ms
      (P0 P1: bool) (IMPL: P1 = true -> P0 = true)
      (WF: wf ms)
:
  <<EMPTY: Beh.of_program (compile (add ms empty) (Some P0)) <1=
          Beh.of_program (compile ms (Some P1))>>
.
Proof.
  destruct P1; cycle 1.
  { ii. eapply initial_itr_not_wf;et. }
  rewrite IMPL; et.
  unfold compile. red. 
  eapply adequacy_local_aux; et.
  2: { exists tt. instantiate (1:= top2). instantiate (1:= (fun _ => empty_st)). econs; et; clarify.
       unfold empty_st. ss. exists (initial_mrs ms). et. }
  i. s.
  unfold add_fnsems, trans_l, trans_r. s.
  rewrite ! alist_find_app_o. rewrite ! alist_find_map. 
  destruct (alist_find fn (fnsems ms)) eqn: MS; cycle 1.
  - left. et.
  - ss. right. esplits; et.
    unfold sim_fsem, "==>". i. apply add_empty_aux; et.
    rewrite H. econs. econs.
Qed.

Theorem add_empty_rev
      ms
      (P0 P1: bool) (IMPL: P1 = true -> P0 = true)
      (WF: wf ms)
:
  <<EMPTY: Beh.of_program (compile ms (Some P0)) <1=
          Beh.of_program (compile (add ms empty) (Some P1))>>
.
Proof.
  destruct P1; cycle 1.
  { ii. eapply initial_itr_not_wf;et. }
  rewrite IMPL; et.
  unfold compile. red. 
  eapply adequacy_local_aux; et.
  2: { exists tt. instantiate (1:= top2). instantiate (1:= (fun _ => empty_rev_st)). econs; et; clarify.
       unfold empty_st. ss. exists (initial_mrs ms). et. }
  i. s.
  unfold add_fnsems, trans_l, trans_r. s.
  rewrite ! alist_find_app_o. rewrite ! alist_find_map. 
  destruct (alist_find fn (fnsems ms)) eqn: MS; cycle 1.
  - left. et.
  - ss. right. esplits; et.
    unfold sim_fsem, "==>". i. apply add_empty_rev_aux; et.
    rewrite H. econs. econs.
Qed.
End EMPTY.


End ModSemFacts.

Module ModFacts.
Import Mod.
Section BEH.

Context `{Sk.ld}.
Context {CONF: EMSConfig}.


Theorem add_comm
        md0 md1
  :
    <<COMM: Beh.of_program (compile (add md0 md1)) <1= Beh.of_program (compile (add md1 md0))>>
.

Proof.
  ii. unfold compile in *.
  destruct (wf_bool (add md1 md0)) eqn: ?.
  2: { eapply ModSem.initial_itr_not_wf. }
  unfold wf_bool in Heqb. destruct wf_dec; clarify. unfold wf in w.
  ss. des. assert (SK': Sk.wf (Sk.add (sk md0) (sk md1))).
  { apply Sk.wf_comm. auto. }
  rewrite Sk.add_comm; et.
  eapply ModSemFacts.add_comm; [| |et]; cycle 1.
  { rewrite Sk.add_comm; et. }
  i. unfold wf_bool. destruct wf_dec; clarify. exfalso. apply n.
  split; auto. unfold enclose. ss. rewrite Sk.add_comm; et.
  inv WF. econs; ss.
  unfold ModSem.add_fnsems in *.
  rewrite ! List.map_app in *.
  rewrite ! List.map_map in *.
  rewrite ModSemFacts.fun_fst_trans_l in *.
  rewrite ModSemFacts.fun_fst_trans_r in *.
  eapply nodup_comm. et.
Qed.

Theorem add_assoc
        md0 md1 md2
  :
    <<ASSOC: Beh.of_program (compile (add (add md0 md1) md2)) <1=
            Beh.of_program (compile (add md0 (add md1 md2)))>>
.
Proof. 
  ii. unfold compile in *.
  destruct (wf_bool (add md0 _)) eqn: ?.
  2: { eapply ModSem.initial_itr_not_wf. }
  unfold wf_bool in Heqb. destruct wf_dec; clarify. unfold wf in w.
  ss. des. assert (SK': Sk.wf (Sk.add (Sk.add (sk md0) (sk md1)) (sk md2))).
  { rewrite <- Sk.add_assoc. et. }
  eapply ModSemFacts.add_assoc; [|rewrite Sk.add_assoc;et].
  i. unfold wf_bool. destruct wf_dec; clarify. exfalso. apply n.
  split; et. unfold enclose. ss.
  rewrite <- Sk.add_assoc.
  inv WF. econs.
  repeat (ss; unfold ModSem.add_fnsems in *; rewrite ! List.map_app in *; rewrite ! List.map_map in *).
  rewrite ModSemFacts.fun_fst_trans_l in *.
  rewrite ModSemFacts.fun_fst_trans_r in *.
  rewrite ModSemFacts.fun_fst_trans_l_l in *.
  rewrite ModSemFacts.fun_fst_trans_l_r in *.
  rewrite ModSemFacts.fun_fst_trans_r_l in *.
  rewrite ModSemFacts.fun_fst_trans_r_r in *.
  rewrite <- app_assoc. apply wf_fnsems.
Qed.

Theorem add_assoc_rev
        md0 md1 md2
  :
    <<COMM: Beh.of_program (compile (add md0 (add md1 md2))) <1=
            Beh.of_program (compile (add (add md0 md1) md2))>>
.
Proof.
  ii. unfold compile in *.
  destruct (wf_bool (add _ md2)) eqn: ?.
  2: { eapply ModSem.initial_itr_not_wf. }
  unfold wf_bool in Heqb. destruct wf_dec; clarify. unfold wf in w.
  ss. des. assert (SK': Sk.wf (Sk.add (sk md0) (Sk.add (sk md1) (sk md2)))).
  { rewrite Sk.add_assoc. et. }
  eapply ModSemFacts.add_assoc_rev; [|rewrite <- Sk.add_assoc;et].
  i. unfold wf_bool. destruct wf_dec; clarify. exfalso. apply n.
  split; et. unfold enclose. ss.
  rewrite Sk.add_assoc.
  inv WF. econs.
  repeat (ss; unfold ModSem.add_fnsems in *; rewrite ! List.map_app in *; rewrite ! List.map_map in *).
  rewrite ModSemFacts.fun_fst_trans_l in *.
  rewrite ModSemFacts.fun_fst_trans_r in *.
  rewrite ModSemFacts.fun_fst_trans_l_l in *.
  rewrite ModSemFacts.fun_fst_trans_l_r in *.
  rewrite ModSemFacts.fun_fst_trans_r_l in *.
  rewrite ModSemFacts.fun_fst_trans_r_r in *.
  rewrite app_assoc. apply wf_fnsems.
Qed.

Lemma add_empty_r
      md
  : 
    << EMPTY: Beh.of_program (compile (add md empty)) <1=
              Beh.of_program (compile md)>>
.
Proof.
  ii. unfold compile in *.
  destruct (wf_bool md) eqn: ?.
  2: { eapply ModSem.initial_itr_not_wf. }
  unfold wf_bool in Heqb. destruct wf_dec; clarify. unfold wf in w.
  ss. des. assert (SK': Sk.wf (Sk.add (sk md) Sk.unit)).
  { rewrite Sk.add_unit_r. et. }
  eapply ModSemFacts.add_empty; [|et|]; cycle 1.
  { unfold ModSem.compile, ModSem.empty, enclose.
    rewrite Sk.add_unit_r in PR. et. }
  i. unfold wf_bool. destruct wf_dec; clarify. exfalso. apply n.
  unfold wf. esplits; et. ss.
  inv WF. econs. 
  rewrite Sk.add_unit_r.
  unfold ModSem.add, ModSem.add_fnsems. ss.
  rewrite List.map_app. rewrite List.map_map.
  ss. rewrite app_nil_r.
  rewrite ModSemFacts.fun_fst_trans_l. ss.
Qed.

Lemma add_empty_l
      md
  : 
    << EMPTY: Beh.of_program (compile (add empty md)) <1=
              Beh.of_program (compile md)>>
.
Proof.
  ii. apply add_empty_r. apply add_comm. et.
Qed.

Lemma add_empty_rev_r
      md
  : 
    << EMPTY: Beh.of_program (compile md) <1=
              Beh.of_program (compile (add md empty))>>
.
Proof.
  ii. unfold compile in *.
  destruct (wf_bool (add md empty)) eqn: ?.
  2: { eapply ModSem.initial_itr_not_wf. }
  unfold wf_bool in Heqb. destruct wf_dec; clarify. unfold wf in w.
  des. assert (SK': Sk.wf (sk md)).
  { ss. rewrite Sk.add_unit_r in SK. et. }
  eapply ModSemFacts.add_empty_rev; cycle 1.
  - ss. rewrite Sk.add_unit_r in *. inv WF. econs.
    unfold ModSem.add in wf_fnsems. ss.
    unfold ModSem.add_fnsems in wf_fnsems. ss.
    rewrite List.map_app in wf_fnsems.
    rewrite List.map_map in wf_fnsems.
    rewrite ModSemFacts.fun_fst_trans_l in wf_fnsems. ss.
    eapply nodup_app_l in wf_fnsems. ss.
  - unfold ModSem.compile, ModSem.empty, enclose. ss.
    rewrite Sk.add_unit_r. et.
  - i. unfold wf_bool. destruct wf_dec; clarify. exfalso. apply n.
    unfold wf. esplits; et. ss.
    inv WF. econs.
    rewrite Sk.add_unit_r in wf_fnsems.
    unfold ModSem.add, ModSem.add_fnsems in *. ss.
    rewrite List.map_app, List.map_map in wf_fnsems.
    ss. rewrite app_nil_r in wf_fnsems.
    rewrite ModSemFacts.fun_fst_trans_l in wf_fnsems. ss.
Qed.

Lemma add_empty_rev_l
      md
  : 
    << EMPTY: Beh.of_program (compile md) <1=
              Beh.of_program (compile (add empty md))>>
.
Proof. 
  ii. apply add_comm. apply add_empty_rev_r. et. 
Qed.

Definition add_list_cons
          x xs
        :
          (add_list (x::xs) = (add x (add_list xs)))
.
Proof. ss. Qed.


(* Do we still add by list? (and refines2, refines_proper, etc.)
Definition add_list (xs: list t): t :=
  fold_right add empty xs
.

(* Lemma add_list_single: forall (x: t), add_list [x] = x.
Proof. ii; cbn. rewrite add_empty_r. refl. Qed. *)


Definition add_list_snoc
          x xs
        :
          << SNOC: Beh.of_program (compile (add_list (snoc xs x))) <1= 
                   Beh.of_program (compile (add (add_list xs) x)) >>
.
Proof. Admitted. *)

  (* ginduction xs; ii; ss.
  { cbn. rewrite add_empty_l, add_empty_r. et. }
  { cbn. rewrite <- add_assoc'.  r in IHxs. r. f_equal.}  *)

End BEH.
End ModFacts.

Section REFINE.
  Context `{Sk.ld}.

  Section CONF.
  Context {CONF: EMSConfig}.

  (*** vertical composition ***)
  Global Program Instance refines_PreOrder: PreOrder refines.

  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H1. eapply H0. ss. Qed.


  Global Program Instance refines_strong_PreOrder: PreOrder refines_strong.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H1. eapply H0. ss. Qed.

  Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. eapply H1. eapply H0. eauto. Qed.

  (*** horizontal composition ***)
  Theorem refines_add
        (md0_src md0_tgt md1_src md1_tgt: Mod.t)
        (SIM0: refines md0_tgt md0_src)
        (SIM1: refines md1_tgt md1_src)
    :
        <<SIM: refines (Mod.add md0_tgt md1_tgt) (Mod.add md0_src md1_src)>>
  .
  Proof. 
    ii. r in SIM0. r in SIM1. 
    pose proof ModFacts.add_comm as COMM. 
    pose proof ModFacts.add_assoc as ASSOC. 
    pose proof ModFacts.add_assoc_rev as ASSOC'. 
    r in COMM. r in ASSOC. r in ASSOC'.
    apply ASSOC. 
    apply SIM1.
    apply ASSOC'. apply COMM. apply ASSOC'. apply COMM.
    apply SIM0.
    apply ASSOC'. apply COMM. apply ASSOC'.
    apply PR.
  Qed.

  Theorem refines_proper_l
    (mds0_src mds0_tgt: list Mod.t) (ctx: Mod.t)
    (SIM0: refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
  :
    <<SIM: refines (Mod.add ctx (Mod.add_list mds0_tgt)) (Mod.add ctx (Mod.add_list mds0_src))>>
  .
  Proof.
    ii. r in SIM0.
    apply ModFacts.add_assoc. apply ModFacts.add_assoc_rev in PR.
    apply SIM0. apply PR. 
  Qed.

  Theorem refines_proper_r
    (mds0_src mds0_tgt: list Mod.t) (ctx: Mod.t)
    (SIM0: refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
  :
    <<SIM: refines (Mod.add (Mod.add_list mds0_tgt) (ctx)) (Mod.add (Mod.add_list mds0_src) (ctx))>>
  .
  Proof.
    ii. r in SIM0.
    pose proof ModFacts.add_comm as COMM.
    apply COMM. apply COMM in PR.
    apply ModFacts.add_assoc_rev. apply ModFacts.add_assoc in PR.
    apply COMM. apply COMM in PR.
    apply SIM0. apply PR.  
  Qed.

  Lemma refines_close: refines <2= refines_closed.
  Proof. 
    ii. specialize (PR Mod.empty). ss.
    pose proof ModFacts.add_empty_l as EMP.
    r in EMP.
    apply EMP with (x0 := x2) in PR.
    2: { apply ModFacts.add_empty_rev_l. et. } 
    apply PR.
  Qed.

  End CONF.

   Theorem refines_strong_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines_strong md0_tgt md0_src)
         (SIM1: refines_strong md1_tgt md1_src)
     :
       <<SIM: refines_strong (Mod.add md0_tgt md1_tgt) (Mod.add md0_src md1_src)>>
   .
   Proof.
     intros CONF. eapply (@refines_add CONF); et.
   Qed.
   Lemma refines_strong_refines {CONF: EMSConfig}: refines_strong <2= refines.
   Proof. ii. eapply PR; et. Qed.

End REFINE.

