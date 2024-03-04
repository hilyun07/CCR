From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
Require Import CoqlibCCR.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import ClightPlusExprgen.
Require Import STS2SmallStep.
Require Import ClightPlusMem0.
Require Import IRed.

Require Import ClightPlus2ClightMatchEnv.
Require Import ClightPlus2ClightArith.
Require Import ClightPlus2ClightLenv.
Require Import ClightPlus2ClightMem.

From compcert Require Import Ctypes Clight Clightdefs Values.

Lemma unbind_trigger E:
  forall [X0 X1 A : Type] (ktr0 : X0 -> itree E A) (ktr1 : X1 -> itree E A) e0 e1,
    (x <- trigger e0;; ktr0 x = x <- trigger e1;; ktr1 x) -> (X0 = X1 /\ e0 ~= e1 /\ ktr0 ~= ktr1).
Proof.
  i. eapply f_equal with (f:=_observe) in H. cbn in H.
  inv H. split; auto.
  dependent destruction H3. dependent destruction H2.
  cbv in x. subst. split; auto.
  assert (ktr0 = ktr1); clarify.
  extensionality x. eapply equal_f in x0.
  irw in x0. eauto.
Qed.

Lemma angelic_step :
  forall (X : Prop) (ktr next : itree eventE Any.t),
    ModSem.step (trigger (Take X);;; ktr) None next -> (next = ktr /\ X).
Proof.
  i. dependent destruction H; try (irw in x; clarify; fail).
  rewrite <- bind_trigger in x. apply unbind_trigger in x.
  des. clarify.
Qed.

Lemma eval_exprlist_length :
  forall a b c d l1 tl l2
    (EE: eval_exprlist a b c d l1 tl l2),
    <<EELEN: List.length l1 = List.length l2>>.
Proof.
  i. induction EE; ss; clarify; eauto.
Qed.

Section PROOF.

  Import ModSem.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Definition compile_val md := @Mod.compile _ EMSConfigC md. 

  Let _sim_mon := Eval simpl in (fun (src: Mod.t) (tgt: Clight.program) => @sim_mon (compile_val src) (Clight.semantics2 tgt)).
  Hint Resolve _sim_mon: paco.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); try pfold; econs 3; ss; clarify; eexists; exists (step_tau _).

  Definition arrow (A B: Prop): Prop := A -> B.
  Opaque arrow.

  Definition oeq [A] (a: A) b: Prop := (a = b).
  Opaque oeq. 

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

  Ltac to_arrow :=
    match goal with
| |- ?A -> ?B => change (arrow A B)
    end.

  Ltac from_arrow :=
    match goal with
    | |- arrow ?A ?B => change (A -> B)
    end.
  Ltac sim_redH H :=
    revert H; to_arrow; (repeat (cbn; Red.prw ltac:(_red_gen) 2 2 0)); from_arrow; intros H.

  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB := 
    (try rename H into HH); ss; unfold triggerUB; try sim_red; try pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Ltac tgt_step := try pfold; econs 4; eexists; eexists; [|left].

  Ltac wrap_up := try pfold; econs 7; et; right.

  Ltac remove_UBcase := des_ifs; try sim_red; try solve [sim_triggerUB].

  Ltac step := repeat (sim_red; try sim_tau).

  Ltac uhu := 
    match goal with
    | |- _sim _ _ _ _ _ (_ <- (unwrapU ?x);; _) _ =>
      let t := fresh in
      set (unwrapU x) as t; unfold unwrapU in t; unfold t; clear t
    end.

  Ltac eapplyf NEXT := let X := fresh "X" in hexploit NEXT;[..|intro X; punfold X; et].
  Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss.

  Local Opaque Pos.of_nat.

  Local Opaque Pos.of_succ_nat.
  Local Opaque translate_r.

  Local Arguments ccallU /.
  Local Arguments run_l /.

  Lemma step_load pstate f_table modl cprog sk tge tle te m tm any
    (PSTATE: Any.split pstate = Some (m↑, any))
    (EQ: f_table = (Mod.add Mem modl).(Mod.enclose))
    (MGE: match_ge sk tge)
    (MM: match_mem sk tge m tm)
    chunk addr
    tf tcode tcont ktr b r
    (NEXT: forall v,
            Mem.loadv chunk tm (map_val sk tge addr) = Some (map_val sk tge v) ->
            paco4
              (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: p_state * val <- 
        (interp_Es
          (prog f_table)
          (translate_r (ccallU "load" (chunk, addr))) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    step. ss. step. unfold loadF. step.
    rewrite PSTATE. step. uhu. remove_UBcase.
    erewrite <- Any.split_pair; et. eapplyf NEXT.
    unfold Mem.loadv in *. des_ifs_safe.
    destruct addr; ss; cycle 1.
    - hexploit match_mem_load; et.
    - destruct Mem.denormalize eqn:? in Heq; clarify.
      destruct p. hexploit match_mem_denormalize; et.
      i. rewrite H. hexploit match_mem_load; et.
  Qed.

  Lemma step_store pstate f_table modl cprog sk tge tle te m tm any
    (PSTATE: Any.split pstate = Some (m↑, any))
    (EQ: f_table = (Mod.add Mem modl).(Mod.enclose))
    (MGE: match_ge sk tge)
    (MM: match_mem sk tge m tm)
    chunk addr v
    tf tcode tcont ktr b r
    (NEXT: forall tm' m',
            Mem.storev chunk tm (map_val sk tge addr) (map_val sk tge v) = Some tm' ->
            match_mem sk tge m' tm' ->
            paco4
              (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (Any.pair m'↑ any, ()))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: p_state * () <- 
        (interp_Es
          (prog f_table)
          (translate_r (ccallU "store" (chunk, addr, v))) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    step. ss. step. unfold storeF. step.
    rewrite PSTATE. step. uhu. remove_UBcase.
    rewrite Any.pair_split. step.
    unfold Mem.storev in Heq. des_ifs.
    - hexploit match_mem_denormalize; et. i. 
      hexploit match_mem_store; et. i. des. eapplyf NEXT; et.
      unfold Mem.storev. ss. des_ifs.
    - hexploit match_mem_store; et. i. des. eapplyf NEXT; et.
  Qed.

  Lemma step_memcpy pstate f_table modl cprog sk tge tle te m tm any
    (PSTATE: Any.split pstate = Some (m↑, any))
    (EQ: f_table = (Mod.add Mem modl).(Mod.enclose))
    (MGE: match_ge sk tge)
    (MM: match_mem sk tge m tm)
    al sz vp v
    tf tcode tcont ktr b r
    (NEXT: forall tm' m',
            extcall_memcpy_sem sz al tge [map_val sk tge vp; map_val sk tge v] tm E0 Vundef tm' ->
            match_mem sk tge m' tm' ->
            paco4
              (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (Any.pair m'↑ any, Vundef))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: p_state * val <- 
        (interp_Es
          (prog f_table)
          (translate_r (ccallU "memcpy" (al, sz, [vp; v]))) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    step. ss. step. destruct dec.
    - step. hexploit NEXT; et. { econs 2; et. }
      i. punfold H. replace pstate with (Any.pair m↑ any); et.
      erewrite <- Any.split_pair; et.
    - step. rewrite PSTATE. step. uhu. remove_UBcase.
      uhu. remove_UBcase. remove_UBcase. uhu. remove_UBcase.
      uhu. remove_UBcase. rewrite Any.pair_split. step.
      hexploit match_to_ptr; et. i. move Heq at bottom.
      hexploit match_to_ptr; et. i. ss.
      hexploit match_mem_loadbytes; et. i.
      hexploit match_mem_storebytes; et. i. des.
      eapplyf NEXT; et.
      bsimpl. repeat destruct Zdivide_dec; ss; try nia.
      repeat destruct Coqlib.zle; ss; try nia.
      repeat destruct dec; ss; try nia.
      all: econs; et; try nia.
      + repeat destruct dec; ss; et; des; clarify.
      + repeat destruct dec; ss; et; des; clarify.
      + destruct (dec (Ptrofs.unsigned _) _) in Heq2; et.
        left. ss. destruct (dec b1 b0); ss; des; clarify.
        all: ii; apply n1; eapply map_blk_inj; et.
  Qed.

  (* Lemma step_loadbytes pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    blk ofs n
    tf tcode tcont ktr b r mn
    (NEXT: forall l,
            Mem.loadbytes tm (map_blk sk tge blk) (Ptrofs.unsigned ofs) n = Some (List.map (map_memval sk tge) l) ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, l))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: p_state * list memval <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "loadbytes" (Vptr blk ofs, n))) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. sim_red. sim_tau. ss. sim_red. unfold loadbytesF. repeat (sim_red; sim_tau). sim_red.
    rewrite PSTATE. sim_red. unfold unwrapU. remove_UBcase. sim_tau. sim_red. rewrite Any.upcast_downcast.
    sim_red. eapplyf NEXT. hexploit match_mem_loadbytes; et.
  Qed.

  Lemma step_storebytes pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    blk ofs l
    tf tcode tcont ktr b r mn
    (NEXT: forall tm' m',
            Mem.storebytes tm (map_blk sk tge blk) (Ptrofs.unsigned ofs) (List.map (map_memval sk tge) l) = Some tm' ->
            match_mem sk tge m' tm' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, ()))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: p_state * () <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "storebytes" (Vptr blk ofs, l))) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. sim_red. sim_tau. ss. sim_red. unfold storebytesF. sim_red. repeat (sim_tau; sim_red).
    rewrite PSTATE. sim_red. unfold unwrapU. remove_UBcase. repeat (sim_tau; sim_red). rewrite Any.upcast_downcast.
    sim_red. hexploit match_mem_storebytes; et. i. des. eapplyf NEXT; et.
  Qed.

  Lemma step_load_bitfield pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    ty sz sg pos width addr
    tf tcode tcont ktr b r mn
    (NEXT: forall v,
            Cop.load_bitfield ty sz sg pos width tm (map_val sk tge addr) (map_val sk tge v)->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (load_bitfield_c ty sz sg pos width addr)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold load_bitfield_c.
    remove_UBcase; eapply step_load; et;
      i; remove_UBcase; eapplyf NEXT; econs; try nia; try des_ifs.
  Qed.

  Lemma step_store_bitfield pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    ty sz sg pos width addr v
    tf tcode tcont ktr b r mn
    (NEXT: forall tm' m' v',
            match_mem sk tge m' tm' ->
            Cop.store_bitfield ty sz sg pos width tm (map_val sk tge addr) (map_val sk tge v) tm' (map_val sk tge v')->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, v'))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (store_bitfield_c ty sz sg pos width addr v)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold store_bitfield_c. remove_UBcase;
      eapply step_load; et; i; remove_UBcase; 
        eapply step_store; et; i; sim_red;
          eapplyf NEXT; et; econs; et; try nia; des_ifs.
  Qed. *)

  Lemma step_sub_ptr pstate f_table modl cprog sk tge tle te m tm any
    (PSTATE: Any.split pstate = Some (m↑, any))
    (EQ: f_table = (Mod.add Mem modl).(Mod.enclose))
    (MGE: match_ge sk tge)
    (MM: match_mem sk tge m tm)
    sz v1 v2
    tf tcode tcont ktr bflag r
    (NEXT: forall ofs,
          Cop._sem_ptr_sub_join_common (map_val sk tge v1) (map_val sk tge v2) tm = Some ofs ->
          (0 < sz <= Ptrofs.max_signed)%Z ->
            paco4
              (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true bflag
              (ktr (pstate, Vptrofs (Ptrofs.divs ofs (Ptrofs.repr sz))))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true bflag
      (`r0: (p_state * val) <- 
        (interp_Es
          (prog f_table)
          (translate_r (ccallU "sub_ptr" (sz, v1, v2))) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    step. ss. step. rewrite PSTATE. step. uhu. remove_UBcase.
    destruct Coqlib.zlt; destruct Coqlib.zle; ss.
    replace (Any.pair _ _) with pstate by now apply Any.split_pair; et.
    eapplyf NEXT; et; try nia.
    unfold Cop._sem_ptr_sub_join_common in *.
    des_ifs; ss; clarify.
    - unfold Cop._sem_ptr_sub_join, Cop._sem_ptr_sub in *. des_ifs.
    - unfold Cop._sem_ptr_sub_join in Heq0. des_ifs.
      + unfold Cop._sem_ptr_sub in *. des_ifs.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        des_ifs. move Heq6 at bottom.
        hexploit match_to_ptr; et. i.
        hexploit match_to_int; et. i.
        simpl in Heq0. simpl in Heq4. simpl map_val in H. simpl map_val in H0.
        clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_int_val, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val.
        rewrite H. rewrite H0. des_ifs.
        { simpl in Heq0. clarify. }
        { simpl in Heq0. simpl in Heq2. clarify. }
        { f_equal. symmetry. simpl in Heq2. clarify. apply Ptrofs.same_if_eq. et. }
      + unfold Cop._sem_ptr_sub in Heq1. des_ifs.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        des_ifs. move Heq3 at bottom.
        hexploit match_to_ptr; et. i.
        simpl in Heq1. simpl map_val in H. clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val.
        rewrite H. des_ifs.
        all: try solve [ss; clarify].
        simpl in Heq0. unfold IntPtrRel.to_int_val in Heq5. simpl in Heq5. clarify. 
        clear - Heq6 H Heq4.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in Heq6.
        des_ifs. unfold Mem.to_ptr, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
        des_ifs. unfold Mem.denormalize in *. apply Maps.PTree.gselectf in Heq2.
        des. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in Heq3.
        des_ifs; bsimpl; clarify. des.
        clear - Heq4. hexploit Ptrofs.eq_spec. rewrite Heq4. i. exfalso.
        apply H. unfold Ptrofs.of_int64, Ptrofs.sub, Int64.sub.
        apply Ptrofs.eqm_samerepr. rewrite <- Ptrofs.eqm64; et.
        eapply Int64.eqm_trans. 2:{ apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        2:{ apply Int64.eqm_sub. apply Int64.eqm_refl. apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        { apply Int64.eqm_sub. apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr. apply Int64.eqm_refl. }
        eapply Int64.eqm_refl2. nia.
      + unfold Cop._sem_ptr_sub in Heq2. des_ifs.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        des_ifs. hexploit match_to_int; et. i.
        simpl in Heq3. simpl map_val in H. clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_int_val, IntPtrRel.option_to_val.
        rewrite H. des_ifs.
        { ss. clarify. f_equal. apply Ptrofs.same_if_eq. et. }
        unfold IntPtrRel.to_ptr_val in Heq7. simpl in Heq7, Heq3. clarify.
        clear - Heq6 H Heq5.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in Heq6.
        des_ifs. unfold Mem.to_ptr, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
        des_ifs. unfold Mem.denormalize in *. apply Maps.PTree.gselectf in Heq2.
        des. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in Heq4.
        des_ifs; bsimpl; clarify. des.
        clear - Heq5. hexploit Ptrofs.eq_spec. rewrite Heq5. i. exfalso.
        apply H. unfold Ptrofs.of_int64, Ptrofs.sub, Int64.sub.
        apply Ptrofs.eqm_samerepr. rewrite <- Ptrofs.eqm64; et.
        eapply Int64.eqm_trans. 2:{ apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        2:{ apply Int64.eqm_sub. apply Int64.eqm_refl. apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        { apply Int64.eqm_sub. apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr. apply Int64.eqm_refl. }
        eapply Int64.eqm_refl2. nia.
    - unfold Cop._sem_ptr_sub_join, Cop._sem_ptr_sub in *. des_ifs.
    - unfold Cop._sem_ptr_sub_join in Heq0. des_ifs.
      + unfold Cop._sem_ptr_sub in *. des_ifs.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        des_ifs. hexploit match_to_ptr; et. i.
        move Heq4 at bottom.
        hexploit match_to_int; et. i.
        simpl in Heq6. simpl in Heq1. simpl map_val in H. simpl map_val in H0.
        clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_int_val, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val.
        rewrite H. rewrite H0. des_ifs.
        { simpl in Heq1. clarify. }
        { simpl in Heq1. simpl in Heq2. clarify. }
        { f_equal. symmetry. simpl in Heq2. clarify. apply Ptrofs.same_if_eq. et. }
      + unfold Cop._sem_ptr_sub in Heq1. des_ifs.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        des_ifs.
        hexploit match_to_ptr; et. i.
        simpl in Heq3. simpl map_val in H. clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val.
        rewrite H. des_ifs.
        all: try solve [ss; clarify].
        simpl in Heq0. unfold IntPtrRel.to_int_val in Heq6. simpl in Heq6. clarify.
        clear - Heq5 H Heq4.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in Heq5.
        des_ifs. unfold Mem.to_ptr, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
        des_ifs. unfold Mem.denormalize in *. apply Maps.PTree.gselectf in Heq2.
        des. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in Heq3.
        des_ifs; bsimpl; clarify. des.
        clear - Heq4. hexploit Ptrofs.eq_spec. rewrite Heq4. i. exfalso.
        apply H. unfold Ptrofs.of_int64, Ptrofs.sub, Int64.sub.
        apply Ptrofs.eqm_samerepr. rewrite <- Ptrofs.eqm64; et.
        eapply Int64.eqm_trans. 2:{ apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        2:{ apply Int64.eqm_sub. apply Int64.eqm_unsigned_repr. apply Int64.eqm_refl. }
        eapply Int64.eqm_trans.
        { apply Int64.eqm_sub. apply Int64.eqm_refl. apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_refl2. nia.
      + unfold Cop._sem_ptr_sub in Heq2. des_ifs.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        des_ifs. move Heq3 at bottom.
        hexploit match_to_int; et. i.
        simpl in Heq2. simpl map_val in H. clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_int_val, IntPtrRel.option_to_val.
        rewrite H. des_ifs.
        { ss. clarify. f_equal. apply Ptrofs.same_if_eq. et. }
        unfold IntPtrRel.to_ptr_val in Heq6. simpl in Heq6, Heq2. clarify.
        clear - Heq7 H Heq5.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in Heq7.
        des_ifs. unfold Mem.to_ptr, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
        des_ifs. unfold Mem.denormalize in *. apply Maps.PTree.gselectf in Heq2.
        des. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in Heq4.
        des_ifs; bsimpl; clarify. des.
        clear - Heq5. hexploit Ptrofs.eq_spec. rewrite Heq5. i. exfalso.
        apply H. unfold Ptrofs.of_int64, Ptrofs.sub, Int64.sub.
        apply Ptrofs.eqm_samerepr. rewrite <- Ptrofs.eqm64; et.
        eapply Int64.eqm_trans. 2:{ apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        2:{ apply Int64.eqm_sub. apply Int64.eqm_unsigned_repr. apply Int64.eqm_refl. }
        eapply Int64.eqm_trans.
        { apply Int64.eqm_sub. apply Int64.eqm_refl. apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_refl2. nia.
    - destruct eq_block eqn:? in Heq0; clarify. 
      subst. destruct eq_block; clarify.
  Qed.

  Lemma step_cmp_ptr pstate f_table modl cprog sk tge tle te m tm any
    (PSTATE: Any.split pstate = Some (m↑, any))
    (EQ: f_table = (Mod.add Mem modl).(Mod.enclose))
    (MGE: match_ge sk tge)
    (MM: match_mem sk tge m tm)
    c v1 v2
    tf tcode tcont ktr bflag r
    (NEXT: forall b,
          Cop.cmp_ptr_join_common tm c (map_val sk tge v1) (map_val sk tge v2) = Some (Val.of_bool b) ->
            paco4
              (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true bflag
              (ktr (pstate, b))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true bflag
      (`r0: (p_state * bool) <- 
        (interp_Es
          (prog f_table)
          (translate_r (ccallU "cmp_ptr" (c, v1, v2))) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    step. ss. step. unfold cmp_ptrF. step. rewrite PSTATE. step.
    unfold cmp_ptr. remove_UBcase.
    (* v1 : Vint, v2 : Vptr *)
    - unfold cmp_ptr_join. unfold cmp_ptr. remove_UBcase. remove_UBcase.
    (* v1 : Vlong, v2 : Vlong *)
    - replace (Any.pair _ _) with pstate by now apply Any.split_pair; et. eapplyf NEXT. ss.
    (* v1 : null, v2 : Vptr *)
    - remove_UBcase. uhu. remove_UBcase.
      replace (Any.pair _ _) with pstate by now apply Any.split_pair; et.
      eapplyf NEXT. ss. unfold Cop.cmp_ptr. des_ifs. ss.
      erewrite !match_valid_pointer; et. des_ifs. rewrite Heq3. ss.
    (* v1 : notnull long, v2 : Vptr *)
    - unfold cmp_ptr_join. unfold cmp_ptr. remove_UBcase.
      unfold Val.cmplu_bool. destruct IntPtrRel.to_ptr_val eqn:?; clarify.
      all: try solve [unfold IntPtrRel.to_ptr_val, Mem.to_ptr in *; des_ifs].
      2: ss; destruct IntPtrRel.to_int_val eqn:?; clarify.
      all: try solve [unfold IntPtrRel.to_int_val, Mem.to_int, Mem.ptr2int_v in *; des_ifs].
      (* v1 : long -> ptr in m fail *)
      + remove_UBcase.
        replace (Any.pair _ _) with pstate by now apply Any.split_pair; et.
        eapplyf NEXT. hexploit match_to_int_val; et. i. ss.
        unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool.
        ss. rewrite Heq0. ss.
        unfold Val.of_bool, Val.cmp_different_blocks.
        (* v2 : ptr -> long suc *)
        des_ifs; ss; clarify; des_ifs.
        (* v1 : long -> ptr in tm should fail *)
        all: try solve [erewrite match_to_ptr_val_rev in Heqv; et; clarify].
        all: try solve [unfold IntPtrRel.to_ptr_val, Mem.to_ptr in *; des_ifs].
        (* two comparison should same *)
        * hexploit (IntPtrRel.cmplu_no_angelic tm Ceq (Vlong i) (Vptr (map_blk sk tge b) i0) false).
          { rewrite Heq7. ss. des_ifs. }
          { rewrite Heq6. ss. }
          i. red in H. clarify.
        * hexploit (IntPtrRel.cmplu_no_angelic tm Ceq (Vlong i) (Vptr (map_blk sk tge b) i0) false).
          { rewrite Heq7. ss. des_ifs. }
          { rewrite Heq6. ss. }
          i. red in H. destruct Int64.eq eqn:? in H; clarify.
      (* v1 : long -> ptr in m success, v2 : ptr -> long in m fail *)
      + hexploit match_to_ptr_val; et. i.
        remove_UBcase.
        all: replace (Any.pair _ _) with pstate by now apply Any.split_pair; et.
        all: eapplyf NEXT.
        all: erewrite <- !(@match_valid_pointer m tm sk tge) in *; et.
        (* two ptrs have same block *)
        { unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool. ss.
          des_ifs; try solve [ss; unfold Val.of_bool in *; des_ifs].
          erewrite match_to_int_val_rev in Heqv0; et. clarify. }
        (* two ptrs have diff block *)
        unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool.
        ss. rewrite Heq0. ss. rewrite H.
        destruct eq_block. { hexploit map_blk_inj; et. clarify. }
        rewrite Heq2. rewrite Heq1. ss.
        des_ifs; ss; try solve [unfold Val.of_bool in *; des_ifs].
        erewrite match_to_int_val_rev in Heqv0; et. clarify.
      (* v1 : long -> ptr in m success, v2 : ptr -> long in m success *)
      + hexploit match_to_ptr_val; et; i; ss.
        hexploit match_to_int_val; et; i.
        remove_UBcase.
        all: replace (Any.pair _ _) with pstate by now apply Any.split_pair; et.
        all: eapplyf NEXT.
        all: rewrite <- ! (@match_valid_pointer m tm sk tge) in *; et.
        (* two ptrs have same block, both pointers are weak valid *)
        * hexploit (IntPtrRel.cmplu_no_angelic tm c (Vlong i) (Vptr (map_blk sk tge b) i0) (Ptrofs.cmpu c i1 i0)).
          { rewrite H. ss. des_ifs. }
          { ss. rewrite H0. ss. }
          i. red in H1. rewrite H1. unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool.
          ss. rewrite Heq0. ss. bsimpl. des_ifs; try solve [unfold Val.of_bool in *; des_ifs].
          rewrite H1 in *. ss. clarify. rewrite H0 in *. clarify. unfold Int.eq in *. des_ifs.
        (* two ptrs have diff block, pointer comparison is defined *)
        * apply Bool.eqb_prop in Heq2. subst.
          unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool.
          ss. rewrite Heq1.
          des_ifs; try solve [hexploit map_blk_inj; et; clarify].
          all: ss; unfold Val.of_bool in *; des_ifs.
          all: unfold Int.eq in *; des_ifs.
        (* two ptrs have same block, some pointer is not weak valid *)
        * unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool. ss. rewrite Heq0. ss.
          des_ifs; try solve [unfold Val.of_bool in *; des_ifs].
        (* two ptrs have diff block, both are valid, but pointer comparison is undefined *)
        * unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool.
          ss. rewrite Heq1.
          des_ifs; try solve [hexploit map_blk_inj; et; clarify].
          all: ss; unfold Val.of_bool in *; des_ifs.
        (* two ptrs have diff block, some is not valid *)
        * unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool. ss.
          des_ifs; try solve [hexploit map_blk_inj; et; clarify].
          all: ss; unfold Val.of_bool in *; des_ifs.
    (* v2 : int *)
    - unfold cmp_ptr_join. unfold cmp_ptr. remove_UBcase. remove_UBcase.
      unfold Val.cmplu_bool in *. des_ifs.
    (* v1 : ptr, v2 : null *)
    - rewrite Heq. ss. remove_UBcase. uhu. remove_UBcase. 
      replace (Any.pair _ _) with pstate by now apply Any.split_pair; et.
      eapplyf NEXT. unfold Cop.cmp_ptr, Val.cmplu_bool. rewrite Heq.
      erewrite !match_valid_pointer; et. des_ifs. rewrite Heq3. ss.
    (* v1 : ptr, v2 : notnull *)
    - unfold cmp_ptr_join. unfold cmp_ptr. remove_UBcase.
      unfold Val.cmplu_bool. destruct IntPtrRel.to_ptr_val eqn:?; clarify.
      all: try solve [unfold IntPtrRel.to_ptr_val, Mem.to_ptr in *; des_ifs].
      2: ss; destruct IntPtrRel.to_int_val eqn:?; clarify.
      all: try solve [unfold IntPtrRel.to_int_val, Mem.to_int, Mem.ptr2int_v in *; des_ifs].
      (* v2 : long -> ptr in m fail *)
      + remove_UBcase.
        replace (Any.pair _ _) with pstate by now apply Any.split_pair; et.
        eapplyf NEXT. hexploit match_to_int_val; et. i. ss.
        unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool.
        ss. rewrite Heq0. ss.
        unfold Val.of_bool, Val.cmp_different_blocks.
        (* v1 : ptr -> long suc *)
        des_ifs; ss; clarify; des_ifs.
        (* v2 : long -> ptr in tm should fail *)
        all: try solve [erewrite match_to_ptr_val_rev in Heqv; et; clarify].
        all: try solve [unfold IntPtrRel.to_ptr_val, Mem.to_ptr in *; des_ifs].
        (* two comparison should same *)
        * hexploit (IntPtrRel.cmplu_no_angelic tm Ceq (Vptr (map_blk sk tge b) i) (Vlong i0) false).
          { rewrite Heq7. ss. des_ifs. }
          { rewrite Heq6. ss. }
          i. red in H. clarify.
        * hexploit (IntPtrRel.cmplu_no_angelic tm Ceq (Vptr (map_blk sk tge b) i) (Vlong i0) false).
          { rewrite Heq7. ss. des_ifs. }
          { rewrite Heq6. ss. }
          i. red in H. destruct Int64.eq eqn:? in H; clarify.
      (* v1 : ptr -> long in m fail, v2 : long -> ptr in m success *)
      + hexploit match_to_ptr_val; et. i.
        remove_UBcase.
        all: replace (Any.pair _ _) with pstate by now apply Any.split_pair; et.
        all: eapplyf NEXT.
        all: erewrite <- !(@match_valid_pointer m tm sk tge) in *; et.
        (* two ptrs have same block *)
        { unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool. ss.
          des_ifs; try solve [ss; unfold Val.of_bool in *; des_ifs].
          erewrite match_to_int_val_rev in Heqv0; et. clarify. }
        (* two ptrs have diff block *)
        unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool.
        ss. rewrite Heq1.
        des_ifs; try solve [hexploit map_blk_inj; et; clarify].
        all: try solve [ss; unfold Val.of_bool in *; des_ifs].
        erewrite match_to_int_val_rev in Heqv0; et. clarify.
      (* v1 : ptr -> long in m success, v2 : long -> ptr in m success *)
      + hexploit match_to_ptr_val; et; i; ss.
        hexploit match_to_int_val; et; i.
        remove_UBcase.
        all: replace (Any.pair _ _) with pstate by now apply Any.split_pair; et.
        all: eapplyf NEXT.
        all: rewrite <- ! (@match_valid_pointer m tm sk tge) in *; et.
        (* two ptrs have same block, both pointers are weak valid *)
        * hexploit (IntPtrRel.cmplu_no_angelic tm c (Vptr (map_blk sk tge b0) i) (Vlong i0) (Ptrofs.cmpu c i i1)).
          { rewrite H. ss. des_ifs. }
          { ss. rewrite H0. ss. }
          i. red in H1. rewrite H1. unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool.
          ss. rewrite Heq0. ss. bsimpl. des_ifs; try solve [unfold Val.of_bool in *; des_ifs].
          rewrite H1 in *. ss. clarify. rewrite H0 in *. clarify. unfold Int.eq in *. des_ifs.
        (* two ptrs have diff block, pointer comparison is defined *)
        * apply Bool.eqb_prop in Heq2. subst.
          unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool.
          ss. rewrite Heq1.
          des_ifs; try solve [hexploit map_blk_inj; et; clarify].
          all: ss; unfold Val.of_bool in *; des_ifs.
          all: unfold Int.eq in *; des_ifs.
        (* two ptrs have same block, some pointer is not weak valid *)
        * unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool. ss. rewrite Heq0. ss.
          des_ifs; try solve [unfold Val.of_bool in *; des_ifs].
        (* two ptrs have diff block, both are valid, but pointer comparison is undefined *)
        * unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool.
          ss. rewrite Heq1.
          des_ifs; try solve [hexploit map_blk_inj; et; clarify].
          all: ss; unfold Val.of_bool in *; des_ifs.
        (* two ptrs have diff block, some is not valid *)
        * unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool. ss.
          des_ifs; try solve [hexploit map_blk_inj; et; clarify].
          all: ss; unfold Val.of_bool in *; des_ifs.
    - ss. remove_UBcase.
      2: uhu; remove_UBcase.
      all: replace (Any.pair _ _) with pstate by now apply Any.split_pair; et.
      all: eapplyf NEXT.
      all: erewrite <- !(@match_valid_pointer m tm sk tge) in *; et.
      all: unfold Cop.cmp_ptr; unfold Val.cmplu_bool; des_ifs; try solve [hexploit map_blk_inj; et; clarify].
      rewrite Heq2. ss.
  Qed.

  Lemma step_non_null_ptr pstate f_table modl cprog sk tge tle te m tm any
    (PSTATE: Any.split pstate = Some (m↑, any))
    (EQ: f_table = (Mod.add Mem modl).(Mod.enclose))
    (MM: match_mem sk tge m tm)
    blk ofs
    tf tcode tcont ktr bflag r
    (NEXT: Mem.weak_valid_pointer tm (map_blk sk tge blk) (Ptrofs.unsigned ofs) = true ->
            paco4
              (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true bflag
              (ktr (pstate, true))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true bflag
      (`r0: (p_state * bool) <-
        (interp_Es
          (prog f_table)
          (translate_r (ccallU "non_null?" (Vptr blk ofs)))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    step. ss. step. unfold non_nullF. step. rewrite PSTATE. step. remove_UBcase.
    replace (Any.pair _ _) with pstate by now apply Any.split_pair; et. eapplyf NEXT; et.
    unfold Mem.weak_valid_pointer, Mem.valid_pointer. inv MM.
    repeat (match goal with | |- context ctx [ Mem.perm_dec ?x ] => destruct (Mem.perm_dec x) end)
    ; et; ss; unfold Mem.perm in *; rewrite <- MEM_PERM in *.
    unfold Mem.weak_valid_pointer, Mem.valid_pointer in Heq.
    destruct Mem.perm_dec in Heq; clarify.
    destruct Mem.perm_dec in Heq; clarify.
  Qed.

  Local Arguments ccallU : simpl never.

  Lemma step_sem_cast pstate f_table modl cprog sk tge tle te m tm any
    (PSTATE: Any.split pstate = Some (m↑, any))
    (EQ: f_table = (Mod.add Mem modl).(Mod.enclose))
    (MM: match_mem sk tge m tm)
    v ty1 ty2
    tf tcode tcont ktr b r
    (NEXT: forall v',
            Cop.sem_cast (map_val sk tge v) ty1 ty2 tm = Some (map_val sk tge v') ->
            paco4
              (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v'))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- 
        (interp_Es
          (prog f_table)
          (translate_r (sem_cast_c v ty1 ty2)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold sem_cast_c. des_ifs_safe. unfold cast_to_ptr. remove_UBcase.
    all: try solve [eapplyf NEXT; unfold Cop.sem_cast; des_ifs].
    all: try solve [unfold unwrapU; remove_UBcase; eapplyf NEXT; unfold Cop.sem_cast; des_ifs; ss; clarify].
    eapply step_non_null_ptr; et. i. sim_red. eapplyf NEXT; et.
    unfold Cop.sem_cast. rewrite Heq1; des_ifs_safe.
    ss. clarify.
  Qed.

  Lemma step_assign_loc pstate f_table modl cprog sk tge tle te m tm ce tce any
    (PSTATE: Any.split pstate = Some (m↑, any))
    (EQ: f_table = (Mod.add Mem modl).(Mod.enclose))
    (MGE: match_ge sk tge)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
    ty vp v
    tf tcode tcont ktr b r
    (NEXT: forall tm' m',
            match_mem sk tge m' tm' ->
            assign_loc tce ty tm (map_val sk tge vp) (map_val sk tge v) tm' ->
            paco4
              (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (Any.pair m'↑ any, ()))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * ())<- 
        (interp_Es
          (prog f_table)
          (translate_r (assign_loc_c ce ty vp v)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold assign_loc_c. des_ifs; try sim_red; try sim_triggerUB.
    - eapply step_store; et. i. eapply NEXT; et. econs; et.
    - eapply step_memcpy; et. i. sim_red. eapply NEXT; et.
      inv H. 2:{ econs 3; et. erewrite match_sizeof; et. }
      erewrite <- !match_sizeof in *; et.
      erewrite <- !match_alignof_blockcopy in *; et.
      econs 2; et.
  Qed.

  Lemma step_deref_loc pstate f_table modl cprog sk tge tle te m tm any
    (PSTATE: Any.split pstate = Some (m↑, any))
    (EQ: f_table = (Mod.add Mem modl).(Mod.enclose))
    (MGE: match_ge sk tge)
    (MM: match_mem sk tge m tm)
    ty vp
    tf tcode tcont ktr b r
    (NEXT: forall v,
            deref_loc ty tm (map_val sk tge vp) (map_val sk tge v) ->
            paco4
              (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- 
        (interp_Es
          (prog f_table)
          (translate_r (deref_loc_c ty vp)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold deref_loc_c. remove_UBcase.
    - eapply step_load; et. i. eapplyf NEXT; ss; econs; et.
    - eapplyf NEXT; ss; econs 2; et.
    - eapplyf NEXT; ss; econs 3; et.
  Qed.

  Lemma step_unary_op pstate f_table modl cprog sk tge tle te m tm any
    (PSTATE: Any.split pstate = Some (m↑, any))
    (EQ: f_table = (Mod.add Mem modl).(Mod.enclose))
    (MM: match_mem sk tge m tm)
    uop v ty 
    tf tcode tcont ktr b r
    (NEXT: forall v',
            Cop.sem_unary_operation uop (map_val sk tge v) ty tm = Some (map_val sk tge v') ->
            paco4
              (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v'))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- 
        (interp_Es
          (prog f_table)
          (translate_r (unary_op_c uop v ty)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold unary_op_c. des_ifs; sim_red.
    - unfold bool_val_c. remove_UBcase.
      + apply NEXT. unfold Cop.sem_unary_operation. unfold Cop.sem_notbool. ss. unfold Cop.bool_val. rewrite Heq. ss. unfold Val.of_bool. des_ifs.
      + apply NEXT. unfold Cop.sem_unary_operation. unfold Cop.sem_notbool. ss. unfold Cop.bool_val. rewrite Heq. ss. unfold Val.of_bool. des_ifs.
      + eapply step_non_null_ptr; et. i. sim_red. apply NEXT. unfold Cop.sem_unary_operation, Cop.sem_notbool, Cop.bool_val. rewrite Heq. ss. rewrite H. des_ifs.
      + apply NEXT. unfold Cop.sem_unary_operation. unfold Cop.sem_notbool. ss. unfold Cop.bool_val. rewrite Heq. ss. unfold Val.of_bool. des_ifs.
      + apply NEXT. unfold Cop.sem_unary_operation. unfold Cop.sem_notbool. ss. unfold Cop.bool_val. rewrite Heq. ss. unfold Val.of_bool. des_ifs.
    - unfold unwrapU. remove_UBcase. apply NEXT.
      unfold Cop.sem_unary_operation, Cop.sem_notint in *.
      des_ifs; ss; clarify.
    - unfold unwrapU. remove_UBcase. apply NEXT.
      unfold Cop.sem_unary_operation, Cop.sem_neg in *.
      des_ifs; ss; clarify.
    - unfold unwrapU. remove_UBcase. apply NEXT.
      unfold Cop.sem_unary_operation, Cop.sem_absfloat in *.
      des_ifs; ss; clarify.
  Qed.

  Lemma step_binary_op pstate f_table modl cprog sk tge ce tce tle te m tm any
    (PSTATE: Any.split pstate = Some (m↑, any))
    (EQ: f_table = (Mod.add Mem modl).(Mod.enclose))
    (MGE: match_ge sk tge)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
    biop v1 ty1 v2 ty2
    tf tcode tcont ktr b r
    (NEXT: forall v',
            Cop.sem_binary_operation tce biop (map_val sk tge v1) ty1 (map_val sk tge v2) ty2 tm = Some (map_val sk tge v') ->
            paco4
              (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v'))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (Mod.compile (Mod.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- 
        (interp_Es
          (prog f_table)
          (translate_r (binary_op_c ce biop v1 ty1 v2 ty2)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold binary_op_c. des_ifs; unfold sem_add_c, sem_sub_c, sem_mul_c, sem_div_c, sem_mod_c, sem_and_c, sem_or_c, sem_xor_c, Cop.sem_shl, Cop.sem_shr, sem_cmp_c.
    - des_ifs.
      all: unfold sem_add_ptr_int_c, sem_add_ptr_long_c. 
      all: remove_UBcase.
      all: try solve [apply NEXT; erewrite <- match_sizeof; et; unfold Cop.sem_binary_operation, Cop.sem_add, Cop.sem_add_ptr_int, Cop.sem_add_ptr_long; ss; des_ifs].
      unfold sem_binarith_c. step. eapply step_sem_cast; et. i. step. eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_add, Cop.sem_binarith; rewrite Heq; rewrite Heq0; des_ifs.
    - remove_UBcase.
      all: try apply NEXT.
      all: try solve [erewrite <- match_sizeof; et; unfold Cop.sem_binary_operation, Cop.sem_sub; ss; des_ifs].
      + eapply step_sub_ptr; et. i. apply NEXT.
        erewrite <- match_sizeof in *; et. unfold Cop.sem_binary_operation, Cop.sem_sub. ss; des_ifs.
        destruct Coqlib.zle; destruct Coqlib.zlt; ss; try nia.
      + unfold sem_binarith_c. step. eapply step_sem_cast; et. i. step.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_sub, Cop.sem_binarith; rewrite Heq; rewrite Heq0; des_ifs.
    - unfold sem_binarith_c. step. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_mul, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_div, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_mod, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_and, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_or, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_xor, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold unwrapU. remove_UBcase.
      eapplyf NEXT. i; clarify; unfold Cop.sem_binary_operation, Cop.sem_shl; unfold Cop.sem_binarith; unfold Cop.sem_shift in *; des_ifs; ss; clarify.
    - unfold unwrapU. remove_UBcase.
      eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_shr; unfold Cop.sem_binarith; unfold Cop.sem_shift in *; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      all: try (eapply step_cmp_ptr; et; i; step).
      all: try (eapply NEXT; simpl; unfold Cop.sem_cmp; des_ifs). 
      all: unfold Vptrofs in *; des_ifs; ss.
      all: try solve [rewrite H; unfold Val.of_bool; des_ifs].
      unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
      all: unfold Val.of_bool; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      all: try (eapply step_cmp_ptr; et; i; step).
      all: try (eapply NEXT; simpl; unfold Cop.sem_cmp; des_ifs). 
      all: unfold Vptrofs in *; des_ifs; ss.
      all: try solve [rewrite H; unfold Val.of_bool; des_ifs].
      unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
      all: unfold Val.of_bool; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      all: try (eapply step_cmp_ptr; et; i; step).
      all: try (eapply NEXT; simpl; unfold Cop.sem_cmp; des_ifs). 
      all: unfold Vptrofs in *; des_ifs; ss.
      all: try solve [rewrite H; unfold Val.of_bool; des_ifs].
      unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
      all: unfold Val.of_bool; des_ifs; ss; clarify.


    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      all: try (eapply step_cmp_ptr; et; i; step).
      all: try (eapply NEXT; simpl; unfold Cop.sem_cmp; des_ifs). 
      all: unfold Vptrofs in *; des_ifs; ss.
      all: try solve [rewrite H; unfold Val.of_bool; des_ifs].
      unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
      all: unfold Val.of_bool; des_ifs; ss; clarify.

    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      all: try (eapply step_cmp_ptr; et; i; step).
      all: try (eapply NEXT; simpl; unfold Cop.sem_cmp; des_ifs). 
      all: unfold Vptrofs in *; des_ifs; ss.
      all: try solve [rewrite H; unfold Val.of_bool; des_ifs].
      unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
      all: unfold Val.of_bool; des_ifs; ss; clarify.

    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. simpl. unfold Cop.sem_cmp. des_ifs.
        simpl map_val in H.
        rewrite H. unfold Val.of_bool. des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
        all: unfold Val.of_bool; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. simpl. unfold Cop.sem_cmp. des_ifs.
        simpl map_val in H.
        rewrite H. unfold Val.of_bool. des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
        all: unfold Val.of_bool; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. simpl. unfold Cop.sem_cmp. des_ifs.
        simpl map_val in H.
        rewrite H. unfold Val.of_bool. des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
        all: unfold Val.of_bool; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. simpl. unfold Cop.sem_cmp. des_ifs.
        simpl map_val in H.
        rewrite H. unfold Val.of_bool. des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
        all: unfold Val.of_bool; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. simpl. unfold Cop.sem_cmp. des_ifs.
        simpl map_val in H.
        rewrite H. unfold Val.of_bool. des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
        all: unfold Val.of_bool; des_ifs; ss; clarify.
  Qed.

  Lemma _step_eval pstate ge ce tce f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: tce = ge.(genv_cenv)) 
    (EQ2: tge = ge.(genv_genv))
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
 r b tcode tf tcont mn a
 :
  (forall ktr1,
    (forall vp, 
      eval_lvalue ge te tle tm a (map_val sk tge vp) ->
      paco4
        (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
        (ktr1 (pstate, vp))
        (State tf tcode tcont te tle tm)) 
    ->
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_lvalue_c sk ce e le a)) 
          pstate);; ktr1 r0)
      (State tf tcode tcont te tle tm)) 
  /\
  (forall ktr2,
    (forall v, 
      eval_expr ge te tle tm a (map_val sk tge v) ->
      paco4
        (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
        (ktr2 (pstate, v))
        (State tf tcode tcont te tle tm)) 
    ->
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * Values.val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_expr_c sk ce e le a))
          pstate);; ktr2 r0)
      (State tf tcode tcont te tle tm)). 
  Proof.
    induction a.
    1,2,3,4 : split; i; remove_UBcase; eapply H; try econs.
    2,4,5,6,7 : des; split; i; remove_UBcase; ss.
    - split; i; ss.
      + remove_UBcase; eapply H; et. 
        * econs. eapply env_match_some in ME; et.
        * econs 2; try solve [eapply env_match_none; et]. inv MGE. unfold valid_check in Heq.
          destruct Pos.eq_dec; ss. rewrite e0. eapply MGE0; et.
      + remove_UBcase; eapply step_deref_loc; et; i; sim_red; eapply H; et; econs; et.
        * econs. hexploit env_match_some; et.
        * econs 2; try solve [eapply env_match_none; et]. inv MGE. unfold valid_check in Heq.
          destruct Pos.eq_dec; ss. rewrite e0. eapply MGE0; et.
    - unfold unwrapU. remove_UBcase. eapply H; et. econs. inv MLE. eapply ML. et.
    - eapply IHa. i. eapply H; et. econs; et.
    - eapply IHa0. i. eapply step_unary_op; et. i. eapply H; et. econs; et.
    - eapply IHa3. i. sim_red. eapply IHa0. i. eapply step_binary_op; et.
      i. eapply H; et. econs; et.
    - eapply IHa0. i. eapply step_sem_cast; et. i. eapply H; et. econs; et. 
    - des; split; i; ss; remove_UBcase; eapply IHa0; i; remove_UBcase.
      + eapply H. econs; et. destruct v; ss.
      + eapply step_deref_loc; et. i. sim_red. eapply H. econs; et. econs;et. destruct v; ss.
    - des. split; i; ss; sim_red; eapply IHa0; i; subst. 
      + remove_UBcase; unfold unwrapU; remove_UBcase; remove_UBcase; eapply H; et.
        * econs; et. { destruct v; ss. }
          { inv MCE. rewrite <- MCE0 in Heq2. apply Maps.PTree.elements_complete. et. }
          2:{ des_ifs. destruct v; ss. }
          { unfold ClightPlusExprgen.field_offset in Heq3.
            clear - Heq3 MCE. unfold field_offset. set 0%Z as d in *.
            clearbody d. destruct c. ss. revert i d Heq3.
            induction co_members; ss. i. des_ifs.
            { erewrite match_alignof; et. } apply IHco_members.
            erewrite match_alignof; et. erewrite match_sizeof; et. }
        * econs 5; et. { destruct v; ss. }
          inv MCE. rewrite <- MCE0 in Heq1. apply Maps.PTree.elements_complete. et.
      + remove_UBcase; unfold unwrapU; remove_UBcase; remove_UBcase;
        eapply step_deref_loc; et; i; sim_red; eapply H; et; econs; et.
        * econs; et. { destruct v; ss. }
          { inv MCE. rewrite <- MCE0 in Heq2. apply Maps.PTree.elements_complete. et. }
          2:{ des_ifs. destruct v; ss. }
          { unfold ClightPlusExprgen.field_offset in Heq3.
            clear - Heq3 MCE. unfold field_offset. set 0%Z as d in *.
            clearbody d. destruct c. ss. revert i d Heq3.
            induction co_members; ss. i. des_ifs.
            { erewrite match_alignof; et. } apply IHco_members.
            erewrite match_alignof; et. erewrite match_sizeof; et. }
        * econs 5; et. { destruct v; ss. }
          inv MCE. rewrite <- MCE0 in Heq1. apply Maps.PTree.elements_complete. et.
    - split; i.
      + ss. remove_UBcase.
      + ss. sim_red. apply H.
        replace (map_val sk _ _) with (Vptrofs (Ptrofs.repr (ClightPlusExprgen.sizeof ce t0))).
        2:{ unfold Vptrofs. des_ifs. }
        erewrite <- match_sizeof; et.
        replace tce with (ge.(genv_cenv)). econs.
    - split; i.
      + ss. remove_UBcase.
      + ss. sim_red. apply H.
        replace (map_val sk _ _) with (Vptrofs (Ptrofs.repr (ClightPlusExprgen.alignof ce t0))).
        2:{ unfold Vptrofs. des_ifs. }
        erewrite <- match_alignof; et.
        replace tce with (ge.(genv_cenv)). econs.
  Qed.

  Lemma step_eval_lvalue pstate ge tce ce f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: tce = ge.(genv_cenv)) 
    (EQ2: tge = ge.(genv_genv)) 
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
 r b tcode tf tcont mn a ktr
    (NEXT: forall vp, 
            eval_lvalue ge te tle tm a (map_val sk tge vp) ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, vp))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_lvalue_c sk ce e le a)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof. hexploit _step_eval; et. i. des. et. Qed.

  Lemma step_eval_expr pstate ge tce ce f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: tce = ge.(genv_cenv)) 
    (EQ2: tge = ge.(genv_genv)) 
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
 r b tcode tf tcont mn a ktr
    (NEXT: forall v v', 
            eval_expr ge te tle tm a v ->
            v = map_val sk tge v' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v'))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * Values.val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_expr_c sk ce e le a))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm). 
  Proof. hexploit _step_eval; et. i. des. et. Qed.

End PROOF.