Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.

Set Implicit Arguments.


Notation gname := string (only parsing). (*** convention: not capitalized ***)
Notation mname := string (only parsing). (*** convention: capitalized ***)

Section EVENTSCOMMON.

  Variant eventE: Type -> Type :=
  | Choose (X: Type): eventE X
  | Take X: eventE X
  | Syscall (fn: gname) (args: Any.t) (rvs: Any.t -> Prop): eventE Any.t
  .

  (* Notation "'Choose' X" := (trigger (Choose X)) (at level 50, only parsing). *)
  (* Notation "'Take' X" := (trigger (Take X)) (at level 50, only parsing). *)

  Definition triggerUB {E A} `{eventE -< E}: itree E A :=
    v <- trigger (Take void);; match v: void with end
  .

  Definition triggerNB {E A} `{eventE -< E}: itree E A :=
    v <- trigger (Choose void);; match v: void with end
  .

  Definition unwrapN {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerNB
    end.

  Definition unwrapU {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerUB
    end.

  Definition assume {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Take P) ;;; Ret tt.
  Definition guarantee {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Choose P) ;;; Ret tt.

  (* Notation "'unint?'" := (unwrapA <*> unint) (at level 57, only parsing). *)
  (* Notation "'unint﹗'" := (unwrapG <*> unint) (at level 57, only parsing). *)
  (* Notation "'Ret!' f" := (RetG f) (at level 57, only parsing). *)
  (* Notation "'Ret?' f" := (RetA f) (at level 57, only parsing). *)

  Definition unleftU {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerUB
    end.

  Definition unleftN {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerNB
    end.

  Definition unrightU {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
    match xy with
    | inl x => triggerUB
    | inr y => Ret y
    end.

  Definition unrightN {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
    match xy with
    | inl x => triggerNB
    | inr y => Ret y
    end.

End EVENTSCOMMON.

Notation "f '?'" := (unwrapU f) (at level 9, only parsing).
Notation "f 'ǃ'" := (unwrapN f) (at level 9, only parsing).
Notation "(?)" := (unwrapU) (only parsing).
Notation "(ǃ)" := (unwrapN) (only parsing).
Goal (tt ↑↓?) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.
Goal (tt ↑↓ǃ) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.







Section EVENTSCOMMON.

  Definition p_state: Type := (mname -> Any.t).

  (*** Same as State.pure_state, but does not use "Vis" directly ***)
  Definition pure_state {S E}: E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
      interp_state h t s = _interp_state h (observe t) s.
  Proof. i. f. apply unfold_interp_state. Qed.

End EVENTSCOMMON.








Module EventsL.
Section EVENTSL.

  Notation thread_id := nat.
  
  Inductive callE: Type -> Type :=
  | Call (mn: option mname) (fn: gname) (args: Any.t): callE Any.t
  .

  Inductive pE: Type -> Type :=
  | PPut (mn: mname) (p: Any.t): pE unit
  | PGet (mn: mname): pE Any.t
  .

  Inductive schE: Type -> Type :=
  | Spawn (mn: mname) (fn: gname) (args: Any.t): schE nat
  | Yield: schE unit
  .

  (*** TODO: we don't want to require "mname" here ***)
  (*** use dummy mname? ***)
  (* Definition FPut E `{rE -< E} (mn: mname) (fr: GRA): itree E unit := *)

  Definition Es: Type -> Type := (schE +' callE +' pE +' eventE).

  (* Inductive mdE: Type -> Type := *)
  (* | MPut (mn: mname) (r: GRA): mdE unit *)
  (* | MGet (mn: mname): mdE GRA *)
  (* . *)

  (* Inductive fnE: Type -> Type := *)
  (* | FPut (r: GRA): fnE unit *)
  (* | FGet: fnE GRA *)
  (* | FPush: fnE unit *)
  (* | FPop: fnE unit *)
  (* . *)






  (********************************************************************)
  (*************************** Interpretation *************************)
  (********************************************************************)
  Section Scheduler.
    Definition interp_schE_aux {R} :
      itree Es R -> itree (callE +' pE +' eventE) ((itree Es R) + R).
    Proof.
      eapply ITree.iter.
      intros itr.
      apply observe in itr; destruct itr as [r | itr | X e k].
      - (* Ret *)
        exact (Ret (inr (inr r))).
      - (* Tau *)
        exact (Ret (inl itr)).
      - (* Vis *)
        destruct e as [|[|[]]].
        + (* schE *)
          destruct s.
          * (* Spawn *)
            exact (Vis (inr1 (inr1 (Spawn_t fn args))) (fun x => Ret (inl (k x)))).
          * (* Yield *)
            exact (Ret (inr (inl (k tt)))).
        + (* callE *)
          exact (Vis (inl1 c) (fun x => Ret (inl (k x)))).
        + (* pE *)
          exact (Vis (inr1 (inl1 p)) (fun x => Ret (inl (k x)))).
        + (* eventE *)
          exact (Vis (inr1 (inr1 e)) (fun x => Ret (inl (k x)))).
    Defined.

    Variant schedulerE (RT : Type) : Type -> Type :=
      | Execute : thread_id -> schedulerE RT (option RT).
    
    Notation threads RT := (alist thread_id (itree Es RT)).
    Notation tids := (alist thread_id unit).
    Definition scheduler RT R := itree (schedulerE RT +' eventE) R.

    Definition new_itr {RT: Type} fn args : itree Es RT :=
      v <- ITree.trigger (inr1 (inl1 (Call None fn args)));;
      triggerNB.
    
    Definition interp_sched RT R : threads RT * thread_id * scheduler RT R -> itree (callE +' pE +' eventE) R.
    Proof.
      eapply ITree.iter. intros [[ts max_tid] sch].
      destruct (observe sch) as [r | sch' | X [e|e] ktr].
      - exact (Ret (inr r)).
      - exact (Ret (inl (ts, max_tid, sch'))).
      - destruct e.
        destruct (alist_find n ts) as [t|].
        * exact (r <- interp_schE_aux t;;
                 match r with
                 | inl t' => Ret (inl (alist_add n t' ts, max_tid, ktr None))
                 | inr r => Ret (inl (alist_remove n ts, max_tid, ktr (Some r)))
                 end).
        * exact triggerUB.
      - destruct e.
        * (* Choose *)
          exact (Vis (inr1 (inr1 (Choose X))) (fun x => Ret (inl (ts, max_tid, ktr x)))).
        * (* Take *)
          exact (Vis (inr1 (inr1 (Take X))) (fun x => Ret (inl (ts, max_tid, ktr x)))).
        * (* Syscall *)
          exact (Vis (inr1 (inr1 (Syscall fn args rvs))) (fun x => Ret (inl (ts, max_tid, ktr x)))).
        * (* Spawn_t *)
          exact (Ret (inl (alist_add max_tid (new_itr fn args) ts, max_tid + 1, ktr max_tid))).
    Defined.

    Definition sched_nondet_body {R} q tid r : itree eventE (thread_id * tids + R) :=
      match r with
      | None =>
          tid' <- ITree.trigger (inr1 (Choose thread_id));;
          match alist_pop tid' (alist_add tid tt q) with
          | None => triggerNB
          | Some (_, q') => Ret (inl (tid', q'))
          end
      (* | spawn *)
      | Some r =>
          if true (* TODO *)
          then Ret (inr r)
          else
            tid' <- ITree.trigger (inr1 (Choose thread_id));;
            match alist_pop tid' q with
            | None => triggerNB
            | Some (_, q') => Ret (inl (tid', q'))
            end
      end.

    Definition sched_nondet R0 : thread_id * tids -> scheduler R0 R0 :=
      ITree.iter (fun '(tid, q) =>
                    r <- ITree.trigger (inl1 (Execute _ tid));;
                    sched_nondet_body q tid r).

    Definition alist_key_set K V (t: alist K V): alist K unit :=
      List.map (fun x => (fst x, tt)) t.

    Definition interp_schE
      R ths tid max_tid : itree (callE +' pE +' eventE) R :=
      interp_sched (ths, max_tid, sched_nondet _ (tid, alist_remove tid (alist_key_set ths))).
  End Scheduler.

  (* Section Sch_example. *)
  (*   Definition f x : itree Es Any.t := *)
  (*     y <- trigger (Call None "g" [x - 1]↑);; *)
  (*     y <- y↓?;; *)
  (*     Ret (x + y)↑. *)
    
  (*   Definition g x : itree Es Any.t := *)
  (*     y <- trigger (Call None "f" [x - 1]↑);; *)
  (*     y <- y↓?;; *)
  (*     Ret (x + y)↑. *)

  (*   Definition main : itree Es Any.t := *)
  (*     a <- trigger (Call None "f" [4]↑);; *)
  (*     Ret a. *)
                        
  (* End Sch_example. *)

  Definition handle_pE {E}: pE ~> stateT p_state (itree E) :=
    fun _ e mps =>
      match e with
      | PPut mn p => Ret (update mps mn p, tt)
      | PGet mn => Ret (mps, mps mn)
      end.
  Definition interp_pE {E}: itree (pE +' E) ~> stateT p_state (itree E) :=
    (* State.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) State.pure_state). *)
    State.interp_state (case_ handle_pE pure_state).

  (* Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (rst0: r_state) (pst0: p_state): itree eventE _ := *)
  (*   interp_pE (interp_rE (interp_mrec prog itr0) rst0) pst0 *)
  (* . *)
  Definition interp_Es A (prog: callE ~> itree (callE +' pE +' eventE)) (itr0: itree Es A) (st0: p_state): itree eventE (p_state * _)%type :=
    '(st1, v) <- interp_pE (interp_mrec prog (interp_schE (alist_add 0 itr0 []) 0 1)) st0;;
    Ret (st1, v)
  .



  Lemma interp_Es_bind
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
        (prog: callE ~> itree Es)
        st0
    :
      interp_Es prog (v <- itr ;; ktr v) st0 =
      '(st1, v) <- interp_Es prog (itr) st0 ;; interp_Es prog (ktr v) st1
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_tau
        (prog: callE ~> itree Es)
        A
        (itr: itree Es A)
        st0
    :
      interp_Es prog (tau;; itr) st0 = tau;; interp_Es prog itr st0
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_ret
        T
        prog st0 (v: T)
    :
      interp_Es prog (Ret v) st0 = Ret (st0, v)
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_callE
        p st0 T
        (* (e: Es Σ) *)
        (e: callE T)
    :
      interp_Es p (trigger e) st0 = tau;; (interp_Es p (p _ e) st0)
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_pE
        p st0
        (* (e: Es Σ) *)
        T
        (e: pE T)
    :
      interp_Es p (trigger e) st0 =
      '(st1, r) <- handle_pE e st0;;
      tau;; tau;;
      Ret (st1, r)
  .
  Proof.
    unfold interp_Es, interp_pE. grind.
  Qed.

  Lemma interp_Es_eventE
        p st0
        (* (e: Es Σ) *)
        T
        (e: eventE T)
    :
      interp_Es p (trigger e) st0 = r <- trigger e;; tau;; tau;; Ret (st0, r)
  .
  Proof.
    unfold interp_Es, interp_pE. grind.
    unfold pure_state. grind.
  Qed.

  Lemma interp_Es_triggerUB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (interp_Es prog (triggerUB) st0: itree eventE (_ * A)) = triggerUB
  .
  Proof.
    unfold interp_Es, interp_pE, pure_state, triggerUB. grind.
  Qed.

  Lemma interp_Es_triggerNB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (interp_Es prog (triggerNB) st0: itree eventE (_ * A)) = triggerNB
  .
  Proof.
    unfold interp_Es, interp_pE, pure_state, triggerNB. grind.
  Qed.
  Opaque interp_Es.
End EVENTSL.
End EventsL.
Opaque EventsL.interp_Es.
