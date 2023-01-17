Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.

Set Implicit Arguments.


Notation gname := string (only parsing). (*** convention: not capitalized ***)
Notation mname := string (only parsing). (*** convention: capitalized ***)
Notation sname := string (only parsing). (*** convention: natural numbers ***)

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

  Definition triggerErr {E A} `{eventE -< E}: itree E A :=
    trigger (Syscall "exit" ["There's an error"]↑ top1);;;triggerUB.
  

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

  Definition unwrapErr {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerErr
    end.

  Definition assume {E} `{eventE -< E} (P: Prop): itree E Any.t := trigger (Take P) ;;; Ret tt↑.
  Definition guarantee {E} `{eventE -< E} (P: Prop): itree E Any.t := trigger (Choose P) ;;; Ret tt↑.

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
Notation "f '#?'" := (unwrapErr f) (at level 9, only parsing).
Notation "(?)" := (unwrapU) (only parsing).
Notation "(ǃ)" := (unwrapN) (only parsing).
Notation "(#?)" := (unwrapErr) (only parsing).
Goal (tt ↑↓?) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.
Goal (tt ↑↓ǃ) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.







Section EVENTSCOMMON.

  Definition p_state: Type := (sname -> mname -> Any.t).

  (*** Same as State.pure_state, but does not use "Vis" directly ***)
  Definition pure_state {S E}: E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
      interp_state h t s = _interp_state h (observe t) s.
  Proof. i. f. apply unfold_interp_state. Qed.

End EVENTSCOMMON.








Module EventsL.
Section EVENTSL.

  Inductive callE: Type -> Type :=
  | Call (sn: sname) (mn: option mname) (fn: gname) (args: Any.t): callE Any.t
  .

  Inductive pE: Type -> Type :=
  | PPut (sn: sname) (mn: mname) (p: Any.t): pE unit
  | PGet (sn: sname) (mn: mname): pE Any.t
  .

  Inductive schE: Type -> Type :=
  | Spawn (sn: sname) (fn: gname) (args: Any.t): schE nat
  | Yield: schE unit
  | Getpid: schE nat
  .

  (*** TODO: we don't want to require "mname" here ***)
  (*** use dummy mname? ***)
  (* Definition FPut E `{rE -< E} (mn: mname) (fr: GRA): itree E unit := *)

  Definition Es: Type -> Type := (callE +' schE +' pE +' eventE).

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
    Definition interp_schE {E}:
      nat * itree (schE +' pE +' eventE) E ->
      itree (pE +' eventE) (E + (string * string * Any.t * (nat -> itree (schE +' pE +' eventE) E))
                            + (itree (schE +' pE +' eventE) E)).
    Proof.
      eapply ITree.iter.
      intros [tid itr].
      apply observe in itr; destruct itr as [r | itr | X e k].
      - (* Ret *)
        exact (Ret (inr (inl (inl r)))).
      - (* Tau *)
        exact (Ret (inl (tid, itr))).
      - (* Vis *)
        destruct e as [|[|]].
        + (* schE *)
          destruct s.
          * (* Spawn *)
            exact (Ret (inr (inl (inr (sn, fn, args, fun x => k x))))).
            (* exact (Vis (inl1 (Spawn_t fn args)) (fun x => Ret (inl (tid, k x)))). *)
          * (* Yield *)
            exact (Ret (inr (inr (k tt)))).
          * (* GetTid *)
            exact (Ret (inl (tid, k tid))).
        + (* pE *)
          exact (Vis (inl1 p) (fun x => Ret (inl (tid, k x)))).
        + (* eventE *)
          exact (Vis (inr1 e) (fun x => Ret (inl (tid, k x)))).
    Defined.

    Notation threads := (alist nat (itree (schE +' pE +' eventE) Any.t)).

    Inductive executeE : Type -> Type :=
    | Execute : nat -> executeE ((list nat) * (Any.t + nat + unit)).

    Definition interp_executeE:
      (callE ~> itree Es) * threads * nat * (itree (executeE +' eventE) Any.t) ->
      itree (pE +' eventE) Any.t.
    Proof.
      eapply ITree.iter. intros [[[prog ts] next_tid] sch].
      destruct (observe sch) as [r | sch' | X [e|e] ktr].
      - exact (Ret (inr r)).
      - exact (Ret (inl (prog, ts, next_tid, sch'))).
      - destruct e. rename n into tid.
        destruct (alist_find tid ts) as [t|].
        * exact (r <- interp_schE (tid, t);;
                 match r with
                 | inl (inl r) => (* finished *)
                     let ts' := alist_remove tid ts in
                     Ret (inl (prog, ts', next_tid, ktr (List.map fst ts, (inl (inl r)))))
                 | inl (inr (sn, fn, args, k)) => (* spawn *)
                     let new_itr := interp_mrec prog (prog _ (Call sn None fn args)) in
                     let ts' := alist_add next_tid new_itr (alist_replace tid (k next_tid) ts) in
                     Ret (inl (prog, ts', next_tid + 1, ktr (List.map fst ts, (inl (inr tid)))))
                 | inr t' => (* yield *)
                     let ts' := alist_replace tid t' ts in
                     Ret (inl (prog, ts', next_tid, ktr (List.map fst ts, (inr tt))))
                 end).
        * exact triggerNB.
      - exact (Vis (inr1 e) (fun x => Ret (inl (prog, ts, next_tid, ktr x)))).
    Defined.

    Definition sched_nondet : nat -> itree (executeE +' eventE) Any.t :=
      ITree.iter (fun tid => 
                    '(ts, retv) <- ITree.trigger (inl1 (Execute tid));;
                    match retv with
                    | inl (inl r) =>
                        match ts with
                        | [] => Ret (inr r)
                        | _ => tid' <- ITree.trigger (inr1 (Choose nat));;
                              Ret (inl tid')
                        end
                    | inl (inr tid') =>
                        Ret (inl tid')
                    | inr tt =>
                        tid' <- ITree.trigger (inr1 (Choose nat));;
                        Ret (inl tid')
                    end).

    Definition interp_scheduler
      (prog: callE ~> itree Es) (ts: threads) (start_tid: nat) : itree (pE +' eventE) Any.t :=
      interp_executeE (prog, ts, List.length ts, sched_nondet start_tid).
  End Scheduler.

  Definition handle_pE {E}: pE ~> stateT p_state (itree E) :=
    fun _ e mps =>
      match e with
      | PPut sn mn p => Ret (update mps sn (update (mps sn) mn p), tt)
      | PGet sn mn => Ret (mps, mps sn mn)
      end.
  
  Definition interp_pE {E}: itree (pE +' E) ~> stateT p_state (itree E) :=
    (* State.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) State.pure_state). *)
    State.interp_state (case_ handle_pE pure_state).

  (* Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (rst0: r_state) (pst0: p_state): itree eventE _ := *)
  (*   interp_pE (interp_rE (interp_mrec prog itr0) rst0) pst0 *)
  (* . *)

  Definition interp_Es (prog: callE ~> itree Es) (itr0: itree Es Any.t) (st0: p_state): itree eventE (p_state * _)%type :=
    let itr1 := interp_mrec prog itr0 in
    let itr2 := interp_scheduler prog (alist_add 0 itr1 []) 0 in
    '(st1, v) <- interp_pE itr2 st0;;
    Ret (st1, v)
  .




  Lemma interp_Es_bind
        A
        (itr: itree Es A) (ktr: A -> itree Es Any.t)
        (prog: callE ~> itree Es)
        st0
    :
      interp_Es prog (v <- itr ;; ktr v) st0 =
      '(st1, v) <- interp_Es prog (v <- itr;; Ret v↑) st0;; v <- unwrapU v↓ ;; interp_Es prog (ktr v) st1
  .
  Proof.
    unfold interp_Es at 1. unfold interp_pE, interp_scheduler, interp_mrec. ss.
  Admitted.

  Lemma interp_Es_tau
        (prog: callE ~> itree Es)
        (itr: itree Es Any.t)
        st0
    :
      interp_Es prog (tau;; itr) st0 = tau;; interp_Es prog itr st0
  .
  (* Proof. *)
  (*   unfold interp_Es at 1. unfold interp_scheduler. *)
  (*   grind. eapply bisimulation_is_eq. *)
  (*   unfold sched_nondet. *)
  (*   remember (fun tid : nat => *)
  (*         ` x_ : list nat * (Any.t + nat + ()) <- ITree.trigger (Execute tid|)%sum;; *)
  (*         (let (ts, retv) := x_ in *)
  (*          match retv with *)
  (*          | inl (inl r) => *)
  (*              match ts with *)
  (*              | [] => Ret (inr r) *)
  (*              | _ :: _ => ` tid' : nat <- ITree.trigger (|Choose nat)%sum;; Ret (inl tid') *)
  (*              end *)
  (*          | inl (inr tid') => Ret (inl tid') *)
  (*          | inr () => ` tid' : nat <- ITree.trigger (|Choose nat)%sum;; Ret (inl tid') *)
  (*          end)) as f. *)
  (*   assert(H: ITree.iter f 0 = *)
  (*        ITree.bind (f 0) (fun lr => ITree.on_left lr l (Tau (ITree.iter f l)))). *)
  (*   { eapply bisimulation_is_eq. rewrite unfold_iter. reflexivity. } *)
  (*   rewrite H. clear H. *)
  (*   rewrite Heqf. grind. *)
  (*   fold sched_nondet. unfold interp_executeE. rewrite unfold_iter. fold interp_executeE. *)
  (*   grind. unfold interp_schE. rewrite unfold_iter. grind. *)
  (*   fold (@interp_schE Any.t). unfold interp_pE. grind. *)
  (*   unfold interp_Es, interp_pE, interp_scheduler. ss. *)
  (*   unfold interp_executeE at 2. ss. rewrite unfold_iter. fold interp_executeE. *)
  (*   grind. *)
  (* Qed. *)
  Admitted.

  Lemma interp_Es_ret
        prog st0 (v: Any.t)
    :
      interp_Es prog (Ret v) st0 = Ret (st0, v)
  .
  (* Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed. *)
  Admitted.

  Lemma interp_Es_callE
        p st0
        (* (e: Es Σ) *)
        (e: callE Any.t)
    :
      interp_Es p (trigger e) st0 = tau;; (interp_Es p (p _ e) st0)
  .
  (* Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed. *)
  Admitted.

  Lemma interp_Es_pE
        p st0
        (* (e: Es Σ) *)
        (e: pE Any.t)
    :
      interp_Es p (trigger e) st0 =
      '(st1, r) <- handle_pE e st0;;
      tau;; tau;;
      Ret (st1, r)
  .
  (* Proof. *)
  (*   unfold interp_Es, interp_pE. grind. *)
  (* Qed. *)
  Admitted.

  Lemma interp_Es_eventE
        p st0
        (* (e: Es Σ) *)
        (e: eventE Any.t)
    :
      interp_Es p (trigger e) st0 = r <- trigger e;; tau;; tau;; Ret (st0, r)
  .
  (* Proof. *)
  (*   unfold interp_Es, interp_pE. grind. *)
  (*   unfold pure_state. grind. *)
  (* Qed. *)
  Admitted.

  Lemma interp_Es_triggerUB
        (prog: callE ~> itree Es)
        st0
    :
      (interp_Es prog (triggerUB) st0: itree eventE (_ * Any.t)) = triggerUB
  .
  (* Proof. *)
  (*   unfold interp_Es, interp_pE, pure_state, triggerUB. grind. *)
  (* Qed. *)
  Admitted.

  Lemma interp_Es_triggerNB
        (prog: callE ~> itree Es)
        st0
    :
      (interp_Es prog (triggerNB) st0: itree eventE (_ * Any.t)) = triggerNB
  .
  (* Proof. *)
  (*   unfold interp_Es, interp_pE, pure_state, triggerNB. grind. *)
  (* Qed. *)
  Admitted.
  Opaque interp_Es.
End EVENTSL.
End EventsL.
Opaque EventsL.interp_Es.
