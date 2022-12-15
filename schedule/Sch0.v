Require Import Coqlib.
(* Require Import ITreelib. *)
Require Import ImpPrelude.
(* Require Import STS. *)
(* Require Import Behavior. *)
Require Import ModSem.
Require Import Skeleton.
(* Require Import PCM. *)

Set Implicit Arguments.
Set Typeclasses Depth 5.





Section PROOF.

  Section BODY.
    Context {Es: Type -> Type}.
    Context `{has_pE: pE -< Es}.
    Context `{has_eventE: eventE -< Es}.
    Context `{has_schE: EventsL.schE -< Es}.
    Definition spawnF: (list val) -> itree Es val :=
      fun varg =>
        match varg with
        | fn::args =>
            fn <- 
            z <- trigger (EventsL.Spawn fn args);; Ret (Vint z)
        | _ => triggerUB
        end.

    Definition yieldF: (list val) -> itree Es val :=
      fun varg =>
        z <- trigger Yield;; Ret Vundef.

    Definition getpidF: (list val) -> itree Es val :=
      fun varg =>
        z <- trigger Gettid;; Ret (Vint z).

  End BODY.



  Definition SchSem (sk: Sk.t): ModSem.t :=
    {|
      ModSem.fnsems := [("spawn", cfunU spawnF) ; ("yield", cfunU yieldF);
                        ("getpid", cfunU getpidF)];
      ModSem.mn := "Sch";
      ModSem.initial_st := Vundef↑;
    |}
  .

  Definition Sch: Mod.t := {|
    Mod.get_modsem := SchSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
