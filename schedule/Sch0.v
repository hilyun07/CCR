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
    Context `{has_evnetE: eventE -< Es}.
    Context `{has_schE: EventsL.schE -< Es}.
    Context `{has_callE: callE -< Es}.
    Definition spawnF: (string * list val) -> itree Es val :=
      fun varg =>
        let '(fn, args) := varg in
        pid <- trigger (EventsL.Spawn fn args↑);; Ret (Vint (Z.of_nat pid)).

    Definition yieldF: (list val) -> itree Es val :=
      fun varg =>
        _ <- trigger EventsL.Yield;; Ret Vundef.

    Definition getpidF: (list val) -> itree Es val :=
      fun varg =>
        pid <- trigger EventsL.Getpid;; Ret (Vint (Z.of_nat pid)).

  End BODY.

Definition temp:= cfunU spawnF.

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
