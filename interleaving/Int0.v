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
    Definition spawnF: (list val) -> itree Es val :=
      fun varg =>
        '(fn, args) <- varg↓?;;
        z <- trigger (Spawn fn args);; Ret Vundef.
              
    Definition yieldF: (list val) -> itree Es val :=
      fun varg =>
        z <- trigger yield;; Ret Vundef.

    Definition getpidF: (list val) -> itree Es val :=
      fun varg =>
        z <- trigger gettid;; Ret (Vint z).

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
