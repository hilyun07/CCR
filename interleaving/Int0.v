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
    Definition spwanF: (list val) -> itree Es val :=
      fun varg =>
        z <- trigger (Syscall "spawn" varg↑ top1);; Ret Vundef.
              
    Definition yieldF: (list val) -> itree Es val :=
      fun varg =>
        z <- trigger (Syscall "yield" varg↑ top1);; Ret Vundef.

  End BODY.



  Definition IntSem (sk: Sk.t): ModSem.t :=
    {|
      ModSem.fnsems := [("spwan", cfunU spwanF) ; ("yield", cfunU yieldF)];
      ModSem.mn := "Int";
      ModSem.initial_st := Vundef↑;
    |}
  .

  Definition Mem: Mod.t := {|
    Mod.get_modsem := IntSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
