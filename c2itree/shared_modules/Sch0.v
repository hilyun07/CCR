Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import AList.
Require Import ConvC2ITree.

From compcert Require Import
     AST Maps Globalenvs Memory Values Linking Integers.
From compcert Require Import
     Ctypes Clight.
                             
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
        pid <- trigger (EventsL.Spawn fn args↑);;
        Ret (Vint (Int.repr (Z.of_nat pid))).

    Definition yieldF: (list val) -> itree Es val :=
      fun varg =>
        z <- trigger EventsL.Yield;; Ret Vundef.

    Definition getpidF: (list val) -> itree Es val :=
      fun varg =>
        pid <- trigger EventsL.Getpid;;
        Ret (Vint (Int.repr (Z.of_nat pid))).

  End BODY.



  Definition SchSem : ModSem.t :=
    {|
      ModSem.fnsems := [("spawn", cfunU spawnF) ; ("yield", cfunU yieldF);
                        ("getpid", cfunU getpidF)];
      ModSem.mn := "Sch";
      ModSem.initial_st := tt↑;
    |}
  .

  Definition Sch: Mod.t := {|
    Mod.get_modsem := fun _ => SchSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
