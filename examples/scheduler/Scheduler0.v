Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.

Set Implicit Arguments.



Section PROOF.

  (***
    f(n) := if (n == 0) then 0 else (n + g(n-1))
  ***)
  Definition fF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- (pargs [Tint] varg)?;;
      _ <- trigger (Syscall "print" [n]↑ top1);;
      `pid:Z <- ccallU "Spawn" ("g", [Vint 2]);;
      _ <- trigger (Syscall "print" [pid]↑ top1);;
      Ret (Vint n).
  
  Definition gF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- (pargs [Tint] varg)?;;
      _ <- trigger (Syscall "print" [n]↑ top1);;
      Ret (Vint n).

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := [("f", cfunU fF); ("g", cfunU gF)];
    ModSem.mn := "F";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition F: Mod.t := {|
    Mod.get_modsem := fun _ => FSem;
    Mod.sk := [("f", Sk.Gfun)];
  |}
  .
End PROOF.
