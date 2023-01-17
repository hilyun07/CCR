Require Import Coqlib.
Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
From compcert Require Import Values.

Require Import parse_compcert.

Set Implicit Arguments.



Section PROOF.

  (***
    f(n) := if (n == 0) then 0 else (n + g(n-1))
  ***)
  Definition mainF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- pargs [Tint] varg;;
      m <- trigger PGet;;
      m : Z <- m↓#?;;
      _ <- trigger (Syscall "print" [n;m]↑ top1);;
      `pid:Z <- ccallU "Spawn" ("f", [Vint 2]);;
      _ <- trigger (Syscall "print" [pid]↑ top1);;
      Ret (Vint n).
  
  Definition FSem: ModSem.t := {|
    ModSem.fnsems := [("f", cfunU fF)];
    ModSem.mn := "F";
    ModSem.initial_st := 1↑;
  |}
  .

  Definition F: Mod.t := {|
    Mod.get_modsem := fun _ => FSem;
    Mod.sk := [("f", Sk.Gfun)];
  |}
  .
End PROOF.
