Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import Sch0.

Set Implicit Arguments.



Section PROOF.

  (***
    f(n) := if (n == 0) then 0 else (n + g(n-1))
  ***)
  Definition mainF: list val -> itree Es val :=
    fun varg =>
      `new_pid:val <- ccallU "spawn" ("f", [Vint 10]);;
      new_pid <- (parg Tint new_pid)?;;
      _ <- trigger (Syscall "print" [new_pid]↑ top1);;
      `_:unit <- ccallU "yield" ([]:list val);;
      _ <- trigger (PPut (7%Z)↑);;

      `pid:val <- ccallU "getpid" ([]:list val);;
      pid <- (parg Tint pid)?;;
      _ <- trigger (Syscall "print" [pid]↑ top1);;
      Ret (Vint 1).

  Definition fF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- (pargs [Tint] varg)?;;
      _ <- trigger (Syscall "print" [n]↑ top1);;
      `pid:val <- ccallU "getpid" ([]:list val);;
      pid <- (parg Tint pid)?;;
      _ <- trigger (Syscall "print" [pid]↑ top1);;
      p <- trigger PGet;;
      `p:Z <- p↓?;;
      _ <- trigger (Syscall "print" [p]↑ top1);;
      Ret (Vint n).

  Definition Sch_examSem: ModSem.t := {|
    ModSem.fnsems := [("main", cfunU mainF); ("f", cfunU fF)];
    ModSem.mn := "Sch_exam";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Sch_exam: Mod.t := {|
    Mod.get_modsem := fun _ => Sch_examSem;
    Mod.sk := [("sch_exam", Sk.Gfun)];
  |}
  .
End PROOF.

Definition sch_exam := ModSemL.initial_itr (ModL.enclose (Mod.add_list [Sch_exam; Sch])) None.
