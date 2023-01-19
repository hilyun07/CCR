Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import AList.

From compcert Require Import
     AST Maps Globalenvs Memory Values Linking Integers.
From compcert Require Import
     Ctypes Clight.

Set Implicit Arguments.

Section PROOF.

  Section BODY.
    Context {Es: Type -> Type}.
    Context `{has_pE: pE -< Es}.
    Context `{has_eventE: eventE -< Es}.

    Definition printF: val -> itree Es val:=
      fun varg => v <- trigger (Syscall "print" [1]↑ top1);;v <- v↓?;;Ret v.
    
  End BODY.

  Variable csl: gname -> bool.
  Variable pgm: Clight.program.
  
  Definition SysSem: ModSem.t :=
    {|
      ModSem.fnsems := [("printf", cfunU printF)];
      ModSem.mn := "Sys";
      ModSem.initial_st := tt↑;
    |}
  .

  Definition Sys: Mod.t := {|
    Mod.get_modsem := fun _ => SysSem;
    Mod.sk := @Sk.unit Sk.gdefs;
  |}
  .
  
End PROOF.
