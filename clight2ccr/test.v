Require Import ConvC2ITree.
Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
Require Import Clight_Mem0.
Require Import Sys.
Require Import src1.
Require Import src2.
From compcert Require Import Clight Globalenvs Linking Values.


Definition globenv1 := genv_genv (globalenv src1.prog).
Definition globenv2 := genv_genv (globalenv src2.prog).
Definition mod1 ge := get_mod src1.prog ge "mod1".
Definition mod2 ge := get_mod src2.prog ge "mod2".
Definition linked := link src1.prog src2.prog.

Program Instance EMSConfigImp: EMSConfig := {|
  finalize := fun rv => Some rv;  initial_arg := ([]: list val)↑;
|}
.

Definition test_itr :=
  pg <- linked?;;
  ge <- Ret (Clight.genv_genv (Clight.globalenv pg));;
  ModSemL.initial_itr ([("first", ModL.enclose (Mod.add_list "first" [mod1 ge;mod2 ge;Mem pg;Sys]))]) None.
