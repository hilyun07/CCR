From compcert Require Import
     Smallstep AST Events Behaviors Errors Csharpminor Linking Compiler Asm.
Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import STS2SmallStep.
Require Import ClightPlusgen.
(* Require Import Csharpminor2Asm. *)

Require Import ClightPlus2ClightSepComp.
(* Require Import Clight2Asm. *)
(* Require Import Clight2AsmProofs. *)

Theorem compile_behavior_improves
    (clight_prog : Clight.program) (asm : Asm.program)
    (mn: string) (md: Mod.t) (sk_mem: Sk.t)
    (COMP: compile clight_prog mn = Errors.OK md)
    (MEMSKEL: mem_skel clight_prog = Errors.OK sk_mem)
:
    (improves2_program (clightp_sem sk_mem md) (Asm.semantics asm)).
Proof.
Admitted.