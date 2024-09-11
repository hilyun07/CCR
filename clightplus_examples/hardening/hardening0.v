Require Import ModSem.
Require Import Skeleton.
Require Import ClightPlusgen.
Require Import hardening.
(* Require Import main. *)
(* From compcert Require Import Linking. *)

Definition _hardening : Clight.program := link hardening.prog.

Definition hardening : Errors.res Mod.t :=
  compile _hardening "hardening".

Definition hardening_sk : Sk.t :=
  match hardening with
  | Errors.OK md => md.(Mod.sk)
  | Errors.Error _ => Sk.unit
  end.

Definition _msk : Errors.res Sk.t :=
  mem_skel _hardening.

Theorem msk_hardening: exists msk, _msk = Errors.OK msk.
Proof.
Admitted.

Theorem valid_hardening: exists p, hardening = Errors.OK p.
Proof.
Admitted.
