Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
Require Import ClightPlusgen.
Require Import main.

(* TODO: one module embedding *)
Definition _main : Errors.res Mod.t := compile prog "main".

Theorem valid_xor: exists xor, _xor = Errors.OK xor.
Proof. eauto. Qed.
