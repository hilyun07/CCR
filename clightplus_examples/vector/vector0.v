Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
Require Import ClightPlusgen.
Require Import vector.

Definition _vector : Errors.res Mod.t := compile prog "vector".

Theorem valid_vector: exists vector, _vector = Errors.OK vector.
Proof. eauto. Qed.
