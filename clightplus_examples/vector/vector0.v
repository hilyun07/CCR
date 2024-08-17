Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
Require Import ClightPlusgen.
Require Import vector.

Definition _vector : Errors.res Mod.t := compile prog "vector".

Theorem valid_vector: exists vector, _vector = Errors.OK vector.
Proof. eauto. Qed.

Definition vector_compiled : Mod.t :=
  match _vector as v return (match v with Errors.OK _ => Mod.t | Errors.Error _ => unit end) with
  | Errors.OK v => v
  | Errors.Error _ => tt
  end.

Theorem vector_compiled_res : _vector = Errors.OK vector_compiled.
Proof. reflexivity. Qed.
