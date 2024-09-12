Require Import CoqlibCCR.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import SimModSem.
Require Import PCM.
Require Import HoareDef.
Require Import STB.
Require Import HTactics ProofMode.
Require Import HSim IProofMode.
Require Import ClightPlusSkel ClightPlusExprgen ClightPlusgen.
Require Import ClightPlusMem0 ClightPlusMem1 ClightPlusMemAux.
Require Import CProofMode CIProofMode.
Require Import vector.
Require Import vector0.
Require Import vector1.
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Clightdefs.

Require Import ClightPlusMem01Proof.
Require Import vector_auxiliary.
Require Import vector01proof_vector_init.
Require Import vector01proof_vector_destruct.
Require Import vector01proof_vector_esize.
Require Import vector01proof_vector_capacity.
Require Import vector01proof_vector_length.
Require Import vector01proof_vector_reserve.
Require Import vector01proof_vector_push.
Require Import vector01proof_vector_get.
Require Import vector01proof_vector_set.
Require Import vector01proof_vector_remove.

Section PROOF.

  Import ClightPlusMem1.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb vectorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).

  Let ce := Maps.PTree.elements (prog_comp_env prog).

  (* Check sim_vector_init. *)
  (* Check sim_vector_destruct. *)
  (* Check sim_vector_esize. *)
  (* Check sim_vector_capacity. *)
  (* Check sim_vector_length. *)
  (* Check sim_vector_reserve. *)
  (* Check sim_vector_push. *)
  (* Check sim_vector_get. *)
  (* Check sim_vector_set. *)
  (* Check sim_vector_remove. *)

  Theorem correct :
    refines2
      [vector_compiled; (ClightPlusMem0.Mem mfsk)]
      [vector1.vector vector_compiled GlobalStb; (ClightPlusMem1.Mem mfsk)].
  Admitted.

End PROOF.
