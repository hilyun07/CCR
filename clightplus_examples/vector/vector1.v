Require Import CoqlibCCR.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import Any.
Require Import ModSem.
Require Import ModSemE.
Require Import ClightPlusMem1.
From compcert Require Export Ctypes Values AST Memdata Integers.

Set Implicit Arguments.

Section PROP.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

End PROP.

Section SPEC.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition vector_init_spec : fspec.
  Admitted.

  Definition vector_total_spec : fspec.
  Admitted.

  Definition vector_resize_spec : fspec.
  Admitted.

  Definition vector_add_spec : fspec.
  Admitted.

  Definition vector_set_spec : fspec.
  Admitted.

  Definition vector_get_spec : fspec.
  Admitted.

  Definition vector_delete_spec : fspec.
  Admitted.

  Definition vector_free_spec : fspec.
  Admitted.

  (* sealed *)
  Definition vectorStb : list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [ ("vector_init", vector_init_spec);
            ("vector_total", vector_total_spec);
            ("vector_resize", vector_resize_spec);
            ("vector_add", vector_add_spec);
            ("vector_set", vector_set_spec);
            ("vector_get", vector_get_spec);
            ("vector_delete", vector_delete_spec);
            ("vector_free", vector_free_spec) ].
  Defined.

End SPEC.

Section SMOD.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition vectorSbtb: list (gname * fspecbody) :=
    [
     ("vector_init", mk_pure vector_init_spec);
     ("vector_total", mk_pure vector_total_spec);
     ("vector_resize", mk_pure vector_resize_spec);
     ("vector_add", mk_pure vector_add_spec);
     ("vector_set", mk_pure vector_set_spec);
     ("vector_get", mk_pure vector_get_spec);
     ("vector_delete", mk_pure vector_delete_spec);
     ("vector_free", mk_pure vector_free_spec)
     ].
  
  Definition SvectorSem : SModSem.t := {|
    SModSem.fnsems := vectorSbtb;
    SModSem.mn := "vector";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}.

  Variable vector0: Mod.t.

  Definition Svector : SMod.t := {|
    SMod.get_modsem := fun _ => SvectorSem;
    SMod.sk := vector0.(Mod.sk);
  |}.

  Definition vector stb : Mod.t := (SMod.to_tgt stb) Svector.

End SMOD.
