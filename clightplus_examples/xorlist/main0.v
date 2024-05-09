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

Section SPEC.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition main_body : list val -> itree hEs val :=
    fun _ => ;;;Ret (Vint (Int.repr 21)).

  Definition main_spec : fspec :=
    (mk_simple
      (fun '() => (
        (ord_top),
        (fun varg => ⌜varg = (@nil val)↑⌝ ** Vnullptr (≃_m_null) Vnullptr),
        (fun _ => ⌜True⌝)
    )))%I.

End SPEC.


Section SMOD.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition mainSbtb: list (gname * fspecbody) :=
    [("main", mk_specbody main_spec (cfunU main_body))].
  
  Definition SmainSem : SModSem.t := {|
    SModSem.fnsems := mainSbtb;
    SModSem.mn := "main";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}.

  Definition Smain : SMod.t := {|
    SMod.get_modsem := fun _ => SmainSem;
    SMod.sk := Sk.unit;
  |}.

  Definition main stb : Mod.t := (SMod.to_tgt stb) Smain.

End SMOD.