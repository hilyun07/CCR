Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Set Implicit Arguments.
Set Typeclasses Depth 5.





Section PROOF.
  Let memRA: URA.t := (RA.excl Mem.t).
  Context `{@GRA.inG memRA Σ}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  Compute (URA.car (t:=memRA)).

  Section BODY.
    Context {Es: Type -> Type}.
    Context `{has_pE: pE -< Es}.
    Context `{has_eventE: eventE -< Es}.
    Definition allocF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        `sz: Z <- (pargs [Tint] varg)?;;
        if (Z_le_gt_dec 0 sz && Z_lt_ge_dec (8 * sz) modulus_64)
        then (delta <- trigger (Choose _);;
              let m0': Mem.t := Mem.mem_pad m0 delta in
              let (blk, m1) := Mem.alloc m0' sz in
              trigger (PPut m1↑);;;
              Ret (Vptr blk 0))
        else triggerUB
    .

    Definition freeF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        v <- (pargs [Tuntyped] varg)?;;
        '(b, ofs) <- val2laddr m0 v;;
        m1 <- (Mem.free m0 b ofs)?;;
        trigger (PPut m1↑);;;
        Ret (Vint 0)
    .

    Definition loadF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        v <- (pargs [Tuntyped] varg)?;;
        '(b, ofs) <- val2laddr m0 v;;
        v <- (Mem.load m0 b ofs)?;;
        Ret v
    .

    Definition storeF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(vaddr, vitem) <- (pargs [Tuntyped; Tuntyped] varg)?;;
        '(b, ofs) <- val2laddr m0 vaddr;;
        m1 <- (Mem.store m0 b ofs vitem)?;;
        trigger (PPut m1↑);;;
        Ret (Vint 0)
    .


    Definition ptr_to_intF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(b, ofs) <- (pargs [Tptr] varg)?;;
        '(exist _ (bID, m1) _) <- trigger (Choose {bID_m | (Mem.capture m0 b (fst bID_m) (snd bID_m))});;
        trigger (PPut m1↑);;;
        Ret (Vint (bID + ofs)).


    Definition int_to_ptrF: list val -> itree Es val :=
      fun varg =>
        i <- (pargs [Tint] varg)?;;
        Ret (Vint i).
        

    Definition cmp_eqF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(v0, v1) <- (pargs [Tuntyped; Tuntyped] varg)?;;
        b <- vcmp_eq m0 v0 v1;;
        if b: bool
        then Ret (Vint 1%Z)
        else Ret (Vint 0%Z)
    .

  End BODY.


  Variable csl: gname -> bool.
  Definition MemSem (sk: Sk.t): ModSem.t :=
    {|
      ModSem.fnsems := [("alloc", cfunU allocF) ; ("free", cfunU freeF) ; ("load", cfunU loadF) ; ("store", cfunU storeF) ; ("ptr_to_int", cfunU ptr_to_intF) ; ("int_to_ptr", cfunU int_to_ptrF) ; ("eq", cfunU cmp_eqF)];
      ModSem.mn := "Mem";
      ModSem.initial_st := (Mem.load_mem csl sk)↑;
    |}
  .

  Definition Mem: Mod.t := {|
    Mod.get_modsem := MemSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
