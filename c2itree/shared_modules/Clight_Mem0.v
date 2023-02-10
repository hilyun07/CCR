Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import AList.
Require Import ConvC2ITree.

From compcert Require Import
     AST Maps Globalenvs Memory Values Linking Integers.
From compcert Require Import
     Ctypes Clight Clightdefs.

Set Implicit Arguments.

Section PROOF.

  Section BODY.
    Context {Es: Type -> Type}.
    Context `{has_pE: pE -< Es}.
    Context `{has_eventE: eventE -< Es}.

    Definition allocF: Z * Z -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let (lo, hi) := varg in
        let (m1, blk) := Mem.alloc m0 lo hi in
        trigger (PPut m1↑);;;
        Ret (Vptr blk (Ptrofs.repr 0)).
    
    Definition freeF: block * Z * Z -> itree Es unit :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(b, lo, hi) := varg in
        m1 <- (Mem.free m0 b lo hi)?;;
        trigger (PPut m1↑);;;
        Ret tt
    .

    Definition loadF: memory_chunk * block * Z -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(chunk, b, ofs) := varg in
        v <- (Mem.load chunk m0 b ofs)?;;
        Ret v
    .

    Definition loadbytesF: block * Z * Z -> itree Es (list memval) :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(b, ofs, n) := varg in
        v <- (Mem.loadbytes m0 b ofs n)?;;
        Ret v
    .

    Definition storeF: memory_chunk * block * Z * val -> itree Es unit :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(chunk, b, ofs, v) := varg in
        m1 <- (Mem.store chunk m0 b ofs v)?;;
        trigger (PPut m1↑);;;
        Ret tt
    .

    Definition storebytesF: block * Z * list memval -> itree Es unit :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(b, ofs, bytes) := varg in
        m1 <- (Mem.storebytes m0 b ofs bytes)?;;
        trigger (PPut m1↑);;;
        Ret tt
    .

    Definition valid_pointerF: block * Z -> itree Es bool :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(b, ofs) := varg in
        Ret (Coqlib.proj_sumbool (Mem.perm_dec m0 b ofs Cur Nonempty))
    .

  End BODY.

  Import Cskel.
  Variable optpgm: option Clight.program.
  Variable skenv: CSkEnv.t.

  Definition store_init_data (m : mem) (b : block) (p : Z) (id : init_data) :=
    match id with
    | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
    | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
    | Init_int32 n => Mem.store Mint32 m b p (Vint n)
    | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
    | Init_float32 n => Mem.store Mfloat32 m b p (Vsingle n)
    | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
    | Init_space _ => Some m
    | Init_addrof symb ofs =>
        match SkEnv.id2blk (string_of_ident symb) with
        | Some b' => Mem.store Mptr m b p (Vptr b' ofs)
        | None => None
        end
    end.


  Fixpoint store_init_data_list (m : mem) (b : block) (p : Z) (idl : list init_data) {struct idl} : option mem :=
    match idl with
    | [] => Some m
    | id :: idl' =>
        match store_init_data m b p id with
        | Some m' => store_init_data_list m' b (p + init_data_size id)%Z idl'
        | None => None
        end
    end.
  
  Definition alloc_global (m : mem) (idg : ident * cglobdef) :=
    let (_, g) := idg in
    match g with
    | Gfun _ => let (m1, b) := Mem.alloc m 0 1 in Mem.drop_perm m1 b 0 1 Nonempty
    | Gvar v =>
        let init := gvar_init v in
        let sz := init_data_list_size init in
        let (m1, b) := Mem.alloc m 0 sz in
        match store_zeros m1 b 0 sz with
        | Some m2 =>
            match store_init_data_list m2 b 0 init with
            | Some m3 => Mem.drop_perm m3 b 0 sz (Genv.perm_globvar v)
            | None => None
            end
        | None => None
        end
    end.
      

  Fixpoint alloc_globals (m: mem) (gl: list (ident * cglobdef))
                       {struct gl} : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match alloc_global m g with
      | None => None
      | Some m' => alloc_globals m' gl'
      end
  end.

  Definition _load_mem := alloc_globals Mem.empty sk.
  
  Definition load_mem :=
    match _load_mem with
    | Some mem => mem
    | None => Mem.empty
    end.
  
  Definition MemSem : ModSem.t :=
    {|
      ModSem.fnsems := [("alloc", cfunU allocF); ("free", cfunU freeF);
                        ("load", cfunU loadF); ("loadbytes", cfunU loadbytesF);
                        ("store", cfunU storeF); ("storebytes", cfunU storebytesF);
                        ("valid_pointer", cfunU valid_pointerF)];
      ModSem.mn := "Mem";
      ModSem.initial_st := (load_mem)↑;
    |}
  .
End PROOF.

  Definition Mem: Mod.t := {|
    Mod.get_modsem := fun sk => MemSem sk;
    Mod.sk := Sk.unit;
  |}
  .
