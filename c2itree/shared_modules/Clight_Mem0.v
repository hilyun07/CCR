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
    Context {has_callE: callE -< Es}.

    Definition check_value: val -> itree Es nat :=
      fun varg =>
        match varg with
        | Vint _ => 
            _ <- trigger (Syscall "print_string" ["is int"]↑ top1);; Ret 0
        | Vlong _ =>
            _ <- trigger (Syscall "print_string" ["is long"]↑ top1);; Ret 0
        | Vfloat _ =>
            _ <- trigger (Syscall "print_string" ["is float"]↑ top1);; Ret 0
        | Vsingle _ =>
            _ <- trigger (Syscall "print_string" ["is single"]↑ top1);; Ret 0
        | Vptr _ _ =>
            _ <- trigger (Syscall "print_string" ["is ptr"]↑ top1);; Ret 0
        | Vundef =>
            _ <- trigger (Syscall "print_string" ["is undef"]↑ top1);; Ret 0
        end.

    (* low level allocation of memory *)
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

    Definition loadF: memory_chunk * val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(chunk, addr) := varg in
        _ <- trigger (Syscall "print_string" ["try load"]↑ top1);;
        _ <- trigger (Syscall "print_string" ["check value"]↑ top1);;
        _ <- check_value addr;;
        '(b, ofs) <- (match addr with Vptr b ofs => Some (Zpos b, Ptrofs.unsigned ofs)| _ => None end)?;;
        _ <- trigger (Syscall "print_num" [b]↑ top1);;
        _ <- trigger (Syscall "print_string" [": block"]↑ top1);;
        _ <- trigger (Syscall "print_num" [ofs]↑ top1);;
        _ <- trigger (Syscall "print_string" [": offset"]↑ top1);;
        v <- (Mem.loadv chunk m0 addr)?;;
        _ <- trigger (Syscall "print_string" ["load success"]↑ top1);;
        Ret v
    .

    Definition loadbytesF: val * Z -> itree Es (list memval) :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(addr, n) := varg in
        match addr with
        | Vptr b ofs =>
            v <- (Mem.loadbytes m0 b (Ptrofs.unsigned ofs) n)?;;
            Ret v
        | _ => triggerUB
        end
    .

    Definition storeF: memory_chunk * val * val -> itree Es unit :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(chunk, addr, v) := varg in
        m1 <- (Mem.storev chunk m0 addr v)?;;
        trigger (PPut m1↑);;;
        Ret tt
    .

    Definition storebytesF: val * list memval -> itree Es unit :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(addr, bytes) := varg in
        match addr with
        | Vptr b ofs =>
            m1 <- (Mem.storebytes m0 b (Ptrofs.unsigned ofs) bytes)?;;
            trigger (PPut m1↑);;;
            Ret tt
        | _ => triggerUB
        end
    .

    Definition valid_pointerF: block * Z -> itree Es bool :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(b, ofs) := varg in
        Ret (Coqlib.proj_sumbool (Mem.perm_dec m0 b ofs Cur Nonempty))
    .

    Definition mallocF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(m1, b) <- (match Archi.ptr64, varg with
                    | true, [Vlong i] =>
                        Ret (Mem.alloc m0 (- size_chunk Mptr) (Int64.unsigned i))
                    | false, [Vint i] =>
                        Ret (Mem.alloc m0 (- size_chunk Mptr) (Int.unsigned i))
                    | _, _ => triggerUB
                    end);;
        v <- (hd_error varg)?;;
        m2 <- (Mem.store Mptr m1 b (- size_chunk Mptr) v)?;;
        trigger (PPut m2↑);;;
        Ret (Vptr b Ptrofs.zero)
    .

    Definition mfreeF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        match Archi.ptr64, varg with
        | _, [Vptr b ofs] =>
            v_sz <- (Mem.load Mptr m0 b (Ptrofs.unsigned ofs - size_chunk Mptr))?;;
            let sz := match Archi.ptr64, v_sz with
                      | true, Vlong i =>
                          Int64.unsigned i
                      | false, Vint i =>
                          Int.unsigned i
                      | _, _ => (- 1)%Z
                      end in
            if (sz >? 0)%Z
            then m1 <- (Mem.free m0 b (Ptrofs.unsigned ofs - size_chunk Mptr) (Ptrofs.unsigned ofs + sz))?;;
                 trigger (PPut m1↑);;;
                 Ret Vundef
            else triggerUB
        | true, [Vlong (Int64.mkint 0 _)] => Ret Vundef
        | false, [Vint (Int.mkint 0 _)] => Ret Vundef
        | _, _ => triggerUB
        end
    .
    
    Definition reallocF: list val -> itree Es val :=
      fun varg =>
        match varg with
        | [addr;v_sz'] =>
            match Archi.ptr64, addr with
            | true, Vlong (Int64.mkint 0 _)
            | false, Vint (Int.mkint 0 _) => ccallU "malloc" v_sz'
            | _, Vptr b ofs =>
                (* Read the size of the allocated memory *)
                mp0 <- trigger (PGet);;
                m0 <- mp0↓?;;
                v_sz <- (Mem.load Mptr m0 b (Ptrofs.unsigned ofs - size_chunk Mptr)%Z)?;;
                let sz := match Archi.ptr64, v_sz with
                      | true, Vlong i =>
                          Int64.unsigned i
                      | false, Vint i =>
                          Int.unsigned i
                      | _, _ => (- 1)%Z
                      end in
                let sz' := match Archi.ptr64, v_sz' with
                      | true, Vlong i =>
                          Int64.unsigned i
                      | false, Vint i =>
                          Int.unsigned i
                      | _, _ => (- 1)%Z
                      end in
                if (sz >=? 0)%Z && (sz' >=? 0)%Z
                then
                    (* if (sz >=? sz')%Z then (* Reducing the size of the allocated memory *) *)
                    (*      `_: () <- ccallU "free" (b, sz', sz);; *)
                    (*          `_: () <- ccallU "store" (Mptr, b, (- size_chunk Mptr)%Z, Vlong (Int64.repr sz'));; *)
                    (*          Ret (Vptr b (Ptrofs.repr ofs)) *)
                    (*    else (* Increasing the size of the allocated memory *) *)
                    `addr': val <- ccallU "malloc" sz';;
                    `data: list memval <- ccallU "loadbytes" (addr, sz);;
                    `_: () <- ccallU "mfree" addr;;
                    `_: () <- ccallU "storebytes" (addr, firstn (Z.to_nat sz') data);;
                    Ret addr'
                else triggerUB (* Behaviours vary depending on implementations *)
            | _, _ => triggerUB
            end
        | _ => triggerUB
        end.
    
  End BODY.

  Variable sk: Sk.t.
  Let skenv: SkEnv.t := Sk.load_skenv sk.

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
        match SkEnv.id2blk skenv (string_of_ident symb) with
        | Some b' => Mem.store Mptr m b p (Vptr (Pos.of_nat (S b')) ofs)
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
  
  Definition alloc_global (m : mem) (idg : string * C_SkelEntry) :=
    let (_, g) := idg in
    match g with
    | Cgfun _ => let (m1, b) := Mem.alloc m 0 1 in Mem.drop_perm m1 b 0 1 Nonempty
    | Cgvar v =>
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
      

  Fixpoint alloc_globals (m: mem) (gl: list (string * C_SkelEntry))
                       {struct gl} : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match alloc_global m g with
      | None => None
      | Some m' => alloc_globals m' gl'
      end
  end.

  Fixpoint unfold_skel (sk: Sk.t) : option (list (string * C_SkelEntry)) :=
    match sk with
    | [] => Some []
    | (ident, any) :: t =>
        match Any.downcast any with
        | Some d => match unfold_skel t with Some t' => Some ((ident, d) :: t') | None => @None (list (string * C_SkelEntry)) end
        | _ => @None (list (string * C_SkelEntry))
        end
    end.

  Definition load_mem :=
    match unfold_skel sk with
    | Some gl =>
        match alloc_globals Mem.empty gl with
        | Some m => m
        | None => Mem.empty
        end
    | None => Mem.empty
    end.
  
  Definition MemSem : ModSem.t :=
    {|
      ModSem.fnsems := [("alloc", cfunU allocF); ("free", cfunU freeF);
                        ("load", cfunU loadF); ("loadbytes", cfunU loadbytesF);
                        ("store", cfunU storeF); ("storebytes", cfunU storebytesF);
                        ("malloc", cfunU mallocF); ("mfree", cfunU mfreeF); 
                        ("realloc", cfunU reallocF);
                        ("valid_pointer", cfunU valid_pointerF)];
      ModSem.mn := "Mem";
      ModSem.initial_st := (load_mem)↑;
    |}
  .
  
End PROOF.

Definition size_t := if Archi.ptr64 then tulong else tuint.

Definition Mem: Mod.t :=
  {|
    Mod.get_modsem := MemSem;
    Mod.sk := [("malloc", (Cgfun (Tfunction (Tcons size_t Tnil) (tptr tvoid) cc_default))↑);
               ("mfree", (Cgfun (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))↑); 
               ("realloc", (Cgfun (Tfunction (Tcons (tptr tvoid) (Tcons size_t Tnil)) (tptr tvoid) cc_default))↑)]
  |}
.
