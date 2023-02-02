Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem.
From compcert Require Import
    Ctypes Values Integers Archi.

Module Wordsize_16.
    Definition wordsize := 16.
    Remark wordsize_not_zero: wordsize <> 0.
    Proof.
        unfold wordsize.
        lia.
    Qed.
End Wordsize_16.

Module Int16 := Make(Wordsize_16).

Section VAL.

(** Redifine pargs with Clight values and types *)

Definition unptr (v: val): option (block * ptrofs) :=
  match v with
  | Vptr b ofs => Some (b, ofs)
  | _ => None
  end.

Definition unint (sz: intsize) (sign: signedness) (v: val): option Z :=
  match v with
  | Vint x => match sz with
    | I8 => match sign with
      | Signed => Some (Byte.signed (Byte.repr (Int.signed x)))
      | Unsigned => Some (Byte.unsigned (Byte.repr (Int.unsigned x)))
      end
    | I16 => match sign with
      | Signed => Some (Int16.signed (Int16.repr (Int.signed x)))
      | Unsigned => Some (Int16.unsigned (Int16.repr (Int.unsigned x)))
      end
    | I32 => match sign with
      | Signed => Some (Int.signed x)
      | Unsigned => Some (Int.unsigned x)
      end
    | _ => None
    end
  | _ => None
  end.

Definition unlong (sign: signedness) (v: val): option Z :=
  match v with
  | Vlong x => match sign with
    | Signed => Some (Int64.signed x)
    | Unsigned => Some (Int64.unsigned x)
    end
  | _ => None
  end.

Definition val_type_sem (t: type): Type :=
  match t with
  | Tvoid => unit
  | Tint sz sign _ => Z
  | Tlong sign _ => Z
  | Tfloat sz _ => unit
  | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tstruct _ _
  | Tunion _ _ => block * ptrofs
  end.

Fixpoint val_types_sem (ts: list type): Type :=
  match ts with
  | [] => unit
  | [hd] => val_type_sem hd
  | hd::tl => val_type_sem hd * val_types_sem tl
  end.

Definition parg (t: type) (v: val): option (val_type_sem t) :=
  match t with
  | Tvoid => Some tt
  | Tint sz sign _ => unint sz sign v
  | Tlong sign _ => unlong sign v
  | Tfloat sz _ => Some tt
  | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tstruct _ _
  | Tunion _ _ => unptr v
  end.

Definition pargs (ts: list type):
  forall (vs: list val), option (val_types_sem ts).
Proof.
  induction ts as [|thd ttl].
  - intros [|]; simpl.
    + exact (Some tt).
    + exact None.
  - simpl. destruct ttl as [|].
    + intros [|vhd []]; simpl.
      * exact None.
      * exact (parg thd vhd).
      * exact None.
    + intros [|vhd vtl].
      * exact None.
      * exact (match parg thd vhd with
               | Some vhd' =>
                 match IHttl vtl with
                 | Some vtl' => Some (vhd', vtl')
                 | None => None
                 end
               | None => None
               end).
Defined.

End VAL.

Section MEM.

Definition Read_byte (blk: block) (ofs: ptrofs): itree Es Byte.int :=
    let p := Vptr blk ofs in
    `v: val <- ccallU "load" [p];;
    match v with
    | Vint i => Ret (Byte.repr (Int.unsigned i))
    | _ => Ret Byte.zero
    end.

Definition Read_short (blk: block) (ofs: ptrofs): itree Es Int16.int :=
    `b1: Byte.int <- Read_byte blk ofs;;
    `b2: Byte.int <- Read_byte blk (Ptrofs.add ofs (Ptrofs.repr 8));;
    if Archi.big_endian then
        Ret (Int16.add
        (Int16.shl (Int16.repr (Byte.unsigned b1)) (Int16.repr 8))
        (Int16.repr (Byte.unsigned b2)))
    else
        Ret (Int16.add
        (Int16.shl (Int16.repr (Byte.unsigned b2)) (Int16.repr 8))
        (Int16.repr (Byte.unsigned b1))).

Definition Read_int (blk: block) (ofs: ptrofs): itree Es int :=
    `s1: Int16.int <- Read_short blk ofs;;
    `s2: Int16.int <- Read_short blk (Ptrofs.add ofs (Ptrofs.repr 16));;
    if Archi.big_endian then
        Ret (Int.add
        (Int.shl (Int.repr (Int16.unsigned s1)) (Int.repr 16))
        (Int.repr (Int16.unsigned s2)))
    else
        Ret (Int.add
        (Int.shl (Int.repr (Int16.unsigned s2)) (Int.repr 16))
        (Int.repr (Int16.unsigned s1))).

Definition Read_long (blk: block) (ofs: ptrofs): itree Es Int64.int :=
    `i1: int <- Read_int blk ofs;;
    `i2: int <- Read_int blk (Ptrofs.add ofs (Ptrofs.repr 32));;
    if Archi.big_endian then
        Ret (Int64.add
        (Int64.shl (Int64.repr (Int.unsigned i1)) (Int64.repr 32))
        (Int64.repr (Int.unsigned i2)))
    else
        Ret (Int64.add
        (Int64.shl (Int64.repr (Int.unsigned i2)) (Int64.repr 32))
        (Int64.repr (Int.unsigned i1))).

Fixpoint Write_Z (blk: block) (ofs: ptrofs) (sz: nat) (n: Z): itree Es () :=
    match sz with
    | 0 => `_: val <- ccallU "store" [Vptr blk ofs; Vint (Int.repr n)];;
        Ret tt
    | S sz => let n1 := (n / (2^(8 * 2^Z.of_nat sz)))%Z in
        let n2 := (n mod (2^(8 * 2^Z.of_nat sz)))%Z in
        let ofs' := Ptrofs.add ofs (Ptrofs.repr (8 * 2^Z.of_nat sz)) in
        if Archi.big_endian then
            Write_Z blk ofs sz n1;;;
            Write_Z blk ofs' sz n2;;;
            Ret tt
        else
            Write_Z blk ofs sz n2;;;
            Write_Z blk ofs' sz n1;;;
            Ret tt
    end.

Fixpoint switch_endianness (sz: nat) (x: Z): Z :=
    (* Here sz is the log2 of the number of bytes.
    Hence 0 for 8 bits, 1 for 16 bits, 2 for 32 bits and 3 for 64 bits. *)
    match sz with
    | 0 => x
    | S sz =>
        (switch_endianness sz (x mod (2^(8 * 2^Z.of_nat sz))))
            * (2^(8 * 2^Z.of_nat sz))
        + (switch_endianness sz (x / (2^(8 * 2^Z.of_nat sz))))
    end.

End MEM.