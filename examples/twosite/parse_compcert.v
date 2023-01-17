Require Import Coqlib.
Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
From compcert Require Import Values Integers Ctypes.

Set Implicit Arguments.

Section Parsing.
  
  Variant val_type :=
    | Tint
    | Tptr.

  Definition val_type_sem (t: val_type): Type :=
    match t with
    | Tint => Z
    | Tptr => (block * Z)
    end.
  
  Fixpoint val_types_sem (ts: list val_type): Type :=
    match ts with
    | [] => unit
    | [hd] => val_type_sem hd
    | hd::tl => val_type_sem hd * val_types_sem tl
    end.
  
  Context `{HasState : eventE -< eff}.


  Definition parg (t: val_type) (v : val) : itree eff (val_type_sem t):=
    match t with
    | Tint =>
        match v with
        | Vint i32 => Ret (Int.intval i32)
        | Vlong i64 => Ret (Int64.intval i64)
        | _ => triggerErr
        end
    | Tptr =>
        match v with
        | Vptr b ofs => Ret (b, Ptrofs.intval ofs)
        | _ => triggerErr
        end
    end.

  Fixpoint pargs (ts : list val_type) (vs : list val) : itree eff (val_types_sem ts):=
    match ts, vs with
    | [], [] => Ret (tt : (val_types_sem (@nil val_type)))
    | [t], [v] => r <- parg t v;; Ret r
    | t1 :: t2 :: tl, v :: vl => r1 <- parg t1 v ;; r2 <- pargs (t2 :: tl) vl ;; Ret (r1, r2)
    | _, _ => triggerErr
    end.

End Parsing.
