Require Import Coqlib.
Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
From compcert Require Import Values.

Set Implicit Arguments.

Section Parsing.
  
(* Definition pargs (ts: list val_type): *)
(*   forall (vs: list val), option (val_types_sem ts). *)
(* Proof. *)
(*   induction ts as [|thd ttl]. *)
(*   - intros [|]; simpl. *)
(*     + exact (Some tt). *)
(*     + exact None. *)
(*   - simpl. destruct ttl as [|]. *)
(*     + intros [|vhd []]; simpl. *)
(*       * exact None. *)
(*       * exact (parg thd vhd). *)
(*       * exact None. *)
(*     + intros [|vhd vtl]. *)
(*       * exact None. *)
(*       * exact (match parg thd vhd with *)
(*                | Some vhd' => *)
(*                  match IHttl vtl with *)
(*                  | Some vtl' => Some (vhd', vtl') *)
(*                  | None => None *)
(*                  end *)
(*                | None => None *)
(*                end). *)
(* Defined. *)

  Context {HasState : Es -< eff}.

  Definition triggerE := trigger (Syscall "print" ["error, there's something wrong"]↑ top1) ;;; trigger (Syscall "exit" []↑ top1).

  Definition parg (t: val_type) (v : val) : itree eff (val_types_sem ts) :=
    match t with
    | Tint =>
        match v with
        | Vint i32 => Ret (Int.intval i32)
        | Vlong i64 => Ret (Int64.intval i64)
        | _ => triggerE
        end
    | Tptr =>
        match v with
        | Vptr b ofs => Ret (b, Ptrofs.intval ofs)
        | _ => triggerE
        end
    end.
    

  Definition pargs (ts : list val_type) : list val -> itree eff (val_types_sem ts).

End Parsing.
