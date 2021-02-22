Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Mem1.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.









Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

(***
(Replaced asterisk with # because of coq-mode's parsing)
int pop(struct Node## llref) {
  if(#llref) {
    int v = (#llref)->val;
    struct Node* next = (#llref)->next;
    free(#llref);
    (#llref) = next;
    return v;
  }
  return -1;
}
***)
  Definition popF_parg: list val -> option val := (@hd_error _).
  Definition popF: list val -> itree Es val :=
    fun varg =>
      `llref: val <- (popF_parg varg)?;;
      `ll: val    <- (ccall "load" [llref]);;
      `b: bool    <- (ccall "cmp"  [ll; Vnullptr]);;
      if b
      then (
          '(blk, ofs) <- (unptr ll)?;;
          let addr_val  := Vptr blk ofs in
          let addr_next := Vptr blk (ofs + 1) in
          `v: val    <- (ccall "load"  [addr_val]);;
          `next: val <- (ccall "load"  [addr_next]);;
          `_: val    <- (ccall "free"  [addr_val]);;
          `_: val    <- (ccall "free"  [addr_next]);; (*** change "free"s specification ***)
          `_: val    <- (ccall "store" [llref; next]);;
          Ret v
        )
      else Ret (Vint (- 1))
  .

(* struct Node* push(struct Node* ll, int x) { *)
(*   struct Node* new_node = malloc(sizeof(struct Node)); *)
(*   new_node->val = x; *)
(*   new_node->next = ll; *)
(*   printf("[DEBUG]: "); *)
(*   print_all(new_node); *)
(*   return new_node; *)
(* } *)

  Definition pushF_parg (varg: list val): option (val * val) :=
    match varg with
    | [node; v] => Some (node, v)
    | _ => None
    end.

  Definition pushF: list val -> itree Es val :=
    fun varg =>
      '(node, v)     <- (pushF_parg varg)?;;
      `new_node: val <- (ccall "alloc" [Vint 2]);;
      addr_v         <- (vadd new_node (Vint 0))?;;
      addr_next      <- (vadd new_node (Vint 1))?;;
      `_: val        <- (ccall "store" [addr_v;    v]);;
      `vret: val     <- (ccall "store" [addr_next; node]);;
      `_: val        <- (ccall "print_all" [new_node]);;
      Ret vret
  .

  Definition LinkedListSem: ModSem.t := {|
    ModSem.fnsems := [("popF", cfun popF); ("pushF", cfun pushF)];
    ModSem.initial_mrs := [("LinkedList", (ε, unit↑))];
  |}
  .

  Definition LinkedList: Mod.t := {|
    Mod.get_modsem := fun _ => LinkedListSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
