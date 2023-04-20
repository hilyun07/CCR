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
     Ctypes Clight Ctypesdefs.
                             
Set Implicit Arguments.
Set Typeclasses Depth 5.





Section PROOF.

  Section BODY.
    Context {Es: Type -> Type}.
    Context `{has_evnetE: eventE -< Es}.
    Context `{has_schE: EventsL.schE -< Es}.
    Context `{has_callE: callE -< Es}.
    Context (sk: Sk.t).
    Definition spawnF: (string * list val) -> itree Es val :=
      fun varg =>
        let '(fn, args) := varg in
        pid <- trigger (EventsL.Spawn fn args↑);;
        Ret (Vint (Int.repr (Z.of_nat pid))).

    Definition yieldF: (list val) -> itree Es val :=
      fun varg =>
        match varg with
        | [] => z <- trigger EventsL.Yield;; Ret Vundef
        | _ => triggerUB
        end.

    Definition getpidF: (list val) -> itree Es val :=
      fun varg =>
        match varg with
        | [] =>
            pid <- trigger EventsL.Getpid;;
            Ret (Vint (Int.repr (Z.of_nat pid)))
        | _ => triggerUB
        end.
    
    Definition thread_createF: list val -> itree Es val :=
      fun varg =>
        match varg with
        | [Vptr bid ofsid;Vptr bf ofsf;Vptr barg ofsarg] =>
            '(gsym, gdata) <- (nth_error sk (pred (Pos.to_nat bf)))?;;
            gd <- (gdata↓)?;;
            _ <- (match gd with Cgfun fd => Some fd | _ => None end)?;;
            `v_pid : val <- ccallU "spawn" (gsym, [Vptr barg ofsarg]);;
            `_ : unit <- ccallU "store" (Mint16signed, bid, ofsid, v_pid);;
            Ret (Vint Int.zero)
        | _ => triggerUB
        end.

  End BODY.



  Definition SchSem (sk : Sk.t) : ModSem.t :=
    {|
      ModSem.fnsems := [("spawn", cfunU spawnF) ; ("yield", cfunU yieldF); ("thread_yield", cfunU yieldF);
                        ("get_curid", cfunU getpidF); ("thread_create", cfunU (thread_createF sk))];
      ModSem.mn := "Sch";
      ModSem.initial_st := tt↑;
    |}
  .

  Definition Sch: Mod.t := {|
    Mod.get_modsem := SchSem;
    Mod.sk := [("thread_yield", (Cgfun (Tfunction Tnil tvoid cc_default))↑);
               ("get_curid", (Cgfun (Tfunction Tnil tint cc_default))↑);
               ("thread_create", (Cgfun (Tfunction
                                           (Tcons (tptr tint)
                                              (Tcons (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))
                                                 (Tcons (tptr tvoid) Tnil))) tint cc_default))↑)];
  |}
  .
End PROOF.
