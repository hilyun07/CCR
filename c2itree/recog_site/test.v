Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.

From compcert Require Import
     AST Maps Globalenvs Memory Values Linking Integers.
From compcert Require Import
  Ctypes Clight Ctypesdefs.

Require Import Clight_Mem0 Sys Sch0 network0.
Require Import parse_compcert.
Require Import ConvC2ITree.

Require Import recog_mod.
Import amisc0 bmisc0.

(** common type in c has followings:
    tvoid
    tschar
    tuchar
    tshort
    tushort
    tint
    tuint
    tbool
    tlong
    tulong
    tfloat
    tdouble
    tptr (ty : type) 
    tarray (ty : type) (size : Z)
    .... and some type attribute replacing operations **)

                                            
Set Implicit Arguments.

Section PROOF.

  Section BODY.

    Definition mainF: list val -> itree Es val:=
      fun vargs =>
        `new_pid : val <- ccallU "spawn" ("first.main", @nil val);; 
        `new_pid : Z <- (pargs [tint] [new_pid])?;;
         _ <- trigger (Syscall "print_num" [new_pid]↑ top1);;
        (* `new_pid : val <- ccallU "spawn" ("second.main", @nil val);; *)
        (* `new_pid : Z <- (pargs [tint] [new_pid])?;; *)
        (*  _ <- trigger (Syscall "print_num" [new_pid]↑ top1);; *)
         Ret (Vint Int.zero).
    
  End BODY.
  
  Definition MainSem: ModSem.t :=
    {|
      ModSem.fnsems := [("main", cfunU mainF)];
      ModSem.mn := "Main";
      ModSem.initial_st := tt↑;
    |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := cskel.(Sk.unit);
  |}
  .
  
End PROOF.

Section TEST.

  Program Instance EMSConfigImp: EMSConfig :=
    {|
      finalize := fun rv => Some rv;  initial_arg := ([]: list val)↑;
    |}
  .

  (** module is classified with whether its memory and local state is shared between process **)
  (** memory directly corresponds to one process **)
  
  Definition local_sharing_modules : ModL.t := Mod.add_list [Main;Sch(* ;Net *)].
  Definition erase_get_mod `{Sk.ld} (md: ModL.t): ModL.t := ModL.mk (fun _ => ModSemL.mk [] []) md.(ModL.sk).

  Definition shared_fun_list := List.map fst local_sharing_modules.(ModL.enclose).(ModSemL.fnsems).

  (* Mem (pgm : Clight.program), c_module (globalenv : Genv.t fundef type) *)
  (* modules that uses memory call each site should be separated *)

  Definition execution_profile : list (string * list Mod.t) := [("first", [amisc0.c_module;bmisc0.c_module])(* ;("second", [client0.c_module]) *)].

  Definition proc_gen :=
    fun '(sn, modlist) =>
    (append_site sn shared_fun_list
       (ModL.enclose (ModL.add (Mod.add_list (Mem::Sys::modlist)) (erase_get_mod local_sharing_modules)))).

  (* Definition site_first := *)
  (*   (ModSemL.append_site "first" shared_fun_list shared_module_list *)
  (*      (ModL.enclose (Mod.add_list *)
  (*                       (Mem::Sys::[tiny0.c_module])))). *)

  (* Definition site_second := *)
  (*   (ModSemL.append_site "second" shared_fun_list shared_module_list *)
  (*      (ModL.enclose (Mod.add_list *)
  (*                       ((Mem)::(Sys)::[tiny0.c_module])))). *)

  Definition test_modseml : ModSemL.t := List.fold_left ModSemL.add (List.map proc_gen execution_profile) (ModSemL.mk [] []).
    
  Definition test_itr :=
    ModSemL.initial_itr
      (ModSemL.add local_sharing_modules.(ModL.enclose) test_modseml) None.

End TEST.
