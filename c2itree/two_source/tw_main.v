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

Require Import Clight_Mem0 Sys Sch0.
Require Import ConvC2ITree.
Require Import parse_compcert.

Require Import src10 src20 tiny_main.
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
        (* `new_pid : Z <- (pargs [tint] [new_pid])?;; *)
        `new_pid : val <- ccallU "spawn" ("second.main", @nil val);;
        (* `new_pid : Z <- (pargs [tint] [new_pid])?;; *)
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

  Program Instance EMSConfig: EMSConfig :=
    {|
      finalize := fun rv => Some rv;  initial_arg := ([]: list val)↑;
    |}
  .
  
  Definition no_memory_modules : ModSemL.t := ModL.enclose (Mod.add_list [Main;Sch]).
  (* Definition shared_memory_modules : ModSemL.t := ModL.enclose (Mod.add_list [Main;Sch]). *)

  Definition shared_fun_list := List.map fst no_memory_modules.(ModSemL.fnsems).
  Definition shared_module_list := List.map fst no_memory_modules.(ModSemL.initial_mrs).

  (* Mem (pgm : Clight.program), c_module (globalenv : Genv.t fundef type) *)
  (* modules that uses memory call each site should be separated *)

  Definition site_first :=
    (ModSemL.append_site "first" shared_fun_list shared_module_list
       (ModL.enclose (Mod.add_list
                        ((Mem)::(Sys)::[src10.c_module;src20.c_module])))).
  Definition site_second :=
    (ModSemL.append_site "second" shared_fun_list shared_module_list
       (ModL.enclose (Mod.add_list
                        ((Mem)::(Sys)::[src10.c_module;src20.c_module])))).
  (* Definition site_second := *)
  (*   (ModSemL.append_site "second" shared_fun_list shared_module_list *)
  (*      (ModL.enclose (Mod.add_list *)
  (*                       ((Mem)::(Sys)::[tiny0.c_module])))). *)

  Definition test_modseml := ModSemL.add site_first site_second.
    
  Definition test_itr :=
    ModSemL.initial_itr
      (ModSemL.add no_memory_modules test_modseml) None.

End TEST.
