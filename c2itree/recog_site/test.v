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

Require Import Clight_Mem0 Sys Sch0 network0 Main0.
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

Section TEST.

  Program Instance EMSConfigImp: EMSConfig :=
    {|
      finalize := fun rv => Some rv;  initial_arg := ([]: list val)↑;
    |}
  .

  (** module is classified with whether its memory and local state is shared between process **)
  (** memory directly corresponds to one process **)
  

  Definition local_sharing_modules : ModL.t := Mod.add_list [Sys;Sch(* ;Net *)].
  Definition erase_get_mod `{Sk.ld} (md: ModL.t): ModL.t := ModL.mk (fun _ => ModSemL.mk [] []) md.(ModL.sk).

  Definition shared_fun_list := List.map fst local_sharing_modules.(ModL.enclose).(ModSemL.fnsems).

  Definition execution_profile : list (string * list Mod.t) :=
    [("first", [amisc0.c_module;bmisc0.c_module]); ("second", [amisc0.c_module;bmisc0.c_module])].

  Definition proc_gen :=
    fun '(sn, modlist) =>
    (append_site_1 sn shared_fun_list
       (ModL.enclose (ModL.add (Mod.add_list (Mem::modlist)) (erase_get_mod local_sharing_modules)))).


  Definition test_modseml : ModSemL.t := List.fold_left ModSemL.add (List.map proc_gen execution_profile) (ModSemL.mk [] []).

  Definition pre_local := append_site_2 shared_fun_list local_sharing_modules.(ModL.enclose).

  Definition test_itr :=
    ModSemL.initial_itr (ModSemL.add MainSem (ModSemL.add pre_local test_modseml)) None.
End TEST.
