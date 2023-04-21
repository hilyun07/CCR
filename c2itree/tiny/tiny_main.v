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

Require Import Clight_Mem0 Sys Sch0 Main0.
Require Import parse_compcert.
Require Import ConvC2ITree.

Require Import tiny0.

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
  
  (* basic component *)
  (* ----------------------------------------------------------------------------------- *)

  Definition shared_module : ModL.t := Mod.add_list [Sys;Sch(* ;Net *)].

  Definition execution_profile : list (string * list Mod.t) :=
    [("first", [tiny0.c_module]);("second", [tiny0.c_module])].

  (* ----------------------------------------------------------------------------------- *)
    
  Definition test_itr :=
    ModSemL.initial_itr (ModSemL.add MainSem (ModSemL.add (view_shared_module execution_profile shared_module) (sum_of_site_modules_view Mem execution_profile shared_module))) None.

End TEST.
