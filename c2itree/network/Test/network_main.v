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

Require Import test0.
Import server0 client0.

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
        `new_pid : val <- ccallU "spawn" ("second.main", @nil val);;
        `new_pid : Z <- (pargs [tint] [new_pid])?;;
         _ <- trigger (Syscall "print_num" [new_pid]↑ top1);;
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


Require Import ModSemE.
Import EventsL.

Section SITE.
    
  Definition sname := string.
  Variable sn: sname.
  Variable shared_fun_list: list gname.

  Let is_shared_fun fn := in_dec string_dec fn shared_fun_list.
  

  Definition site_append_morph : Es ~> Es.
  Proof.
    intros. destruct X.
    { destruct c.
      assert (new_mn: option mname) by now destruct mn; [apply (Some (sn ++ "." ++ s)%string) | apply None].
      assert (new_fn: gname) by now destruct (is_shared_fun fn); [apply fn | apply (sn ++ "." ++ fn)%string]. 
      exact (inl1 (Call new_mn new_fn args)). }
    destruct s.
    { destruct s.
      { destruct (is_shared_fun fn).
        - exact (inr1 (inl1 (Spawn fn args))).
        - exact (inr1 (inl1 (Spawn (sn ++ "." ++ fn) args))). }
      exact (inr1 (inl1 Yield)).
      exact (inr1 (inl1 Getpid)). }
    destruct s.
    { destruct p.
      - exact (inr1 (inr1 (inl1 (PPut (sn ++ "." ++ mn) p)))).
      - exact (inr1 (inr1 (inl1 (PGet (sn ++ "." ++ mn))))). }
    { destruct e.
      exact (inr1 (inr1 (inr1 (Choose X)))).
      exact (inr1 (inr1 (inr1 (Take X)))).
      exact (inr1 (inr1 (inr1 (Syscall fn args rvs)))). }
  Defined.
    

  Definition site_appended_itree : itree Es ~> itree Es := translate site_append_morph.

  Definition append_site (ms: ModSemL.t) : ModSemL.t :=
    {|
      ModSemL.fnsems := List.map (fun '(gn, fnsem) =>
                       ((sn ++ "." ++ gn)%string, fun x => site_appended_itree (fnsem x))) ms.(ModSemL.fnsems);
      ModSemL.initial_mrs := List.map (map_fst (fun mn => (sn ++ "." ++ mn)%string)) ms.(ModSemL.initial_mrs);
    |}
  .

End SITE.

Section TEST.

  Program Instance EMSConfigImp: EMSConfig :=
    {|
      finalize := fun rv => Some rv;  initial_arg := ([]: list val)↑;
    |}
  .

  (** module is classified with whether its memory and local state is shared between process **)
  (** memory directly corresponds to one process **)
  
  Definition local_sharing_modules : ModL.t := Mod.add_list [Main;Sch;Net].
  Definition erase_get_mod `{Sk.ld} (md: ModL.t): ModL.t := ModL.mk (fun _ => ModSemL.mk [] []) md.(ModL.sk).

  Definition shared_fun_list := List.map fst local_sharing_modules.(ModL.enclose).(ModSemL.fnsems).

  (* Mem (pgm : Clight.program), c_module (globalenv : Genv.t fundef type) *)
  (* modules that uses memory call each site should be separated *)

  Definition execution_profile : list (string * list Mod.t) := [("first", [server0.c_module]);("second", [client0.c_module])].

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
