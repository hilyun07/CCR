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
     Ctypes Clight.
                                            
Set Implicit Arguments.

Section PROOF.

  Section BODY.

    Definition printF: list val -> itree Es val:=
      fun vargs  =>                (* array ptr, number *)
        match vargs with
        | [] => triggerUB
        | msgptr :: nums =>
            match msgptr with
            | Vptr b ofs =>
                _ <- ITree.iter
                      (fun '(ofs, nums) =>
                         v <- ccallU "load" (Mint8signed, b, ofs);;
                         match v with
                         | Vint i =>
                             if Int.eq i Int.zero then Ret (inr Vundef) (* null is end of string *)
                             else
                               if Int.eq i (Int.repr 37%Z)
                               then
                                 match hd_error nums with
                                 | Some (Vint i') =>
                                     _ <- trigger (Syscall "print_num" [Int.intval i]↑ top1);;
                                     Ret (inl ((ofs + 2 * Z.of_nat (size_chunk_nat Mint8signed))%Z, tl nums))
                                 | _ => triggerUB
                                 end
                               else _ <- trigger (Syscall "print_ascii" [Int.intval i]↑ top1);;
                                    Ret (inl ((ofs + Z.of_nat (size_chunk_nat Mint8signed))%Z, tl nums))
                         | _ => triggerUB
                         end
                      ) (Ptrofs.intval ofs, nums);;
                _ <- trigger (Syscall "print_newline" (@nil unit)↑ top1);; Ret (Vundef)
            | _ => triggerUB
            end
        end.
    
  End BODY.

  Variable csl: gname -> bool.
  Variable pgm: Clight.program.
  
  Definition SysSem: ModSem.t :=
    {|
      ModSem.fnsems := [("puts", cfunU printF)];
      ModSem.mn := "Sys";
      ModSem.initial_st := tt↑;
    |}
  .

  Definition Sys: Mod.t := {|
    Mod.get_modsem := fun _ => SysSem;
    Mod.sk := Sk.unit ;
  |}
  .
  
End PROOF.

