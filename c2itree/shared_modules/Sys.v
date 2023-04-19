Require Import Ascii.
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

    Definition ptr_to_string: val -> itree Es string :=
        fun ptr => match ptr with
        | Vptr b ofs => ITree.iter (fun '(ofs, str) =>
            v <- ccallU "load" (Mint8signed, b, ofs);;
            match v with
            | Vint i => if Int.eq i Int.zero then Ret (inr (String.string_of_list_ascii str))
                else
                let c := Ascii.ascii_of_nat (Z.to_nat (Int.unsigned i)) in
                let ofs := Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (size_chunk_nat Mint8signed))) in
                Ret (inl (ofs, str ++ [c]))
            | _ => triggerUB
            end
            ) (ofs, [])
        | _ => triggerUB
        end.

    Definition digit_to_char (n: nat): ascii :=
        ascii_of_nat (n + 48).

    (* Maybe a better way than using fuel? *)
    Fixpoint nat_to_char_aux (n: nat) (fuel: nat): list ascii :=
        match fuel with
        | 0 => [Ascii.zero]
        | S fuel =>
            if (n <? 10)%nat then
                [digit_to_char n]
            else (nat_to_char_aux (n / 10) fuel) ++ nat_to_char_aux (n mod 10) fuel
        end.

    Definition nat_to_char (n: nat): list ascii :=
        nat_to_char_aux n (n + 1).

    Definition pos_to_char (p: positive): list ascii :=
        nat_to_char (Pos.to_nat p).

    Definition Z_to_char (z: Z): list ascii :=
        match z with
        | Z0 => ["0"%char]
        | Zneg p => "-"%char :: pos_to_char p
        | Zpos p => pos_to_char p
        end.

    Fixpoint format_replace_aux (l: list ascii) (args: list val): itree Es (list ascii) :=
        match l with
        | "%"%char :: "d"%char :: l => match args with
            | Vint i :: args =>
                l <- format_replace_aux l args;;
                Ret (Z_to_char (Int.signed i) ++ l)
            | _ => triggerUB
            end
        | "%"%char :: "u"%char :: l => match args with
            | Vint i :: args =>
                l <- format_replace_aux l args;;
                Ret (Z_to_char (Int.unsigned i) ++ l)
            | _ => triggerUB
            end
        | "%"%char :: "l"%char :: "d"%char :: l => match args with
            | Vlong i :: args =>
                l <- format_replace_aux l args;;
                Ret (Z_to_char (Int64.signed i) ++ l)
            | _ => triggerUB
            end
        | "%"%char :: "l"%char :: "u"%char :: l => match args with
            | Vlong i :: args =>
                l <- format_replace_aux l args;;
                Ret (Z_to_char (Int64.unsigned i) ++ l)
            | _ => triggerUB
            end
        | "%"%char :: "s"%char :: l => match args with
            | Vptr b ofs :: args =>
                str <- ptr_to_string (Vptr b ofs);;
                let str := String.list_ascii_of_string str in
                l <- format_replace_aux l args;;
                Ret (str ++ l)
            | _ => triggerUB
            end
        | c :: l =>
            l <- format_replace_aux l args;;
            Ret (c :: l)
        | [] => match args with
            | [] => Ret []
            | _ => triggerUB
            end
        end.

    Definition format_replace (str: string) (args: list val): itree Es string :=
        str <- format_replace_aux (String.list_ascii_of_string str) args;;
        Ret (String.string_of_list_ascii str).

    Program Definition dprintfF: list val -> itree Es val :=
        fun vargs => match vargs with
        | ptr :: args =>
            str <- ptr_to_string ptr;;
            str <- format_replace str args;;
            trigger (Syscall "print_string" [str]↑ top1);;;
            Ret Vundef
        | _ => triggerUB
        end.
  End BODY.

  Variable csl: gname -> bool.
  Variable pgm: Clight.program.

  Definition SysSem: ModSem.t :=
    {|
      ModSem.fnsems := [("puts", cfunU printF); ("dprintf0", cfunU dprintfF);
      ("dprintf1i", cfunU dprintfF); ("dprintf2si", cfunU dprintfF);
      ("dprintf2ii", cfunU dprintfF); ("dprintf3isi", cfunU dprintfF);
      ("dprintf3iii", cfunU dprintfF)];
      ModSem.mn := "Sys";
      ModSem.initial_st := tt↑;
    |}
  .

  Definition Sys: Mod.t := {|
    Mod.get_modsem := fun _ => SysSem;
    Mod.sk := [("puts", (Cgfun (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))↑);
               ("dprintf0", (Cgfun (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))↑); 
               ("dprintf1i", (Cgfun (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil)) tvoid cc_default))↑); 
               ("dprintf2si", (Cgfun (Tfunction (Tcons (tptr tvoid) (Tcons tshort (Tcons tint Tnil))) tvoid cc_default))↑); 
               ("dprintf2ii", (Cgfun (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tint Tnil))) tvoid cc_default))↑); 
               ("dprintf3iii", (Cgfun (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tint (Tcons tint Tnil)))) tvoid cc_default))↑); 
               ("dprintf3isi", (Cgfun (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tshort (Tcons tint Tnil)))) tvoid cc_default))↑)];
  |}
  .

End PROOF.

