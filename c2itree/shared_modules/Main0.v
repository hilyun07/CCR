Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import ModSem.

From compcert Require Import Values Integers.
                             
Set Implicit Arguments.



Definition mainF: list val -> itree Es val:=
  fun vargs =>
    trigger (EventsL.Spawn "first.main" (@nil val)↑);;;
      trigger (EventsL.Spawn "second.main" (@nil val)↑);;;
      Ret (Vint Int.zero).


Definition MainSem: ModSem.t :=
  {|
    ModSem.fnsems := [("main", cfunU mainF)];
    ModSem.mn := "Main";
    ModSem.initial_st := tt↑;
  |}
.

