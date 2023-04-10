Require Import Any.
Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import ConvC2ITree.
From compcert Require Import AST Ctypes Clight Clightdefs Integers.

Require amisc bmisc.


Module amisc0.

Import amisc.

Let src_name := get_source_name Info.source_file.
Definition lgdef := trans_global_defs global_definitions public_idents src_name global_definitions.
Definition c_module := get_mod composites lgdef Logic.I src_name.

End amisc0. 

Module bmisc0.

Import bmisc.

Let src_name := get_source_name Info.source_file.
Definition lgdef := trans_global_defs global_definitions public_idents src_name global_definitions.
Definition c_module := get_mod composites lgdef Logic.I src_name.

End bmisc0.
