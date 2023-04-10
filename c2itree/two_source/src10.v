Require Import Any.
Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import ConvC2ITree.

Require Import src1.

Let src_name := get_source_name Info.source_file.
Definition lgdef := trans_global_defs global_definitions public_idents src_name global_definitions.
Definition c_module := get_mod composites lgdef Logic.I src_name.
