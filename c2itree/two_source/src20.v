Require Import Any.
Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import ConvC2ITree.

Require Import src2.


Let src_name := get_source_name Info.source_file.
Definition prog := append_srcname prog src_name.
Definition c_module ge := get_mod prog ge src_name.
