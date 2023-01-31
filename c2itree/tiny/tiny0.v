Require Import Any.
Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import ConvC2ITree.

Require Import tiny.


Let src_name := get_source_name Info.source_file.
Definition prog := append_srcname prog src_name.
Definition c_module := get_mod prog src_name.
