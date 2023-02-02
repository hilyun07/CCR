Require Import Any.
Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import ConvC2ITree.

Require server client.


Module server0.

Import server.

Let src_name := get_source_name Info.source_file.
Definition prog := append_srcname prog src_name.
Definition c_module := get_mod prog src_name.

End server0.

Module client0.

Import client.

Let src_name := get_source_name Info.source_file.
Definition prog := append_srcname prog src_name.
Definition c_module := get_mod prog src_name.

End client0.
