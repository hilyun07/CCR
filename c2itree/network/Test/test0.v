Require Import Any.
Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import ConvC2ITree.
From compcert Require Import AST Ctypes Clight Clightdefs Integers.

Require server client.


Module server0.

Import server.

Let src_name := get_source_name Info.source_file.
Definition prog := append_srcname prog src_name.
Compute rpl_body prog src_name (Scall (Some _t'1)
        (Evar _socket (Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil)))
                        tint cc_default))
        ((Econst_int (Int.repr 2) tint) :: (Econst_int (Int.repr 1) tint) ::
         (Econst_int (Int.repr 0) tint) :: nil)).

Compute string_of_ident 72572125994398620%positive.

Definition c_module := get_mod prog src_name.

End server0.

Module client0.

Import client.

Let src_name := get_source_name Info.source_file.
Definition prog := append_srcname prog src_name.
Definition c_module := get_mod prog src_name.

End client0.
