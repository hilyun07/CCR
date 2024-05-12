From compcert Require Import Ctypes Errors Compiler.

Require Import String.

Set Implicit Arguments.

Section ASMGEN.

  Definition transf_clight_program (p: Clight.program) : res Asm.program :=
    OK p
       @@@ transf_clight_program.

End ASMGEN.