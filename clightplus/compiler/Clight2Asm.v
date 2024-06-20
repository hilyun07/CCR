From compcert Require Import Ctypes Errors Compiler.

Require Import String.

Set Implicit Arguments.

Section ASMGEN.

  Definition transf_clight_program (p: Clight.program) : res Asm.program :=
    OK p
    @@ print print_Clight
    @@@ time "C#minor generation" Cshmgen.transl_program
    @@@ time "Cminor generation" Cminorgen.transl_program
    @@@ transf_cminor_program.

End ASMGEN.