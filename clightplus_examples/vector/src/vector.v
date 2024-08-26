From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "clightplus_examples/vector/src/vector.c".
  Definition normalized := false.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___compound : ident := $"__compound".
Definition _capacity : ident := $"capacity".
Definition _data : ident := $"data".
Definition _dst : ident := $"dst".
Definition _esize : ident := $"esize".
Definition _free : ident := $"free".
Definition _i : ident := $"i".
Definition _index : ident := $"index".
Definition _length : ident := $"length".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _memcpy : ident := $"memcpy".
Definition _min_capacity : ident := $"min_capacity".
Definition _realloc : ident := $"realloc".
Definition _src : ident := $"src".
Definition _v : ident := $"v".
Definition _vector : ident := $"vector".
Definition _vector_capacity : ident := $"vector_capacity".
Definition _vector_destruct : ident := $"vector_destruct".
Definition _vector_esize : ident := $"vector_esize".
Definition _vector_get : ident := $"vector_get".
Definition _vector_init : ident := $"vector_init".
Definition _vector_length : ident := $"vector_length".
Definition _vector_push : ident := $"vector_push".
Definition _vector_remove : ident := $"vector_remove".
Definition _vector_reserve : ident := $"vector_reserve".
Definition _vector_set : ident := $"vector_set".
Definition _t'1 : ident := 128%positive.

Definition f_vector_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: (_esize, tulong) ::
                (_capacity, tulong) :: nil);
  fn_vars := ((___compound, (Tstruct _vector noattr)) :: nil);
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                            cc_default))
            ((Ebinop Omul (Etempvar _esize tulong)
               (Etempvar _capacity tulong) tulong) :: nil))
          (Sassign
            (Efield (Evar ___compound (Tstruct _vector noattr)) _data
              (tptr tvoid)) (Etempvar _t'1 (tptr tvoid))))
        (Sassign
          (Efield (Evar ___compound (Tstruct _vector noattr)) _esize tulong)
          (Etempvar _esize tulong)))
      (Sassign
        (Efield (Evar ___compound (Tstruct _vector noattr)) _capacity tulong)
        (Etempvar _capacity tulong)))
    (Sassign
      (Efield (Evar ___compound (Tstruct _vector noattr)) _length tulong)
      (Econst_int (Int.repr 0) tint)))
  (Sassign
    (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
      (Tstruct _vector noattr)) (Evar ___compound (Tstruct _vector noattr))))
|}.

Definition f_vector_destruct := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
         (Tstruct _vector noattr)) _data (tptr tvoid)) :: nil))
  (Sassign
    (Efield
      (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
        (Tstruct _vector noattr)) _data (tptr tvoid))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
|}.

Definition f_vector_esize := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                   (Tstruct _vector noattr)) _esize tulong)))
|}.

Definition f_vector_capacity := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                   (Tstruct _vector noattr)) _capacity tulong)))
|}.

Definition f_vector_length := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                   (Tstruct _vector noattr)) _length tulong)))
|}.

Definition f_vector_reserve := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) ::
                (_min_capacity, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _min_capacity tulong)
                 (Efield
                   (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                     (Tstruct _vector noattr)) _capacity tulong) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _realloc (Tfunction (Tcons (tptr tvoid) (Tcons tulong Tnil))
                         (tptr tvoid) cc_default))
        ((Efield
           (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
             (Tstruct _vector noattr)) _data (tptr tvoid)) ::
         (Ebinop Omul
           (Efield
             (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
               (Tstruct _vector noattr)) _esize tulong)
           (Etempvar _min_capacity tulong) tulong) :: nil))
      (Sassign
        (Efield
          (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
            (Tstruct _vector noattr)) _data (tptr tvoid))
        (Etempvar _t'1 (tptr tvoid))))
    (Sassign
      (Efield
        (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
          (Tstruct _vector noattr)) _capacity tulong)
      (Etempvar _min_capacity tulong))))
|}.

Definition f_vector_push := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) ::
                (_src, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_dst, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Efield
                   (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                     (Tstruct _vector noattr)) _length tulong)
                 (Efield
                   (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                     (Tstruct _vector noattr)) _capacity tulong) tint)
    (Scall None
      (Evar _vector_reserve (Tfunction
                              (Tcons (tptr (Tstruct _vector noattr))
                                (Tcons tulong Tnil)) tvoid cc_default))
      ((Etempvar _v (tptr (Tstruct _vector noattr))) ::
       (Ebinop Omul (Econst_int (Int.repr 2) tint)
         (Efield
           (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
             (Tstruct _vector noattr)) _capacity tulong) tulong) :: nil))
    Sskip)
  (Ssequence
    (Sset _dst
      (Ecast
        (Ebinop Oadd
          (Ecast
            (Efield
              (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                (Tstruct _vector noattr)) _data (tptr tvoid)) (tptr tschar))
          (Ebinop Omul
            (Efield
              (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                (Tstruct _vector noattr)) _esize tulong)
            (Efield
              (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                (Tstruct _vector noattr)) _length tulong) tulong)
          (tptr tschar)) (tptr tvoid)))
    (Ssequence
      (Scall None
        (Evar _memcpy (Tfunction
                        (Tcons (tptr tvoid)
                          (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                        (tptr tvoid) cc_default))
        ((Etempvar _dst (tptr tvoid)) :: (Etempvar _src (tptr tvoid)) ::
         (Efield
           (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
             (Tstruct _vector noattr)) _esize tulong) :: nil))
      (Sassign
        (Efield
          (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
            (Tstruct _vector noattr)) _length tulong)
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _length tulong)
          (Econst_int (Int.repr 1) tint) tulong)))))
|}.

Definition f_vector_get := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: (_index, tulong) ::
                (_dst, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_src, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _src
    (Ecast
      (Ebinop Oadd
        (Ecast
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _data (tptr tvoid)) (tptr tschar))
        (Ebinop Omul
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _esize tulong)
          (Etempvar _index tulong) tulong) (tptr tschar)) (tptr tvoid)))
  (Scall None
    (Evar _memcpy (Tfunction
                    (Tcons (tptr tvoid)
                      (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid)
                    cc_default))
    ((Etempvar _dst (tptr tvoid)) :: (Etempvar _src (tptr tvoid)) ::
     (Efield
       (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
         (Tstruct _vector noattr)) _esize tulong) :: nil)))
|}.

Definition f_vector_set := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: (_index, tulong) ::
                (_src, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_dst, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _dst
    (Ecast
      (Ebinop Oadd
        (Ecast
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _data (tptr tvoid)) (tptr tschar))
        (Ebinop Omul
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _esize tulong)
          (Etempvar _index tulong) tulong) (tptr tschar)) (tptr tvoid)))
  (Scall None
    (Evar _memcpy (Tfunction
                    (Tcons (tptr tvoid)
                      (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid)
                    cc_default))
    ((Etempvar _dst (tptr tvoid)) :: (Etempvar _src (tptr tvoid)) ::
     (Efield
       (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
         (Tstruct _vector noattr)) _esize tulong) :: nil)))
|}.

Definition f_vector_remove := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: (_index, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_dst, (tptr tvoid)) ::
               (_src, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i
      (Ebinop Oadd (Etempvar _index tulong) (Econst_int (Int.repr 1) tint)
        tulong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                       (Efield
                         (Ederef
                           (Etempvar _v (tptr (Tstruct _vector noattr)))
                           (Tstruct _vector noattr)) _length tulong) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _dst
            (Ecast
              (Ebinop Oadd
                (Ecast
                  (Efield
                    (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                      (Tstruct _vector noattr)) _data (tptr tvoid))
                  (tptr tschar))
                (Ebinop Omul
                  (Efield
                    (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                      (Tstruct _vector noattr)) _esize tulong)
                  (Ebinop Osub (Etempvar _i tulong)
                    (Econst_int (Int.repr 1) tint) tulong) tulong)
                (tptr tschar)) (tptr tvoid)))
          (Ssequence
            (Sset _src
              (Ecast
                (Ebinop Oadd
                  (Ecast
                    (Efield
                      (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                        (Tstruct _vector noattr)) _data (tptr tvoid))
                    (tptr tschar))
                  (Ebinop Omul
                    (Efield
                      (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                        (Tstruct _vector noattr)) _esize tulong)
                    (Etempvar _i tulong) tulong) (tptr tschar)) (tptr tvoid)))
            (Scall None
              (Evar _memcpy (Tfunction
                              (Tcons (tptr tvoid)
                                (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                              (tptr tvoid) cc_default))
              ((Etempvar _dst (tptr tvoid)) ::
               (Etempvar _src (tptr tvoid)) ::
               (Efield
                 (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                   (Tstruct _vector noattr)) _esize tulong) :: nil)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Sassign
    (Efield
      (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
        (Tstruct _vector noattr)) _length tulong)
    (Ebinop Osub
      (Efield
        (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
          (Tstruct _vector noattr)) _length tulong)
      (Econst_int (Int.repr 1) tint) tulong)))
|}.

Definition composites : list composite_definition :=
(Composite _vector Struct
   ((_data, (tptr tvoid)) :: (_esize, tulong) :: (_capacity, tulong) ::
    (_length, tulong) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_realloc,
   Gfun(External (EF_external "realloc"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil)))
     (tptr tvoid) cc_default)) ::
 (_vector_init, Gfun(Internal f_vector_init)) ::
 (_vector_destruct, Gfun(Internal f_vector_destruct)) ::
 (_vector_esize, Gfun(Internal f_vector_esize)) ::
 (_vector_capacity, Gfun(Internal f_vector_capacity)) ::
 (_vector_length, Gfun(Internal f_vector_length)) ::
 (_vector_reserve, Gfun(Internal f_vector_reserve)) ::
 (_vector_push, Gfun(Internal f_vector_push)) ::
 (_vector_get, Gfun(Internal f_vector_get)) ::
 (_vector_set, Gfun(Internal f_vector_set)) ::
 (_vector_remove, Gfun(Internal f_vector_remove)) :: nil).

Definition public_idents : list ident :=
(_vector_remove :: _vector_set :: _vector_get :: _vector_push ::
 _vector_reserve :: _vector_length :: _vector_capacity :: _vector_esize ::
 _vector_destruct :: _vector_init :: _memcpy :: _free :: _realloc ::
 _malloc :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___builtin_expect :: ___builtin_unreachable ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


