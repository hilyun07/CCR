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

Definition ___assert_fail : ident := $"__assert_fail".
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
Definition ___func__ : ident := $"__func__".
Definition ___func____1 : ident := $"__func____1".
Definition ___func____2 : ident := $"__func____2".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition _capacity : ident := $"capacity".
Definition _free : ident := $"free".
Definition _i : ident := $"i".
Definition _index : ident := $"index".
Definition _item : ident := $"item".
Definition _item_size : ident := $"item_size".
Definition _items : ident := $"items".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _memcpy : ident := $"memcpy".
Definition _pre_ptr : ident := $"pre_ptr".
Definition _ptr : ident := $"ptr".
Definition _realloc : ident := $"realloc".
Definition _sub_ptr : ident := $"sub_ptr".
Definition _total : ident := $"total".
Definition _v : ident := $"v".
Definition _vector : ident := $"vector".
Definition _vector_add : ident := $"vector_add".
Definition _vector_delete : ident := $"vector_delete".
Definition _vector_free : ident := $"vector_free".
Definition _vector_get : ident := $"vector_get".
Definition _vector_init : ident := $"vector_init".
Definition _vector_resize : ident := $"vector_resize".
Definition _vector_set : ident := $"vector_set".
Definition _vector_total : ident := $"vector_total".
Definition _t'1 : ident := 128%positive.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 40);
  gvar_init := (Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_vector_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) ::
                (_item_size, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
        (Tstruct _vector noattr)) _capacity tulong)
    (Econst_int (Int.repr 4) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
          (Tstruct _vector noattr)) _total tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                          cc_default))
          ((Ebinop Omul (Etempvar _item_size tulong)
             (Efield
               (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                 (Tstruct _vector noattr)) _capacity tulong) tulong) :: nil))
        (Sassign
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _items (tptr tvoid))
          (Etempvar _t'1 (tptr tvoid))))
      (Sassign
        (Efield
          (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
            (Tstruct _vector noattr)) _item_size tulong)
        (Etempvar _item_size tulong)))))
|}.

Definition f_vector_total := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                   (Tstruct _vector noattr)) _total tulong)))
|}.

Definition f_vector_resize := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) ::
                (_capacity, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_items, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _capacity tulong)
                 (Efield
                   (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                     (Tstruct _vector noattr)) _total tulong) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _realloc (Tfunction (Tcons (tptr tvoid) (Tcons tulong Tnil))
                         (tptr tvoid) cc_default))
        ((Efield
           (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
             (Tstruct _vector noattr)) _items (tptr tvoid)) ::
         (Ebinop Omul
           (Efield
             (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
               (Tstruct _vector noattr)) _item_size tulong)
           (Etempvar _capacity tulong) tulong) :: nil))
      (Sset _items (Etempvar _t'1 (tptr tvoid))))
    (Sifthenelse (Etempvar _items (tptr tvoid))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _items (tptr tvoid))
          (Etempvar _items (tptr tvoid)))
        (Sassign
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _capacity tulong)
          (Etempvar _capacity tulong)))
      Sskip)))
|}.

Definition f_vector_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) ::
                (_item, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_ptr, (tptr tvoid)) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Efield
                   (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                     (Tstruct _vector noattr)) _capacity tulong)
                 (Efield
                   (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                     (Tstruct _vector noattr)) _total tulong) tint)
    (Scall None
      (Evar _vector_resize (Tfunction
                             (Tcons (tptr (Tstruct _vector noattr))
                               (Tcons tulong Tnil)) tvoid cc_default))
      ((Etempvar _v (tptr (Tstruct _vector noattr))) ::
       (Ebinop Omul
         (Efield
           (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
             (Tstruct _vector noattr)) _capacity tulong)
         (Econst_int (Int.repr 2) tint) tulong) :: nil))
    Sskip)
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _total tulong))
        (Sassign
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _total tulong)
          (Ebinop Oadd (Etempvar _t'1 tulong) (Econst_int (Int.repr 1) tint)
            tulong)))
      (Sset _ptr
        (Ebinop Oadd
          (Ecast
            (Efield
              (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                (Tstruct _vector noattr)) _items (tptr tvoid)) (tptr tschar))
          (Ebinop Omul (Etempvar _t'1 tulong)
            (Efield
              (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                (Tstruct _vector noattr)) _item_size tulong) tulong)
          (tptr tschar))))
    (Scall None
      (Evar _memcpy (Tfunction
                      (Tcons (tptr tvoid)
                        (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                      (tptr tvoid) cc_default))
      ((Etempvar _ptr (tptr tvoid)) :: (Etempvar _item (tptr tvoid)) ::
       (Efield
         (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
           (Tstruct _vector noattr)) _item_size tulong) :: nil))))
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_vector_set := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: (_index, tulong) ::
                (_item, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_ptr, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _index tulong)
                 (Efield
                   (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                     (Tstruct _vector noattr)) _total tulong) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_2 (tarray tschar 17)) ::
       (Evar ___stringlit_1 (tarray tschar 40)) ::
       (Econst_int (Int.repr 29) tint) ::
       (Evar ___func__ (tarray tschar 11)) :: nil)))
  (Ssequence
    (Sset _ptr
      (Ebinop Oadd
        (Ecast
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _items (tptr tvoid)) (tptr tschar))
        (Ebinop Omul (Etempvar _index tulong)
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _item_size tulong) tulong)
        (tptr tschar)))
    (Scall None
      (Evar _memcpy (Tfunction
                      (Tcons (tptr tvoid)
                        (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                      (tptr tvoid) cc_default))
      ((Etempvar _ptr (tptr tvoid)) :: (Etempvar _item (tptr tvoid)) ::
       (Efield
         (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
           (Tstruct _vector noattr)) _item_size tulong) :: nil))))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_vector_get := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: (_index, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_ptr, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _index tulong)
                 (Efield
                   (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                     (Tstruct _vector noattr)) _total tulong) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_2 (tarray tschar 17)) ::
       (Evar ___stringlit_1 (tarray tschar 40)) ::
       (Econst_int (Int.repr 36) tint) ::
       (Evar ___func____1 (tarray tschar 11)) :: nil)))
  (Ssequence
    (Sset _ptr
      (Ebinop Oadd
        (Ecast
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _items (tptr tvoid)) (tptr tschar))
        (Ebinop Omul (Etempvar _index tulong)
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _item_size tulong) tulong)
        (tptr tschar)))
    (Sreturn (Some (Etempvar _ptr (tptr tvoid))))))
|}.

Definition v___func____2 := {|
  gvar_info := (tarray tschar 14);
  gvar_init := (Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_vector_delete := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: (_index, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_pre_ptr, (tptr tvoid)) ::
               (_sub_ptr, (tptr tvoid)) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _index tulong)
                 (Efield
                   (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                     (Tstruct _vector noattr)) _total tulong) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_2 (tarray tschar 17)) ::
       (Evar ___stringlit_1 (tarray tschar 40)) ::
       (Econst_int (Int.repr 43) tint) ::
       (Evar ___func____2 (tarray tschar 14)) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                         (Ebinop Osub
                           (Efield
                             (Ederef
                               (Etempvar _v (tptr (Tstruct _vector noattr)))
                               (Tstruct _vector noattr)) _total tulong)
                           (Econst_int (Int.repr 1) tint) tulong) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _pre_ptr
              (Ebinop Oadd
                (Ecast
                  (Efield
                    (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                      (Tstruct _vector noattr)) _items (tptr tvoid))
                  (tptr tschar))
                (Ebinop Omul (Etempvar _i tulong)
                  (Efield
                    (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                      (Tstruct _vector noattr)) _item_size tulong) tulong)
                (tptr tschar)))
            (Ssequence
              (Sset _sub_ptr
                (Ebinop Oadd
                  (Ecast
                    (Efield
                      (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                        (Tstruct _vector noattr)) _items (tptr tvoid))
                    (tptr tschar))
                  (Ebinop Omul
                    (Ebinop Oadd (Etempvar _i tulong)
                      (Econst_int (Int.repr 1) tint) tulong)
                    (Efield
                      (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                        (Tstruct _vector noattr)) _item_size tulong) tulong)
                  (tptr tschar)))
              (Ssequence
                (Scall None
                  (Evar _memcpy (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                                  (tptr tvoid) cc_default))
                  ((Etempvar _pre_ptr (tptr tvoid)) ::
                   (Etempvar _sub_ptr (tptr tvoid)) ::
                   (Efield
                     (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                       (Tstruct _vector noattr)) _item_size tulong) :: nil))
                (Sset _sub_ptr
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
            tulong))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
            (Tstruct _vector noattr)) _total tulong)
        (Ebinop Osub
          (Efield
            (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
              (Tstruct _vector noattr)) _total tulong)
          (Econst_int (Int.repr 1) tint) tulong))
      (Ssequence
        (Sifthenelse (Ebinop Ogt
                       (Efield
                         (Ederef
                           (Etempvar _v (tptr (Tstruct _vector noattr)))
                           (Tstruct _vector noattr)) _total tulong)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sset _t'1
            (Ecast
              (Ebinop Oeq
                (Efield
                  (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                    (Tstruct _vector noattr)) _total tulong)
                (Ebinop Odiv
                  (Efield
                    (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                      (Tstruct _vector noattr)) _capacity tulong)
                  (Econst_int (Int.repr 4) tint) tulong) tint) tbool))
          (Sset _t'1 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'1 tint)
          (Scall None
            (Evar _vector_resize (Tfunction
                                   (Tcons (tptr (Tstruct _vector noattr))
                                     (Tcons tulong Tnil)) tvoid cc_default))
            ((Etempvar _v (tptr (Tstruct _vector noattr))) ::
             (Ebinop Odiv
               (Efield
                 (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                   (Tstruct _vector noattr)) _capacity tulong)
               (Econst_int (Int.repr 2) tint) tulong) :: nil))
          Sskip)))))
|}.

Definition f_vector_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct _vector noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Efield
                   (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
                     (Tstruct _vector noattr)) _items (tptr tvoid))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _v (tptr (Tstruct _vector noattr)))
         (Tstruct _vector noattr)) _items (tptr tvoid)) :: nil)))
|}.

Definition composites : list composite_definition :=
(Composite _vector Struct
   ((_items, (tptr tvoid)) :: (_item_size, tulong) :: (_capacity, tulong) ::
    (_total, tulong) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_ais_annot,
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
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) ::
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
 (_vector_total, Gfun(Internal f_vector_total)) ::
 (_vector_resize, Gfun(Internal f_vector_resize)) ::
 (_vector_add, Gfun(Internal f_vector_add)) ::
 (___func__, Gvar v___func__) ::
 (_vector_set, Gfun(Internal f_vector_set)) ::
 (___func____1, Gvar v___func____1) ::
 (_vector_get, Gfun(Internal f_vector_get)) ::
 (___func____2, Gvar v___func____2) ::
 (_vector_delete, Gfun(Internal f_vector_delete)) ::
 (_vector_free, Gfun(Internal f_vector_free)) :: nil).

Definition public_idents : list ident :=
(_vector_free :: _vector_delete :: _vector_get :: _vector_set ::
 _vector_add :: _vector_total :: _vector_init :: _memcpy :: _free ::
 _realloc :: _malloc :: ___assert_fail :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___builtin_expect :: ___builtin_unreachable :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


