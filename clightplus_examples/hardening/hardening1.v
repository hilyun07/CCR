Require Import CoqlibCCR.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import Any.
Require Import ModSem.
Require Import ModSemE.
Require Import ClightPlusMemRA.
Require Import ClightPlusMem1.
From compcert Require Export Ctypes Values AST Memdata Integers.

Set Implicit Arguments.

Section PROP.

  Context `{@GRA.inG Mem.t Σ}.

  (* Definition swab_func (v: val) : val := *)
  (*   match v with *)
  (*   | Vlong n => if Archi.ptr64 then Vlong n else Vundef *)
  (*   | Vint n => if negb Archi.ptr64 then Vint n else Vundef *)
  (*   | _ => Vundef *)
  (*   end. *)

End PROP.

Section SPEC.

  Context `{@GRA.inG Mem.t Σ}.

  (* uintptr_t encode(uintptr_t key, void *ptr) { *)
  (*   uintptr_t encoded; *)
  (*   encoded = (uintptr_t)ptr ^ key; *)
  (*   return encoded; *)
  (* } *)

  Definition encode_spec : fspec :=
    (mk_simple
      (fun '(key, ptr, ofs, m_ptr, tg, q) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [Vlong key; ptr]↑⌝
                     ** live_(m_ptr,tg,q) (Val.subl ptr (Vptrofs ofs))),
        (fun vret => ∃ iptr, ⌜vret = (Val.xorl iptr (Vlong key))↑⌝
                     ** live_(m_ptr,tg,q) (Val.subl ptr (Vptrofs ofs)) ** ptr (≃_ m_ptr) iptr)
    )))%I.

  (* void *decode(uintptr_t key, uintptr_t ptr) { *)
  (*   void *decoded; *)
  (*   decoded = (void *\) (ptr ^ key); *)
  (*   return decoded; *)
  (* } *)
  
  Definition decode_spec : fspec :=
    (mk_simple
      (fun '(key, ptr) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [Vlong key; (Vlong ptr)]↑⌝),
        (fun vret => ⌜vret = (Val.xorl (Vlong ptr) (Vlong key))↑⌝)
    )))%I.

  (* sealed *)
  Definition hardeningStb : list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [
           ("encode", encode_spec);
           ("decode", decode_spec)
           (* ; *)
           (* ("delete_hd", delete_hd_spec); *)
           (* ("delete_tl", delete_tl_spec) *)
           (* ("search", search_spec) *)
           ].
  Defined.

End SPEC.

Section SMOD.

  Context `{@GRA.inG Mem.t Σ}.

  Definition hardeningSbtb: list (gname * fspecbody) :=
    [
     ("encode", mk_pure encode_spec);
     ("decode", mk_pure decode_spec)
     (* ; *)
     (* ("delete_hd", mk_pure delete_hd_spec); *)
     (* ("delete_tl", mk_pure delete_tl_spec) *)
     ].

End SMOD.
