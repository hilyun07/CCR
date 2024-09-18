Require Import CoqlibCCR.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import SimModSem.
Require Import PCM.
Require Import HoareDef.
Require Import STB.
Require Import HTactics ProofMode.
Require Import HSim IProofMode.
Require Import ClightPlusSkel ClightPlusExprgen ClightPlusgen.
Require Import ClightPlusMemRA ClightPlusMem0 ClightPlusMem1 ClightPlusMemAux.
Require Import CProofMode CIProofMode.
Require Import hardening.
Require Import hardening0.
Require Import hardening1.

(* Require Import xorlist. *)
(* Require Import xorlistall0. *)
(* Require Import xorlist1. *)
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Memory Clightdefs.


Section LEMMA.

  Lemma f_bind_ret_r E R A (s : A -> itree E R)
    : (fun a => ` x : R <- (s a);; Ret x) = s.
  Proof. apply func_ext. i. apply bind_ret_r. Qed.

  Lemma decode_encode_ofs i : decode_val Mint64 (encode_val Mint64 (Vptrofs i)) = Vptrofs i.
  Proof.
    pose proof (decode_encode_val_general (Vptrofs i) Mint64 Mint64).
    unfold Vptrofs in *. des_ifs.
  Qed.

  Lemma decode_encode_item i : decode_val Mint64 (encode_val Mint64 (Vlong i)) = Vlong i.
  Proof. apply (decode_encode_val_general (Vlong i) Mint64 Mint64). Qed.

  Lemma decode_encode_null : decode_val Mint64 (encode_val Mint64 Vnullptr) = Vnullptr.
  Proof. rewrite (decode_encode_val_general Vnullptr Mint64 Mint64). et. Qed.

  Lemma null_zero i : Vptrofs i = Vnullptr -> i = Ptrofs.zero.
  Proof.
    unfold Vptrofs, Vnullptr. des_ifs. i.
    apply (f_equal (fun v: val => match v with Vlong i => i | _ => Int64.zero end)) in H.
    rewrite <- (Ptrofs.of_int64_to_int64 Heq i). rewrite H. et.
  Qed.

  Context `{eventE -< eff}.

  Lemma cast_ptrofs i : cast_to_ptr (Vptrofs i) = Ret (Vptrofs i).
  Proof. des_ifs. Qed.

  Lemma cast_long i : Archi.ptr64 = true -> cast_to_ptr (Vlong i) = Ret (Vlong i).
  Proof. ss. Qed.

End LEMMA.

Section PROOF.

  Import ClightPlusMem1.

  Context `{@GRA.inG Mem.t Σ}.

  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb hardeningStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).


  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.

  Let mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)); ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))].

  Section SIMFUNS.
  Variable hardening_code : Clight.program.
  (* Variable xormod : Mod.t. *)
  (* Hypothesis VALID_link : xorlistall0._xor = Some xorlink. *)
  (* Hypothesis VALID_comp : compile xorlink "xorlist" = Errors.OK xormod. *)
  Let ce := Maps.PTree.elements (prog_comp_env hardening_code).

  Variable sk: Sk.t.
  (* TODO: How to encapsulate fuction info? *)
  (* Hypothesis SKINCL1 : Sk.le (xormod.(Mod.sk)) sk. *)
  Hypothesis SKINCL : Sk.le mfsk sk.
  Hypothesis SKWF : Sk.wf sk.

  Lemma encode :
    sim_fnsem wf top2
      ("encode", fun_to_tgt "hardening" (GlobalStb sk) (mk_pure encode_spec))
      ("encode", cfunU (decomp_func sk ce f_encode)).
  Proof.
    Local Opaque encode_val.
    Local Opaque cast_to_ptr.
    eassert (_hardening = _).
    { unfold _hardening. reflexivity. }
    (* rewrite H0 in *. clear H0. *)
    (* destruct Ctypes.link_build_composite_env. destruct a. *)
    (* inversion VALID_link. clear VALID_link. subst. *)
    (* clear a. simpl in ce. *)
    econs; ss. red.

    (* get_composite ce e. *)
    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply incl_incl_env in SKINCLENV.
    unfold incl_env in SKINCLENV.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_encode. i; ss.
    unfold decomp_func, function_entry_c. ss.

    let H := fresh "HIDDEN" in
    set (H := hide 1).
    
    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% PRE] %]".
    des. clarify. hred_r.

    rename v into iptr, v0 into ptr.

    unhide. hred_r. unhide. remove_tau. unhide. remove_tau.



  End SIMFUNS.

End Proof.
