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
Require Import ClightPlusMem0 ClightPlusMem1 ClightPlusMemAux.
Require Import CProofMode CIProofMode.
Require Import vector.
Require Import vector0.
Require Import vector1.
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Clightdefs.

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

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.
  
  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb vectorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).


  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.

  (* TODO: need to be expanded to realloc and memcpy *)
  Let mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)); ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))].
  Let ce := Maps.PTree.elements (prog_comp_env prog).

  Section SIMFUNS.
  Variable vector0 : Mod.t.
  Hypothesis VALID : vector0._vector = Errors.OK vector0.

  Variable sk: Sk.t.
  Hypothesis SKINCL1 : Sk.le (vector0.(Mod.sk)) sk.
  Hypothesis SKINCL2 : Sk.le mfsk sk.
  Hypothesis SKWF : Sk.wf sk.

  Ltac unfold_comp optsrc EQ :=
    unfold optsrc, compile, get_sk in EQ;
    destruct Coqlib.list_norepet_dec; clarify; des_ifs; ss;
    repeat match goal with
          | H: Coqlib.list_norepet _ |- _ => clear H
          | H: forallb _ _ = true |- _ => clear H
          | H: forallb _ _ && _ = true |- _ => clear H
          | H: Ctypes.prog_main _ = _ |- _ => clear H
          end.

  Lemma sim_vector_init :
    sim_fnsem wf top2
      ("vector_init", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_init_spec))
      ("vector_init", cfunU (decomp_func sk ce f_vector_init)).
  Proof.
  Admitted.

  Lemma sim_vector_total :
    sim_fnsem wf top2
      ("vector_total", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_total_spec))
      ("vector_total", cfunU (decomp_func sk ce f_vector_total)).
  Proof.
  Admitted.

  Lemma sim_vector_resize :
    sim_fnsem wf top2
      ("vector_resize", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_resize_spec))
      ("vector_resize", cfunU (decomp_func sk ce f_vector_resize)).
  Proof.
  Admitted.

  Lemma sim_vector_add :
    sim_fnsem wf top2
      ("vector_add", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_add_spec))
      ("vector_add", cfunU (decomp_func sk ce f_vector_add)).
  Proof.
  Admitted.

  Lemma sim_vector_set :
    sim_fnsem wf top2
      ("vector_set", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_set_spec))
      ("vector_set", cfunU (decomp_func sk ce f_vector_set)).
  Proof.
  Admitted.

  Lemma sim_vector_get :
    sim_fnsem wf top2
      ("vector_get", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_get_spec))
      ("vector_get", cfunU (decomp_func sk ce f_vector_get)).
  Proof.
  Admitted.

  Lemma sim_vector_delete :
    sim_fnsem wf top2
      ("vector_delete", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_delete_spec))
      ("vector_delete", cfunU (decomp_func sk ce f_vector_delete)).
  Proof.
  Admitted.

  Lemma sim_vector_free :
    sim_fnsem wf top2
      ("vector_free", fun_to_tgt "vector" (GlobalStb sk) (mk_pure vector_free_spec))
      ("vector_free", cfunU (vector_initvector_freefun_to_tgt sk ce f_vector_free)).
  Proof.
  Admitted.

  End SIMFUNS.


  Require Import ClightPlusMem01Proof.

  Variable vector0 : Mod.t.
  Hypothesis VALID : vector0._vector = Errors.OK vector0.

  Theorem correct : refines2 [vector0; (ClightPlusMem0.Mem mfsk)] [vector1.vector vector0 GlobalStb; (ClightPlusMem1.Mem mfsk)].
  Proof.
  Admitted.

End PROOF.
