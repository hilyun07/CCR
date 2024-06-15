From compcert Require Import Globalenvs Smallstep Simulation AST Integers Events Behaviors Errors Memory Values Maps.
From compcert Require Import Ctypes Clight Clightdefs Globalenvs.
Require Import ClightPlus2ClightMatchEnv.
From Paco Require Export paco.
Require Import String CoqlibCCR.

Definition match_temps le le' := forall id, CoqlibCCR.option_rel Val.lessdef (le ! id) (le' ! id).

Inductive match_cont : cont -> cont -> Prop :=
  | match_Kstop : match_cont Kstop Kstop
  | match_Kseq
        s k k'
        (NEXT: match_cont k k') :
      match_cont (Kseq s k) (Kseq s k')
  | match_Kloop1
        s1 s2 k k'
        (NEXT: match_cont k k') :
      match_cont (Kloop1 s1 s2 k) (Kloop1 s1 s2 k')
  | match_Kloop2
        s1 s2 k k'
        (NEXT: match_cont k k') :
      match_cont (Kloop2 s1 s2 k) (Kloop2 s1 s2 k')
  | match_Kswitch
        k k'
        (NEXT: match_cont k k') :
      match_cont (Kswitch k) (Kswitch k')
  | match_Kcall
        id f e le le' k k' 
        (LEINJ: match_temps le le') 
        (NEXT: match_cont k k') :
      match_cont (Kcall id f e le k) (Kcall id f e le' k').

Variant match_states : state -> state -> Prop :=
  | match_state
        f s k k' e le le' m m' 
        (EXT: Mem.extends m m')
        (LEINJ: match_temps le le')
        (NEXT: match_cont k k') :
      match_states (State f s k e le m) (State f s k' e le' m')
  | match_callstate
        fd args args' k k' m m' 
        (EXT: Mem.extends m m')
        (VALINJ: List.Forall2 (Val.inject inject_id) args args')
        (NEXT: match_cont k k') :
      match_states (Callstate fd args k m) (Callstate fd args' k' m')
  | match_returnstate
        res res' k k' m m' 
        (EXT: Mem.extends m m')
        (VALINJ: Val.inject inject_id res res')
        (NEXT: match_cont k k') :
      match_states (Returnstate res k m) (Returnstate res' k' m').

Lemma match_call_cont
    k k'
    (MC: match_cont k k')
    (IS: is_call_cont k') :
  is_call_cont k.
Proof. unfold is_call_cont in *. des_ifs; inv MC. Qed.

Lemma match_free_list
    m m' m0 m0' l
    (MM: Mem.extends m m')
    (FREE: Mem.free_list m' l = Some m0')
    (FREE0: Mem.free_list m l = Some m0) :
  Mem.extends m0 m0'.
Proof.
  ginduction l; i; ss; eauto; clarify.
  des_ifs_safe.
  hexploit Mem.free_parallel_extends; eauto.
  i. des. clarify. eapply IHl; eauto.
Qed.

Lemma match_free_list_match 
    m m' m0 l
    (MM: Mem.extends m m')
    (FREE: Mem.free_list m l = Some m0) :
  exists m0', Mem.free_list m' l = Some m0' /\ Mem.extends m0 m0'.
Proof.
  ginduction l; i; ss; clarify. { esplits; eauto. }
  des_ifs_safe.
  hexploit Mem.free_parallel_extends; eauto.
  i. des. des_ifs. eapply IHl; eauto.
Qed.

(* IntPtrRel.binded_val
(* IntptrRel.load_concrete_extends *)
(* Mem.loadv_extends *)
(* Mem.storev_extends *)
Search IntPtrRel.concrete_extends.
volatile_load *)

Lemma match_sem_cast_match
    m m' v v' ty1 ty2 v0' v0
    (MM: Mem.extends m m')
    (CAST: Cop.sem_cast v' ty1 ty2 m' = Some v0')
    (CAST': Cop.sem_cast v ty1 ty2 m = Some v0)
    (MV: Val.lessdef v v') :
  Val.lessdef v0 v0'.
Proof.
  unfold Cop.sem_cast in *. des_ifs; inv MV; ss; clarify.
Qed.

Lemma match_sem_cast
    m m' v v' ty1 ty2 v0
    (MM: Mem.extends m m')
    (CAST: Cop.sem_cast v ty1 ty2 m = Some v0)
    (MV: Val.lessdef v v') :
  exists v0', Cop.sem_cast v' ty1 ty2 m' = Some v0'.
Proof.
  unfold Cop.sem_cast in *. des_ifs; inv MV; ss; clarify; eauto.
  hexploit Mem.weak_valid_pointer_extends; eauto. i. clarify.
Qed.

Lemma match_sem_un_match
    m m' o v v' ty v0' v0
    (MM: Mem.extends m m')
    (OP: Cop.sem_unary_operation o v' ty m' = Some v0')
    (OP': Cop.sem_unary_operation o v ty m = Some v0)
    (MV: Val.lessdef v v') :
  Val.lessdef v0 v0'.
Proof.
  destruct o; ss.
  - unfold Cop.sem_notbool in *. unfold Cop.bool_val in *. des_ifs; inv MV; ss; clarify.
  - unfold Cop.sem_notint in *. des_ifs; inv MV; ss; clarify.
  - unfold Cop.sem_neg in *. des_ifs; inv MV; ss; clarify.
  - unfold Cop.sem_absfloat in *. des_ifs; inv MV; ss; clarify.
Qed.

Lemma match_sem_un
    m m' o v v' ty v0
    (MM: Mem.extends m m')
    (OP': Cop.sem_unary_operation o v ty m = Some v0)
    (MV: Val.lessdef v v') :
  exists v0', Cop.sem_unary_operation o v' ty m' = Some v0'.
Proof.
  destruct o; ss.
  - unfold Cop.sem_notbool in *. unfold Cop.bool_val in *. des_ifs; inv MV; ss; clarify; eauto.
    hexploit Mem.weak_valid_pointer_extends; eauto. i. clarify.
  - unfold Cop.sem_notint in *. des_ifs; inv MV; ss; clarify; eauto.
  - unfold Cop.sem_neg in *. des_ifs; inv MV; ss; clarify; eauto.
  - unfold Cop.sem_absfloat in *. des_ifs; inv MV; ss; clarify; eauto.
Qed.

Ltac wd :=
  match goal with
  | H: IntPtrRel.to_ptr_val _ _ = Vlong _ |- _ => unfold IntPtrRel.to_ptr_val, Mem.to_ptr in H; des_ifs
  | H: IntPtrRel.to_int_val _ _ = Vptr _ _ |- _ => unfold IntPtrRel.to_int_val, Mem.to_int in H; des_ifs
  end.

Ltac re :=
  match goal with
  | H: Int.eq _ _ = true |- _ => apply Int.same_if_eq in H
  | H: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in H
  | H: Ptrofs.eq _ _ = true |- _ => apply Ptrofs.same_if_eq in H
  end.

Lemma match_sem_ptr_sub_match m m' v1 v2 i
  (MM: Mem.extends m m')
  (OP: Cop._sem_ptr_sub_join v1 v2 m = Some i)
:
  Cop._sem_ptr_sub_join v1 v2 m' = Some i.
Proof.
  unfold Cop._sem_ptr_sub_join in OP. des_ifs.
  - apply Ptrofs.same_if_eq in Heq1. clarify.
    unfold Cop._sem_ptr_sub in Heq, Heq0. des_ifs; repeat wd; try solve [ss; des_ifs].
    + repeat wd. repeat re. clarify. ss. unfold Vnullptr in *. clarify.
      unfold IntPtrRel.to_int_val in *. ss. clarify. unfold Cop._sem_ptr_sub_join.
      unfold IntPtrRel.to_ptr_val. ss.
      des_ifs; unfold Cop._sem_ptr_sub in *; des_ifs.
      { repeat re. rewrite Heq1. ss. rewrite Heq5. eauto. }
      ss. unfold Vnullptr in *. clarify.
    + unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val in *.
      unfold IntPtrRel.option_to_val in *. des_ifs.
      hexploit (Mem.to_ptr_extends m v1 v1); eauto. i.
      hexploit (Mem.to_ptr_extends m v2 v2); eauto. i.
      hexploit (Mem.to_int_extends m v1 v1); eauto. i.
      hexploit (Mem.to_int_extends m v2 v2); eauto. i. 
      unfold Cop._sem_ptr_sub_join, Cop._sem_ptr_sub, IntPtrRel.to_int_val, IntPtrRel.to_ptr_val.
      rewrite H, H0, H1, H2. ss. des_ifs.
      { repeat re. f_equal. etransitivity; eauto. }
      rewrite Heq5 in Heq7. rewrite Heq in Heq7. unfold Ptrofs.eq in Heq7. ss. des_ifs.
  - clear Heq0. unfold Cop._sem_ptr_sub in Heq. des_ifs; repeat wd; try solve [ss; des_ifs]; ss.
    { repeat re. unfold Vnullptr in *. clarify. }
    unfold IntPtrRel.to_ptr_val in *.
    unfold IntPtrRel.option_to_val in *. des_ifs.
    hexploit (Mem.to_ptr_extends m v1 v1); eauto. i.
    hexploit (Mem.to_ptr_extends m v2 v2); eauto. i.
    unfold Cop._sem_ptr_sub_join, Cop._sem_ptr_sub, IntPtrRel.to_ptr_val.
    rewrite H, H0. ss. des_ifs; try solve [repeat wd; ss; des_ifs].
    hexploit IntPtrRel.psubl_wrapper_no_angelic.
    { unfold IntPtrRel.to_ptr_val. rewrite H. rewrite H0. ss. }
    { rewrite Heq4. rewrite Heq5. ss. }
    i. ss; des; des_ifs; clarify. unfold lib.sflib.NW in *. des; clarify.
    exfalso. hexploit Ptrofs.eq_spec. rewrite Heq3. i. apply H2. 
    rewrite <- Ptrofs.of_int64_to_int64 at 1; ss. f_equal. apply Int64.same_if_eq.
    unfold Int64.eq. des_ifs.
  - clear Heq. unfold Cop._sem_ptr_sub in Heq0. des_ifs; repeat wd; try solve [ss; des_ifs]; ss.
    unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
    hexploit (Mem.to_int_extends m v1 v1); eauto. i.
    hexploit (Mem.to_int_extends m v2 v2); eauto. i.
    unfold Cop._sem_ptr_sub_join, Cop._sem_ptr_sub, IntPtrRel.to_int_val.
    rewrite H, H0. ss. des_ifs; try solve [re; f_equal; eauto].
    { repeat wd. repeat re. ss. unfold Vnullptr in *. clarify. }
    hexploit IntPtrRel.psubl_wrapper_no_angelic.
    { rewrite Heq4. rewrite Heq5. ss. }
    { unfold IntPtrRel.to_int_val. rewrite H. rewrite H0. ss. }
    i. unfold lib.sflib.NW in *. ss; des; des_ifs; clarify.
    exfalso. hexploit Ptrofs.eq_spec. rewrite Heq3. i. apply H1. 
    rewrite <- Ptrofs.of_int64_to_int64 at 1; ss. f_equal. rewrite Heq7.
    apply Int64.same_if_eq. unfold Int64.eq. des_ifs.
Qed.

Lemma match_sem_ptr_cmp_match m m' o v1 v2 v
  (MM: Mem.extends m m')
  (OP: Cop.cmp_ptr_join_common m o v1 v2 = Some v)
:
  exists v', Cop.cmp_ptr_join_common m' o v1 v2 = Some v' /\ Val.lessdef v v'.
Proof.
  unfold Cop.cmp_ptr_join_common in OP. des_ifs.
  - unfold Cop.cmp_ptr in *. des_ifs. ss. clarify. ss.
    unfold Cop.cmp_ptr in *. ss. clarify. ss. esplits; eauto.
  - unfold Cop.cmp_ptr in *. des_ifs. ss. clarify. ss.
    unfold Cop.cmp_ptr in *. ss. clarify. ss. esplits; eauto.
    des_ifs.
    hexploit Mem.weak_valid_pointer_extends; eauto. i. unfold Mem.weak_valid_pointer in *.
    clarify.
  - unfold Cop.cmp_ptr_join in *. des_ifs.
    + re. clarify. unfold Cop.cmp_ptr in *. des_ifs. unfold Val.cmplu_bool in *.
      des_ifs.
      * apply andb_prop in Heq8. destruct Heq8. unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit Mem.to_ptr_extends. 3: et. all: et. i.
        hexploit Mem.to_ptr_extends. 3: apply Heq6. all: et. i.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join in *. unfold IntPtrRel.to_ptr_val. rewrite H3, H4. ss.
        clear Heq6 H4. unfold Cop.cmp_ptr, Val.cmplu_bool. 
        unfold Mem.weak_valid_pointer in H1. des_ifs.
        all: try solve [unfold Val.of_bool in *; ss; des_ifs].
        all: re; clarify; try solve [esplits; et].
        all: unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *; des_ifs.
        all: hexploit (Mem.to_int_extends m (Vlong i) (Vlong i)); et; i.
        all: hexploit (Mem.to_int_extends m (Vptr b0 i5) (Vptr b0 i5)); et; i.
        all: rewrite H in *; rewrite H4 in *; clarify; ss; clarify; red in H; clarify.
        rewrite H7 in *. clarify. unfold Int.eq in Heq6. des_ifs.
      * apply andb_prop in Heq8. destruct Heq8. unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit Mem.to_ptr_extends. 3: et. all: et. i.
        hexploit Mem.to_ptr_extends. 3: apply Heq6. all: et. i.
        hexploit (Mem.to_int_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_int_extends m (Vptr b i0) (Vptr b i0)); et; i.
        unfold lib.sflib.NW in *.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool, IntPtrRel.to_int_val, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        unfold Mem.weak_valid_pointer in *. des_ifs.
        all: try solve [esplits; et]. unfold Int.eq in Heq10. des_ifs.
      * bsimpl. des.
        hexploit Mem.valid_pointer_extends; eauto. i.
        hexploit Mem.valid_pointer_extends; eauto. i.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.to_ptr_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_ptr_extends m (Vptr b i0) (Vptr b i0)); et; i.
        hexploit (Mem.to_int_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_int_extends m (Vptr b i0) (Vptr b i0)); et; i.
        unfold lib.sflib.NW in *.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool, IntPtrRel.to_int_val, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        des_ifs.
        all: try solve [esplits; et]. unfold Int.eq in Heq12. des_ifs.
      * apply andb_prop in Heq9. des. apply andb_prop in Heq6. des.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit (Mem.weak_valid_pointer_extends m m' b1); eauto. i.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.to_ptr_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_ptr_extends m (Vptr b i0) (Vptr b i0)); et; i.
        hexploit (Mem.to_int_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_int_extends m (Vptr b i0) (Vptr b i0)); et; i.
        unfold lib.sflib.NW in *.
        repeat re. clarify.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool, IntPtrRel.to_int_val, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        des_ifs.
        all: try solve [esplits; et].
        unfold Int.eq in Heq9. des_ifs.
      * apply andb_prop in Heq9. des. apply andb_prop in Heq6. des.
        hexploit (Mem.weak_valid_pointer_extends m m' b2); eauto. i.
        hexploit (Mem.weak_valid_pointer_extends m m' b2 (Ptrofs.unsigned i4)); eauto. i.
        hexploit (Mem.weak_valid_pointer_extends m m' b0); eauto. i.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.to_ptr_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_ptr_extends m (Vptr b i0) (Vptr b i0)); et; i.
        hexploit (Mem.to_int_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_int_extends m (Vptr b i0) (Vptr b i0)); et; i.
        unfold lib.sflib.NW in *.
        repeat re. clarify.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool, IntPtrRel.to_int_val, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        des_ifs. all: try solve [esplits; et].
        unfold Int.eq in Heq13. des_ifs.
      * apply andb_prop in Heq9. des. apply andb_prop in Heq6. des.
        hexploit (Mem.weak_valid_pointer_extends m m' b0); eauto. i.
        hexploit (Mem.valid_pointer_extends m m' b1); eauto. i.
        hexploit (Mem.valid_pointer_extends m m' b2); eauto. i.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.to_ptr_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_ptr_extends m (Vptr b i0) (Vptr b i0)); et; i.
        hexploit (Mem.to_int_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_int_extends m (Vptr b i0) (Vptr b i0)); et; i.
        unfold lib.sflib.NW in *. repeat re. clarify.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr_join, Cop.cmp_ptr, Val.cmplu_bool, IntPtrRel.to_int_val, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        des_ifs. all: try solve [esplits; et].
        unfold Int.eq in Heq13. des_ifs.
    + clear Heq1. unfold Cop.cmp_ptr in *. des_ifs. unfold Val.cmplu_bool in *. des_ifs.
      * apply andb_prop in Heq5. des.
        hexploit (Mem.weak_valid_pointer_extends m m' b0); eauto. i.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.to_ptr_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_ptr_extends m (Vptr b i0) (Vptr b i0)); et; i.
        unfold lib.sflib.NW in *. repeat re. clarify.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr_join, Val.cmplu_bool, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        unfold Cop.cmp_ptr at 1.
        des_ifs. all: try solve [ss; clarify; des_ifs].
      * apply andb_prop in Heq5. des.
        hexploit (Mem.weak_valid_pointer_extends m m' b1 (Ptrofs.unsigned i2)); eauto. i.
        hexploit (Mem.weak_valid_pointer_extends m m' b1 (Ptrofs.unsigned i3)); eauto. i.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.to_ptr_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_ptr_extends m (Vptr b i0) (Vptr b i0)); et; i.
        unfold lib.sflib.NW in *.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr_join, Val.cmplu_bool, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        unfold Cop.cmp_ptr at 1.
        des_ifs. all: try solve [ss; clarify; des_ifs].
        all: try solve [unfold Val.of_bool in *; ss; des_ifs].
        { unfold Cop.cmp_ptr in *. unfold Val.of_bool in *. ss. des_ifs; ss; clarify; des_ifs. }
        { esplits; et. re. clarify. ss. des_ifs. ss. clarify. rewrite H2 in *. clarify. }
        { unfold Coqlib.option_map in Heq2. des_ifs. unfold Cop.cmp_ptr, Coqlib.option_map in Heq8. des_ifs.
          hexploit IntPtrRel.cmplu_no_angelic. 2:et. { unfold IntPtrRel.to_ptr_val. rewrite Heq10. rewrite Heq11. et. }
          i. rewrite H1 in *. rewrite H2 in *. clarify. unfold Int.eq in *. des_ifs. }
        { unfold Cop.cmp_ptr in *. unfold Val.of_bool in *. ss. des_ifs; ss; clarify; des_ifs. }
        { unfold Cop.cmp_ptr in *. unfold Val.of_bool in *. ss. des_ifs; ss; clarify; des_ifs. }
        { unfold Cop.cmp_ptr in *. unfold Val.of_bool in *. ss. des_ifs; ss; clarify; des_ifs. }
        { unfold Cop.cmp_ptr in *. unfold Val.of_bool in *. ss. des_ifs; ss; clarify; des_ifs. }
        esplits; et.
        unfold Coqlib.option_map in Heq2. des_ifs. clear Heq8. ss. des_ifs. rewrite H3 in *.
        clarify.
      * bsimpl. des.
        hexploit (Mem.valid_pointer_extends m m' b0); eauto. i.
        hexploit (Mem.valid_pointer_extends m m' b1); eauto. i.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.to_ptr_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_ptr_extends m (Vptr b i0) (Vptr b i0)); et; i.
        unfold lib.sflib.NW in *.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join, Cop.cmp_ptr in *.
        des_ifs.
        all: try solve [unfold Val.of_bool, Coqlib.option_map in *; ss; des_ifs].
        { re. clarify. clear Heq8. unfold IntPtrRel.to_ptr_val in Heq2 at 1.
          rewrite H1 in Heq2. clear Heq3 H1. ss. des_ifs. esplits; et. }
        { unfold Coqlib.option_map in *. des_ifs. hexploit IntPtrRel.cmplu_no_angelic; et.
          i. rewrite H3 in *. rewrite H4 in *. clarify. unfold Int.eq in *. des_ifs. }
        { clear Heq8. unfold IntPtrRel.to_ptr_val in Heq2 at 1.
          rewrite H1 in Heq2. clear Heq3 H1. ss. des_ifs. esplits; et. }
        { clear Heq8. unfold IntPtrRel.to_ptr_val in Heq2 at 1.
          rewrite H1 in Heq2. clear Heq3 H1. ss. des_ifs. }
        { clear Heq8. unfold IntPtrRel.to_ptr_val in Heq2 at 1.
          rewrite H1 in Heq2. clear Heq3 H1. ss. des_ifs. }
    + clear Heq0. unfold Cop.cmp_ptr in *. des_ifs. unfold Val.cmplu_bool in *. des_ifs.
      * unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.to_int_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_int_extends m (Vptr b i0) (Vptr b i0)); et; i.
        unfold lib.sflib.NW in *.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join, Val.cmplu_bool, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        unfold Cop.cmp_ptr at 2.
        des_ifs.
        all: try solve [unfold Cop.cmp_ptr, Val.of_bool, Coqlib.option_map in *; ss; des_ifs].
        { re. clarify. clear Heq2. ss. rewrite Heq1 in *. clarify. esplits; et. }
        { unfold Cop.cmp_ptr in *. des_ifs. unfold Coqlib.option_map in *. des_ifs.
          hexploit IntPtrRel.cmplu_no_angelic; et. unfold IntPtrRel.to_int_val at 2. rewrite Heq8.
          et. i. rewrite H in *. ss. clarify. rewrite H2 in *. clarify. unfold Int.eq in *. des_ifs. }
        { clear Heq2. unfold Cop.cmp_ptr in *. des_ifs. ss. clarify. rewrite H0 in *. clarify. esplits; et. }
      * apply andb_prop in Heq5. des.
        hexploit (Mem.weak_valid_pointer_extends m m' b0); eauto. i.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.to_int_extends m (Vlong i) (Vlong i)); et; i.
        hexploit (Mem.to_int_extends m (Vptr b i0) (Vptr b i0)); et; i.
        unfold lib.sflib.NW in *.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr_join, Val.cmplu_bool, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        unfold Cop.cmp_ptr at 2 3.
        des_ifs. 
        all: try solve [unfold Cop.cmp_ptr, Val.of_bool, Coqlib.option_map in *; ss; des_ifs].
  - unfold Cop.cmp_ptr_join in *. des_ifs. clear Heq0.
    unfold Cop.cmp_ptr in *. des_ifs. unfold Coqlib.option_map in *. des_ifs.
    unfold Val.cmplu_bool in *. des_ifs.
  - re. clarify. ss. des_ifs. unfold Cop.cmp_ptr, Coqlib.option_map in OP. des_ifs.
    unfold Val.cmplu_bool in *. des_ifs. ss.
    hexploit (Mem.weak_valid_pointer_extends); et. i.
    unfold Cop.cmp_ptr. unfold Val.cmplu_bool.
    unfold Mem.weak_valid_pointer in *.
    des_ifs; ss. rewrite Heq0. ss. esplits; et.
  - unfold Cop.cmp_ptr_join in *. des_ifs.
    + re. clarify. unfold Cop.cmp_ptr in *. des_ifs. unfold Coqlib.option_map in *.
      des_ifs. unfold Val.cmplu_bool in *. des_ifs.
      * apply andb_prop in Heq7. destruct Heq7.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit Mem.to_ptr_extends. 3: et. all: et. i.
        hexploit Mem.to_ptr_extends. 3: apply Heq5. all: et. i.
        hexploit (Mem.to_int_extends m (Vptr b i) (Vptr b i)); et; i.
        hexploit (Mem.to_int_extends m (Vlong i0) (Vlong i0)); et; i.
        unfold lib.sflib.NW in *. unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join in *.
        unfold Cop.cmp_ptr, IntPtrRel.to_ptr_val, IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        all: try solve [unfold Coqlib.option_map, Val.of_bool in *; ss; des_ifs].
      * apply andb_prop in Heq7. destruct Heq7.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit Mem.to_ptr_extends. 3: et. all: et. i.
        hexploit Mem.to_ptr_extends. 3: apply Heq5. all: et. i.
        hexploit (Mem.to_int_extends m (Vptr b i) (Vptr b i)); et; i.
        hexploit (Mem.to_int_extends m (Vlong i0) (Vlong i0)); et; i.
        unfold lib.sflib.NW in *. unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join, Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr, IntPtrRel.to_ptr_val, IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        all: try solve [unfold Coqlib.option_map, Val.of_bool in *; ss; des_ifs].
        { unfold Coqlib.option_map in *. des_ifs. re. clarify. clear Heq7. ss. clarify. rewrite H0 in *. clarify. esplits; et. }
        { unfold Coqlib.option_map in *. des_ifs.
          hexploit IntPtrRel.cmplu_no_angelic; unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val.
          rewrite Heq11, Heq12; et. rewrite Heq9, Heq10; et. i. rewrite H5 in *. rewrite H6 in *. clarify.
          unfold Int.eq in *. des_ifs. }
        { clear Heq3. ss. clarify. rewrite H0 in *. clarify. esplits; et. }
      * apply andb_prop in Heq7. destruct Heq7.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit Mem.valid_pointer_extends; eauto. i.
        hexploit Mem.valid_pointer_extends; eauto. i.
        hexploit Mem.to_ptr_extends. 3: et. all: et. i.
        hexploit Mem.to_ptr_extends. 3: apply Heq5. all: et. i.
        hexploit (Mem.to_int_extends m (Vptr b i) (Vptr b i)); et; i.
        hexploit (Mem.to_int_extends m (Vlong i0) (Vlong i0)); et; i.
        unfold lib.sflib.NW in *. unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join, Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr, IntPtrRel.to_ptr_val, IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        all: try solve [unfold Coqlib.option_map, Val.of_bool in *; ss; des_ifs].
        { unfold Coqlib.option_map in *. des_ifs. re. clarify. clear Heq8. ss. clarify. rewrite H0 in *. clarify. esplits; et. }
        { unfold Coqlib.option_map in *. des_ifs.
          hexploit IntPtrRel.cmplu_no_angelic; unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val.
          rewrite Heq12, Heq13; et. rewrite Heq10, Heq11; et. i. rewrite H5 in *. rewrite H6 in *. clarify.
          unfold Int.eq in *. des_ifs. }
        { clear Heq3. ss. clarify. rewrite H0 in *. clarify. esplits; et. }
      * apply andb_prop in Heq9. destruct Heq9.
        apply andb_prop in Heq6. destruct Heq6.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit (Mem.weak_valid_pointer_extends m m' b3); eauto. i.
        hexploit Mem.to_ptr_extends. 3: et. all: et. i.
        hexploit Mem.to_ptr_extends. 3: apply Heq6. all: et. i.
        hexploit (Mem.to_int_extends m (Vptr b i) (Vptr b i)); et; i.
        hexploit (Mem.to_int_extends m (Vlong i0) (Vlong i0)); et; i.
        unfold lib.sflib.NW in *. unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join, Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr, IntPtrRel.to_ptr_val, IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        all: try solve [unfold Coqlib.option_map, Val.of_bool in *; ss; des_ifs].
      * apply andb_prop in Heq9. destruct Heq9.
        apply andb_prop in Heq6. destruct Heq6.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.weak_valid_pointer_extends m m' b4 (Ptrofs.unsigned i4)); eauto. i.
        hexploit (Mem.weak_valid_pointer_extends m m' b4); eauto. i.
        hexploit (Mem.weak_valid_pointer_extends m m' b2); eauto. i.
        hexploit Mem.to_ptr_extends. 3: et. all: et. i.
        hexploit Mem.to_ptr_extends. 3: apply Heq6. all: et. i.
        hexploit (Mem.to_int_extends m (Vptr b i) (Vptr b i)); et; i.
        hexploit (Mem.to_int_extends m (Vlong i0) (Vlong i0)); et; i.
        unfold lib.sflib.NW in *. unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join, Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr, IntPtrRel.to_ptr_val, IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        all: try solve [unfold Coqlib.option_map, Val.of_bool in *; ss; des_ifs].
      * apply andb_prop in Heq9. destruct Heq9.
        apply andb_prop in Heq6. destruct Heq6.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.valid_pointer_extends m m' b3); eauto. i.
        hexploit (Mem.valid_pointer_extends m m' b4); eauto. i.
        hexploit (Mem.weak_valid_pointer_extends m m' b2); eauto. i.
        hexploit Mem.to_ptr_extends. 3: et. all: et. i.
        hexploit Mem.to_ptr_extends. 3: apply Heq6. all: et. i.
        hexploit (Mem.to_int_extends m (Vptr b i) (Vptr b i)); et; i.
        hexploit (Mem.to_int_extends m (Vlong i0) (Vlong i0)); et; i.
        unfold lib.sflib.NW in *. unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join, Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr, IntPtrRel.to_ptr_val, IntPtrRel.to_ptr_val, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        all: try solve [unfold Coqlib.option_map, Val.of_bool in *; ss; des_ifs].
    + clear Heq1. unfold Cop.cmp_ptr in *. des_ifs. unfold Coqlib.option_map in *.
      des_ifs. unfold Val.cmplu_bool in *. des_ifs.
      * apply andb_prop in Heq5. destruct Heq5. re. clarify.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit Mem.to_ptr_extends. 3: et. all: et. i.
        hexploit Mem.to_ptr_extends. 3: apply Heq3. all: et. i.
        unfold lib.sflib.NW in *. unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join in *.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        unfold Cop.cmp_ptr at 1. des_ifs.
        all: try solve [unfold Coqlib.option_map, Val.of_bool in *; ss; des_ifs].
      * apply andb_prop in Heq5. destruct Heq5.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit Mem.weak_valid_pointer_extends; eauto. i. move H at bottom.
        hexploit Mem.weak_valid_pointer_extends; eauto. i.
        hexploit Mem.to_ptr_extends. 3: et. all: et. i.
        hexploit Mem.to_ptr_extends. 3: apply Heq3. all: et. i.
        unfold lib.sflib.NW in *. unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join in *.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        unfold Cop.cmp_ptr at 1. des_ifs.
        all: try solve [unfold Cop.cmp_ptr, Coqlib.option_map, Val.of_bool in *; ss; des_ifs].
        { re. clarify. clear Heq5. ss. clarify. clear Heq8 Heq2. des_ifs.
          ss. clarify. rewrite H0 in *. clarify. esplits; et. } 
        { unfold Cop.cmp_ptr in *. des_ifs. unfold Coqlib.option_map in *. des_ifs.
          hexploit IntPtrRel.cmplu_no_angelic; et. unfold IntPtrRel.to_ptr_val. rewrite Heq7, Heq8.
          et. i. rewrite H4 in *. ss. clarify. rewrite H5 in *. clarify. unfold Int.eq in *. des_ifs. }
        { clear Heq5. ss. clarify. des_ifs. ss. clarify. rewrite H0 in *. clarify. esplits; et. }
        { clear -Heq0 H2 H3. ss. unfold Mem.weak_valid_pointer in *. des_ifs. }
        { clear -Heq0 H2 H3. ss. unfold Mem.weak_valid_pointer in *. des_ifs. }
      * bsimpl. des.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit Mem.valid_pointer_extends; eauto. i. move Heq5 at bottom.
        hexploit Mem.valid_pointer_extends; eauto. i.
        hexploit Mem.to_ptr_extends. 3: et. all: et. i.
        hexploit Mem.to_ptr_extends. 3: apply Heq3. all: et. i.
        unfold lib.sflib.NW in *. unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join in *.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        unfold Cop.cmp_ptr at 1. des_ifs.
        all: try solve [unfold Cop.cmp_ptr, Coqlib.option_map, Val.of_bool in *; ss; des_ifs].
        { re. clarify. clear Heq8. ss. des_ifs. ss. unfold Coqlib.option_map in *. des_ifs. 
          rewrite H3 in *. clarify. esplits; et. }
        { unfold Cop.cmp_ptr in *. des_ifs. unfold Coqlib.option_map in *. des_ifs.
          hexploit IntPtrRel.cmplu_no_angelic; et. unfold IntPtrRel.to_ptr_val. rewrite Heq11, Heq10.
          et. i. rewrite H2 in *. ss. clarify. rewrite H3 in *. clarify. unfold Int.eq in *. des_ifs. }
        { clear Heq8. ss. clarify. des_ifs. unfold Coqlib.option_map in *. des_ifs. rewrite H3 in *. clarify. esplits; et. }
    + clear Heq0. unfold Cop.cmp_ptr in *. des_ifs. unfold Coqlib.option_map in *.
      des_ifs. unfold Val.cmplu_bool in *. des_ifs.
      * unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.to_int_extends m (Vlong i0) (Vlong i0)); et; i.
        hexploit (Mem.to_int_extends m (Vptr b i) (Vptr b i)); et; i.
        unfold lib.sflib.NW in *.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Cop.cmp_ptr_join, Val.cmplu_bool, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        unfold Cop.cmp_ptr at 2.
        des_ifs.
        all: try solve [unfold Cop.cmp_ptr, Val.of_bool, Coqlib.option_map in *; ss; des_ifs].
        { re. clarify. clear Heq1. ss. rewrite H0 in *. clarify. esplits; et. }
        { unfold Cop.cmp_ptr in *. des_ifs. unfold Coqlib.option_map in *. des_ifs.
          hexploit IntPtrRel.cmplu_no_angelic; et. unfold IntPtrRel.to_int_val. rewrite Heq7, Heq6.
          et. i. rewrite H in *. ss. clarify. rewrite H2 in *. clarify. unfold Int.eq in *. des_ifs. }
        { clear Heq1. unfold Cop.cmp_ptr in *. des_ifs. ss. clarify. rewrite H0 in *. clarify. esplits; et. }
      * apply andb_prop in Heq5. des.
        hexploit (Mem.weak_valid_pointer_extends m m' b1); eauto. i.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
        hexploit (Mem.to_int_extends m (Vlong i0) (Vlong i0)); et; i.
        hexploit (Mem.to_int_extends m (Vptr b i) (Vptr b i)); et; i.
        unfold lib.sflib.NW in *.
        unfold Cop.cmp_ptr_join_common in *. rewrite Heq.
        unfold Mem.weak_valid_pointer in *.
        unfold Cop.cmp_ptr_join, Val.cmplu_bool, IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        unfold Cop.cmp_ptr at 2 3.
        des_ifs. 
        all: try solve [unfold Cop.cmp_ptr, Val.of_bool, Coqlib.option_map in *; ss; des_ifs].
  - ss. unfold Cop.cmp_ptr in OP. des_ifs. unfold Coqlib.option_map in *. des_ifs.
    unfold Val.cmplu_bool in *. des_ifs.
    + apply andb_prop in Heq2. des.
      hexploit Mem.weak_valid_pointer_extends; eauto. i. move Heq2 at bottom.
      hexploit Mem.weak_valid_pointer_extends; eauto. i.
      unfold Cop.cmp_ptr, Val.cmplu_bool, Mem.weak_valid_pointer in *. des_ifs.
      ss. esplits; et.
    + bsimpl. des. 
      hexploit Mem.valid_pointer_extends; eauto. i. move Heq2 at bottom.
      hexploit Mem.valid_pointer_extends; eauto. i.
      unfold Cop.cmp_ptr, Val.cmplu_bool in *. des_ifs.
      ss. rewrite Heq0. esplits; et.
Qed.

(* TODO: integrate two kinds of lemma to forward sim-lemma *)

Lemma match_sem_bin_match ce m m' o v v' ty1 ty2 v0' v0 v1
  (MM: Mem.extends m m')
  (OP': Cop.sem_binary_operation ce o v ty1 v0 ty2 m = Some v1)
  (MV: Val.lessdef v v')
  (MV': Val.lessdef v0 v0')
:
  exists v1', Cop.sem_binary_operation ce o v' ty1 v0' ty2 m' = Some v1' /\ Val.lessdef v1 v1'.
Proof.
  destruct o; ss.
  - unfold Cop.sem_add in *. des_ifs; inv MV; inv MV'; ss; clarify; try rewrite OP'; eauto.
    + unfold Cop.sem_add_ptr_int in *. des_ifs.
    + unfold Cop.sem_add_ptr_long in *. des_ifs.
    + unfold Cop.sem_add_ptr_int in *. des_ifs.
    + unfold Cop.sem_add_ptr_long in *. des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq2 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
  - unfold Cop.sem_sub in *. des_ifs; inv MV; inv MV'; ss; clarify; try solve [esplits; eauto].
    + unfold Cop._sem_ptr_sub_join_common in *. des_ifs; try solve [esplits; eauto].
      all: hexploit match_sem_ptr_sub_match; eauto; i; clarify; esplits; eauto.
    + unfold Cop._sem_ptr_sub_join_common in *. des_ifs; try solve [esplits; eauto].
      all: hexploit match_sem_ptr_sub_match; eauto; i; clarify; esplits; eauto.
    + unfold Cop._sem_ptr_sub_join_common in *. des_ifs; try solve [esplits; eauto].
      all: hexploit match_sem_ptr_sub_match; eauto; i; clarify; esplits; eauto.
    + unfold Cop._sem_ptr_sub_join_common in *. des_ifs; try solve [esplits; eauto].
      all: hexploit match_sem_ptr_sub_match; eauto; i; clarify; esplits; eauto.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq2 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H|inv H0].
      all: inv H; inv H0; esplits; eauto.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_mul in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_div in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_mod in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_and in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_or in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_xor in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_shl in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
  - unfold Cop.sem_shr in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
  - unfold Cop.sem_cmp in *. des_ifs; inv MV; inv MV'; ss; clarify.
    all: try solve [eapply match_sem_ptr_cmp_match; et].
    + unfold Cop.cmp_ptr_join_common in OP'. des_ifs.
    + des_ifs. 

    admit "".
Qed.


Lemma match_deref_loc_match t m m' vp vp' v v'
  (MM: Mem.extends m m')
  (DEREF: deref_loc t m vp v)
  (DEREF': deref_loc t m' vp' v')
  (MV: Val.lessdef vp vp')
:
  Val.lessdef v v'.
Proof.
  inv DEREF; inv DEREF'; ss; clarify; rewrite H in *; clarify.
  hexploit Mem.loadv_extends; eauto. i. des. clarify. 
Qed.

Lemma match_eval_match ge e le le' m m' a
  (MM: Mem.extends m m')
  (MLE: match_temps le le')
:
  (forall v v', Clight.eval_expr ge e le m a v -> Clight.eval_expr ge e le' m' a v' -> Val.lessdef v v')
  /\ (forall v v', Clight.eval_lvalue ge e le m a v -> Clight.eval_lvalue ge e le' m' a v' -> Val.lessdef v v').
Proof.
  ginduction a; i; ss; clarify.
  all: try solve [split; i; inv H; inv H0; ss; inv H1; inv H].
  - split; i; inv H; inv H0; ss; clarify.
    inv H; inv H1; clarify; eapply match_deref_loc_match; eauto.
  - split; i; inv H; inv H0; ss; clarify; try solve [inv H| inv H1].
    specialize (MLE i). rewrite H4 in *. rewrite H3 in *. inv MLE. eauto.
  - hexploit IHa; eauto. i. des. split; i; inv H1; inv H2; cycle 1. { hexploit H; eauto. }
    inv H3; inv H1. hexploit H; eauto. i. hexploit match_deref_loc_match; eauto. 
  - hexploit IHa; eauto. i. des. split; i; inv H1; inv H2; try solve [inv H1|inv H3].
    hexploit H0; eauto.
  - hexploit IHa; eauto. i. des. split; i; inv H1; inv H2; try solve [inv H1|inv H3].
    hexploit H; eauto. i. hexploit match_sem_un_match; eauto.
  - hexploit IHa1; eauto. i. des. hexploit IHa2; eauto. i. des.
    split; i; inv H3; inv H4; try solve [inv H5|inv H3].
    hexploit H; eauto. hexploit H1; eauto. i. hexploit match_sem_bin_match; eauto.
  -
    inv H3; inv H1. hexploit H; eauto. i. hexploit match_deref_loc_match; eauto. 
  -
      
    

Admitted.

Lemma match_eval_expr_match ge e le le' m m' a
  (MM: Mem.extends m m')
  (MLE: match_temps le le')
:
  forall v', Clight.eval_expr ge e le' m' a v' -> exists v, Val.lessdef v v' /\ Clight.eval_expr ge e le m a v.
Proof.
  hexploit match_eval_match; eauto. i. des. eauto.
Qed.

Lemma match_eval_lvalue_match ge e le le' m m' a
  (MM: Mem.extends m m')
  (MLE: match_temps le le')
:
  forall v', Clight.eval_lvalue ge e le' m' a v' -> exists v, Val.lessdef v v' /\ Clight.eval_lvalue ge e le m a v.
Proof.
  hexploit match_eval_match; eauto. i. des. eauto.
Qed.

Lemma match_assign_loc_match ce m m' m0' vp vp' v v' ty
  (MM: Mem.extends m m')
  (CAST: assign_loc ce ty m' vp' v' m0')
  (MV: Val.lessdef vp vp')
  (MV': Val.lessdef v v')
:
  exists m0, Mem.extends m0 m0' /\ assign_loc ce ty m vp v m0.
Proof.
Admitted.
  
Lemma match_states_bsim p gmtgt st_src st_tgt
  (M: match_states st_src st_tgt)
:
  NOSTUTTER.bsim (semantics3 p) (semantics2 p) gmtgt
  (* (concrete_snapshot (Genv.globalenv p) (Callstate f [] Kstop m'))  *)
  lt 0%nat st_src st_tgt.
Proof.
  revert_until st_src. revert st_src. pcofix CIH.
  i. inv M.
  - destruct s.
    + pfold. econs. i. rr.
      unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des. { inv H. } econs.
      * i. left. inv STEPTGT.
        ** inv NEXT. esplits.
            { instantiate (1:=E0). econs. }
            { left. apply plus_one. econs. }
            { right. apply CIH. econs; eauto. }
        ** inv NEXT. esplits.
            { instantiate (1:=E0). econs. }
            { left. apply plus_one. econs. eauto. }
            { right. apply CIH. econs; eauto. econs; eauto. }
        ** inv NEXT. esplits.
            { instantiate (1:=E0). econs. }
            { left. apply plus_one. econs. }
            { right. apply CIH. econs; eauto. }
        ** hexploit match_call_cont; eauto. i.
           inv H; ss. hexploit match_free_list; eauto. i.
           esplits.
           { instantiate (1:=E0). econs. }
           { left. apply plus_one. econs; eauto. }
           { right. apply CIH. econs; eauto. }
        ** inv NEXT. esplits.
            { instantiate (1:=E0). econs. }
            { left. apply plus_one. apply step_skip_break_switch. eauto. }
            { right. apply CIH. econs; eauto. }
      * i. inv FINALTGT.
      * right. destruct k'.
        ** inv NEXT. inv H. hexploit match_free_list_match; eauto.
           i. des. esplits. apply step_skip_call; eauto.
        ** esplits. econs.
        ** esplits. econs. eauto.
        ** esplits. econs.
        ** esplits. apply step_skip_break_switch. eauto.
        ** inv NEXT. inv H. hexploit match_free_list_match; eauto.
           i. des. esplits. apply step_skip_call; eauto.
    + pfold. econs. i. rr.
      unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des. { inv H. } inv H; des; clarify. econs.
      * i. left. inv STEPTGT; des; clarify.
        (* change to consistency lemma *)
        hexploit match_eval_expr_match; eauto. i. des.
        hexploit match_eval_lvalue_match; eauto. i. des.
        hexploit match_sem_cast_match; eauto. i. des.
        hexploit match_assign_loc_match; eauto. i. des.
        esplits.
        { instantiate (1:=E0). econs. }
        { left. apply plus_one. econs; eauto. }
        { right. apply CIH. econs; eauto. }
      * i. inv FINALTGT.
        (* change to progress lemma *)
      * right. esplits.  2:{  }
    +
Admitted.

Lemma semantics2to3 p:
  forall obs1, program_observes (Clight.semantics2 p) obs1 ->
  exists obs0, program_observes (semantics3 p) obs0 /\ observation_improves obs0 obs1.
Proof.
  apply backward_simulation_observation_improves.
  econs. econs.
  { apply Arith.Wf_nat.lt_wf. }
  { i. inversion INITSRC. eexists. econs; eauto. }
  i. inv INITSRC. inv INITTGT. inv TGTCAP.
  replace ge0 with ge in * by auto. clear ge0. clarify.
  esplits; ss.
  { econs; eauto. }
  { eauto. admit "asd". }
  { eapply match_states_bsim. econs; eauto. 2:econs. admit "". }
Admitted.
