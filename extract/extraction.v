Require Import ModSem.
Require Import ClassicalDescription.

Require Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
(* Require Import Coq.extraction.ExtrOcamlZInt. *)
(* Require Import ExtrOcamlNatInt. *)

Extraction Blacklist List String Int.

Extract Constant excluded_middle_informative => "true".
Extract Constant assume => "(fun _ -> lazy (Coq_go (RetF ())))".
Extract Constant guarantee => "(fun _ -> lazy (Coq_go (RetF ())))".
Extract Constant EventsL.choose_from =>
  "fun l ->
    ITree.bind
      (ITree.trigger (Coq_inr1 (Syscall
        (('c'::('h'::('o'::('o'::('s'::('e'::('_'::('f'::('r'::('o'::('m'::[]))))))))))),
        (Any.Any.upcast l))))) (fun tid ->
      ITree.bind
        (unwrapU
          (coq_ReSum_inr (Obj.magic __)
            (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0)) (fun _ _ _ ->
            coq_Inr_sum1) __ __ __
            (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))
          (Any.Any.downcast tid)) (fun tid0 -> lazy (Coq_go (RetF tid0))))".

Extract Constant EventsL.dummy_return =>
 " let coq_ReSum_sum bif h1 a b c h4 h5 =
  case_ bif h1 a b c (resum a c h4) (resum b c h5) in
ITree.trigger
      (subevent
        (coq_ReSum_sum (Obj.magic __)
          (Obj.magic (fun _ _ _ x x0 _ -> coq_Case_sum1 x x0)) __ __ __
          (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __)
          (coq_ReSum_inr (Obj.magic __)
            (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
            (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __)))))
        (Coq_inr1 (Syscall (('d'::('u'::('m'::('m'::('y'::('_'::('r'::('e'::('t'::('u'::('r'::('n'::[])))))))))))), (Any.Any.upcast [])))))".


Require Import tiny_main tw_main test.
        (* EchoAll *)

Cd "extract".

Separate Extraction tiny_main.test_itr tw_main.test_itr test.test_itr.
         (* mw_impl_itr mw_abs_itr EXTRACT_MW_IMPL_LINKING_CHECK *)
         (* echo_prog *)

Cd "..".
