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

Require Import tiny_main tw_main.
        (* EchoAll *)

Cd "extract".

Separate Extraction tiny_main.test_itr tw_main.test_itr.
         (* mw_impl_itr mw_abs_itr EXTRACT_MW_IMPL_LINKING_CHECK *)
         (* echo_prog *)

Cd "..".
