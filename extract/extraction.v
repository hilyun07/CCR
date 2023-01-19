Require Import ModSem.
Require Import ClassicalDescription.

Require Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
(* Require Import Coq.extraction.ExtrOcamlZInt. *)
(* Require Import ExtrOcamlNatInt. *)

Extraction Blacklist List String Int.

Extract Constant excluded_middle_informative => "true".
Extract Constant assume => "(fun _ -> lazy (Coq_go (RetF (Any.Any.upcast ()))))".
Extract Constant guarantee => "(fun _ -> lazy (Coq_go (RetF (Any.Any.upcast ()))))".

Require Import test.
        (* EchoAll *)

Cd "extract".

Separate Extraction test_itr.
         (* mw_impl_itr mw_abs_itr EXTRACT_MW_IMPL_LINKING_CHECK *)
.
         (* echo_prog *)

Cd "..".
