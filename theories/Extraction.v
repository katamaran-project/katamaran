From Stdlib Require Extraction.

From Katamaran Require Import BlockVer.Examples.

Extraction Language OCaml.

Set Extraction Output Directory "src/lib".

(* breaks otherwise *)
Set Extraction KeepSingleton.


(* TODO: figure out why coq_Pred, coq_SHeapSpec and coq_CHeapSpec are defined too far down the mli *)

Recursive Extraction Examples.exec_VC.
Extraction "BlockVerifier" Examples.exec_VC.
