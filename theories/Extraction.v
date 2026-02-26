From Stdlib Require Extraction.

From Katamaran Require Import BlockVer.Examples.

Extraction Language OCaml.

Set Extraction Output Directory "src/lib".

(* Extract Inductive nat => "int" [ "0" "succ" ]. *)
(* Extract Inductive bool => "bool" [ "true" "false" ]. *)
(* Extract Inductive unit => "unit" [ "()" ]. *)
(* Extract Inductive list => "list" [ "[]" "(::)" ]. *)
(* the below definition should not have spaces around the asterisk (prod type constructor) but if you remove them then proof general cannot advance the proof cursor............................. *)
(* Extract Inductive prod => "( * )" [ "(,)" ]. *)

(* (* Unsound for big nats *) *)
(* Extract Inductive nat => int [ "0" "succ" ] *)
(*    "(fun fO fS n -> if n=0 then fO () else fS (n-1))". *)

(* Extract Inlined Constant Nat.add => "( + )". *)

(* breaks otherwise *)
(* Set Extraction KeepSingleton. *)


(* TODO: figure out why coq_Pred, coq_SHeapSpec and coq_CHeapSpec are defined too far down the mli *)

(* TODO: currently need to apply a patch that removes from the extracted code in Base1.ml and Base1.mli the following definitions:
   - type MMIOENV
   - Parameter mmioenv
   - fun_read_mmio
   - fun_write_mmio *)

(* TODO: stub this better *)
Extract Constant Base.mmioenv => "fail".

Separate Extraction Examples.exec_VC.
