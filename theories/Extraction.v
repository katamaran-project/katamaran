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

(* TODO: manually patch this constant to a record of type Base.MMIOENV as below:

+let mmioenv = { state_tra_read = (fun a b c -> failwith "called undefined state_tra_read");
+                state_tra_write = (fun a b c d -> failwith "called undefined state_tra_write");
+                state_tra_world_updates = (fun a -> failwith "called undefined state_tra_world_updates");
+                state_init = failwith "called state_init" }
Extract Constant Base.mmioenv => "fail".

*)

(* TODO: this Parameter needs replacing with a concrete value since state_init is called at some point during execution; currently the extracted verifier fails here. *)

Separate Extraction Examples.exec_VC.
