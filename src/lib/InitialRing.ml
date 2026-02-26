open BinNums
open Datatypes

(** val get_signZ : coq_Z -> coq_Z option **)

let get_signZ = function
| Zneg p -> Some (Zpos p)
| _ -> None
