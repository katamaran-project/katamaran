open Datatypes

type 'a coq_Finite =
  'a list
  (* singleton inductive, whose constructor was Build_Finite *)

(** val unit_finite : coq_unit coq_Finite **)

let unit_finite =
  Coq_tt::[]
