open Datatypes

type __ = Obj.t

type chain =
  nat -> __
  (* singleton inductive, whose constructor was Build_chain *)

type coq_Cofe =
  chain -> __
  (* singleton inductive, whose constructor was Build_Cofe *)

(** val discrete_cofe : __ -> coq_Cofe **)

let discrete_cofe _ c =
  c O
