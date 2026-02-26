open Datatypes

type 't coq_IsDuplicable =
  't -> bool
  (* singleton inductive, whose constructor was Build_IsDuplicable *)
