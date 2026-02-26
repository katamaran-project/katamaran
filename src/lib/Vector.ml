open Datatypes
open VectorDef

type 'a t = 'a VectorDef.t =
| Coq_nil
| Coq_cons of 'a * nat * 'a t

(** val map : ('a1 -> 'a2) -> nat -> 'a1 t -> 'a2 t **)

let rec map f _ = function
| Coq_nil -> Coq_nil
| Coq_cons (a, n0, v') -> Coq_cons ((f a), n0, (map f n0 v'))
