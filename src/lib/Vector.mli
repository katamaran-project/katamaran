open Datatypes
open VectorDef

type 'a t = 'a VectorDef.t =
| Coq_nil
| Coq_cons of 'a * nat * 'a t

val map : ('a1 -> 'a2) -> nat -> 'a1 t -> 'a2 t
