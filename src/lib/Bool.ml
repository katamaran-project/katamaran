open Datatypes
open Specif

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | Coq_true -> (match b2 with
                 | Coq_true -> Coq_left
                 | Coq_false -> Coq_right)
  | Coq_false -> (match b2 with
                  | Coq_true -> Coq_right
                  | Coq_false -> Coq_left)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | Coq_true -> b2
  | Coq_false -> (match b2 with
                  | Coq_true -> Coq_false
                  | Coq_false -> Coq_true)

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| Coq_true -> ReflectT
| Coq_false -> ReflectF
