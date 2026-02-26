open Datatypes
open Specif
open Base

(** val coq_False_dec : coq_Decision **)

let coq_False_dec =
  Coq_right

(** val and_dec : coq_Decision -> coq_Decision -> coq_Decision **)

let and_dec p_dec q_dec =
  match p_dec with
  | Coq_left -> q_dec
  | Coq_right -> Coq_right

(** val bool_decide : coq_Decision -> bool **)

let bool_decide = function
| Coq_left -> Coq_true
| Coq_right -> Coq_false
