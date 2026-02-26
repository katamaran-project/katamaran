open Datatypes
open Specif
open Base

type __ = Obj.t

(** val list_fmap : (__ -> __) -> __ list -> __ list **)

let rec list_fmap f = function
| Coq_nil -> Coq_nil
| Coq_cons (x, l0) -> Coq_cons ((f x), (list_fmap f l0))

(** val elem_of_list_dec :
    ('a1, 'a1) coq_RelDecision -> ('a1, 'a1 list) coq_RelDecision **)

let rec elem_of_list_dec dec x = function
| Coq_nil -> Coq_right
| Coq_cons (y, l0) ->
  (match decide (decide_rel dec x y) with
   | Coq_left -> Coq_left
   | Coq_right -> elem_of_list_dec dec x l0)
