open Datatypes
open ListDef
open Predicates
open Base

(** val heap_extractions :
    'a1 coq_IsDuplicable -> 'a1 list -> ('a1, 'a1 list) prod list **)

let rec heap_extractions h = function
| Coq_nil -> Coq_nil
| Coq_cons (c, h1) ->
  let h' = match h c with
           | Coq_true -> Coq_cons (c, h1)
           | Coq_false -> h1 in
  let ec = Coq_pair (c, h') in
  Coq_cons (ec,
  (map (prod_map (Obj.magic id) (fun x -> Coq_cons (c, x)))
    (heap_extractions h h1)))
