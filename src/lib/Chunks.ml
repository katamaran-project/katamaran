open Datatypes
open ListDef
open Predicates
open Base

(** val heap_extractions :
    'a1 coq_IsDuplicable -> 'a1 list -> ('a1, 'a1 list) prod list **)

let rec heap_extractions h = function
| [] -> []
| c::h1 ->
  let h' = match h c with
           | Coq_true -> c::h1
           | Coq_false -> h1 in
  let ec = Coq_pair (c, h') in
  ec::(map (prod_map (Obj.magic id) (fun x -> c::x)) (heap_extractions h h1))
