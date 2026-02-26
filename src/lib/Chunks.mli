open Datatypes
open ListDef
open Predicates
open Base

val heap_extractions :
  'a1 coq_IsDuplicable -> 'a1 list -> ('a1, 'a1 list) prod list
