open Datatypes
open Specif
open Base

type __ = Obj.t

val list_fmap : (__ -> __) -> __ list -> __ list

val elem_of_list_dec :
  ('a1, 'a1) coq_RelDecision -> ('a1, 'a1 list) coq_RelDecision
