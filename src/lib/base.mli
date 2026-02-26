open Datatypes
open Specif

type __ = Obj.t

type coq_Decision = sumbool

val decide : coq_Decision -> sumbool

type ('a, 'b) coq_RelDecision = 'a -> 'b -> coq_Decision

val decide_rel : ('a1, 'a2) coq_RelDecision -> 'a1 -> 'a2 -> coq_Decision

type 'a coq_Inhabited =
  'a
  (* singleton inductive, whose constructor was populate *)

val list_inhabited : 'a1 list coq_Inhabited

val bool_inhabated : bool coq_Inhabited

val unit_inhabited : coq_unit coq_Inhabited

val prod_map :
  ('a1 -> 'a2) -> ('a3 -> 'a4) -> ('a1, 'a3) prod -> ('a2, 'a4) prod

val prod_inhabited :
  'a1 coq_Inhabited -> 'a2 coq_Inhabited -> ('a1, 'a2) prod coq_Inhabited

val sum_inhabited_r : 'a2 coq_Inhabited -> ('a1, 'a2) sum coq_Inhabited

type 'a coq_Union = 'a -> 'a -> 'a

val union : 'a1 coq_Union -> 'a1 -> 'a1 -> 'a1

type 'm coq_FMap = __ -> __ -> (__ -> __) -> 'm -> 'm

val fmap : 'a1 coq_FMap -> ('a2 -> 'a3) -> 'a1 -> 'a1

type ('a, 'm) coq_UnionWith = ('a -> 'a -> 'a option) -> 'm -> 'm -> 'm

val union_with :
  ('a1, 'a2) coq_UnionWith -> ('a1 -> 'a1 -> 'a1 option) -> 'a2 -> 'a2 -> 'a2
