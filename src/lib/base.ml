open Datatypes
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_Decision = sumbool

(** val decide : coq_Decision -> sumbool **)

let decide decision =
  decision

type ('a, 'b) coq_RelDecision = 'a -> 'b -> coq_Decision

(** val decide_rel :
    ('a1, 'a2) coq_RelDecision -> 'a1 -> 'a2 -> coq_Decision **)

let decide_rel relDecision =
  relDecision

type 'a coq_Inhabited =
  'a
  (* singleton inductive, whose constructor was populate *)

(** val list_inhabited : 'a1 list coq_Inhabited **)

let list_inhabited =
  Coq_nil

(** val bool_inhabated : bool coq_Inhabited **)

let bool_inhabated =
  Coq_true

(** val unit_inhabited : coq_unit coq_Inhabited **)

let unit_inhabited =
  Coq_tt

(** val prod_map :
    ('a1 -> 'a2) -> ('a3 -> 'a4) -> ('a1, 'a3) prod -> ('a2, 'a4) prod **)

let prod_map f g p =
  Coq_pair ((f (fst p)), (g (snd p)))

(** val prod_inhabited :
    'a1 coq_Inhabited -> 'a2 coq_Inhabited -> ('a1, 'a2) prod coq_Inhabited **)

let prod_inhabited iA iB =
  Coq_pair (iA, iB)

(** val sum_inhabited_r :
    'a2 coq_Inhabited -> ('a1, 'a2) sum coq_Inhabited **)

let sum_inhabited_r iB =
  Coq_inr iB

type 'a coq_Union = 'a -> 'a -> 'a

(** val union : 'a1 coq_Union -> 'a1 -> 'a1 -> 'a1 **)

let union union0 =
  union0

type 'm coq_FMap = __ -> __ -> (__ -> __) -> 'm -> 'm

(** val fmap : 'a1 coq_FMap -> ('a2 -> 'a3) -> 'a1 -> 'a1 **)

let fmap fMap x x0 =
  Obj.magic fMap __ __ x x0

type ('a, 'm) coq_UnionWith = ('a -> 'a -> 'a option) -> 'm -> 'm -> 'm

(** val union_with :
    ('a1, 'a2) coq_UnionWith -> ('a1 -> 'a1 -> 'a1 option) -> 'a2 -> 'a2 ->
    'a2 **)

let union_with unionWith =
  unionWith
