open Datatypes
open Base

(** val option_union_with : ('a1, 'a1 option) coq_UnionWith **)

let option_union_with f mx my =
  match mx with
  | Some x -> (match my with
               | Some y -> f x y
               | None -> Some x)
  | None -> my

(** val option_union : 'a1 option coq_Union **)

let option_union x =
  union_with option_union_with (fun x0 _ -> Some x0) x
