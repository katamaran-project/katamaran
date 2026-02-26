open BinNums
open BinPos
open Datatypes

(** val plusNatPos : nat -> positive -> positive **)

let rec plusNatPos n p =
  match n with
  | O -> p
  | S n0 -> Pos.succ (plusNatPos n0 p)
