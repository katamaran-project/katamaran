open BinNums
open Datatypes
open Decimal
open Specif

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val leb : positive -> positive -> bool

  val of_succ_nat : nat -> positive

  val pow : positive -> positive -> positive

  val shiftl : positive -> coq_N -> positive

  val of_uint_acc : uint -> positive -> positive

  val of_uint : uint -> coq_N

  val to_little_uint : positive -> uint

  val to_uint : positive -> uint

  val eq_dec : positive -> positive -> sumbool
 end
