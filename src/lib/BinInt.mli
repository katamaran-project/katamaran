open BinNums
open BinPos
open Datatypes
open NatDef
open PosDef
open Specif

module Z :
 sig
  val double : coq_Z -> coq_Z

  val succ_double : coq_Z -> coq_Z

  val pred_double : coq_Z -> coq_Z

  val pos_sub : positive -> positive -> coq_Z

  val add : coq_Z -> coq_Z -> coq_Z

  val opp : coq_Z -> coq_Z

  val sub : coq_Z -> coq_Z -> coq_Z

  val mul : coq_Z -> coq_Z -> coq_Z

  val pow_pos : coq_Z -> positive -> coq_Z

  val pow : coq_Z -> coq_Z -> coq_Z

  val compare : coq_Z -> coq_Z -> comparison

  val leb : coq_Z -> coq_Z -> bool

  val ltb : coq_Z -> coq_Z -> bool

  val eqb : coq_Z -> coq_Z -> bool

  val to_nat : coq_Z -> nat

  val of_nat : nat -> coq_Z

  val of_N : coq_N -> coq_Z

  val pos_div_eucl : positive -> coq_Z -> (coq_Z, coq_Z) prod

  val div_eucl : coq_Z -> coq_Z -> (coq_Z, coq_Z) prod

  val modulo : coq_Z -> coq_Z -> coq_Z

  val div2 : coq_Z -> coq_Z

  val shiftl : coq_Z -> coq_Z -> coq_Z

  val shiftr : coq_Z -> coq_Z -> coq_Z

  val coq_land : coq_Z -> coq_Z -> coq_Z

  val to_N : coq_Z -> coq_N

  val eq_dec : coq_Z -> coq_Z -> sumbool
 end
