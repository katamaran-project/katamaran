open BinNums
open BinPos
open Datatypes
open Decimal
open PosDef
open Specif

module N :
 sig
  val succ_double : coq_N -> coq_N

  val double : coq_N -> coq_N

  val sub : coq_N -> coq_N -> coq_N

  val compare : coq_N -> coq_N -> comparison

  val leb : coq_N -> coq_N -> bool

  val coq_lor : coq_N -> coq_N -> coq_N

  val coq_land : coq_N -> coq_N -> coq_N

  val coq_lxor : coq_N -> coq_N -> coq_N

  val succ : coq_N -> coq_N

  val add : coq_N -> coq_N -> coq_N

  val mul : coq_N -> coq_N -> coq_N

  val eqb : coq_N -> coq_N -> bool

  val ltb : coq_N -> coq_N -> bool

  val max : coq_N -> coq_N -> coq_N

  val pow : coq_N -> coq_N -> coq_N

  val shiftl : coq_N -> coq_N -> coq_N

  val of_nat : nat -> coq_N

  val of_uint : uint -> coq_N

  val to_uint : coq_N -> uint

  val eq_dec : coq_N -> coq_N -> sumbool
 end
