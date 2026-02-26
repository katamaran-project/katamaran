open BinInt
open BinNat
open BinNums
open Classes
open Datatypes
open ListDef
open Nat
open Base
open Finite
open List_numbers

type __ = Obj.t

module Coq_bv :
 sig
  type bv = coq_N
    (* singleton inductive, whose constructor was mk *)

  val bin : nat -> bv -> coq_N

  val eqb : nat -> bv -> bv -> bool

  val eqdec_bv : nat -> bv coq_EqDec

  val trunc : nat -> positive -> coq_N

  val truncn : nat -> coq_N -> coq_N

  val of_N : nat -> coq_N -> bv

  val of_nat : nat -> nat -> bv

  val nil : bv

  val cons : nat -> bool -> bv -> bv

  val bv_case : 'a1 -> (nat -> bool -> bv -> 'a1) -> nat -> bv -> 'a1

  val fold_right : (nat -> bool -> 'a1 -> 'a1) -> 'a1 -> nat -> bv -> 'a1

  val fold_left : (nat -> 'a1 -> bool -> 'a1) -> 'a1 -> nat -> bv -> 'a1

  type coq_NilView =
  | Coq_nvnil

  type coq_ConsView =
  | Coq_cvcons of bool * bv

  val view : nat -> bv -> __

  val app : nat -> nat -> bv -> bv -> bv

  type coq_AppView =
  | Coq_isapp of bv * bv

  val avcons : nat -> nat -> bool -> bv -> coq_AppView -> coq_AppView

  val appView : nat -> nat -> bv -> coq_AppView

  val zero : nat -> bv

  val one : nat -> bv

  val onesp : nat -> positive

  val onesn : nat -> coq_N

  val ones : nat -> bv

  val bv_inhabited : nat -> bv coq_Inhabited

  val msbwithcarry : nat -> bool -> bv -> bool

  val msb : nat -> bv -> bool

  val sext' : nat -> bv -> nat -> bv

  val zext' : nat -> bv -> nat -> bv

  type coq_LeView = nat
    (* singleton inductive, whose constructor was is_le *)

  val leview : nat -> nat -> coq_LeView

  val sext : nat -> bv -> nat -> bv

  val zext : nat -> bv -> nat -> bv

  val truncate : nat -> nat -> bv -> bv

  val unsigned : nat -> bv -> coq_Z

  val signed : nat -> bv -> coq_Z

  val truncz : nat -> coq_Z -> coq_Z

  val of_Z : nat -> coq_Z -> bv

  val drop : nat -> nat -> bv -> bv

  val take : nat -> nat -> bv -> bv

  val vector_subrange : nat -> nat -> nat -> bv -> bv

  val update_vector_subrange : nat -> nat -> nat -> bv -> bv -> bv

  val shiftr : nat -> nat -> bv -> bv -> bv

  val shiftl : nat -> nat -> bv -> bv -> bv

  val add : nat -> bv -> bv -> bv

  val negate : nat -> bv -> bv

  val sub : nat -> bv -> bv -> bv

  val mul : nat -> bv -> bv -> bv

  val uleb : nat -> bv -> bv -> bool

  val ultb : nat -> bv -> bv -> bool

  val sleb : nat -> bv -> bv -> bool

  val sltb : nat -> bv -> bv -> bool

  val coq_land : nat -> bv -> bv -> bv

  val coq_lor : nat -> bv -> bv -> bv

  val coq_lxor : nat -> bv -> bv -> bv

  val notp : nat -> positive -> coq_N

  val notn : nat -> coq_N -> coq_N

  val not : nat -> bv -> bv

  module Coq_finite :
   sig
    val enumV : (nat -> bool -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 list

    val enum : nat -> bv list

    val finite_bv : nat -> bv coq_Finite
   end

  module Coq_bitstring :
   sig
    type null =
    | Coq_bN

    type 'a digit =
    | Coq_bO of 'a
    | Coq_bI of 'a
   end

  type bitstring = __

  val bitstring_zeroes : nat -> bitstring

  val fold_left_nat : (nat -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1

  val fold_left_positive :
    (nat -> 'a1 -> 'a1) -> (nat -> 'a1 -> 'a1) -> 'a1 -> nat -> positive ->
    'a1

  val to_bitstring : nat -> bv -> bitstring

  val fold_bitstring_left :
    (nat -> 'a1 -> bool -> 'a1) -> 'a1 -> nat -> bitstring -> 'a1

  val of_bitstring : nat -> bitstring -> bv

  val seqBv : nat -> bv -> coq_N -> bv list
 end
