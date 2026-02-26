open BinInt
open BinNat
open BinNums
open Classes
open Datatypes
open List
open ListDef
open Specif
open String
open Base
open Finite

type __ = Obj.t

type 'a coq_EqbSpecPoint = 'a -> reflect

val f_equal_dec : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 dec_eq -> 'a2 dec_eq

val f_equal2_dec :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 dec_eq -> 'a2 dec_eq
  -> 'a3 dec_eq

val coq_Z_eqdec : coq_Z coq_EqDec

val string_eqdec : string coq_EqDec

val eq_dec_het :
  ('a1, 'a2) sigT coq_EqDec -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) sigT
  dec_eq

val coq_EqDecision_from_EqDec : 'a1 coq_EqDec -> ('a1, 'a1) coq_RelDecision

val coq_Finite_sigT :
  'a1 coq_EqDec -> 'a1 coq_Finite -> ('a1 -> 'a2 coq_EqDec) -> ('a1 -> 'a2
  coq_Finite) -> ('a1, 'a2) sigT coq_Finite

val coq_Finite_bool : bool coq_Finite

type coq_NatComparison =
| EQ of nat
| LT of nat * nat
| GT of nat * nat

val succ_nat_comparison : nat -> nat -> coq_NatComparison -> coq_NatComparison

val nat_compare : nat -> nat -> coq_NatComparison

type 'a coq_IsSome = __

val fromSome : 'a1 option -> 'a1 coq_IsSome -> 'a1

module Coq_option :
 sig
  val isNone : 'a1 option -> bool

  val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

  val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

  val traverse_list : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option
 end

val findAD : 'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) sigT list -> 'a2 option

val find_index_aux : ('a1 -> bool) -> 'a1 list -> nat -> nat option

val find_index : ('a1 -> bool) -> 'a1 list -> nat option

type coq_Stats = { branches : coq_N; pruned : coq_N }

val plus_stats : coq_Stats -> coq_Stats -> coq_Stats
