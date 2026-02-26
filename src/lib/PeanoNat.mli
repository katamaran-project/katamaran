open Bool
open Datatypes

module Nat :
 sig
  val add : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val eqb_spec : nat -> nat -> reflect
 end
