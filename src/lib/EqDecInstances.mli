open Classes
open Datatypes
open Specif

val unit_eqdec : coq_unit -> coq_unit -> coq_unit dec_eq

val unit_EqDec : coq_unit coq_EqDec

val bool_eqdec : bool -> bool -> bool dec_eq

val bool_EqDec : bool coq_EqDec

val nat_eqdec : nat -> nat -> nat dec_eq

val nat_EqDec : nat coq_EqDec

val prod_eqdec : 'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1, 'a2) prod coq_EqDec

val sum_eqdec : 'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1, 'a2) sum coq_EqDec

val list_eqdec : 'a1 coq_EqDec -> 'a1 list coq_EqDec

val sigma_eqdec :
  'a1 coq_EqDec -> ('a1 -> 'a2 coq_EqDec) -> ('a1, 'a2) sigT coq_EqDec
