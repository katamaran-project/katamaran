open Datatypes
open Specif
open Base

val coq_False_dec : coq_Decision

val and_dec : coq_Decision -> coq_Decision -> coq_Decision

val bool_decide : coq_Decision -> bool
