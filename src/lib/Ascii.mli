open Bool
open Datatypes
open Specif

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val ascii_dec : ascii -> ascii -> sumbool

val eqb : ascii -> ascii -> bool
