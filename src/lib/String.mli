open Ascii
open Datatypes
open Specif

type string =
| EmptyString
| String of ascii * string

val string_dec : string -> string -> sumbool

val eqb : string -> string -> bool

val append : string -> string -> string
