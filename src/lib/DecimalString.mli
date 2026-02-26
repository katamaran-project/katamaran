open Ascii
open Datatypes
open Decimal
open String

val uint_of_char : ascii -> uint option -> uint option

module NilEmpty :
 sig
  val string_of_uint : uint -> string

  val uint_of_string : string -> uint option
 end
