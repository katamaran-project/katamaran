open BinNat
open BinNums
open Datatypes
open Specif
open Base

module N :
 sig
  val lt_dec : (coq_N, coq_N) coq_RelDecision
 end

module Z :
 sig
  val inhabited : coq_Z coq_Inhabited
 end
