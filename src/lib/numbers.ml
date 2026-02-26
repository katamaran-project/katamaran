open BinNat
open BinNums
open Datatypes
open Specif
open Base

module N =
 struct
  (** val lt_dec : (coq_N, coq_N) coq_RelDecision **)

  let lt_dec x y =
    let filtered_var = N.compare x y in
    (match filtered_var with
     | Lt -> Coq_left
     | _ -> Coq_right)
 end

module Z =
 struct
  (** val inhabited : coq_Z coq_Inhabited **)

  let inhabited =
    Zpos Coq_xH
 end
