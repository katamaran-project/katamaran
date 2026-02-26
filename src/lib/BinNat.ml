open BinNums
open BinPos
open Datatypes
open Decimal
open PosDef
open Specif

module N =
 struct
  (** val succ_double : coq_N -> coq_N **)

  let succ_double = function
  | N0 -> Npos Coq_xH
  | Npos p -> Npos (Coq_xI p)

  (** val double : coq_N -> coq_N **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (Coq_xO p)

  (** val sub : coq_N -> coq_N -> coq_N **)

  let sub n m =
    match n with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n
       | Npos m' ->
         (match Pos.sub_mask n' m' with
          | Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val compare : coq_N -> coq_N -> comparison **)

  let compare n m =
    match n with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Pos.compare n' m')

  (** val leb : coq_N -> coq_N -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> Coq_false
    | _ -> Coq_true

  (** val coq_lor : coq_N -> coq_N -> coq_N **)

  let coq_lor n m =
    match n with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n
                 | Npos q -> Npos (Pos.coq_lor p q))

  (** val coq_land : coq_N -> coq_N -> coq_N **)

  let coq_land n m =
    match n with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Pos.coq_land p q)

  (** val coq_lxor : coq_N -> coq_N -> coq_N **)

  let coq_lxor n m =
    match n with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n
                 | Npos q -> Pos.coq_lxor p q)

  (** val succ : coq_N -> coq_N **)

  let succ = function
  | N0 -> Npos Coq_xH
  | Npos p -> Npos (Pos.succ p)

  (** val add : coq_N -> coq_N -> coq_N **)

  let add n m =
    match n with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n
                 | Npos q -> Npos (BinPos.Pos.add p q))

  (** val mul : coq_N -> coq_N -> coq_N **)

  let mul n m =
    match n with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (BinPos.Pos.mul p q))

  (** val eqb : coq_N -> coq_N -> bool **)

  let eqb n m =
    match n with
    | N0 -> (match m with
             | N0 -> Coq_true
             | Npos _ -> Coq_false)
    | Npos p -> (match m with
                 | N0 -> Coq_false
                 | Npos q -> Pos.eqb p q)

  (** val ltb : coq_N -> coq_N -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> Coq_true
    | _ -> Coq_false

  (** val max : coq_N -> coq_N -> coq_N **)

  let max n n' =
    match compare n n' with
    | Gt -> n
    | _ -> n'

  (** val pow : coq_N -> coq_N -> coq_N **)

  let pow n = function
  | N0 -> Npos Coq_xH
  | Npos p0 -> (match n with
                | N0 -> N0
                | Npos q -> Npos (BinPos.Pos.pow q p0))

  (** val shiftl : coq_N -> coq_N -> coq_N **)

  let shiftl a n =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (BinPos.Pos.shiftl a0 n)

  (** val of_nat : nat -> coq_N **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Pos.of_succ_nat n')

  (** val of_uint : uint -> coq_N **)

  let of_uint =
    BinPos.Pos.of_uint

  (** val to_uint : coq_N -> uint **)

  let to_uint = function
  | N0 -> D0 Nil
  | Npos p -> BinPos.Pos.to_uint p

  (** val eq_dec : coq_N -> coq_N -> sumbool **)

  let eq_dec n m =
    match n with
    | N0 -> (match m with
             | N0 -> Coq_left
             | Npos _ -> Coq_right)
    | Npos p ->
      (match m with
       | N0 -> Coq_right
       | Npos p0 -> BinPos.Pos.eq_dec p p0)
 end
