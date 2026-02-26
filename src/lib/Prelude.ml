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

(** val f_equal_dec :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 dec_eq -> 'a2 dec_eq **)

let f_equal_dec _ _ _ hyp =
  hyp

(** val f_equal2_dec :
    ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 dec_eq -> 'a2
    dec_eq -> 'a3 dec_eq **)

let f_equal2_dec _ _ _ _ _ hyp1 hyp2 =
  match hyp1 with
  | Coq_left -> hyp2
  | Coq_right -> Coq_right

(** val coq_Z_eqdec : coq_Z coq_EqDec **)

let coq_Z_eqdec =
  Z.eq_dec

(** val string_eqdec : string coq_EqDec **)

let string_eqdec =
  string_dec

(** val eq_dec_het :
    ('a1, 'a2) sigT coq_EqDec -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) sigT
    dec_eq **)

let eq_dec_het eqdec i1 i2 x1 x2 =
  eq_dec eqdec (Coq_existT (i1, x1)) (Coq_existT (i2, x2))

(** val coq_EqDecision_from_EqDec :
    'a1 coq_EqDec -> ('a1, 'a1) coq_RelDecision **)

let coq_EqDecision_from_EqDec eqdec =
  eqdec

(** val coq_Finite_sigT :
    'a1 coq_EqDec -> 'a1 coq_Finite -> ('a1 -> 'a2 coq_EqDec) -> ('a1 -> 'a2
    coq_Finite) -> ('a1, 'a2) sigT coq_Finite **)

let coq_Finite_sigT _ finA _ finB =
  fold_right (fun a xs -> app (map (fun x -> Coq_existT (a, x)) (finB a)) xs)
    [] finA

(** val coq_Finite_bool : bool coq_Finite **)

let coq_Finite_bool =
  Coq_true::(Coq_false::[])

type coq_NatComparison =
| EQ of nat
| LT of nat * nat
| GT of nat * nat

(** val succ_nat_comparison :
    nat -> nat -> coq_NatComparison -> coq_NatComparison **)

let succ_nat_comparison _ _ = function
| EQ n -> EQ (S n)
| LT (n, m) -> LT ((S n), m)
| GT (n, m) -> GT ((S n), m)

(** val nat_compare : nat -> nat -> coq_NatComparison **)

let rec nat_compare n m =
  match n with
  | O -> (match m with
          | O -> EQ O
          | S m0 -> LT (O, m0))
  | S n0 ->
    (match m with
     | O -> GT (O, n0)
     | S m0 -> succ_nat_comparison n0 m0 (nat_compare n0 m0))

type 'a coq_IsSome = __

(** val fromSome : 'a1 option -> 'a1 coq_IsSome -> 'a1 **)

let fromSome m _ =
  match m with
  | Some a -> a
  | None -> assert false (* absurd case *)

module Coq_option =
 struct
  (** val isNone : 'a1 option -> bool **)

  let isNone = function
  | Some _ -> Coq_false
  | None -> Coq_true

  (** val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

  let map f = function
  | Some a -> Some (f a)
  | None -> None

  (** val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

  let bind a f =
    match a with
    | Some x -> f x
    | None -> None

  (** val traverse_list :
      ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option **)

  let rec traverse_list f = function
  | [] -> Some []
  | x::xs0 ->
    bind (f x) (fun b -> bind (traverse_list f xs0) (fun bs -> Some (b::bs)))
 end

(** val findAD :
    'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) sigT list -> 'a2 option **)

let rec findAD eqA a = function
| [] -> None
| s::xs0 ->
  let Coq_existT (a', b) = s in
  (match eq_dec eqA a a' with
   | Coq_left -> Some b
   | Coq_right -> findAD eqA a xs0)

(** val find_index_aux : ('a1 -> bool) -> 'a1 list -> nat -> nat option **)

let rec find_index_aux p xs acc =
  match xs with
  | [] -> None
  | x::xs0 ->
    (match p x with
     | Coq_true -> Some acc
     | Coq_false -> find_index_aux p xs0 (S acc))

(** val find_index : ('a1 -> bool) -> 'a1 list -> nat option **)

let find_index p xs =
  find_index_aux p xs O

type coq_Stats = { branches : coq_N; pruned : coq_N }

(** val plus_stats : coq_Stats -> coq_Stats -> coq_Stats **)

let plus_stats x y =
  { branches = (N.add x.branches y.branches); pruned =
    (N.add x.pruned y.pruned) }
