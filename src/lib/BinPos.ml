open BinNums
open Datatypes
open Decimal
open Specif

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | Coq_xI p -> Coq_xO (succ p)
  | Coq_xO p -> Coq_xI p
  | Coq_xH -> Coq_xO Coq_xH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> Coq_xO (add_carry p q)
       | Coq_xO q -> Coq_xI (add p q)
       | Coq_xH -> Coq_xO (succ p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> Coq_xI (add p q)
       | Coq_xO q -> Coq_xO (add p q)
       | Coq_xH -> Coq_xI p)
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Coq_xO (succ q)
       | Coq_xO q -> Coq_xI q
       | Coq_xH -> Coq_xO Coq_xH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> Coq_xI (add_carry p q)
       | Coq_xO q -> Coq_xO (add_carry p q)
       | Coq_xH -> Coq_xI (succ p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> Coq_xO (add_carry p q)
       | Coq_xO q -> Coq_xI (add p q)
       | Coq_xH -> Coq_xO (succ p))
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Coq_xI (succ q)
       | Coq_xO q -> Coq_xO (succ q)
       | Coq_xH -> Coq_xI Coq_xH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | Coq_xI p -> Coq_xI (Coq_xO p)
  | Coq_xO p -> Coq_xI (pred_double p)
  | Coq_xH -> Coq_xH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | Coq_xI p -> add y (Coq_xO (mul p y))
    | Coq_xO p -> Coq_xO (mul p y)
    | Coq_xH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | Coq_xI n' -> f (iter f (iter f x n') n')
  | Coq_xO n' -> iter f (iter f x n') n'
  | Coq_xH -> f x

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> compare_cont r p q
       | Coq_xO q -> compare_cont Gt p q
       | Coq_xH -> Gt)
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> compare_cont Lt p q
       | Coq_xO q -> compare_cont r p q
       | Coq_xH -> Gt)
    | Coq_xH -> (match y with
                 | Coq_xH -> r
                 | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val leb : positive -> positive -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> Coq_false
    | _ -> Coq_true

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> Coq_xH
  | S x -> succ (of_succ_nat x)

  (** val pow : positive -> positive -> positive **)

  let pow x =
    iter (mul x) Coq_xH

  (** val shiftl : positive -> coq_N -> positive **)

  let shiftl p = function
  | N0 -> p
  | Npos n0 -> iter (fun x -> Coq_xO x) p n0

  (** val of_uint_acc : uint -> positive -> positive **)

  let rec of_uint_acc d acc =
    match d with
    | Nil -> acc
    | D0 l -> of_uint_acc l (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc)
    | D1 l ->
      of_uint_acc l (add Coq_xH (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | D2 l ->
      of_uint_acc l
        (add (Coq_xO Coq_xH) (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | D3 l ->
      of_uint_acc l
        (add (Coq_xI Coq_xH) (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | D4 l ->
      of_uint_acc l
        (add (Coq_xO (Coq_xO Coq_xH))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | D5 l ->
      of_uint_acc l
        (add (Coq_xI (Coq_xO Coq_xH))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | D6 l ->
      of_uint_acc l
        (add (Coq_xO (Coq_xI Coq_xH))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | D7 l ->
      of_uint_acc l
        (add (Coq_xI (Coq_xI Coq_xH))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | D8 l ->
      of_uint_acc l
        (add (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | D9 l ->
      of_uint_acc l
        (add (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))

  (** val of_uint : uint -> coq_N **)

  let rec of_uint = function
  | Nil -> N0
  | D0 l -> of_uint l
  | D1 l -> Npos (of_uint_acc l Coq_xH)
  | D2 l -> Npos (of_uint_acc l (Coq_xO Coq_xH))
  | D3 l -> Npos (of_uint_acc l (Coq_xI Coq_xH))
  | D4 l -> Npos (of_uint_acc l (Coq_xO (Coq_xO Coq_xH)))
  | D5 l -> Npos (of_uint_acc l (Coq_xI (Coq_xO Coq_xH)))
  | D6 l -> Npos (of_uint_acc l (Coq_xO (Coq_xI Coq_xH)))
  | D7 l -> Npos (of_uint_acc l (Coq_xI (Coq_xI Coq_xH)))
  | D8 l -> Npos (of_uint_acc l (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  | D9 l -> Npos (of_uint_acc l (Coq_xI (Coq_xO (Coq_xO Coq_xH))))

  (** val to_little_uint : positive -> uint **)

  let rec to_little_uint = function
  | Coq_xI p0 -> Little.succ_double (to_little_uint p0)
  | Coq_xO p0 -> Little.double (to_little_uint p0)
  | Coq_xH -> D1 Nil

  (** val to_uint : positive -> uint **)

  let to_uint p =
    rev (to_little_uint p)

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | Coq_xI p0 -> (match x0 with
                    | Coq_xI p1 -> eq_dec p0 p1
                    | _ -> Coq_right)
    | Coq_xO p0 -> (match x0 with
                    | Coq_xO p1 -> eq_dec p0 p1
                    | _ -> Coq_right)
    | Coq_xH -> (match x0 with
                 | Coq_xH -> Coq_left
                 | _ -> Coq_right)
 end
