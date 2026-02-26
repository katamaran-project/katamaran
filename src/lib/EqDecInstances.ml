open Classes
open Datatypes
open Specif

(** val unit_eqdec : coq_unit -> coq_unit -> coq_unit dec_eq **)

let unit_eqdec _ _ =
  Coq_left

(** val unit_EqDec : coq_unit coq_EqDec **)

let unit_EqDec =
  unit_eqdec

(** val bool_eqdec : bool -> bool -> bool dec_eq **)

let bool_eqdec x y =
  match x with
  | Coq_true -> (match y with
                 | Coq_true -> Coq_left
                 | Coq_false -> Coq_right)
  | Coq_false -> (match y with
                  | Coq_true -> Coq_right
                  | Coq_false -> Coq_left)

(** val bool_EqDec : bool coq_EqDec **)

let bool_EqDec =
  bool_eqdec

(** val nat_eqdec : nat -> nat -> nat dec_eq **)

let rec nat_eqdec n y =
  match n with
  | O -> (match y with
          | O -> Coq_left
          | S _ -> Coq_right)
  | S n0 -> (match y with
             | O -> Coq_right
             | S n1 -> nat_eqdec n0 n1)

(** val nat_EqDec : nat coq_EqDec **)

let nat_EqDec =
  nat_eqdec

(** val prod_eqdec :
    'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1, 'a2) prod coq_EqDec **)

let prod_eqdec h h0 x y =
  let Coq_pair (a, b) = x in
  let Coq_pair (a0, b0) = y in
  (match eq_dec_point a (coq_EqDec_EqDecPoint h a) a0 with
   | Coq_left -> eq_dec_point b (coq_EqDec_EqDecPoint h0 b) b0
   | Coq_right -> Coq_right)

(** val sum_eqdec :
    'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1, 'a2) sum coq_EqDec **)

let sum_eqdec h h0 x y =
  match x with
  | Coq_inl a ->
    (match y with
     | Coq_inl a0 -> eq_dec_point a (coq_EqDec_EqDecPoint h a) a0
     | Coq_inr _ -> Coq_right)
  | Coq_inr b ->
    (match y with
     | Coq_inl _ -> Coq_right
     | Coq_inr b0 -> eq_dec_point b (coq_EqDec_EqDecPoint h0 b) b0)

(** val list_eqdec : 'a1 coq_EqDec -> 'a1 list coq_EqDec **)

let rec list_eqdec h x y =
  match x with
  | Coq_nil ->
    (match y with
     | Coq_nil -> Coq_left
     | Coq_cons (_, _) -> Coq_right)
  | Coq_cons (y0, l) ->
    (match y with
     | Coq_nil -> Coq_right
     | Coq_cons (a, l0) ->
       (match eq_dec_point y0 (coq_EqDec_EqDecPoint h y0) a with
        | Coq_left -> list_eqdec h l l0
        | Coq_right -> Coq_right))

(** val sigma_eqdec :
    'a1 coq_EqDec -> ('a1 -> 'a2 coq_EqDec) -> ('a1, 'a2) sigT coq_EqDec **)

let sigma_eqdec h h0 x y =
  let Coq_existT (x0, p) = x in
  let Coq_existT (x1, b) = y in
  (match eq_dec_point x0 (coq_EqDec_EqDecPoint h x0) x1 with
   | Coq_left -> eq_dec_point p (coq_EqDec_EqDecPoint (h0 x1) p) b
   | Coq_right -> Coq_right)
