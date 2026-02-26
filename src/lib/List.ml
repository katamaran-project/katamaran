open Datatypes

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default = function
| Coq_nil -> default
| Coq_cons (x, _) -> x

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| Coq_nil -> Coq_nil
| Coq_cons (_, l') -> l'

(** val nth_error : 'a1 list -> nat -> 'a1 option **)

let rec nth_error l = function
| O -> (match l with
        | Coq_nil -> None
        | Coq_cons (x, _) -> Some x)
| S n0 -> (match l with
           | Coq_nil -> None
           | Coq_cons (_, l') -> nth_error l' n0)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Coq_nil -> Coq_nil
| Coq_cons (x, l') -> app (rev l') (Coq_cons (x, Coq_nil))

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | Coq_nil -> l'
  | Coq_cons (a, l0) -> rev_append l0 (Coq_cons (a, l'))

(** val rev' : 'a1 list -> 'a1 list **)

let rev' l =
  rev_append l Coq_nil

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| Coq_nil -> Coq_nil
| Coq_cons (x, l0) -> app (f x) (flat_map f l0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Coq_nil -> a0
  | Coq_cons (b, l0) -> fold_left f l0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Coq_nil -> a0
| Coq_cons (b, l0) -> f b (fold_right f a0 l0)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| Coq_nil -> Coq_false
| Coq_cons (a, l0) ->
  (match f a with
   | Coq_true -> Coq_true
   | Coq_false -> existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Coq_nil -> Coq_true
| Coq_cons (a, l0) ->
  (match f a with
   | Coq_true -> forallb f l0
   | Coq_false -> Coq_false)

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| Coq_nil -> None
| Coq_cons (x, tl0) ->
  (match f x with
   | Coq_true -> Some x
   | Coq_false -> find f tl0)
