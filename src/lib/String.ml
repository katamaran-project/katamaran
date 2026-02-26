open Ascii
open Datatypes
open Specif

type string =
| EmptyString
| String of ascii * string

(** val string_dec : string -> string -> sumbool **)

let rec string_dec s x =
  match s with
  | EmptyString ->
    (match x with
     | EmptyString -> Coq_left
     | String (_, _) -> Coq_right)
  | String (a, s0) ->
    (match x with
     | EmptyString -> Coq_right
     | String (a0, s1) ->
       (match ascii_dec a a0 with
        | Coq_left -> string_dec s0 s1
        | Coq_right -> Coq_right))

(** val eqb : string -> string -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> Coq_true
     | String (_, _) -> Coq_false)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> Coq_false
     | String (c2, s2') ->
       (match Ascii.eqb c1 c2 with
        | Coq_true -> eqb s1' s2'
        | Coq_false -> Coq_false))

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))
