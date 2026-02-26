open Datatypes

type 'a t =
| Coq_nil
| Coq_cons of 'a * nat * 'a t
