open BinNums
open PosDef

module N =
 struct
  (** val succ_pos : coq_N -> positive **)

  let succ_pos = function
  | N0 -> Coq_xH
  | Npos p -> Pos.succ p

  (** val coq_lor : coq_N -> coq_N -> coq_N **)

  let coq_lor n m =
    match n with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n
                 | Npos q -> Npos (Pos.coq_lor p q))

  (** val ldiff : coq_N -> coq_N -> coq_N **)

  let ldiff n m =
    match n with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n
                 | Npos q -> Pos.ldiff p q)
 end
