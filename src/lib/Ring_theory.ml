open BinNums

(** val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let rec pow_pos rmul x = function
| Coq_xI i0 -> let p = pow_pos rmul x i0 in rmul x (rmul p p)
| Coq_xO i0 -> let p = pow_pos rmul x i0 in rmul p p
| Coq_xH -> x

(** val pow_N : 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> coq_N -> 'a1 **)

let pow_N rI rmul x = function
| N0 -> rI
| Npos p0 -> pow_pos rmul x p0

(** val id_phi_N : coq_N -> coq_N **)

let id_phi_N x =
  x
