open BinNums
open List

(** val jump : positive -> 'a1 list -> 'a1 list **)

let rec jump p l =
  match p with
  | Coq_xI p0 -> jump p0 (jump p0 (tl l))
  | Coq_xO p0 -> jump p0 (jump p0 l)
  | Coq_xH -> tl l

(** val nth : 'a1 -> positive -> 'a1 list -> 'a1 **)

let rec nth default p l =
  match p with
  | Coq_xI p0 -> nth default p0 (jump p0 (tl l))
  | Coq_xO p0 -> nth default p0 (jump p0 l)
  | Coq_xH -> hd default l
