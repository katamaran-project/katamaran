open BinInt
open BinNums
open Datatypes
open ListDef
open Base
open List0

(** val seqZ : coq_Z -> coq_Z -> coq_Z list **)

let seqZ m len =
  fmap (Obj.magic (fun _ _ -> list_fmap)) (fun i -> Z.add (Z.of_nat i) m)
    (Obj.magic seq O (Z.to_nat len))
