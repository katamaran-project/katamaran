open Base1
open Bitvector

module RiscvPmpIrisInstancePredicates =
 struct
  (** val write_addr : coq_Addr **)

  let write_addr =
    Coq_bv.of_N xlenbits maxAddr
 end
