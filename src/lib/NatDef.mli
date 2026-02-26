open BinNums
open PosDef

module N :
 sig
  val succ_pos : coq_N -> positive

  val coq_lor : coq_N -> coq_N -> coq_N

  val ldiff : coq_N -> coq_N -> coq_N
 end
