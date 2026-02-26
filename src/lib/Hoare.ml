open Datatypes

module type FailLogic =
 sig
  val fail_rule_pre : bool
 end

module DefaultFailLogic =
 struct
  (** val fail_rule_pre : bool **)

  let fail_rule_pre =
    Coq_true
 end
