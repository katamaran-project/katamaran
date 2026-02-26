open Datatypes

module type FailLogic =
 sig
  val fail_rule_pre : bool
 end

module DefaultFailLogic :
 sig
  val fail_rule_pre : bool
 end
