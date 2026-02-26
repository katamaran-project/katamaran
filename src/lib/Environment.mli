open Classes
open Context
open Datatypes
open Prelude
open Specif

type __ = Obj.t

module Coq_env :
 sig
  type ('b, 'd) coq_Env =
  | Coq_nil
  | Coq_snoc of 'b Coq_ctx.coq_Ctx * ('b, 'd) coq_Env * 'b * 'd

  val coq_Env_rect :
    'a3 -> ('a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a3 -> 'a1 -> 'a2 ->
    'a3) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a3

  type ('b, 'd) coq_NilView =
  | Coq_isNil

  type ('b, 'd) coq_SnocView =
  | Coq_isSnoc of ('b, 'd) coq_Env * 'd

  val view : 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> __

  val cat :
    'a1 Coq_ctx.coq_Ctx -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1,
    'a2) coq_Env -> ('a1, 'a2) coq_Env

  type ('b, 'd) coq_CatView =
  | Coq_isCat of ('b, 'd) coq_Env * ('b, 'd) coq_Env

  val catView :
    'a1 Coq_ctx.coq_Ctx -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1,
    'a2) coq_CatView

  val coq_NoConfusionPackage_Env :
    ('a1 Coq_ctx.coq_Ctx * ('a1, 'a2) coq_Env) coq_NoConfusionPackage

  val lookup :
    'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a1 -> 'a1 Coq_ctx.coq_In ->
    'a2

  type ('b, 'd, 'q) coq_All =
  | Coq_all_nil
  | Coq_all_snoc of 'b Coq_ctx.coq_Ctx * ('b, 'd) coq_Env * 'b * 'd
     * ('b, 'd, 'q) coq_All * 'q

  val all_snoc_inv_1 :
    'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a2 -> ('a1, 'a2,
    'a3) coq_All -> ('a1, 'a2, 'a3) coq_All

  val all_snoc_inv_2 :
    'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a2 -> ('a1, 'a2,
    'a3) coq_All -> 'a3

  val all_intro :
    ('a1 -> 'a2 -> 'a3) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1,
    'a2, 'a3) coq_All

  val eqb_hom :
    ('a1 -> 'a2 -> 'a2 -> bool) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env
    -> ('a1, 'a2) coq_Env -> bool

  val eqb_hom_spec_point :
    ('a1 -> 'a2 -> 'a2 -> bool) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env
    -> ('a1, 'a2, 'a2 coq_EqbSpecPoint) coq_All -> ('a1, 'a2) coq_Env
    coq_EqbSpecPoint

  val eqb_hom_spec :
    ('a1 -> 'a2 -> 'a2 -> bool) -> ('a1 -> 'a2 -> 'a2 -> reflect) -> 'a1
    Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1, 'a2) coq_Env -> reflect

  val tabulate :
    'a1 Coq_ctx.coq_Ctx -> ('a1 -> 'a1 Coq_ctx.coq_In -> 'a2) -> ('a1, 'a2)
    coq_Env

  val update :
    'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a1 -> 'a1 Coq_ctx.coq_In ->
    'a2 -> ('a1, 'a2) coq_Env

  val head : 'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a2

  val tail :
    'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> ('a1, 'a2) coq_Env

  val drop :
    'a1 Coq_ctx.coq_Ctx -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1,
    'a2) coq_Env

  val remove :
    'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a1 Coq_ctx.coq_In ->
    ('a1, 'a2) coq_Env

  type ('b, 'd, 'r) abstract = __

  val kvsnoc :
    'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1, 'a2) sigT -> ('a1,
    'a2) coq_Env

  val map :
    ('a1 -> 'a2 -> 'a3) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1,
    'a3) coq_Env
 end

module Coq_envrec :
 sig
  type ('b, 'd) coq_EnvRec = __

  val to_env :
    'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_EnvRec -> ('a1, 'a2) Coq_env.coq_Env

  val of_env :
    'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) Coq_env.coq_Env -> ('a1, 'a2) coq_EnvRec
 end

type ('x, 't, 'd) coq_NamedEnv =
  (('x, 't) Binding.coq_Binding, 'd) Coq_env.coq_Env

type ('x, 't, 'd, 'r) abstract_named =
  (('x, 't) Binding.coq_Binding, 'd, 'r) Coq_env.abstract
