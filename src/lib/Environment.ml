open Classes
open Context
open Datatypes
open Prelude
open Specif

type __ = Obj.t

module Coq_env =
 struct
  type ('b, 'd) coq_Env =
  | Coq_nil
  | Coq_snoc of 'b Coq_ctx.coq_Ctx * ('b, 'd) coq_Env * 'b * 'd

  (** val coq_Env_rect :
      'a3 -> ('a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a3 -> 'a1 -> 'a2
      -> 'a3) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a3 **)

  let rec coq_Env_rect f f0 _ = function
  | Coq_nil -> f
  | Coq_snoc (_UU0393_, e0, b, db) ->
    f0 _UU0393_ e0 (coq_Env_rect f f0 _UU0393_ e0) b db

  type ('b, 'd) coq_NilView =
  | Coq_isNil

  type ('b, 'd) coq_SnocView =
  | Coq_isSnoc of ('b, 'd) coq_Env * 'd

  (** val view : 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> __ **)

  let view _ = function
  | Coq_nil -> Obj.magic Coq_isNil
  | Coq_snoc (_, e0, _, v) -> Obj.magic (Coq_isSnoc (e0, v))

  (** val cat :
      'a1 Coq_ctx.coq_Ctx -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env ->
      ('a1, 'a2) coq_Env -> ('a1, 'a2) coq_Env **)

  let rec cat _UU0393_ _ e_UU0393_ = function
  | Coq_nil -> e_UU0393_
  | Coq_snoc (_UU0393_0, e, b, db) ->
    Coq_snoc ((Coq_ctx.cat _UU0393_ _UU0393_0),
      (cat _UU0393_ _UU0393_0 e_UU0393_ e), b, db)

  type ('b, 'd) coq_CatView =
  | Coq_isCat of ('b, 'd) coq_Env * ('b, 'd) coq_Env

  (** val catView :
      'a1 Coq_ctx.coq_Ctx -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env ->
      ('a1, 'a2) coq_CatView **)

  let rec catView _UU0393_ _UU0394_ e_UU0393_ =
    match _UU0394_ with
    | Coq_ctx.Coq_nil -> Coq_isCat (e_UU0393_, Coq_nil)
    | Coq_ctx.Coq_snoc (_UU0394_0, b) ->
      let Coq_isSnoc (e_UU0393__UU0394_, v) =
        Obj.magic view (Coq_ctx.Coq_snoc ((Coq_ctx.cat _UU0393_ _UU0394_0),
          b)) e_UU0393_
      in
      let Coq_isCat (e_UU0393_0, e_UU0394_) =
        catView _UU0393_ _UU0394_0 e_UU0393__UU0394_
      in
      Coq_isCat (e_UU0393_0, (Coq_snoc (_UU0394_0, e_UU0394_, b, v)))

  (** val coq_NoConfusionPackage_Env :
      ('a1 Coq_ctx.coq_Ctx * ('a1, 'a2) coq_Env) coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_Env =
    Build_NoConfusionPackage

  (** val lookup :
      'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a1 -> 'a1 Coq_ctx.coq_In
      -> 'a2 **)

  let rec lookup _ e b bIn =
    match e with
    | Coq_nil -> assert false (* absurd case *)
    | Coq_snoc (_UU0393_0, e0, b0, v) ->
      (match Obj.magic Coq_ctx.view b (Coq_ctx.Coq_snoc (_UU0393_0, b0)) bIn with
       | Coq_ctx.Coq_isZero -> v
       | Coq_ctx.Coq_isSucc (b1, i) -> lookup _UU0393_0 e0 b1 i)

  type ('b, 'd, 'q) coq_All =
  | Coq_all_nil
  | Coq_all_snoc of 'b Coq_ctx.coq_Ctx * ('b, 'd) coq_Env * 'b * 'd
     * ('b, 'd, 'q) coq_All * 'q

  (** val all_snoc_inv_1 :
      'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a2 -> ('a1, 'a2,
      'a3) coq_All -> ('a1, 'a2, 'a3) coq_All **)

  let all_snoc_inv_1 _ _ _ _ = function
  | Coq_all_nil -> assert false (* absurd case *)
  | Coq_all_snoc (_, _, _, _, a0, _) -> a0

  (** val all_snoc_inv_2 :
      'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a2 -> ('a1, 'a2,
      'a3) coq_All -> 'a3 **)

  let all_snoc_inv_2 _ _ _ _ = function
  | Coq_all_nil -> assert false (* absurd case *)
  | Coq_all_snoc (_, _, _, _, _, y) -> y

  (** val all_intro :
      ('a1 -> 'a2 -> 'a3) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env ->
      ('a1, 'a2, 'a3) coq_All **)

  let rec all_intro hQ _ = function
  | Coq_nil -> Coq_all_nil
  | Coq_snoc (_UU0393_, e0, b, db) ->
    Coq_all_snoc (_UU0393_, e0, b, db, (all_intro hQ _UU0393_ e0), (hQ b db))

  (** val eqb_hom :
      ('a1 -> 'a2 -> 'a2 -> bool) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2)
      coq_Env -> ('a1, 'a2) coq_Env -> bool **)

  let rec eqb_hom eqb _ _UU03b4_1 _UU03b4_2 =
    match _UU03b4_1 with
    | Coq_nil ->
      (match _UU03b4_2 with
       | Coq_nil -> Coq_true
       | Coq_snoc (_, _, _, _) -> assert false (* absurd case *))
    | Coq_snoc (_UU0393_, e, b, db) ->
      (match _UU03b4_2 with
       | Coq_nil -> assert false (* absurd case *)
       | Coq_snoc (_, e0, _, db0) ->
         (match eqb b db db0 with
          | Coq_true -> eqb_hom eqb _UU0393_ e e0
          | Coq_false -> Coq_false))

  (** val eqb_hom_spec_point :
      ('a1 -> 'a2 -> 'a2 -> bool) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2)
      coq_Env -> ('a1, 'a2, 'a2 coq_EqbSpecPoint) coq_All -> ('a1, 'a2)
      coq_Env coq_EqbSpecPoint **)

  let rec eqb_hom_spec_point eqb _ xs hYP ys =
    match xs with
    | Coq_nil -> ReflectT
    | Coq_snoc (_UU0393_, e, b, db) ->
      let y = view (Coq_ctx.Coq_snoc (_UU0393_, b)) ys in
      let Coq_isSnoc (e0, v) = Obj.magic y in
      let iHxs =
        eqb_hom_spec_point eqb _UU0393_ e (all_snoc_inv_1 _UU0393_ b e db hYP)
      in
      let iHb = all_snoc_inv_2 _UU0393_ b e db hYP in
      let r = iHb v in
      (match r with
       | ReflectT -> iHxs e0
       | ReflectF -> ReflectF)

  (** val eqb_hom_spec :
      ('a1 -> 'a2 -> 'a2 -> bool) -> ('a1 -> 'a2 -> 'a2 -> reflect) -> 'a1
      Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1, 'a2) coq_Env -> reflect **)

  let eqb_hom_spec eqb eqb_spec _UU0393_ _UU03b4_1 _UU03b4_2 =
    eqb_hom_spec_point eqb _UU0393_ _UU03b4_1
      (all_intro eqb_spec _UU0393_ _UU03b4_1) _UU03b4_2

  (** val tabulate :
      'a1 Coq_ctx.coq_Ctx -> ('a1 -> 'a1 Coq_ctx.coq_In -> 'a2) -> ('a1, 'a2)
      coq_Env **)

  let rec tabulate _UU0393_ x =
    match _UU0393_ with
    | Coq_ctx.Coq_nil -> Coq_nil
    | Coq_ctx.Coq_snoc (_UU0393_0, b) ->
      Coq_snoc (_UU0393_0,
        (tabulate _UU0393_0 (fun y yIn ->
          x y (Coq_ctx.in_succ y _UU0393_0 b yIn))),
        b, (x b (Coq_ctx.in_zero b _UU0393_0)))

  (** val update :
      'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a1 -> 'a1 Coq_ctx.coq_In
      -> 'a2 -> ('a1, 'a2) coq_Env **)

  let rec update _ e b bIn x =
    match e with
    | Coq_nil -> assert false (* absurd case *)
    | Coq_snoc (_UU0393_0, e0, b0, old) ->
      (match Obj.magic Coq_ctx.view b (Coq_ctx.Coq_snoc (_UU0393_0, b0)) bIn with
       | Coq_ctx.Coq_isZero -> Coq_snoc (_UU0393_0, e0, b0, x)
       | Coq_ctx.Coq_isSucc (b1, bIn0) ->
         Coq_snoc (_UU0393_0, (update _UU0393_0 e0 b1 bIn0 x), b0, old))

  (** val head : 'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a2 **)

  let head _ _ = function
  | Coq_nil -> Obj.magic Coq_tt
  | Coq_snoc (_, _, _, db) -> db

  (** val tail :
      'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> ('a1, 'a2) coq_Env **)

  let tail _ _ = function
  | Coq_nil -> Obj.magic Coq_tt
  | Coq_snoc (_, e0, _, _) -> e0

  (** val drop :
      'a1 Coq_ctx.coq_Ctx -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env ->
      ('a1, 'a2) coq_Env **)

  let rec drop _UU0393_ _UU0394_ e =
    match _UU0394_ with
    | Coq_ctx.Coq_nil -> e
    | Coq_ctx.Coq_snoc (_UU0394_0, b) ->
      drop _UU0393_ _UU0394_0
        (tail
          (let rec cat0 _UU0393_1 = function
           | Coq_ctx.Coq_nil -> _UU0393_1
           | Coq_ctx.Coq_snoc (_UU0393_3, _UU03c4_) ->
             Coq_ctx.Coq_snoc ((cat0 _UU0393_1 _UU0393_3), _UU03c4_)
           in cat0 _UU0393_ _UU0394_0)
          b e)

  (** val remove :
      'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a1 Coq_ctx.coq_In
      -> ('a1, 'a2) coq_Env **)

  let rec remove _ b e bIn =
    match e with
    | Coq_nil -> assert false (* absurd case *)
    | Coq_snoc (_UU0393_0, e0, b0, v) ->
      (match Obj.magic Coq_ctx.view b (Coq_ctx.Coq_snoc (_UU0393_0, b0)) bIn with
       | Coq_ctx.Coq_isZero -> e0
       | Coq_ctx.Coq_isSucc (b1, bIn0) ->
         Coq_snoc ((Coq_ctx.remove _UU0393_0 b1 bIn0),
           (remove _UU0393_0 b1 e0 bIn0), b0, v))

  type ('b, 'd, 'r) abstract = __

  (** val kvsnoc :
      'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1, 'a2) sigT -> ('a1,
      'a2) coq_Env **)

  let kvsnoc _UU0393_ e = function
  | Coq_existT (k, v) -> Coq_snoc (_UU0393_, e, k, v)

  (** val map :
      ('a1 -> 'a2 -> 'a3) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env ->
      ('a1, 'a3) coq_Env **)

  let rec map f _ = function
  | Coq_nil -> Coq_nil
  | Coq_snoc (_UU0393_0, e0, b, db) ->
    Coq_snoc (_UU0393_0, (map f _UU0393_0 e0), b, (f b db))
 end

module Coq_envrec =
 struct
  type ('b, 'd) coq_EnvRec = __

  (** val to_env :
      'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_EnvRec -> ('a1, 'a2)
      Coq_env.coq_Env **)

  let rec to_env _UU03c3_s x =
    match _UU03c3_s with
    | Coq_ctx.Coq_nil -> Coq_env.Coq_nil
    | Coq_ctx.Coq_snoc (_UU03c3_s0, _UU03c3_) ->
      Coq_env.Coq_snoc (_UU03c3_s0, (to_env _UU03c3_s0 (fst (Obj.magic x))),
        _UU03c3_, (snd (Obj.magic x)))

  (** val of_env :
      'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) Coq_env.coq_Env -> ('a1, 'a2)
      coq_EnvRec **)

  let rec of_env _ = function
  | Coq_env.Coq_nil -> Obj.magic Coq_tt
  | Coq_env.Coq_snoc (_UU0393_, e0, _, v) ->
    Obj.magic (Coq_pair ((of_env _UU0393_ e0), v))
 end

type ('x, 't, 'd) coq_NamedEnv =
  (('x, 't) Binding.coq_Binding, 'd) Coq_env.coq_Env

type ('x, 't, 'd, 'r) abstract_named =
  (('x, 't) Binding.coq_Binding, 'd, 'r) Coq_env.abstract
