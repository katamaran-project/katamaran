open Ascii
open Base1
open Basics
open BinInt
open BinNat
open BinNums
open BinOps
open BinPos
open Bitvector
open Bool
open CRelationClasses
open Chunks
open Classes
open Context
open Datatypes
open Environment
open EqDecInstances
open EqdepFacts
open List
open Nat
open PmpCheck
open Predicates
open Prelude
open Specif
open String
open TypeDecl
open UnOps
open Variables
open Base
open Finite
open Interface
open Modalities
open Ofe

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_PurePredicate =
| Coq_gen_pmp_access
| Coq_pmp_access
| Coq_pmp_check_perms
| Coq_pmp_check_rwx
| Coq_sub_perm
| Coq_access_pmp_perm
| Coq_within_cfg
| Coq_not_within_cfg
| Coq_prev_addr
| Coq_in_entries
| Coq_in_mmio of nat

type coq_Exec =
| Left
| Right

type coq_Predicate =
| Coq_pmp_entries
| Coq_pmp_addr_access
| Coq_pmp_addr_access_without of nat
| Coq_gprs
| Coq_ptsto
| Coq_ptsto_one of coq_Exec
| Coq_ptstomem_readonly of nat
| Coq_inv_mmio of nat
| Coq_mmio_checked_write of nat
| Coq_encodes_instr
| Coq_ptstomem of nat
| Coq_ptstoinstr

(** val coq_PurePredicate_eqdec :
    coq_PurePredicate -> coq_PurePredicate -> coq_PurePredicate dec_eq **)

let coq_PurePredicate_eqdec x y =
  match x with
  | Coq_gen_pmp_access ->
    (match y with
     | Coq_gen_pmp_access -> Coq_left
     | _ -> Coq_right)
  | Coq_pmp_access ->
    (match y with
     | Coq_pmp_access -> Coq_left
     | _ -> Coq_right)
  | Coq_pmp_check_perms ->
    (match y with
     | Coq_pmp_check_perms -> Coq_left
     | _ -> Coq_right)
  | Coq_pmp_check_rwx ->
    (match y with
     | Coq_pmp_check_rwx -> Coq_left
     | _ -> Coq_right)
  | Coq_sub_perm -> (match y with
                     | Coq_sub_perm -> Coq_left
                     | _ -> Coq_right)
  | Coq_access_pmp_perm ->
    (match y with
     | Coq_access_pmp_perm -> Coq_left
     | _ -> Coq_right)
  | Coq_within_cfg ->
    (match y with
     | Coq_within_cfg -> Coq_left
     | _ -> Coq_right)
  | Coq_not_within_cfg ->
    (match y with
     | Coq_not_within_cfg -> Coq_left
     | _ -> Coq_right)
  | Coq_prev_addr -> (match y with
                      | Coq_prev_addr -> Coq_left
                      | _ -> Coq_right)
  | Coq_in_entries ->
    (match y with
     | Coq_in_entries -> Coq_left
     | _ -> Coq_right)
  | Coq_in_mmio bytes ->
    (match y with
     | Coq_in_mmio bytes0 ->
       eq_dec_point bytes (coq_EqDec_EqDecPoint nat_EqDec bytes) bytes0
     | _ -> Coq_right)

(** val coq_Exec_eqdec : coq_Exec -> coq_Exec -> coq_Exec dec_eq **)

let coq_Exec_eqdec x y =
  match x with
  | Left -> (match y with
             | Left -> Coq_left
             | Right -> Coq_right)
  | Right -> (match y with
              | Left -> Coq_right
              | Right -> Coq_left)

(** val coq_Exec_EqDec : coq_Exec coq_EqDec **)

let coq_Exec_EqDec =
  coq_Exec_eqdec

(** val coq_Predicate_eqdec :
    coq_Predicate -> coq_Predicate -> coq_Predicate dec_eq **)

let coq_Predicate_eqdec x y =
  match x with
  | Coq_pmp_entries ->
    (match y with
     | Coq_pmp_entries -> Coq_left
     | _ -> Coq_right)
  | Coq_pmp_addr_access ->
    (match y with
     | Coq_pmp_addr_access -> Coq_left
     | _ -> Coq_right)
  | Coq_pmp_addr_access_without bytes ->
    (match y with
     | Coq_pmp_addr_access_without bytes0 ->
       eq_dec_point bytes (coq_EqDec_EqDecPoint nat_EqDec bytes) bytes0
     | _ -> Coq_right)
  | Coq_gprs -> (match y with
                 | Coq_gprs -> Coq_left
                 | _ -> Coq_right)
  | Coq_ptsto -> (match y with
                  | Coq_ptsto -> Coq_left
                  | _ -> Coq_right)
  | Coq_ptsto_one k ->
    (match y with
     | Coq_ptsto_one k0 ->
       eq_dec_point k (coq_EqDec_EqDecPoint coq_Exec_EqDec k) k0
     | _ -> Coq_right)
  | Coq_ptstomem_readonly bytes ->
    (match y with
     | Coq_ptstomem_readonly bytes0 ->
       eq_dec_point bytes (coq_EqDec_EqDecPoint nat_EqDec bytes) bytes0
     | _ -> Coq_right)
  | Coq_inv_mmio bytes ->
    (match y with
     | Coq_inv_mmio bytes0 ->
       eq_dec_point bytes (coq_EqDec_EqDecPoint nat_EqDec bytes) bytes0
     | _ -> Coq_right)
  | Coq_mmio_checked_write bytes ->
    (match y with
     | Coq_mmio_checked_write bytes0 ->
       eq_dec_point bytes (coq_EqDec_EqDecPoint nat_EqDec bytes) bytes0
     | _ -> Coq_right)
  | Coq_encodes_instr ->
    (match y with
     | Coq_encodes_instr -> Coq_left
     | _ -> Coq_right)
  | Coq_ptstomem bytes ->
    (match y with
     | Coq_ptstomem bytes0 ->
       eq_dec_point bytes (coq_EqDec_EqDecPoint nat_EqDec bytes) bytes0
     | _ -> Coq_right)
  | Coq_ptstoinstr ->
    (match y with
     | Coq_ptstoinstr -> Coq_left
     | _ -> Coq_right)

module RiscvPmpSignature =
 struct
  type _UU1d477_ = coq_PurePredicate

  (** val _UU1d477__Ty : _UU1d477_ -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx **)

  let _UU1d477__Ty = function
  | Coq_gen_pmp_access ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
      RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)),
      RiscvPmpBase.ty_access_type)
  | Coq_pmp_access ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)),
      RiscvPmpBase.ty_access_type)
  | Coq_pmp_check_perms ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)),
      RiscvPmpBase.ty_privilege)
  | Coq_pmp_check_rwx ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)
  | Coq_sub_perm ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_access_type)
  | Coq_access_pmp_perm ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_pmpcfgperm)
  | Coq_within_cfg ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_xlenbits)),
      RiscvPmpBase.ty_xlenbits)
  | Coq_not_within_cfg ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))
  | Coq_prev_addr ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_pmpcfgidx)), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_xlenbits)
  | Coq_in_entries ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_pmpcfgidx)), RiscvPmpBase.ty_pmpentry)),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))
  | Coq_in_mmio _ ->
    Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)

  (** val default_pmpcfg_ent : coq_Pmpcfg_ent **)

  let default_pmpcfg_ent =
    { coq_L = Coq_false; coq_A = OFF; coq_X = Coq_false; coq_W = Coq_false;
      coq_R = Coq_false }

  (** val default_pmpentries : (coq_Pmpcfg_ent, coq_Xlenbits) prod list **)

  let default_pmpentries =
    Coq_cons ((Coq_pair (default_pmpcfg_ent, (Coq_bv.zero xlenbits))),
      (Coq_cons ((Coq_pair (default_pmpcfg_ent, (Coq_bv.zero xlenbits))),
      Coq_nil)))

  (** val pmp_check_RWX : Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool **)

  let pmp_check_RWX cfg acc =
    let { coq_L = _; coq_A = _; coq_X = x; coq_W = w; coq_R = r } =
      Obj.magic cfg
    in
    (match Obj.magic acc with
     | Read -> r
     | Write -> w
     | ReadWrite -> (match r with
                     | Coq_true -> w
                     | Coq_false -> Coq_false)
     | Execute -> x)

  (** val decide_pmp_check_perms :
      Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool **)

  let decide_pmp_check_perms cfg acc p =
    match Obj.magic p with
    | User -> pmp_check_RWX cfg acc
    | Machine ->
      (match (Obj.magic cfg).coq_L with
       | Coq_true -> pmp_check_RWX cfg acc
       | Coq_false -> Coq_true)

  (** val access_type_eqb : Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool **)

  let access_type_eqb a1 a2 =
    match Obj.magic a1 with
    | Read -> (match Obj.magic a2 with
               | Read -> Coq_true
               | _ -> Coq_false)
    | Write -> (match Obj.magic a2 with
                | Write -> Coq_true
                | _ -> Coq_false)
    | ReadWrite ->
      (match Obj.magic a2 with
       | ReadWrite -> Coq_true
       | _ -> Coq_false)
    | Execute ->
      (match Obj.magic a2 with
       | Execute -> Coq_true
       | _ -> Coq_false)

  (** val decide_sub_perm : Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool **)

  let decide_sub_perm a1 a2 =
    match Obj.magic a1 with
    | Read -> (match Obj.magic a2 with
               | Write -> Coq_false
               | _ -> Coq_true)
    | Write ->
      (match Obj.magic a2 with
       | Read -> Coq_false
       | Execute -> Coq_false
       | _ -> Coq_true)
    | ReadWrite ->
      (match Obj.magic a2 with
       | ReadWrite -> Coq_true
       | _ -> Coq_false)
    | Execute ->
      (match Obj.magic a2 with
       | Execute -> Coq_true
       | _ -> Coq_false)

  (** val coq_PmpAddrMatchType_eqb :
      coq_PmpAddrMatchType -> coq_PmpAddrMatchType -> bool **)

  let coq_PmpAddrMatchType_eqb a1 a2 =
    match a1 with
    | OFF -> (match a2 with
              | OFF -> Coq_true
              | TOR -> Coq_false)
    | TOR -> (match a2 with
              | OFF -> Coq_false
              | TOR -> Coq_true)

  type coq_PmpAddrMatchType_eqb_graph =
  | PmpAddrMatchType_eqb_graph_equation_1
  | PmpAddrMatchType_eqb_graph_equation_2
  | PmpAddrMatchType_eqb_graph_equation_3
  | PmpAddrMatchType_eqb_graph_equation_4

  (** val coq_PmpAddrMatchType_eqb_graph_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_PmpAddrMatchType ->
      coq_PmpAddrMatchType -> bool -> coq_PmpAddrMatchType_eqb_graph -> 'a1 **)

  let coq_PmpAddrMatchType_eqb_graph_rect f f0 f1 f2 _ _ _ = function
  | PmpAddrMatchType_eqb_graph_equation_1 -> f
  | PmpAddrMatchType_eqb_graph_equation_2 -> f0
  | PmpAddrMatchType_eqb_graph_equation_3 -> f1
  | PmpAddrMatchType_eqb_graph_equation_4 -> f2

  (** val coq_PmpAddrMatchType_eqb_graph_correct :
      coq_PmpAddrMatchType -> coq_PmpAddrMatchType ->
      coq_PmpAddrMatchType_eqb_graph **)

  let coq_PmpAddrMatchType_eqb_graph_correct a1 a2 =
    match a1 with
    | OFF ->
      (match a2 with
       | OFF -> PmpAddrMatchType_eqb_graph_equation_1
       | TOR -> PmpAddrMatchType_eqb_graph_equation_2)
    | TOR ->
      (match a2 with
       | OFF -> PmpAddrMatchType_eqb_graph_equation_3
       | TOR -> PmpAddrMatchType_eqb_graph_equation_4)

  (** val coq_PmpAddrMatchType_eqb_elim :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_PmpAddrMatchType ->
      coq_PmpAddrMatchType -> 'a1 **)

  let coq_PmpAddrMatchType_eqb_elim f f0 f1 f2 a1 a2 =
    match coq_PmpAddrMatchType_eqb_graph_correct a1 a2 with
    | PmpAddrMatchType_eqb_graph_equation_1 -> f
    | PmpAddrMatchType_eqb_graph_equation_2 -> f0
    | PmpAddrMatchType_eqb_graph_equation_3 -> f1
    | PmpAddrMatchType_eqb_graph_equation_4 -> f2

  (** val coq_FunctionalElimination_PmpAddrMatchType_eqb :
      __ -> __ -> __ -> __ -> coq_PmpAddrMatchType -> coq_PmpAddrMatchType ->
      __ **)

  let coq_FunctionalElimination_PmpAddrMatchType_eqb =
    coq_PmpAddrMatchType_eqb_elim

  (** val coq_FunctionalInduction_PmpAddrMatchType_eqb :
      (coq_PmpAddrMatchType -> coq_PmpAddrMatchType -> bool)
      coq_FunctionalInduction **)

  let coq_FunctionalInduction_PmpAddrMatchType_eqb =
    Obj.magic coq_PmpAddrMatchType_eqb_graph_correct

  (** val pmpcfg_ent_eqb : coq_Pmpcfg_ent -> coq_Pmpcfg_ent -> bool **)

  let pmpcfg_ent_eqb c1 c2 =
    let { coq_L = l1; coq_A = a1; coq_X = x1; coq_W = w1; coq_R = r1 } = c1 in
    let { coq_L = l2; coq_A = a2; coq_X = x2; coq_W = w2; coq_R = r2 } = c2 in
    (match match match match Bool.eqb l1 l2 with
                       | Coq_true -> coq_PmpAddrMatchType_eqb a1 a2
                       | Coq_false -> Coq_false with
                 | Coq_true -> Bool.eqb x1 x2
                 | Coq_false -> Coq_false with
           | Coq_true -> Bool.eqb w1 w2
           | Coq_false -> Coq_false with
     | Coq_true -> Bool.eqb r1 r2
     | Coq_false -> Coq_false)

  (** val decide_in_entries :
      Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool **)

  let decide_in_entries idx e es =
    match Obj.magic es with
    | Coq_nil -> Coq_false
    | Coq_cons (cfg0, l) ->
      (match l with
       | Coq_nil -> Coq_false
       | Coq_cons (cfg1, l0) ->
         (match l0 with
          | Coq_nil ->
            let Coq_pair (c, a) = Obj.magic e in
            let Coq_pair (c', a') =
              match Obj.magic idx with
              | PMP0CFG -> cfg0
              | PMP1CFG -> cfg1
            in
            (match pmpcfg_ent_eqb c c' with
             | Coq_true -> Coq_bv.eqb xlenbits a a'
             | Coq_false -> Coq_false)
          | Coq_cons (_, _) -> Coq_false))

  (** val decide_prev_addr :
      Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool **)

  let decide_prev_addr cfg entries prev =
    match Obj.magic entries with
    | Coq_nil -> Coq_false
    | Coq_cons (v, l) ->
      let Coq_pair (_, a0) = v in
      (match l with
       | Coq_nil -> Coq_false
       | Coq_cons (_, l0) ->
         (match l0 with
          | Coq_nil ->
            (match Obj.magic cfg with
             | PMP0CFG -> Coq_bv.eqb xlenbits (Obj.magic prev) N0
             | PMP1CFG -> Coq_bv.eqb xlenbits (Obj.magic prev) a0)
          | Coq_cons (_, _) -> Coq_false))

  (** val decide_within_cfg :
      Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
      bool **)

  let decide_within_cfg paddr cfg prev_addr addr =
    match (Obj.magic cfg).coq_A with
    | OFF -> Coq_false
    | TOR ->
      (match Coq_bv.uleb xlenbits (Obj.magic prev_addr) (Obj.magic paddr) with
       | Coq_true -> Coq_bv.ultb xlenbits (Obj.magic paddr) (Obj.magic addr)
       | Coq_false -> Coq_false)

  (** val decide_not_within_cfg : Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool **)

  let decide_not_within_cfg paddr entries =
    match Obj.magic entries with
    | Coq_nil -> Coq_false
    | Coq_cons (v, l) ->
      let Coq_pair (c0, a0) = v in
      (match l with
       | Coq_nil -> Coq_false
       | Coq_cons (v0, l0) ->
         let Coq_pair (c1, a1) = v0 in
         (match l0 with
          | Coq_nil ->
            (match match coq_PmpAddrMatchType_eqb c0.coq_A OFF with
                   | Coq_true -> coq_PmpAddrMatchType_eqb c1.coq_A OFF
                   | Coq_false -> Coq_false with
             | Coq_true -> Coq_true
             | Coq_false ->
               (match match Coq_bv.uleb xlenbits N0 (Obj.magic paddr) with
                      | Coq_true -> Coq_bv.uleb xlenbits a0 (Obj.magic paddr)
                      | Coq_false -> Coq_false with
                | Coq_true -> Coq_bv.uleb xlenbits a1 (Obj.magic paddr)
                | Coq_false -> Coq_false))
          | Coq_cons (_, _) -> Coq_false))

  (** val is_pmp_cfg_unlocked : Coq_ty.coq_Val -> bool **)

  let is_pmp_cfg_unlocked cfg =
    negb (Obj.magic cfg).coq_L

  (** val _UU1d477__inst :
      _UU1d477_ -> (Coq_ty.coq_Ty, Coq_ty.coq_Val, __) Coq_env.abstract **)

  let _UU1d477__inst = function
  | Coq_in_mmio x -> Obj.magic __ x
  | _ -> Obj.magic __

  (** val _UU1d477__eq_dec : _UU1d477_ coq_EqDec **)

  let _UU1d477__eq_dec =
    coq_PurePredicate_eqdec

  type _UU1d46f_ = coq_Predicate

  (** val _UU1d46f__Ty : _UU1d46f_ -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx **)

  let _UU1d46f__Ty = function
  | Coq_pmp_entries ->
    Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))
  | Coq_pmp_addr_access ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)
  | Coq_pmp_addr_access_without _ ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)
  | Coq_gprs -> Coq_ctx.Coq_nil
  | Coq_ptstomem_readonly width ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
  | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
  | Coq_mmio_checked_write width ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
  | Coq_encodes_instr ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
  | Coq_ptstomem width ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
  | Coq_ptstoinstr ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
  | _ ->
    Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte)

  (** val _UU1d46f__is_dup : coq_Predicate coq_IsDuplicable **)

  let _UU1d46f__is_dup = function
  | Coq_ptstomem_readonly _ -> Coq_true
  | Coq_inv_mmio _ -> Coq_true
  | Coq_encodes_instr -> Coq_true
  | _ -> Coq_false

  (** val _UU1d46f__eq_dec : _UU1d46f_ coq_EqDec **)

  let _UU1d46f__eq_dec =
    coq_Predicate_eqdec

  (** val _UU1d46f__precise :
      _UU1d46f_ -> _UU1d46f_ RiscvPmpBase.coq_Precise option **)

  let _UU1d46f__precise = function
  | Coq_pmp_entries ->
    Some { RiscvPmpBase.prec_input = Coq_ctx.Coq_nil;
      RiscvPmpBase.prec_output = (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))) }
  | Coq_pmp_addr_access ->
    Some { RiscvPmpBase.prec_input = Coq_ctx.Coq_nil;
      RiscvPmpBase.prec_output = (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
      RiscvPmpBase.ty_privilege)) }
  | Coq_pmp_addr_access_without _ ->
    Some { RiscvPmpBase.prec_input = (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)); RiscvPmpBase.prec_output =
      (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)) }
  | Coq_gprs ->
    Some { RiscvPmpBase.prec_input = Coq_ctx.Coq_nil;
      RiscvPmpBase.prec_output = Coq_ctx.Coq_nil }
  | Coq_ptstomem_readonly width ->
    Some { RiscvPmpBase.prec_input = (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)); RiscvPmpBase.prec_output =
      (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_bvec
      (mul width byte)))) }
  | Coq_inv_mmio _ ->
    Some { RiscvPmpBase.prec_input = Coq_ctx.Coq_nil;
      RiscvPmpBase.prec_output = Coq_ctx.Coq_nil }
  | Coq_mmio_checked_write width ->
    Some { RiscvPmpBase.prec_input = Coq_ctx.Coq_nil;
      RiscvPmpBase.prec_output = (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
      (mul width byte)))) }
  | Coq_encodes_instr ->
    Some { RiscvPmpBase.prec_input = (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_word)); RiscvPmpBase.prec_output = (Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_ast)) }
  | Coq_ptstomem width ->
    Some { RiscvPmpBase.prec_input = (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)); RiscvPmpBase.prec_output =
      (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_bvec
      (mul width byte)))) }
  | Coq_ptstoinstr ->
    Some { RiscvPmpBase.prec_input = (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)); RiscvPmpBase.prec_output =
      (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_ast)) }
  | _ ->
    Some { RiscvPmpBase.prec_input = (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)); RiscvPmpBase.prec_output =
      (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_byte)) }

  type coq_PredicateDef = { lptsreg : (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg
                                      -> Coq_ty.coq_Val -> __);
                            luser : (coq_Predicate -> (Coq_ty.coq_Ty,
                                    Coq_ty.coq_Val) Coq_env.coq_Env -> __) }

  (** val lptsreg :
      bi -> coq_PredicateDef -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg ->
      Coq_ty.coq_Val -> __ **)

  let lptsreg _ predicateDef =
    predicateDef.lptsreg

  (** val luser :
      bi -> coq_PredicateDef -> coq_Predicate -> (Coq_ty.coq_Ty,
      Coq_ty.coq_Val) Coq_env.coq_Env -> __ **)

  let luser _ predicateDef =
    predicateDef.luser

  type coq_Formula =
  | Coq_formula_user of coq_PurePredicate
     * (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env
  | Coq_formula_bool of RiscvPmpBase.coq_Term
  | Coq_formula_prop of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                        Coq_ctx.coq_Ctx
     * RiscvPmpBase.coq_Sub
     * (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named
  | Coq_formula_relop of Coq_ty.coq_Ty * Coq_bop.coq_RelOp
     * RiscvPmpBase.coq_Term * RiscvPmpBase.coq_Term
  | Coq_formula_true
  | Coq_formula_false
  | Coq_formula_and of coq_Formula * coq_Formula
  | Coq_formula_or of coq_Formula * coq_Formula

  (** val coq_Formula_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PurePredicate -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
      Coq_env.coq_Env -> 'a1) -> (RiscvPmpBase.coq_Term -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Sub -> (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __)
      abstract_named -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> 'a1) -> 'a1 -> 'a1 ->
      (coq_Formula -> 'a1 -> coq_Formula -> 'a1 -> 'a1) -> (coq_Formula ->
      'a1 -> coq_Formula -> 'a1 -> 'a1) -> coq_Formula -> 'a1 **)

  let rec coq_Formula_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 = function
  | Coq_formula_user (p, ts) -> f p ts
  | Coq_formula_bool t -> f0 t
  | Coq_formula_prop (_UU03a3_', _UU03b6_, p) -> f1 _UU03a3_' _UU03b6_ p
  | Coq_formula_relop (_UU03c3_, rop, t1, t2) -> f2 _UU03c3_ rop t1 t2
  | Coq_formula_true -> f3
  | Coq_formula_false -> f4
  | Coq_formula_and (f8, f9) ->
    f5 f8 (coq_Formula_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f8) f9
      (coq_Formula_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f9)
  | Coq_formula_or (f8, f9) ->
    f6 f8 (coq_Formula_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f8) f9
      (coq_Formula_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f9)

  (** val coq_Formula_rec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PurePredicate -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
      Coq_env.coq_Env -> 'a1) -> (RiscvPmpBase.coq_Term -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Sub -> (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __)
      abstract_named -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> 'a1) -> 'a1 -> 'a1 ->
      (coq_Formula -> 'a1 -> coq_Formula -> 'a1 -> 'a1) -> (coq_Formula ->
      'a1 -> coq_Formula -> 'a1 -> 'a1) -> coq_Formula -> 'a1 **)

  let rec coq_Formula_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 = function
  | Coq_formula_user (p, ts) -> f p ts
  | Coq_formula_bool t -> f0 t
  | Coq_formula_prop (_UU03a3_', _UU03b6_, p) -> f1 _UU03a3_' _UU03b6_ p
  | Coq_formula_relop (_UU03c3_, rop, t1, t2) -> f2 _UU03c3_ rop t1 t2
  | Coq_formula_true -> f3
  | Coq_formula_false -> f4
  | Coq_formula_and (f8, f9) ->
    f5 f8 (coq_Formula_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f8) f9
      (coq_Formula_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f9)
  | Coq_formula_or (f8, f9) ->
    f6 f8 (coq_Formula_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f8) f9
      (coq_Formula_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f9)

  (** val formula_relop_neg :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> coq_Formula **)

  let formula_relop_neg _ _ = function
  | Coq_bop.Coq_eq _UU03c3_0 ->
    (fun x x0 -> Coq_formula_relop (_UU03c3_0, (Coq_bop.Coq_neq _UU03c3_0),
      x, x0))
  | Coq_bop.Coq_neq _UU03c3_0 ->
    (fun x x0 -> Coq_formula_relop (_UU03c3_0, (Coq_bop.Coq_eq _UU03c3_0), x,
      x0))
  | Coq_bop.Coq_le ->
    flip (fun x x0 -> Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_lt, x,
      x0))
  | Coq_bop.Coq_lt ->
    flip (fun x x0 -> Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le, x,
      x0))
  | Coq_bop.Coq_bvsle n ->
    flip (fun x x0 -> Coq_formula_relop ((Coq_ty.Coq_bvec n),
      (Coq_bop.Coq_bvslt n), x, x0))
  | Coq_bop.Coq_bvslt n ->
    flip (fun x x0 -> Coq_formula_relop ((Coq_ty.Coq_bvec n),
      (Coq_bop.Coq_bvsle n), x, x0))
  | Coq_bop.Coq_bvule n ->
    flip (fun x x0 -> Coq_formula_relop ((Coq_ty.Coq_bvec n),
      (Coq_bop.Coq_bvult n), x, x0))
  | Coq_bop.Coq_bvult n ->
    flip (fun x x0 -> Coq_formula_relop ((Coq_ty.Coq_bvec n),
      (Coq_bop.Coq_bvule n), x, x0))

  (** val subSU_formula :
      'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_Formula)
      RiscvPmpBase.coq_SubstSU **)

  let rec subSU_formula h _UU03a3_1 _UU03a3_2 fml _UU03b6_ =
    match fml with
    | Coq_formula_user (p, ts) ->
      Coq_formula_user (p,
        (RiscvPmpBase.substSU
          (RiscvPmpBase.coq_SubstSU_env h
            (match p with
             | Coq_gen_pmp_access ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
             | Coq_pmp_access ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
             | Coq_pmp_check_perms ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
                 RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_privilege)
             | Coq_pmp_check_rwx ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)
             | Coq_sub_perm ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_access_type)
             | Coq_access_pmp_perm ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_pmpcfgperm)
             | Coq_within_cfg ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)
             | Coq_not_within_cfg ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
                 RiscvPmpBase.ty_pmpentry))
             | Coq_prev_addr ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_xlenbits)
             | Coq_in_entries ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
                 RiscvPmpBase.ty_pmpentry)), (Coq_ty.Coq_list
                 RiscvPmpBase.ty_pmpentry))
             | Coq_in_mmio _ ->
               Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits))
            (RiscvPmpBase.coq_SubstSUTerm h))
          _UU03a3_1 _UU03a3_2 ts _UU03b6_))
    | Coq_formula_bool t ->
      Coq_formula_bool
        (RiscvPmpBase.substSU
          (RiscvPmpBase.coq_SubstSUTerm h Coq_ty.Coq_bool) _UU03a3_1
          _UU03a3_2 t _UU03b6_)
    | Coq_formula_prop (_UU03a3_', _UU03b6_', p) ->
      Coq_formula_prop (_UU03a3_',
        (RiscvPmpBase.substSU (RiscvPmpBase.coq_SubstSU_sub h _UU03a3_')
          _UU03a3_1 _UU03a3_2 _UU03b6_' _UU03b6_),
        p)
    | Coq_formula_relop (_UU03c3_, op, t1, t2) ->
      Coq_formula_relop (_UU03c3_, op,
        (RiscvPmpBase.substSU (RiscvPmpBase.coq_SubstSUTerm h _UU03c3_)
          _UU03a3_1 _UU03a3_2 t1 _UU03b6_),
        (RiscvPmpBase.substSU (RiscvPmpBase.coq_SubstSUTerm h _UU03c3_)
          _UU03a3_1 _UU03a3_2 t2 _UU03b6_))
    | Coq_formula_and (f1, f2) ->
      Coq_formula_and ((subSU_formula h _UU03a3_1 _UU03a3_2 f1 _UU03b6_),
        (subSU_formula h _UU03a3_1 _UU03a3_2 f2 _UU03b6_))
    | Coq_formula_or (f1, f2) ->
      Coq_formula_or ((subSU_formula h _UU03a3_1 _UU03a3_2 f1 _UU03b6_),
        (subSU_formula h _UU03a3_1 _UU03a3_2 f2 _UU03b6_))
    | x -> x

  (** val sub_formula : coq_Formula RiscvPmpBase.coq_Subst **)

  let rec sub_formula _UU03a3_ fml _UU03a3_2 _UU03b6_ =
    match fml with
    | Coq_formula_user (p, ts) ->
      Coq_formula_user (p,
        (RiscvPmpBase.subst
          (RiscvPmpBase.coq_SubstEnv RiscvPmpBase.coq_SubstTerm
            (match p with
             | Coq_gen_pmp_access ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
             | Coq_pmp_access ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
             | Coq_pmp_check_perms ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
                 RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_privilege)
             | Coq_pmp_check_rwx ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)
             | Coq_sub_perm ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_access_type)
             | Coq_access_pmp_perm ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_pmpcfgperm)
             | Coq_within_cfg ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)
             | Coq_not_within_cfg ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
                 RiscvPmpBase.ty_pmpentry))
             | Coq_prev_addr ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_xlenbits)
             | Coq_in_entries ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
                 RiscvPmpBase.ty_pmpentry)), (Coq_ty.Coq_list
                 RiscvPmpBase.ty_pmpentry))
             | Coq_in_mmio _ ->
               Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)))
          _UU03a3_ ts _UU03a3_2 _UU03b6_))
    | Coq_formula_bool t ->
      Coq_formula_bool
        (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm Coq_ty.Coq_bool)
          _UU03a3_ t _UU03a3_2 _UU03b6_)
    | Coq_formula_prop (_UU03a3_', _UU03b6_', p) ->
      Coq_formula_prop (_UU03a3_',
        (RiscvPmpBase.subst
          (RiscvPmpBase.coq_SubstEnv (fun b ->
            RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_')
          _UU03a3_ _UU03b6_' _UU03a3_2 _UU03b6_),
        p)
    | Coq_formula_relop (_UU03c3_, op, t1, t2) ->
      Coq_formula_relop (_UU03c3_, op,
        (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm _UU03c3_) _UU03a3_ t1
          _UU03a3_2 _UU03b6_),
        (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm _UU03c3_) _UU03a3_ t2
          _UU03a3_2 _UU03b6_))
    | Coq_formula_and (f1, f2) ->
      Coq_formula_and ((sub_formula _UU03a3_ f1 _UU03a3_2 _UU03b6_),
        (sub_formula _UU03a3_ f2 _UU03a3_2 _UU03b6_))
    | Coq_formula_or (f1, f2) ->
      Coq_formula_or ((sub_formula _UU03a3_ f1 _UU03a3_2 _UU03b6_),
        (sub_formula _UU03a3_ f2 _UU03a3_2 _UU03b6_))
    | x -> x

  (** val substlaws_formula : coq_Formula RiscvPmpBase.coq_SubstLaws **)

  let substlaws_formula =
    RiscvPmpBase.Build_SubstLaws

  (** val coq_OccursCheckFormula :
      coq_Formula RiscvPmpBase.coq_OccursCheck **)

  let rec coq_OccursCheckFormula _UU03a3_ x xIn = function
  | Coq_formula_user (p, ts) ->
    Coq_option.map (fun x0 -> Coq_formula_user (p, x0))
      (RiscvPmpBase.occurs_check
        (RiscvPmpBase.occurs_check_env RiscvPmpBase.occurs_check_term
          (match p with
           | Coq_gen_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_check_perms ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_privilege)
           | Coq_pmp_check_rwx ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)
           | Coq_sub_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_access_type)
           | Coq_access_pmp_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_pmpcfgperm)
           | Coq_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)
           | Coq_not_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_prev_addr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_xlenbits)
           | Coq_in_entries ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               RiscvPmpBase.ty_pmpentry)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_in_mmio _ ->
             Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)))
        _UU03a3_ x xIn ts)
  | Coq_formula_bool t ->
    Coq_option.map (fun x0 -> Coq_formula_bool x0)
      (RiscvPmpBase.occurs_check
        (RiscvPmpBase.occurs_check_term Coq_ty.Coq_bool) _UU03a3_ x xIn t)
  | Coq_formula_prop (_UU03a3_', _UU03b6_, p) ->
    Coq_option.map (fun _UU03b6_' -> Coq_formula_prop (_UU03a3_', _UU03b6_',
      p))
      (RiscvPmpBase.occurs_check (RiscvPmpBase.occurs_check_sub _UU03a3_')
        _UU03a3_ x xIn _UU03b6_)
  | Coq_formula_relop (_UU03c3_, op, t1, t2) ->
    Coq_option.bind
      (RiscvPmpBase.occurs_check (RiscvPmpBase.occurs_check_term _UU03c3_)
        _UU03a3_ x xIn t1)
      (fun t1' ->
      Coq_option.bind
        (RiscvPmpBase.occurs_check (RiscvPmpBase.occurs_check_term _UU03c3_)
          _UU03a3_ x xIn t2)
        (fun t2' -> Some (Coq_formula_relop (_UU03c3_, op, t1', t2'))))
  | Coq_formula_and (f1, f2) ->
    Coq_option.bind (coq_OccursCheckFormula _UU03a3_ x xIn f1) (fun f1' ->
      Coq_option.bind (coq_OccursCheckFormula _UU03a3_ x xIn f2) (fun f2' ->
        Some (Coq_formula_and (f1', f2'))))
  | Coq_formula_or (f1, f2) ->
    Coq_option.bind (coq_OccursCheckFormula _UU03a3_ x xIn f1) (fun f1' ->
      Coq_option.bind (coq_OccursCheckFormula _UU03a3_ x xIn f2) (fun f2' ->
        Some (Coq_formula_or (f1', f2'))))
  | x0 -> Some x0

  (** val coq_GenOccursCheckFormula :
      'a1 RiscvPmpBase.coq_SubstUniv -> 'a1 RiscvPmpBase.coq_SubstUnivMeet ->
      'a1 RiscvPmpBase.coq_SubstUnivVar -> 'a1 RiscvPmpBase.coq_SubstUniv ->
      'a1 RiscvPmpBase.coq_SubstUnivMeet -> 'a1 RiscvPmpBase.coq_SubstUniv ->
      'a1 RiscvPmpBase.coq_SubstUnivMeet -> ('a1, coq_Formula)
      RiscvPmpBase.coq_GenOccursCheck **)

  let rec coq_GenOccursCheckFormula h h0 h1 h2 h3 h4 h5 _UU03a3_ = function
  | Coq_formula_user (p, ts) ->
    RiscvPmpBase.liftUnOp h4 _UU03a3_
      (RiscvPmpBase.coq_SubstSU_env h4
        (match p with
         | Coq_gen_pmp_access ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
             RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
             (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
             RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
         | Coq_pmp_access ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
             (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
             RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
         | Coq_pmp_check_perms ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
             RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_privilege)
         | Coq_pmp_check_rwx ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)
         | Coq_sub_perm ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_access_type)
         | Coq_access_pmp_perm ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_pmpcfgperm)
         | Coq_within_cfg ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
             RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_xlenbits)),
             RiscvPmpBase.ty_xlenbits)
         | Coq_not_within_cfg ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
             RiscvPmpBase.ty_pmpentry))
         | Coq_prev_addr ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)), (Coq_ty.Coq_list
             RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_xlenbits)
         | Coq_in_entries ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
             RiscvPmpBase.ty_pmpentry)), (Coq_ty.Coq_list
             RiscvPmpBase.ty_pmpentry))
         | Coq_in_mmio _ ->
           Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits))
        (RiscvPmpBase.coq_SubstSUTerm h4))
      (subSU_formula h4) (fun _ x -> Coq_formula_user (p, x))
      (RiscvPmpBase.gen_occurs_check h4
        (RiscvPmpBase.coq_SubstSU_env h4
          (match p with
           | Coq_gen_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_check_perms ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_privilege)
           | Coq_pmp_check_rwx ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)
           | Coq_sub_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_access_type)
           | Coq_access_pmp_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_pmpcfgperm)
           | Coq_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)
           | Coq_not_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_prev_addr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_xlenbits)
           | Coq_in_entries ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               RiscvPmpBase.ty_pmpentry)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_in_mmio _ ->
             Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits))
          (RiscvPmpBase.coq_SubstSUTerm h4))
        (RiscvPmpBase.gen_occurs_check_env h4 h5 h4 h5
          (RiscvPmpBase.coq_SubstSUTerm h4)
          (RiscvPmpBase.gen_occurs_check_term h h0 h1 h4 h5 h4 h5)
          (match p with
           | Coq_gen_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_check_perms ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_privilege)
           | Coq_pmp_check_rwx ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)
           | Coq_sub_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_access_type)
           | Coq_access_pmp_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_pmpcfgperm)
           | Coq_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)
           | Coq_not_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_prev_addr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_xlenbits)
           | Coq_in_entries ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               RiscvPmpBase.ty_pmpentry)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_in_mmio _ ->
             Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)))
        _UU03a3_ ts)
  | Coq_formula_bool t ->
    RiscvPmpBase.liftUnOp h4 _UU03a3_
      (RiscvPmpBase.coq_SubstSUTerm h4 Coq_ty.Coq_bool) (subSU_formula h4)
      (fun _ x -> Coq_formula_bool x)
      (RiscvPmpBase.gen_occurs_check h4
        (RiscvPmpBase.coq_SubstSUTerm h4 Coq_ty.Coq_bool)
        (RiscvPmpBase.gen_occurs_check_term h h0 h1 h4 h5 h4 h5
          Coq_ty.Coq_bool)
        _UU03a3_ t)
  | Coq_formula_prop (_UU03a3_', _UU03b6_, p) ->
    RiscvPmpBase.liftUnOp h4 _UU03a3_
      (RiscvPmpBase.coq_SubstSU_sub h4 _UU03a3_') (subSU_formula h4)
      (fun _ _UU03b6_0 -> Coq_formula_prop (_UU03a3_', _UU03b6_0, p))
      (RiscvPmpBase.gen_occurs_check h4
        (RiscvPmpBase.coq_SubstSU_sub h4 _UU03a3_')
        (RiscvPmpBase.gen_occurs_check_env h4 h5 h4 h5 (fun b ->
          RiscvPmpBase.coq_SubstSUTerm h4 b.Binding.coq_type) (fun i ->
          RiscvPmpBase.gen_occurs_check_term h h0 h1 h4 h5 h4 h5
            i.Binding.coq_type)
          _UU03a3_')
        _UU03a3_ _UU03b6_)
  | Coq_formula_relop (_UU03c3_, op, t1, t2) ->
    RiscvPmpBase.liftBinOp h4 h5 h4 h5 _UU03a3_
      (RiscvPmpBase.coq_SubstSUTerm h4 _UU03c3_)
      (RiscvPmpBase.coq_SubstSUTerm h4 _UU03c3_) (subSU_formula h4)
      (fun _ x x0 -> Coq_formula_relop (_UU03c3_, op, x, x0))
      (RiscvPmpBase.gen_occurs_check h4
        (RiscvPmpBase.coq_SubstSUTerm h4 _UU03c3_)
        (RiscvPmpBase.gen_occurs_check_term h h0 h1 h4 h5 h4 h5 _UU03c3_)
        _UU03a3_ t1)
      (RiscvPmpBase.gen_occurs_check h4
        (RiscvPmpBase.coq_SubstSUTerm h4 _UU03c3_)
        (RiscvPmpBase.gen_occurs_check_term h h0 h1 h4 h5 h4 h5 _UU03c3_)
        _UU03a3_ t2)
  | Coq_formula_and (f1, f2) ->
    RiscvPmpBase.liftBinOp h4 h5 h4 h5 _UU03a3_ (subSU_formula h4)
      (subSU_formula h4) (subSU_formula h4) (fun _ f1' f2' -> Coq_formula_and
      (f1', f2')) (coq_GenOccursCheckFormula h h0 h1 h2 h3 h4 h5 _UU03a3_ f1)
      (coq_GenOccursCheckFormula h h0 h1 h2 h3 h4 h5 _UU03a3_ f2)
  | Coq_formula_or (f1, f2) ->
    RiscvPmpBase.liftBinOp h4 h5 h4 h5 _UU03a3_ (subSU_formula h4)
      (subSU_formula h4) (subSU_formula h4) (fun _ f1' f2' -> Coq_formula_or
      (f1', f2')) (coq_GenOccursCheckFormula h h0 h1 h2 h3 h4 h5 _UU03a3_ f1)
      (coq_GenOccursCheckFormula h h0 h1 h2 h3 h4 h5 _UU03a3_ f2)
  | x -> RiscvPmpBase.weakenInit h4 h5 (subSU_formula h4) h4 h5 _UU03a3_ x

  type coq_PathCondition = coq_Formula Coq_ctx.coq_Ctx

  (** val formula_eqs_ctx :
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) Coq_env.coq_Env -> coq_PathCondition **)

  let rec formula_eqs_ctx _ _UU03a3_ _UU03b4_ _UU03b4_' =
    match _UU03b4_ with
    | Coq_env.Coq_nil ->
      (match _UU03b4_' with
       | Coq_env.Coq_nil -> Coq_ctx.Coq_nil
       | Coq_env.Coq_snoc (_, _, _, _) -> assert false (* absurd case *))
    | Coq_env.Coq_snoc (_UU0393_, e, b, db) ->
      (match _UU03b4_' with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db0) ->
         Coq_ctx.Coq_snoc ((formula_eqs_ctx _UU0393_ _UU03a3_ e e0),
           (Coq_formula_relop (b, (Coq_bop.Coq_eq b), db, db0))))

  (** val formula_eqs_nctx :
      ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
      Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) coq_NamedEnv -> ('a1,
      Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) coq_NamedEnv -> coq_PathCondition **)

  let rec formula_eqs_nctx _ _UU03a3_ _UU03b4_ _UU03b4_' =
    match _UU03b4_ with
    | Coq_env.Coq_nil ->
      (match _UU03b4_' with
       | Coq_env.Coq_nil -> Coq_ctx.Coq_nil
       | Coq_env.Coq_snoc (_, _, _, _) -> assert false (* absurd case *))
    | Coq_env.Coq_snoc (_UU0393_, e, b, db) ->
      (match _UU03b4_' with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db0) ->
         Coq_ctx.Coq_snoc ((formula_eqs_nctx _UU0393_ _UU03a3_ e e0),
           (Coq_formula_relop (b.Binding.coq_type, (Coq_bop.Coq_eq
           b.Binding.coq_type), db, db0))))

  type coq_EFormula =
  | Coq_eformula_user of coq_PurePredicate
     * (Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) Coq_env.coq_Env
  | Coq_eformula_bool of RiscvPmpBase.coq_ETerm
  | Coq_eformula_prop of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                         Coq_ctx.coq_Ctx
     * ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding,
       RiscvPmpBase.coq_ETerm) Coq_env.coq_Env
     * (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named
  | Coq_eformula_relop of Coq_ty.coq_Ty * Coq_bop.coq_RelOp
     * RiscvPmpBase.coq_ETerm * RiscvPmpBase.coq_ETerm
  | Coq_eformula_true
  | Coq_eformula_false
  | Coq_eformula_and of coq_EFormula * coq_EFormula
  | Coq_eformula_or of coq_EFormula * coq_EFormula

  (** val coq_EFormula_rect :
      (coq_PurePredicate -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
      Coq_env.coq_Env -> 'a1) -> (RiscvPmpBase.coq_ETerm -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, RiscvPmpBase.coq_ETerm)
      Coq_env.coq_Env -> (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __)
      abstract_named -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp ->
      RiscvPmpBase.coq_ETerm -> RiscvPmpBase.coq_ETerm -> 'a1) -> 'a1 -> 'a1
      -> (coq_EFormula -> 'a1 -> coq_EFormula -> 'a1 -> 'a1) -> (coq_EFormula
      -> 'a1 -> coq_EFormula -> 'a1 -> 'a1) -> coq_EFormula -> 'a1 **)

  let rec coq_EFormula_rect f f0 f1 f2 f3 f4 f5 f6 = function
  | Coq_eformula_user (p, ts) -> f p ts
  | Coq_eformula_bool t -> f0 t
  | Coq_eformula_prop (_UU03a3_', _UU03b6_, p) -> f1 _UU03a3_' _UU03b6_ p
  | Coq_eformula_relop (_UU03c3_, op, t1, t2) -> f2 _UU03c3_ op t1 t2
  | Coq_eformula_true -> f3
  | Coq_eformula_false -> f4
  | Coq_eformula_and (f7, f8) ->
    f5 f7 (coq_EFormula_rect f f0 f1 f2 f3 f4 f5 f6 f7) f8
      (coq_EFormula_rect f f0 f1 f2 f3 f4 f5 f6 f8)
  | Coq_eformula_or (f7, f8) ->
    f6 f7 (coq_EFormula_rect f f0 f1 f2 f3 f4 f5 f6 f7) f8
      (coq_EFormula_rect f f0 f1 f2 f3 f4 f5 f6 f8)

  (** val coq_EFormula_rec :
      (coq_PurePredicate -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
      Coq_env.coq_Env -> 'a1) -> (RiscvPmpBase.coq_ETerm -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, RiscvPmpBase.coq_ETerm)
      Coq_env.coq_Env -> (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __)
      abstract_named -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp ->
      RiscvPmpBase.coq_ETerm -> RiscvPmpBase.coq_ETerm -> 'a1) -> 'a1 -> 'a1
      -> (coq_EFormula -> 'a1 -> coq_EFormula -> 'a1 -> 'a1) -> (coq_EFormula
      -> 'a1 -> coq_EFormula -> 'a1 -> 'a1) -> coq_EFormula -> 'a1 **)

  let rec coq_EFormula_rec f f0 f1 f2 f3 f4 f5 f6 = function
  | Coq_eformula_user (p, ts) -> f p ts
  | Coq_eformula_bool t -> f0 t
  | Coq_eformula_prop (_UU03a3_', _UU03b6_, p) -> f1 _UU03a3_' _UU03b6_ p
  | Coq_eformula_relop (_UU03c3_, op, t1, t2) -> f2 _UU03c3_ op t1 t2
  | Coq_eformula_true -> f3
  | Coq_eformula_false -> f4
  | Coq_eformula_and (f7, f8) ->
    f5 f7 (coq_EFormula_rec f f0 f1 f2 f3 f4 f5 f6 f7) f8
      (coq_EFormula_rec f f0 f1 f2 f3 f4 f5 f6 f8)
  | Coq_eformula_or (f7, f8) ->
    f6 f7 (coq_EFormula_rec f f0 f1 f2 f3 f4 f5 f6 f7) f8
      (coq_EFormula_rec f f0 f1 f2 f3 f4 f5 f6 f8)

  (** val erase_formula :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_EFormula **)

  let rec erase_formula _UU03a3_ = function
  | Coq_formula_user (p, ts) ->
    Coq_eformula_user (p,
      (Coq_env.map (RiscvPmpBase.erase_term _UU03a3_)
        (match p with
         | Coq_gen_pmp_access ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
             RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
             (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
             RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
         | Coq_pmp_access ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
             (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
             RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
         | Coq_pmp_check_perms ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
             RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_privilege)
         | Coq_pmp_check_rwx ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)
         | Coq_sub_perm ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_access_type)
         | Coq_access_pmp_perm ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_pmpcfgperm)
         | Coq_within_cfg ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
             RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_xlenbits)),
             RiscvPmpBase.ty_xlenbits)
         | Coq_not_within_cfg ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
             RiscvPmpBase.ty_pmpentry))
         | Coq_prev_addr ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)), (Coq_ty.Coq_list
             RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_xlenbits)
         | Coq_in_entries ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
             RiscvPmpBase.ty_pmpentry)), (Coq_ty.Coq_list
             RiscvPmpBase.ty_pmpentry))
         | Coq_in_mmio _ ->
           Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits))
        ts))
  | Coq_formula_bool t ->
    Coq_eformula_bool (RiscvPmpBase.erase_term _UU03a3_ Coq_ty.Coq_bool t)
  | Coq_formula_prop (_UU03a3_', _UU03b6_, p) ->
    Coq_eformula_prop (_UU03a3_',
      (Coq_env.map (fun b ->
        RiscvPmpBase.erase_term _UU03a3_ b.Binding.coq_type) _UU03a3_'
        _UU03b6_),
      p)
  | Coq_formula_relop (_UU03c3_, op, t1, t2) ->
    Coq_eformula_relop (_UU03c3_, op,
      (RiscvPmpBase.erase_term _UU03a3_ _UU03c3_ t1),
      (RiscvPmpBase.erase_term _UU03a3_ _UU03c3_ t2))
  | Coq_formula_true -> Coq_eformula_true
  | Coq_formula_false -> Coq_eformula_false
  | Coq_formula_and (f1, f2) ->
    Coq_eformula_and ((erase_formula _UU03a3_ f1),
      (erase_formula _UU03a3_ f2))
  | Coq_formula_or (f1, f2) ->
    Coq_eformula_or ((erase_formula _UU03a3_ f1), (erase_formula _UU03a3_ f2))

  (** val erase_Formula :
      (coq_Formula, coq_EFormula) RiscvPmpBase.coq_Erase **)

  let erase_Formula =
    erase_formula

  type 'v coq_GChunk =
  | Coq_chunk_user of coq_Predicate * (Coq_ty.coq_Ty, 'v) Coq_env.coq_Env
  | Coq_chunk_ptsreg of Coq_ty.coq_Ty * RiscvPmpBase.coq_Reg * 'v
  | Coq_chunk_conj of 'v coq_GChunk * 'v coq_GChunk
  | Coq_chunk_wand of 'v coq_GChunk * 'v coq_GChunk

  (** val coq_GChunk_rect :
      (coq_Predicate -> (Coq_ty.coq_Ty, 'a1) Coq_env.coq_Env -> 'a2) ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> 'a1 -> 'a2) -> ('a1
      coq_GChunk -> 'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> ('a1 coq_GChunk
      -> 'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> 'a1 coq_GChunk -> 'a2 **)

  let rec coq_GChunk_rect f f0 f1 f2 = function
  | Coq_chunk_user (p, ts) -> f p ts
  | Coq_chunk_ptsreg (_UU03c3_, r, v) -> f0 _UU03c3_ r v
  | Coq_chunk_conj (c1, c2) ->
    f1 c1 (coq_GChunk_rect f f0 f1 f2 c1) c2 (coq_GChunk_rect f f0 f1 f2 c2)
  | Coq_chunk_wand (c1, c2) ->
    f2 c1 (coq_GChunk_rect f f0 f1 f2 c1) c2 (coq_GChunk_rect f f0 f1 f2 c2)

  (** val coq_GChunk_rec :
      (coq_Predicate -> (Coq_ty.coq_Ty, 'a1) Coq_env.coq_Env -> 'a2) ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> 'a1 -> 'a2) -> ('a1
      coq_GChunk -> 'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> ('a1 coq_GChunk
      -> 'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> 'a1 coq_GChunk -> 'a2 **)

  let rec coq_GChunk_rec f f0 f1 f2 = function
  | Coq_chunk_user (p, ts) -> f p ts
  | Coq_chunk_ptsreg (_UU03c3_, r, v) -> f0 _UU03c3_ r v
  | Coq_chunk_conj (c1, c2) ->
    f1 c1 (coq_GChunk_rec f f0 f1 f2 c1) c2 (coq_GChunk_rec f f0 f1 f2 c2)
  | Coq_chunk_wand (c1, c2) ->
    f2 c1 (coq_GChunk_rec f f0 f1 f2 c1) c2 (coq_GChunk_rec f f0 f1 f2 c2)

  type coq_SCChunk = Coq_ty.coq_Val coq_GChunk

  type coq_Chunk = RiscvPmpBase.coq_Term coq_GChunk

  (** val coq_NoConfusionPackage_GChunk :
      'a1 coq_GChunk coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_GChunk =
    Build_NoConfusionPackage

  (** val chunk_isdup : 'a1 coq_GChunk coq_IsDuplicable **)

  let chunk_isdup = function
  | Coq_chunk_user (p, _) -> _UU1d46f__is_dup p
  | _ -> Coq_false

  (** val chunk_eqb :
      (Coq_ty.coq_Ty -> 'a1 -> 'a1 -> bool) -> 'a1 coq_GChunk -> 'a1
      coq_GChunk -> bool **)

  let rec chunk_eqb eqv c1 c2 =
    match c1 with
    | Coq_chunk_user (p1, ts1) ->
      (match c2 with
       | Coq_chunk_user (p2, ts2) ->
         (match eq_dec _UU1d46f__eq_dec p1 p2 with
          | Coq_left ->
            Coq_env.eqb_hom eqv
              (match p2 with
               | Coq_pmp_entries ->
                 Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
                   RiscvPmpBase.ty_pmpentry))
               | Coq_pmp_addr_access ->
                 Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                   (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                   RiscvPmpBase.ty_privilege)
               | Coq_pmp_addr_access_without _ ->
                 Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                   (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                   (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                   RiscvPmpBase.ty_privilege)
               | Coq_gprs -> Coq_ctx.Coq_nil
               | Coq_ptstomem_readonly width ->
                 Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                   RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                   (mul width byte)))
               | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
               | Coq_mmio_checked_write width ->
                 Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                   RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                   (mul width byte)))
               | Coq_encodes_instr ->
                 Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                   RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
               | Coq_ptstomem width ->
                 Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                   RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                   (mul width byte)))
               | Coq_ptstoinstr ->
                 Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                   RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
               | _ ->
                 Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                   RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte))
              ts1 ts2
          | Coq_right -> Coq_false)
       | _ -> Coq_false)
    | Coq_chunk_ptsreg (_UU03c3_, r1, t1) ->
      (match c2 with
       | Coq_chunk_ptsreg (_UU03c3_0, r2, t2) ->
         (match eq_dec_het RiscvPmpBase._UU1d479__UU1d46c__UU1d46e__eq_dec
                  _UU03c3_ _UU03c3_0 r1 r2 with
          | Coq_left -> eqv (projT1 (Coq_existT (_UU03c3_0, r2))) t1 t2
          | Coq_right -> Coq_false)
       | _ -> Coq_false)
    | Coq_chunk_conj (c11, c12) ->
      (match c2 with
       | Coq_chunk_conj (c21, c22) ->
         (match chunk_eqb eqv c11 c21 with
          | Coq_true -> chunk_eqb eqv c12 c22
          | Coq_false -> Coq_false)
       | _ -> Coq_false)
    | Coq_chunk_wand (c11, c12) ->
      (match c2 with
       | Coq_chunk_wand (c21, c22) ->
         (match chunk_eqb eqv c11 c21 with
          | Coq_true -> chunk_eqb eqv c12 c22
          | Coq_false -> Coq_false)
       | _ -> Coq_false)

  (** val chunk_eqb_spec :
      (Coq_ty.coq_Ty -> 'a1 -> 'a1 -> bool) -> (Coq_ty.coq_Ty -> 'a1 -> 'a1
      -> reflect) -> 'a1 coq_GChunk -> 'a1 coq_GChunk -> reflect **)

  let rec chunk_eqb_spec eqv eqv_spec c1 c2 =
    match c1 with
    | Coq_chunk_user (p, ts) ->
      (match c2 with
       | Coq_chunk_user (p0, ts0) ->
         let s = eq_dec _UU1d46f__eq_dec p p0 in
         (match s with
          | Coq_left ->
            internal_eq_rew_r_dep p p0 (fun ts1 ->
              Coq_env.eqb_hom_spec eqv eqv_spec
                (match p0 with
                 | Coq_pmp_entries ->
                   Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
                     RiscvPmpBase.ty_pmpentry))
                 | Coq_pmp_addr_access ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                     RiscvPmpBase.ty_privilege)
                 | Coq_pmp_addr_access_without _ ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                     (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                     (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                     RiscvPmpBase.ty_privilege)
                 | Coq_gprs -> Coq_ctx.Coq_nil
                 | Coq_ptstomem_readonly width ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                     (mul width byte)))
                 | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
                 | Coq_mmio_checked_write width ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                     (mul width byte)))
                 | Coq_encodes_instr ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
                 | Coq_ptstomem width ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                     (mul width byte)))
                 | Coq_ptstoinstr ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
                 | _ ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte))
                ts1 ts0)
              ts
          | Coq_right -> ReflectF)
       | _ -> ReflectF)
    | Coq_chunk_ptsreg (_UU03c3_, r, v) ->
      (match c2 with
       | Coq_chunk_ptsreg (_UU03c3_0, r0, v0) ->
         let d =
           eq_dec_het RiscvPmpBase._UU1d479__UU1d46c__UU1d46e__eq_dec
             _UU03c3_ _UU03c3_0 r r0
         in
         (match d with
          | Coq_left -> eqv_spec _UU03c3_ v v0
          | Coq_right -> ReflectF)
       | _ -> ReflectF)
    | Coq_chunk_conj (c3, c4) ->
      (match c2 with
       | Coq_chunk_conj (c5, c6) ->
         let r = chunk_eqb_spec eqv eqv_spec c3 c5 in
         (match r with
          | ReflectT -> chunk_eqb_spec eqv eqv_spec c4 c6
          | ReflectF -> ReflectF)
       | _ -> ReflectF)
    | Coq_chunk_wand (c3, c4) ->
      (match c2 with
       | Coq_chunk_wand (c5, c6) ->
         let r = chunk_eqb_spec eqv eqv_spec c3 c5 in
         (match r with
          | ReflectT -> chunk_eqb_spec eqv eqv_spec c4 c6
          | ReflectF -> ReflectF)
       | _ -> ReflectF)

  (** val coq_SubstChunk : coq_Chunk RiscvPmpBase.coq_Subst **)

  let rec coq_SubstChunk _UU03a3_1 c _UU03a3_2 _UU03b6_ =
    match c with
    | Coq_chunk_user (p, ts) ->
      Coq_chunk_user (p,
        (RiscvPmpBase.subst
          (RiscvPmpBase.coq_SubstEnv RiscvPmpBase.coq_SubstTerm
            (match p with
             | Coq_pmp_entries ->
               Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
                 RiscvPmpBase.ty_pmpentry))
             | Coq_pmp_addr_access ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_privilege)
             | Coq_pmp_addr_access_without _ ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_privilege)
             | Coq_gprs -> Coq_ctx.Coq_nil
             | Coq_ptstomem_readonly width ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                 (mul width byte)))
             | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
             | Coq_mmio_checked_write width ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                 (mul width byte)))
             | Coq_encodes_instr ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
             | Coq_ptstomem width ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                 (mul width byte)))
             | Coq_ptstoinstr ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
             | _ ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte)))
          _UU03a3_1 ts _UU03a3_2 _UU03b6_))
    | Coq_chunk_ptsreg (_UU03c3_, r, t) ->
      Coq_chunk_ptsreg (_UU03c3_, r,
        (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm _UU03c3_) _UU03a3_1 t
          _UU03a3_2 _UU03b6_))
    | Coq_chunk_conj (c1, c2) ->
      Coq_chunk_conj ((coq_SubstChunk _UU03a3_1 c1 _UU03a3_2 _UU03b6_),
        (coq_SubstChunk _UU03a3_1 c2 _UU03a3_2 _UU03b6_))
    | Coq_chunk_wand (c1, c2) ->
      Coq_chunk_wand ((coq_SubstChunk _UU03a3_1 c1 _UU03a3_2 _UU03b6_),
        (coq_SubstChunk _UU03a3_1 c2 _UU03a3_2 _UU03b6_))

  (** val coq_SubstSUChunk :
      'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_Chunk)
      RiscvPmpBase.coq_SubstSU **)

  let rec coq_SubstSUChunk h _UU03a3_1 _UU03a3_2 c _UU03b6_ =
    match c with
    | Coq_chunk_user (p, ts) ->
      Coq_chunk_user (p,
        (RiscvPmpBase.substSU
          (RiscvPmpBase.coq_SubstSU_env h
            (match p with
             | Coq_pmp_entries ->
               Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
                 RiscvPmpBase.ty_pmpentry))
             | Coq_pmp_addr_access ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_privilege)
             | Coq_pmp_addr_access_without _ ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_privilege)
             | Coq_gprs -> Coq_ctx.Coq_nil
             | Coq_ptstomem_readonly width ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                 (mul width byte)))
             | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
             | Coq_mmio_checked_write width ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                 (mul width byte)))
             | Coq_encodes_instr ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
             | Coq_ptstomem width ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                 (mul width byte)))
             | Coq_ptstoinstr ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
             | _ ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte))
            (RiscvPmpBase.coq_SubstSUTerm h))
          _UU03a3_1 _UU03a3_2 ts _UU03b6_))
    | Coq_chunk_ptsreg (_UU03c3_, r, t) ->
      Coq_chunk_ptsreg (_UU03c3_, r,
        (RiscvPmpBase.substSU (RiscvPmpBase.coq_SubstSUTerm h _UU03c3_)
          _UU03a3_1 _UU03a3_2 t _UU03b6_))
    | Coq_chunk_conj (c1, c2) ->
      Coq_chunk_conj ((coq_SubstSUChunk h _UU03a3_1 _UU03a3_2 c1 _UU03b6_),
        (coq_SubstSUChunk h _UU03a3_1 _UU03a3_2 c2 _UU03b6_))
    | Coq_chunk_wand (c1, c2) ->
      Coq_chunk_wand ((coq_SubstSUChunk h _UU03a3_1 _UU03a3_2 c1 _UU03b6_),
        (coq_SubstSUChunk h _UU03a3_1 _UU03a3_2 c2 _UU03b6_))

  (** val substlaws_chunk : coq_Chunk RiscvPmpBase.coq_SubstLaws **)

  let substlaws_chunk =
    RiscvPmpBase.Build_SubstLaws

  (** val map_GChunk :
      (Coq_ty.coq_Ty -> 'a1 -> 'a2) -> 'a1 coq_GChunk -> 'a2 coq_GChunk **)

  let rec map_GChunk f = function
  | Coq_chunk_user (p, ts) ->
    Coq_chunk_user (p,
      (Coq_env.map f
        (match p with
         | Coq_pmp_entries ->
           Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
             RiscvPmpBase.ty_pmpentry))
         | Coq_pmp_addr_access ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
             RiscvPmpBase.ty_privilege)
         | Coq_pmp_addr_access_without _ ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
             RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)
         | Coq_gprs -> Coq_ctx.Coq_nil
         | Coq_ptstomem_readonly width ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
         | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
         | Coq_mmio_checked_write width ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
         | Coq_encodes_instr ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
         | Coq_ptstomem width ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
         | Coq_ptstoinstr ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
         | _ ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte))
        ts))
  | Coq_chunk_ptsreg (_UU03c3_, r, t) ->
    Coq_chunk_ptsreg (_UU03c3_, r, (f _UU03c3_ t))
  | Coq_chunk_conj (c1, c2) ->
    Coq_chunk_conj ((map_GChunk f c1), (map_GChunk f c2))
  | Coq_chunk_wand (c1, c2) ->
    Coq_chunk_wand ((map_GChunk f c1), (map_GChunk f c2))

  (** val inst_chunk : (coq_Chunk, coq_SCChunk) RiscvPmpBase.coq_Inst **)

  let inst_chunk _UU03a3_ c _UU03b9_ =
    map_GChunk (fun _UU03c3_ v ->
      RiscvPmpBase.inst (RiscvPmpBase.inst_term _UU03c3_) _UU03a3_ v _UU03b9_)
      c

  (** val coq_OccursCheckChunk : coq_Chunk RiscvPmpBase.coq_OccursCheck **)

  let rec coq_OccursCheckChunk _UU03a3_ b bIn = function
  | Coq_chunk_user (p, ts) ->
    Coq_option.map (fun x -> Coq_chunk_user (p, x))
      (RiscvPmpBase.occurs_check
        (RiscvPmpBase.occurs_check_env RiscvPmpBase.occurs_check_term
          (match p with
           | Coq_pmp_entries ->
             Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_pmp_addr_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)
           | Coq_pmp_addr_access_without _ ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)
           | Coq_gprs -> Coq_ctx.Coq_nil
           | Coq_ptstomem_readonly width ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
           | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
           | Coq_mmio_checked_write width ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
           | Coq_encodes_instr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
           | Coq_ptstomem width ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
           | Coq_ptstoinstr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
           | _ ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte)))
        _UU03a3_ b bIn ts)
  | Coq_chunk_ptsreg (_UU03c3_, r, t) ->
    Coq_option.map (fun x -> Coq_chunk_ptsreg (_UU03c3_, r, x))
      (RiscvPmpBase.occurs_check (RiscvPmpBase.occurs_check_term _UU03c3_)
        _UU03a3_ b bIn t)
  | Coq_chunk_conj (c1, c2) ->
    Coq_option.bind (coq_OccursCheckChunk _UU03a3_ b bIn c1) (fun c1' ->
      Coq_option.bind (coq_OccursCheckChunk _UU03a3_ b bIn c2) (fun c2' ->
        Some (Coq_chunk_conj (c1', c2'))))
  | Coq_chunk_wand (c1, c2) ->
    Coq_option.bind (coq_OccursCheckChunk _UU03a3_ b bIn c1) (fun c1' ->
      Coq_option.bind (coq_OccursCheckChunk _UU03a3_ b bIn c2) (fun c2' ->
        Some (Coq_chunk_wand (c1', c2'))))

  (** val coq_GenOccursCheckChunk :
      (RiscvPmpBase.coq_WeakensTo, coq_Chunk) RiscvPmpBase.coq_GenOccursCheck **)

  let rec coq_GenOccursCheckChunk _UU03a3_ = function
  | Coq_chunk_user (p, ts) ->
    RiscvPmpBase.liftUnOp RiscvPmpBase.substUniv_weaken _UU03a3_
      (RiscvPmpBase.coq_SubstSU_env RiscvPmpBase.substUniv_weaken
        (match p with
         | Coq_pmp_entries ->
           Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
             RiscvPmpBase.ty_pmpentry))
         | Coq_pmp_addr_access ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
             RiscvPmpBase.ty_privilege)
         | Coq_pmp_addr_access_without _ ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
             (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
             RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)
         | Coq_gprs -> Coq_ctx.Coq_nil
         | Coq_ptstomem_readonly width ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
         | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
         | Coq_mmio_checked_write width ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
         | Coq_encodes_instr ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
         | Coq_ptstomem width ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
         | Coq_ptstoinstr ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
         | _ ->
           Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte))
        (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken))
      (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken) (fun _ x ->
      Coq_chunk_user (p, x))
      (RiscvPmpBase.gen_occurs_check RiscvPmpBase.substUniv_weaken
        (RiscvPmpBase.coq_SubstSU_env RiscvPmpBase.substUniv_weaken
          (match p with
           | Coq_pmp_entries ->
             Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_pmp_addr_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)
           | Coq_pmp_addr_access_without _ ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)
           | Coq_gprs -> Coq_ctx.Coq_nil
           | Coq_ptstomem_readonly width ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
           | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
           | Coq_mmio_checked_write width ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
           | Coq_encodes_instr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
           | Coq_ptstomem width ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
           | Coq_ptstoinstr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
           | _ ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte))
          (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken))
        (RiscvPmpBase.gen_occurs_check_env RiscvPmpBase.substUniv_weaken
          RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
          RiscvPmpBase.substUnivMeet_weaken
          (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken)
          (RiscvPmpBase.gen_occurs_check_term RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken
            RiscvPmpBase.substUnivVar_weaken RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken)
          (match p with
           | Coq_pmp_entries ->
             Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_pmp_addr_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)
           | Coq_pmp_addr_access_without _ ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)
           | Coq_gprs -> Coq_ctx.Coq_nil
           | Coq_ptstomem_readonly width ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
           | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
           | Coq_mmio_checked_write width ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
           | Coq_encodes_instr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
           | Coq_ptstomem width ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec (mul width byte)))
           | Coq_ptstoinstr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
           | _ ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte)))
        _UU03a3_ ts)
  | Coq_chunk_ptsreg (_UU03c3_, r, t) ->
    RiscvPmpBase.liftUnOp RiscvPmpBase.substUniv_weaken _UU03a3_
      (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken _UU03c3_)
      (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken) (fun _ x ->
      Coq_chunk_ptsreg (_UU03c3_, r, x))
      (RiscvPmpBase.gen_occurs_check RiscvPmpBase.substUniv_weaken
        (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken _UU03c3_)
        (RiscvPmpBase.gen_occurs_check_term RiscvPmpBase.substUniv_weaken
          RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUnivVar_weaken
          RiscvPmpBase.substUniv_weaken RiscvPmpBase.substUnivMeet_weaken
          RiscvPmpBase.substUniv_weaken RiscvPmpBase.substUnivMeet_weaken
          _UU03c3_)
        _UU03a3_ t)
  | Coq_chunk_conj (c1, c2) ->
    RiscvPmpBase.liftBinOp RiscvPmpBase.substUniv_weaken
      RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
      RiscvPmpBase.substUnivMeet_weaken _UU03a3_
      (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken)
      (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken)
      (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken) (fun _ c1' c2' ->
      Coq_chunk_conj (c1', c2')) (coq_GenOccursCheckChunk _UU03a3_ c1)
      (coq_GenOccursCheckChunk _UU03a3_ c2)
  | Coq_chunk_wand (c1, c2) ->
    RiscvPmpBase.liftBinOp RiscvPmpBase.substUniv_weaken
      RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
      RiscvPmpBase.substUnivMeet_weaken _UU03a3_
      (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken)
      (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken)
      (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken) (fun _ c1' c2' ->
      Coq_chunk_wand (c1', c2')) (coq_GenOccursCheckChunk _UU03a3_ c1)
      (coq_GenOccursCheckChunk _UU03a3_ c2)

  type coq_SCHeap = coq_SCChunk list

  type coq_SHeap = coq_Chunk list

  (** val inst_heap : (coq_SHeap, coq_SCHeap) RiscvPmpBase.coq_Inst **)

  let inst_heap =
    RiscvPmpBase.inst_list inst_chunk

  (** val peval_chunk :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Chunk -> coq_Chunk **)

  let peval_chunk _UU03a3_ c =
    map_GChunk (RiscvPmpBase.peval _UU03a3_) c

  (** val try_consume_chunk_exact :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SHeap -> coq_Chunk -> coq_SHeap option **)

  let rec try_consume_chunk_exact _UU03a3_ h c =
    match h with
    | Coq_nil -> None
    | Coq_cons (c', h0) ->
      (match chunk_eqb (RiscvPmpBase.coq_Term_eqb _UU03a3_) c c' with
       | Coq_true ->
         Some
           (match chunk_isdup c with
            | Coq_true -> Coq_cons (c, h0)
            | Coq_false -> h0)
       | Coq_false ->
         option_map (fun x -> Coq_cons (c', x))
           (try_consume_chunk_exact _UU03a3_ h0 c))

  (** val match_chunk_user_precise_clause_1 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Predicate -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
      Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
      Coq_env.coq_Env -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
      Coq_env.coq_Env -> coq_Predicate -> sumbool -> (Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) Coq_env.coq_Env -> coq_PathCondition option **)

  let match_chunk_user_precise_clause_1 _UU03a3_ _ _UU0394_I _UU0394_O tsI tsO _ refine ts' =
    match refine with
    | Coq_left ->
      let Coq_env.Coq_isCat (tsI', tsO') =
        Coq_env.catView _UU0394_I _UU0394_O ts'
      in
      (match Coq_env.eqb_hom (RiscvPmpBase.coq_Term_eqb _UU03a3_) _UU0394_I
               tsI tsI' with
       | Coq_true -> Some (formula_eqs_ctx _UU0394_O _UU03a3_ tsO tsO')
       | Coq_false -> None)
    | Coq_right -> None

  (** val match_chunk_user_precise :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Predicate -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
      Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
      Coq_env.coq_Env -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
      Coq_env.coq_Env -> coq_Chunk -> coq_PathCondition option **)

  let match_chunk_user_precise _UU03a3_ p _UU0394_I _UU0394_O tsI tsO = function
  | Coq_chunk_user (p0, ts) ->
    (match eq_dec _UU1d46f__eq_dec p p0 with
     | Coq_left ->
       let Coq_env.Coq_isCat (tsI', tsO') =
         Coq_env.catView _UU0394_I _UU0394_O ts
       in
       (match Coq_env.eqb_hom (RiscvPmpBase.coq_Term_eqb _UU03a3_) _UU0394_I
                tsI tsI' with
        | Coq_true -> Some (formula_eqs_ctx _UU0394_O _UU03a3_ tsO tsO')
        | Coq_false -> None)
     | Coq_right -> None)
  | _ -> None

  (** val try_consume_chunk_user_precise :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Predicate -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
      Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
      Coq_env.coq_Env -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
      Coq_env.coq_Env -> coq_SHeap -> (coq_SHeap, coq_PathCondition) prod
      option **)

  let rec try_consume_chunk_user_precise _UU03a3_ p _UU0394_I _UU0394_O tsI tsO = function
  | Coq_nil -> None
  | Coq_cons (c, h') ->
    (match match_chunk_user_precise _UU03a3_ p _UU0394_I _UU0394_O tsI tsO c with
     | Some eqs ->
       Some (Coq_pair
         ((match _UU1d46f__is_dup p with
           | Coq_true -> Coq_cons (c, h')
           | Coq_false -> h'),
         eqs))
     | None ->
       option_map (prod_map (fun x -> Coq_cons (c, x)) (Obj.magic id))
         (try_consume_chunk_user_precise _UU03a3_ p _UU0394_I _UU0394_O tsI
           tsO h'))

  (** val match_chunk_ptsreg_precise_clause_1 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_Reg -> sumbool -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term option **)

  let match_chunk_ptsreg_precise_clause_1 _ _ _ _ _ refine t =
    match refine with
    | Coq_left -> Some t
    | Coq_right -> None

  (** val match_chunk_ptsreg_precise :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> coq_Chunk ->
      RiscvPmpBase.coq_Term option **)

  let match_chunk_ptsreg_precise _ _UU03c3_ r = function
  | Coq_chunk_ptsreg (_UU03c3_0, r0, v) ->
    (match eq_dec_het RiscvPmpBase._UU1d479__UU1d46c__UU1d46e__eq_dec
             _UU03c3_ _UU03c3_0 r r0 with
     | Coq_left -> Some v
     | Coq_right -> None)
  | _ -> None

  (** val find_chunk_ptsreg_precise :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> coq_SHeap ->
      (RiscvPmpBase.coq_Term, coq_SHeap) prod option **)

  let rec find_chunk_ptsreg_precise _UU03a3_ _UU03c3_ r = function
  | Coq_nil -> None
  | Coq_cons (c, h') ->
    (match match_chunk_ptsreg_precise _UU03a3_ _UU03c3_ r c with
     | Some t -> Some (Coq_pair (t, h'))
     | None ->
       option_map (prod_map (Obj.magic id) (fun x -> Coq_cons (c, x)))
         (find_chunk_ptsreg_precise _UU03a3_ _UU03c3_ r h'))

  (** val try_consume_chunk_ptsreg_precise :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> coq_SHeap ->
      RiscvPmpBase.coq_Term -> (coq_SHeap, coq_PathCondition) prod option **)

  let try_consume_chunk_ptsreg_precise _UU03a3_ _UU03c3_ r h t =
    Coq_option.map (fun pat ->
      let Coq_pair (t', h') = pat in
      Coq_pair (h', (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_relop
      (_UU03c3_, (Coq_bop.Coq_eq _UU03c3_), t, t'))))))
      (find_chunk_ptsreg_precise _UU03a3_ _UU03c3_ r h)

  (** val try_consume_chunk_precise :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SHeap -> coq_Chunk -> (coq_SHeap, coq_PathCondition) prod option **)

  let try_consume_chunk_precise _UU03a3_ h = function
  | Coq_chunk_user (p, ts) ->
    (match _UU1d46f__precise p with
     | Some p0 ->
       let { RiscvPmpBase.prec_input = _UU0394_I; RiscvPmpBase.prec_output =
         _UU0394_O } = p0
       in
       let Coq_env.Coq_isCat (tsI, tsO) =
         Coq_env.catView _UU0394_I _UU0394_O ts
       in
       try_consume_chunk_user_precise _UU03a3_ p _UU0394_I _UU0394_O tsI tsO h
     | None -> None)
  | Coq_chunk_ptsreg (_UU03c3_, r, t) ->
    try_consume_chunk_ptsreg_precise _UU03a3_ _UU03c3_ r h t
  | _ -> None

  (** val interpret_chunk :
      bi -> coq_PredicateDef -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Chunk -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> __ **)

  let rec interpret_chunk hProp pI _UU03a3_ c _UU03b9_ =
    match c with
    | Coq_chunk_user (p, ts) ->
      pI.luser p
        (RiscvPmpBase.inst
          (RiscvPmpBase.inst_env RiscvPmpBase.inst_term
            (match p with
             | Coq_pmp_entries ->
               Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
                 RiscvPmpBase.ty_pmpentry))
             | Coq_pmp_addr_access ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_privilege)
             | Coq_pmp_addr_access_without _ ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                 (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                 RiscvPmpBase.ty_privilege)
             | Coq_gprs -> Coq_ctx.Coq_nil
             | Coq_ptstomem_readonly width ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                 (mul width byte)))
             | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
             | Coq_mmio_checked_write width ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                 (mul width byte)))
             | Coq_encodes_instr ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
             | Coq_ptstomem width ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                 (mul width byte)))
             | Coq_ptstoinstr ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
             | _ ->
               Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte)))
          _UU03a3_ ts _UU03b9_)
    | Coq_chunk_ptsreg (_UU03c3_, r, t) ->
      pI.lptsreg _UU03c3_ r
        (RiscvPmpBase.inst (RiscvPmpBase.inst_term _UU03c3_) _UU03a3_ t
          _UU03b9_)
    | Coq_chunk_conj (c1, c2) ->
      hProp.bi_sep (interpret_chunk hProp pI _UU03a3_ c1 _UU03b9_)
        (interpret_chunk hProp pI _UU03a3_ c2 _UU03b9_)
    | Coq_chunk_wand (c1, c2) ->
      hProp.bi_wand (interpret_chunk hProp pI _UU03a3_ c1 _UU03b9_)
        (interpret_chunk hProp pI _UU03a3_ c2 _UU03b9_)

  (** val interpret_scchunk : bi -> coq_PredicateDef -> coq_SCChunk -> __ **)

  let rec interpret_scchunk hProp pI = function
  | Coq_chunk_user (p, vs) -> pI.luser p vs
  | Coq_chunk_ptsreg (_UU03c3_, r, v) -> pI.lptsreg _UU03c3_ r v
  | Coq_chunk_conj (c1, c2) ->
    hProp.bi_sep (interpret_scchunk hProp pI c1)
      (interpret_scchunk hProp pI c2)
  | Coq_chunk_wand (c1, c2) ->
    hProp.bi_wand (interpret_scchunk hProp pI c1)
      (interpret_scchunk hProp pI c2)

  (** val interpret_scheap : bi -> coq_PredicateDef -> coq_SCHeap -> __ **)

  let interpret_scheap hProp pI =
    fold_right (fun c h -> hProp.bi_sep (interpret_scchunk hProp pI c) h)
      hProp.bi_emp

  type coq_EChunk = RiscvPmpBase.coq_ETerm coq_GChunk

  (** val coq_Erase_Chunk : (coq_Chunk, coq_EChunk) RiscvPmpBase.coq_Erase **)

  let coq_Erase_Chunk _UU03a3_ =
    map_GChunk (fun _UU03c3_ t ->
      RiscvPmpBase.erase (RiscvPmpBase.erase_Term _UU03c3_) _UU03a3_ t)

  type coq_World = { wctx : (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                            Coq_ctx.coq_Ctx;
                     wco : coq_PathCondition }

  (** val wctx :
      coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let wctx w =
    w.wctx

  (** val wco : coq_World -> coq_PathCondition **)

  let wco w =
    w.wco

  (** val wnil : coq_World **)

  let wnil =
    { wctx = Coq_ctx.Coq_nil; wco = Coq_ctx.Coq_nil }

  (** val wlctx :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_World **)

  let wlctx _UU03a3_ =
    { wctx = _UU03a3_; wco = Coq_ctx.Coq_nil }

  (** val wsnoc :
      coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_World **)

  let wsnoc w b =
    { wctx = (Coq_ctx.Coq_snoc (w.wctx, b)); wco =
      (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) w.wctx w.wco
        (Coq_ctx.Coq_snoc (w.wctx, b)) (RiscvPmpBase.sub_wk1 w.wctx b)) }

  (** val term_var_zero :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> RiscvPmpBase.coq_Term **)

  let term_var_zero _UU03a3_ b =
    RiscvPmpBase.Coq_term_var (b.Binding.name, b.Binding.coq_type,
      (Coq_ctx.in_zero { Binding.name = b.Binding.name; Binding.coq_type =
        b.Binding.coq_type } _UU03a3_))

  (** val wlet :
      coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      Coq_ty.coq_Val -> coq_World **)

  let wlet w b v =
    { wctx = (Coq_ctx.Coq_snoc (w.wctx, b)); wco = (Coq_ctx.Coq_snoc
      ((RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) w.wctx w.wco
         (Coq_ctx.Coq_snoc (w.wctx, b)) (RiscvPmpBase.sub_wk1 w.wctx b)),
      (Coq_formula_relop (b.Binding.coq_type, (Coq_bop.Coq_eq
      b.Binding.coq_type), (term_var_zero w.wctx b),
      (RiscvPmpBase.Coq_term_val (b.Binding.coq_type, v)))))) }

  (** val wcat :
      coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_World **)

  let wcat w _UU0394_ =
    { wctx = (Coq_ctx.cat w.wctx _UU0394_); wco =
      (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) w.wctx w.wco
        (Coq_ctx.cat w.wctx _UU0394_)
        (RiscvPmpBase.sub_cat_left w.wctx _UU0394_)) }

  (** val wformula : coq_World -> coq_Formula -> coq_World **)

  let wformula w f =
    { wctx = w.wctx; wco = (Coq_ctx.Coq_snoc (w.wco, f)) }

  (** val wpathcondition : coq_World -> coq_PathCondition -> coq_World **)

  let wpathcondition w c =
    { wctx = w.wctx; wco = (Coq_ctx.cat w.wco c) }

  (** val wsubst :
      coq_World -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> coq_World **)

  let wsubst w x _UU03c3_ xIn t =
    { wctx =
      (Coq_ctx.remove w.wctx { Binding.name = x; Binding.coq_type =
        _UU03c3_ } xIn);
      wco =
      (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) w.wctx w.wco
        (Coq_ctx.remove w.wctx { Binding.name = x; Binding.coq_type =
          _UU03c3_ } xIn)
        (RiscvPmpBase.sub_single w.wctx { Binding.name = x;
          Binding.coq_type = _UU03c3_ } xIn t)) }

  (** val wmatch :
      coq_World -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> coq_LVar
      RiscvPmpBase.coq_Pattern -> coq_LVar RiscvPmpBase.coq_PatternCase ->
      coq_World **)

  let wmatch w _UU03c3_ s p pc =
    let _UU0394_ = RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc in
    let ts = RiscvPmpBase.sub_cat_right w.wctx _UU0394_ in
    let f1 = Coq_formula_relop (_UU03c3_, (Coq_bop.Coq_eq _UU03c3_),
      (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm _UU03c3_) w.wctx s
        (Coq_ctx.cat w.wctx _UU0394_)
        (RiscvPmpBase.sub_cat_left w.wctx _UU0394_)),
      (RiscvPmpBase.pattern_match_term_reverse (Coq_ctx.cat w.wctx _UU0394_)
        _UU03c3_ p pc ts))
    in
    wformula (wcat w _UU0394_) f1

  (** val wmatchvar_patternvars :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> coq_LVar RiscvPmpBase.coq_Pattern
      -> coq_LVar RiscvPmpBase.coq_PatternCase -> RiscvPmpBase.coq_Sub **)

  let wmatchvar_patternvars _UU03a3_ x _UU03c3_ xIn p pc =
    let _UU0394_ = RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc in
    RiscvPmpBase.sub_cat_right
      (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
        _UU03c3_ } xIn)
      _UU0394_

  (** val wmatchvar :
      coq_World -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> coq_LVar RiscvPmpBase.coq_Pattern
      -> coq_LVar RiscvPmpBase.coq_PatternCase -> coq_World **)

  let wmatchvar w x _UU03c3_ xIn p pc =
    let _UU0394_ = RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc in
    let w1 = wcat w _UU0394_ in
    let t' =
      RiscvPmpBase.pattern_match_term_reverse
        (Coq_ctx.remove
          (Coq_ctx.cat w.wctx (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc))
          { Binding.name = x; Binding.coq_type = _UU03c3_ }
          (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
            _UU03c3_ } w.wctx (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc)
            xIn))
        _UU03c3_ p pc (wmatchvar_patternvars w.wctx x _UU03c3_ xIn p pc)
    in
    wsubst w1 x _UU03c3_
      (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type = _UU03c3_ }
        w.wctx (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc) xIn)
      t'

  type 'a coq_Valid = coq_World -> 'a

  type ('a, 'b) coq_Impl = 'a -> 'b

  type ('i, 'a) coq_Forall = 'i -> 'a

  type coq_Tri =
  | Coq_tri_id
  | Coq_tri_cons of coq_World * coq_LVar * Coq_ty.coq_Ty
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * RiscvPmpBase.coq_Term * coq_Tri

  (** val coq_Tri_rect :
      (coq_World -> 'a1) -> (coq_World -> coq_World -> coq_LVar ->
      Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> coq_Tri -> 'a1 -> 'a1) ->
      coq_World -> coq_World -> coq_Tri -> 'a1 **)

  let rec coq_Tri_rect f f0 w _ = function
  | Coq_tri_id -> f w
  | Coq_tri_cons (w', x, _UU03c3_, xIn, t0, _UU03bd_) ->
    f0 w w' x _UU03c3_ xIn t0 _UU03bd_
      (coq_Tri_rect f f0 (wsubst w x _UU03c3_ xIn t0) w' _UU03bd_)

  (** val coq_Tri_rec :
      (coq_World -> 'a1) -> (coq_World -> coq_World -> coq_LVar ->
      Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> coq_Tri -> 'a1 -> 'a1) ->
      coq_World -> coq_World -> coq_Tri -> 'a1 **)

  let rec coq_Tri_rec f f0 w _ = function
  | Coq_tri_id -> f w
  | Coq_tri_cons (w', x, _UU03c3_, xIn, t0, _UU03bd_) ->
    f0 w w' x _UU03c3_ xIn t0 _UU03bd_
      (coq_Tri_rec f f0 (wsubst w x _UU03c3_ xIn t0) w' _UU03bd_)

  (** val tri_comp :
      coq_World -> coq_World -> coq_World -> coq_Tri -> coq_Tri -> coq_Tri **)

  let rec tri_comp w1 _ w3 _UU03bd_12 _UU03bd_ =
    match _UU03bd_12 with
    | Coq_tri_id -> _UU03bd_
    | Coq_tri_cons (w', x, _UU03c3_, xIn, t, _UU03bd_13) ->
      Coq_tri_cons (w3, x, _UU03c3_, xIn, t,
        (tri_comp (wsubst w1 x _UU03c3_ xIn t) w' w3 _UU03bd_13 _UU03bd_))

  (** val sub_wmatch_patctx :
      coq_World -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> coq_LVar
      RiscvPmpBase.coq_Pattern -> coq_LVar RiscvPmpBase.coq_PatternCase ->
      RiscvPmpBase.coq_Sub **)

  let sub_wmatch_patctx w _UU03c3_ _ p pc =
    RiscvPmpBase.sub_cat_right w.wctx
      (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc)

  (** val sub_triangular :
      coq_World -> coq_World -> coq_Tri -> RiscvPmpBase.coq_Sub **)

  let rec sub_triangular w1 _ = function
  | Coq_tri_id -> RiscvPmpBase.sub_id w1.wctx
  | Coq_tri_cons (w', x, _UU03c3_, xIn, t, _UU03b6_0) ->
    RiscvPmpBase.subst
      (RiscvPmpBase.coq_SubstEnv (fun b ->
        RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) w1.wctx)
      (Coq_ctx.remove w1.wctx { Binding.name = x; Binding.coq_type =
        _UU03c3_ } xIn)
      (RiscvPmpBase.sub_single w1.wctx { Binding.name = x; Binding.coq_type =
        _UU03c3_ } xIn t)
      w'.wctx (sub_triangular (wsubst w1 x _UU03c3_ xIn t) w' _UU03b6_0)

  (** val sub_triangular_inv :
      coq_World -> coq_World -> coq_Tri -> RiscvPmpBase.coq_Sub **)

  let rec sub_triangular_inv w1 _ = function
  | Coq_tri_id -> RiscvPmpBase.sub_id w1.wctx
  | Coq_tri_cons (w', x, _UU03c3_, xIn, t, _UU03b6_0) ->
    RiscvPmpBase.subst
      (RiscvPmpBase.coq_SubstEnv (fun b ->
        RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) w'.wctx)
      (wsubst w1 x _UU03c3_ xIn t).wctx
      (sub_triangular_inv (wsubst w1 x _UU03c3_ xIn t) w' _UU03b6_0) w1.wctx
      (RiscvPmpBase.sub_shift w1.wctx { Binding.name = x; Binding.coq_type =
        _UU03c3_ } xIn)

  type coq_Acc =
  | Coq_acc_refl
  | Coq_acc_sub of coq_World * RiscvPmpBase.coq_Sub

  (** val coq_Acc_rect :
      coq_World -> 'a1 -> (coq_World -> RiscvPmpBase.coq_Sub -> __ -> 'a1) ->
      coq_World -> coq_Acc -> 'a1 **)

  let coq_Acc_rect _ f f0 _ = function
  | Coq_acc_refl -> f
  | Coq_acc_sub (w2, _UU03b6_) -> f0 w2 _UU03b6_ __

  (** val coq_Acc_rec :
      coq_World -> 'a1 -> (coq_World -> RiscvPmpBase.coq_Sub -> __ -> 'a1) ->
      coq_World -> coq_Acc -> 'a1 **)

  let coq_Acc_rec _ f f0 _ = function
  | Coq_acc_refl -> f
  | Coq_acc_sub (w2, _UU03b6_) -> f0 w2 _UU03b6_ __

  (** val acc_trans :
      coq_World -> coq_World -> coq_World -> coq_Acc -> coq_Acc -> coq_Acc **)

  let acc_trans w0 _ _ _UU03c9_01 _UU03c9_12 =
    match _UU03c9_01 with
    | Coq_acc_refl -> _UU03c9_12
    | Coq_acc_sub (w2, _UU03b6_) ->
      (match _UU03c9_12 with
       | Coq_acc_refl -> Coq_acc_sub (w2, _UU03b6_)
       | Coq_acc_sub (w3, _UU03b6_0) ->
         Coq_acc_sub (w3,
           (RiscvPmpBase.subst
             (RiscvPmpBase.coq_SubstEnv (fun b ->
               RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) w0.wctx)
             w2.wctx _UU03b6_ w3.wctx _UU03b6_0)))

  (** val sub_acc :
      coq_World -> coq_World -> coq_Acc -> RiscvPmpBase.coq_Sub **)

  let sub_acc w1 _ = function
  | Coq_acc_refl -> RiscvPmpBase.sub_id w1.wctx
  | Coq_acc_sub (_, _UU03b6_) -> _UU03b6_

  type 'a coq_Box = coq_World -> coq_Acc -> 'a

  (** val acc_wnil_init : coq_World -> coq_Acc **)

  let acc_wnil_init w =
    Coq_acc_sub (w, Coq_env.Coq_nil)

  (** val acc_wlctx_valuation :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
      Coq_env.coq_Env -> coq_Acc **)

  let acc_wlctx_valuation _UU03a3_ _UU03b9_ =
    Coq_acc_sub (wnil,
      (RiscvPmpBase.lift
        (RiscvPmpBase.lift_env (fun _UU03c4_ ->
          RiscvPmpBase.lift_term _UU03c4_.Binding.coq_type) _UU03a3_)
        wnil.wctx _UU03b9_))

  (** val acc_snoc_right :
      coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Acc **)

  let acc_snoc_right w b =
    Coq_acc_sub ((wsnoc w b), (RiscvPmpBase.sub_wk1 w.wctx b))

  (** val acc_cat_right :
      coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Acc **)

  let acc_cat_right w _UU0394_ =
    Coq_acc_sub ((wcat w _UU0394_),
      (RiscvPmpBase.sub_cat_left w.wctx _UU0394_))

  (** val acc_snoc_left :
      coq_World -> coq_World -> coq_Acc -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> RiscvPmpBase.coq_Term -> coq_Acc **)

  let acc_snoc_left w1 w2 _UU03c9_12 b t =
    Coq_acc_sub (w2,
      (RiscvPmpBase.sub_snoc w1.wctx w2.wctx (sub_acc w1 w2 _UU03c9_12) b t))

  (** val acc_snoc_left' :
      coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      RiscvPmpBase.coq_Term -> coq_Acc **)

  let acc_snoc_left' w b t =
    acc_snoc_left w w Coq_acc_refl b t

  (** val acc_cat_left :
      coq_World -> coq_World -> coq_Acc -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Sub -> coq_Acc **)

  let acc_cat_left w1 w2 _UU03c9_12 _UU0394_ _UU03b6_ =
    Coq_acc_sub (w2,
      (Coq_env.cat w1.wctx _UU0394_ (sub_acc w1 w2 _UU03c9_12) _UU03b6_))

  (** val acc_formula_right : coq_World -> coq_Formula -> coq_Acc **)

  let acc_formula_right w f =
    Coq_acc_sub ((wformula w f), (RiscvPmpBase.sub_id w.wctx))

  (** val acc_pathcondition_right :
      coq_World -> coq_PathCondition -> coq_Acc **)

  let acc_pathcondition_right w c =
    Coq_acc_sub ((wpathcondition w c), (RiscvPmpBase.sub_id w.wctx))

  (** val acc_subst_right :
      coq_World -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> coq_Acc **)

  let acc_subst_right w x _UU03c3_ xIn t =
    let _UU03b6_ =
      RiscvPmpBase.sub_single w.wctx { Binding.name = x; Binding.coq_type =
        _UU03c3_ } xIn t
    in
    let w' = { wctx =
      (Coq_ctx.remove w.wctx { Binding.name = x; Binding.coq_type =
        _UU03c3_ } xIn);
      wco =
      (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) w.wctx w.wco
        (Coq_ctx.remove w.wctx { Binding.name = x; Binding.coq_type =
          _UU03c3_ } xIn)
        _UU03b6_) }
    in
    Coq_acc_sub (w', _UU03b6_)

  (** val acc_match_right :
      coq_World -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> coq_LVar
      RiscvPmpBase.coq_Pattern -> coq_LVar RiscvPmpBase.coq_PatternCase ->
      coq_Acc **)

  let acc_match_right w _UU03c3_ s p pc =
    Coq_acc_sub ((wmatch w _UU03c3_ s p pc),
      (RiscvPmpBase.sub_cat_left w.wctx
        (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc)))

  (** val sub_matchvar_right :
      coq_World -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> coq_LVar RiscvPmpBase.coq_Pattern
      -> coq_LVar RiscvPmpBase.coq_PatternCase -> RiscvPmpBase.coq_Sub **)

  let sub_matchvar_right w x _UU03c3_ xIn p pc =
    let _UU0394_ = RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc in
    let t =
      RiscvPmpBase.pattern_match_term_reverse
        (Coq_ctx.remove
          (Coq_ctx.cat w.wctx (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc))
          { Binding.name = x; Binding.coq_type = _UU03c3_ }
          (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
            _UU03c3_ } w.wctx (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc)
            xIn))
        _UU03c3_ p pc (wmatchvar_patternvars w.wctx x _UU03c3_ xIn p pc)
    in
    let sub_UU2081_ = RiscvPmpBase.sub_cat_left w.wctx _UU0394_ in
    let sub_UU2082_ =
      RiscvPmpBase.sub_single (Coq_ctx.cat w.wctx _UU0394_) { Binding.name =
        x; Binding.coq_type = _UU03c3_ }
        (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
          _UU03c3_ } w.wctx (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc)
          xIn)
        t
    in
    RiscvPmpBase.subst
      (RiscvPmpBase.coq_SubstEnv (fun b ->
        RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) w.wctx)
      (Coq_ctx.cat w.wctx _UU0394_) sub_UU2081_
      (Coq_ctx.remove (Coq_ctx.cat w.wctx _UU0394_) { Binding.name = x;
        Binding.coq_type = _UU03c3_ }
        (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
          _UU03c3_ } w.wctx (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc)
          xIn))
      sub_UU2082_

  (** val acc_matchvar_right :
      coq_World -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> coq_LVar RiscvPmpBase.coq_Pattern
      -> coq_LVar RiscvPmpBase.coq_PatternCase -> coq_Acc **)

  let acc_matchvar_right w x _UU03c3_ xIn p pc =
    let _UU0394_ = RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc in
    let w1 = wcat w _UU0394_ in
    let t =
      RiscvPmpBase.pattern_match_term_reverse
        (Coq_ctx.remove
          (Coq_ctx.cat w.wctx (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc))
          { Binding.name = x; Binding.coq_type = _UU03c3_ }
          (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
            _UU03c3_ } w.wctx (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc)
            xIn))
        _UU03c3_ p pc (wmatchvar_patternvars w.wctx x _UU03c3_ xIn p pc)
    in
    let wmv =
      wsubst w1 x _UU03c3_
        (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
          _UU03c3_ } w.wctx (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ p pc)
          xIn)
        t
    in
    let sub0 = sub_matchvar_right w x _UU03c3_ xIn p pc in
    Coq_acc_sub (wmv, sub0)

  (** val acc_triangular : coq_World -> coq_World -> coq_Tri -> coq_Acc **)

  let rec acc_triangular w1 _ = function
  | Coq_tri_id -> Coq_acc_refl
  | Coq_tri_cons (w', x, _UU03c3_, xIn, t, _UU03bd_0) ->
    acc_trans w1 (wsubst w1 x _UU03c3_ xIn t) w'
      (acc_subst_right w1 x _UU03c3_ xIn t)
      (acc_triangular (wsubst w1 x _UU03c3_ xIn t) w' _UU03bd_0)

  (** val preorder_acc : (coq_World, coq_Acc) coq_PreOrder **)

  let preorder_acc =
    { coq_PreOrder_Reflexive = (Obj.magic (fun _ -> Coq_acc_refl));
      coq_PreOrder_Transitive = acc_trans }

  (** val coq_K :
      (('a1, 'a2) coq_Impl coq_Box, ('a1 coq_Box, 'a2 coq_Box) coq_Impl)
      coq_Impl coq_Valid **)

  let coq_K _ f a w1 _UU03c9_01 =
    f w1 _UU03c9_01 (a w1 _UU03c9_01)

  (** val coq_T : ('a1 coq_Box, 'a1) coq_Impl coq_Valid **)

  let coq_T w0 a =
    a w0 Coq_acc_refl

  (** val four : ('a1 coq_Box, 'a1 coq_Box coq_Box) coq_Impl coq_Valid **)

  let four w0 a w1 _UU03c9_01 w2 _UU03c9_12 =
    a w2 (acc_trans w0 w1 w2 _UU03c9_01 _UU03c9_12)

  (** val valid_box : 'a1 coq_Valid -> 'a1 coq_Box coq_Valid **)

  let valid_box a _ w1 _ =
    a w1

  (** val fmap_box :
      ('a1, 'a2) coq_Impl coq_Valid -> ('a1 coq_Box, 'a2 coq_Box) coq_Impl
      coq_Valid **)

  let fmap_box f _ a w1 _UU03c9_01 =
    f w1 (a w1 _UU03c9_01)

  (** val extend_box :
      ('a1 coq_Box, 'a2) coq_Impl coq_Valid -> ('a1 coq_Box, 'a2 coq_Box)
      coq_Impl coq_Valid **)

  let extend_box f w0 a w1 _UU03c9_01 =
    f w1 (four w0 a w1 _UU03c9_01)

  (** val comp :
      (('a2, 'a3) coq_Impl, (('a1, 'a2) coq_Impl, ('a1, 'a3) coq_Impl)
      coq_Impl) coq_Impl coq_Valid **)

  let comp _ =
    compose

  module ModalNotations =
   struct
   end

  type 'a coq_Persistent = ('a, 'a coq_Box) coq_Impl coq_Valid

  (** val persist :
      'a1 coq_Persistent -> ('a1, 'a1 coq_Box) coq_Impl coq_Valid **)

  let persist persistent =
    persistent

  (** val persistent_box : 'a1 coq_Box coq_Persistent **)

  let persistent_box =
    four

  (** val persistent_subst :
      'a1 RiscvPmpBase.coq_Subst -> 'a1 coq_Persistent **)

  let persistent_subst h w0 x _ = function
  | Coq_acc_refl -> x
  | Coq_acc_sub (w2, _UU03b6_) ->
    RiscvPmpBase.subst h w0.wctx x w2.wctx _UU03b6_

  type coq_Pred = __

  type 'a coq_Tm = 'a

  (** val bi_pred : coq_World -> bi **)

  let bi_pred _ =
    { bi_emp = (Obj.magic __); bi_pure = (Obj.magic __); bi_and =
      (Obj.magic __); bi_or = (Obj.magic __); bi_impl = (Obj.magic __);
      bi_forall = (Obj.magic __); bi_exist = (Obj.magic __); bi_sep =
      (Obj.magic __); bi_wand = (Obj.magic __); bi_persistently =
      (Obj.magic __); bi_later = (Obj.magic __); bi_cofe_aux =
      (discrete_cofe __) }

  type 't coq_InstPred =
  | MkInstPred

  (** val instpred_option :
      'a1 coq_InstPred -> 'a1 RiscvPmpBase.coq_Option coq_InstPred **)

  let instpred_option _ =
    MkInstPred

  (** val instpred_pair :
      'a1 coq_InstPred -> 'a2 coq_InstPred -> ('a1, 'a2)
      RiscvPmpBase.coq_Pair coq_InstPred **)

  let instpred_pair _ _ =
    MkInstPred

  (** val instpred_ctx_inst :
      'a1 coq_InstPred -> 'a1 Coq_ctx.coq_Ctx coq_InstPred **)

  let instpred_ctx_inst _ =
    MkInstPred

  (** val instpred_inst_formula : coq_Formula coq_InstPred **)

  let instpred_inst_formula =
    MkInstPred

  type coq_Solver =
    coq_World -> coq_PathCondition -> (coq_World, (coq_Tri,
    coq_PathCondition) prod) sigT option

  (** val solver_null : coq_Solver **)

  let solver_null w c =
    Some (Coq_existT (w, (Coq_pair (Coq_tri_id, c))))

  type coq_SolverUserOnly =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_PurePredicate -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
    Coq_env.coq_Env -> coq_PathCondition RiscvPmpBase.coq_Option

  (** val simplify_all :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_Formula -> coq_PathCondition -> coq_PathCondition option) ->
      coq_PathCondition -> coq_PathCondition -> coq_PathCondition option **)

  let rec simplify_all _UU03a3_ g c k =
    match c with
    | Coq_ctx.Coq_nil -> Some k
    | Coq_ctx.Coq_snoc (c0, f) ->
      Coq_option.bind (simplify_all _UU03a3_ g c0 k) (fun k' -> g f k')

  (** val solveruseronly_simplify_formula :
      coq_SolverUserOnly -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Formula -> coq_PathCondition ->
      coq_PathCondition option **)

  let solveruseronly_simplify_formula user _UU03a3_ f k =
    match f with
    | Coq_formula_user (p, ts) ->
      Coq_option.map (fun r -> Coq_ctx.cat k r) (user _UU03a3_ p ts)
    | _ -> Some (Coq_ctx.Coq_snoc (k, f))

  (** val solveruseronly_to_solver : coq_SolverUserOnly -> coq_Solver **)

  let solveruseronly_to_solver user w c =
    option_map (fun l -> Coq_existT (w, (Coq_pair (Coq_tri_id, l))))
      (simplify_all w.wctx (solveruseronly_simplify_formula user w.wctx) c
        Coq_ctx.Coq_nil)

  (** val solver_compose : coq_Solver -> coq_Solver -> coq_Solver **)

  let solver_compose s1 s2 w0 fmls0 =
    Coq_option.bind (s1 w0 fmls0) (fun pat ->
      let Coq_existT (w1, p) = pat in
      let Coq_pair (_UU03bd_01, fmls1) = p in
      Coq_option.map (fun pat0 ->
        let Coq_existT (w2, y) = pat0 in
        let Coq_pair (_UU03bd_12, fmls2) = y in
        Coq_existT (w2, (Coq_pair ((tri_comp w0 w1 w2 _UU03bd_01 _UU03bd_12),
        fmls2)))) (s2 w1 fmls1))

  module DList =
   struct
    type coq_DList =
      coq_PathCondition -> coq_PathCondition RiscvPmpBase.coq_Option
      (* singleton inductive, whose constructor was MkDList *)

    (** val raw :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_DList -> coq_PathCondition -> coq_PathCondition
        RiscvPmpBase.coq_Option **)

    let raw _ d =
      d

    (** val instpred_dlist : coq_DList coq_InstPred **)

    let instpred_dlist =
      MkInstPred

    (** val singleton :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> coq_DList **)

    let singleton _ f k =
      Some (Coq_ctx.Coq_snoc (k, f))

    (** val run :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_DList -> coq_PathCondition RiscvPmpBase.coq_Option **)

    let run _ xs =
      xs Coq_ctx.Coq_nil

    (** val error :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_DList **)

    let error _ _ =
      None

    (** val empty :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_DList **)

    let empty _ x =
      Some x

    (** val cat :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_DList -> coq_DList -> coq_DList **)

    let cat _ xs ys k =
      Coq_option.bind (xs k) ys
   end

  (** val is_off :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> coq_Formula **)

  let is_off _ a =
    Coq_formula_relop (RiscvPmpBase.ty_pmpaddrmatchtype, (Coq_bop.Coq_eq
      RiscvPmpBase.ty_pmpaddrmatchtype), a, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_pmpaddrmatchtype, (Obj.magic OFF))))

  (** val is_on :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> coq_Formula **)

  let is_on _ a =
    Coq_formula_relop (RiscvPmpBase.ty_pmpaddrmatchtype, (Coq_bop.Coq_neq
      RiscvPmpBase.ty_pmpaddrmatchtype), a, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_pmpaddrmatchtype, (Obj.magic OFF))))

  (** val is_TOR :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> coq_Formula **)

  let is_TOR _ a =
    Coq_formula_relop (RiscvPmpBase.ty_pmpaddrmatchtype, (Coq_bop.Coq_eq
      RiscvPmpBase.ty_pmpaddrmatchtype), a, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_pmpaddrmatchtype, (Obj.magic TOR))))

  (** val is_machine_mode :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> coq_Formula **)

  let is_machine_mode _ p =
    Coq_formula_relop (RiscvPmpBase.ty_privilege, (Coq_bop.Coq_eq
      RiscvPmpBase.ty_privilege), (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine))), p)

  (** val fml_pmp_match_conditions :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> RiscvPmpBase.coq_Term -> coq_Formula **)

  let fml_pmp_match_conditions _ a width lo hi =
    Coq_formula_and ((Coq_formula_relop ((Coq_ty.Coq_bvec xlenbits),
      (Coq_bop.Coq_bvule xlenbits), lo, hi)), (Coq_formula_and
      ((Coq_formula_relop ((Coq_ty.Coq_bvec xlenbits), (Coq_bop.Coq_bvult
      xlenbits), lo, (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_bvec
      xlenbits), (Coq_ty.Coq_bvec xlenbits), (Coq_ty.Coq_bvec xlenbits),
      (Coq_bop.Coq_bvadd xlenbits), a, width)))), (Coq_formula_and
      ((Coq_formula_relop ((Coq_ty.Coq_bvec xlenbits), (Coq_bop.Coq_bvule
      xlenbits), lo, a)), (Coq_formula_and ((Coq_formula_relop
      ((Coq_ty.Coq_bvec xlenbits), (Coq_bop.Coq_bvult xlenbits), a, hi)),
      (Coq_formula_relop ((Coq_ty.Coq_bvec xlenbits), (Coq_bop.Coq_bvule
      xlenbits), (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_bvec xlenbits),
      (Coq_ty.Coq_bvec xlenbits), (Coq_ty.Coq_bvec xlenbits),
      (Coq_bop.Coq_bvadd xlenbits), a, width)), hi)))))))))

  (** val fml_pmp_match :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> RiscvPmpBase.coq_Term -> (Coq_ty.recordf, Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) coq_NamedEnv -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> coq_Formula **)

  let fml_pmp_match _UU03a3_ a width prev_pmpaddr pmpaddr cfg p acc =
    Coq_formula_and
      ((is_on _UU03a3_
         (Coq_env.lookup
           (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty
             Coq_rpmpcfg_ent)
           (Obj.magic cfg) { Binding.name = (String ((Ascii (Coq_true,
           Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
           Coq_false)), EmptyString)); Binding.coq_type = (Coq_ty.Coq_enum
           (Obj.magic Coq_pmpaddrmatchtype)) } (S (S (S O))))),
      (Coq_formula_and
      ((fml_pmp_match_conditions _UU03a3_ a width prev_pmpaddr pmpaddr),
      (Coq_formula_user (Coq_pmp_check_perms, (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      (Coq_ty.Coq_record (Obj.magic Coq_rpmpcfg_ent)))),
      RiscvPmpBase.ty_access_type)), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, (Coq_ty.Coq_record (Obj.magic Coq_rpmpcfg_ent)))),
      (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil, (Coq_ty.Coq_record
      (Obj.magic Coq_rpmpcfg_ent)), (RiscvPmpBase.Coq_term_record
      ((Obj.magic Coq_rpmpcfg_ent), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_pmpaddrmatchtype })),
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_pmpaddrmatchtype })),
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_pmpaddrmatchtype })),
      (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool },
      (Coq_env.lookup
        (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty Coq_rpmpcfg_ent)
        (Obj.magic cfg) { Binding.name = (String ((Ascii (Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false)), EmptyString)); Binding.coq_type = Coq_ty.Coq_bool } (S
        (S (S (S O))))))),
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_pmpaddrmatchtype },
      (Coq_env.lookup
        (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty Coq_rpmpcfg_ent)
        (Obj.magic cfg) { Binding.name = (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_false)), EmptyString)); Binding.coq_type =
        RiscvPmpBase.ty_pmpaddrmatchtype } (S (S (S O)))))),
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool },
      (Coq_env.lookup
        (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty Coq_rpmpcfg_ent)
        (Obj.magic cfg) { Binding.name = (String ((Ascii (Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_false)), EmptyString)); Binding.coq_type = Coq_ty.Coq_bool } (S
        (S O))))),
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool },
      (Coq_env.lookup
        (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty Coq_rpmpcfg_ent)
        (Obj.magic cfg) { Binding.name = (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)),
        EmptyString)); Binding.coq_type = Coq_ty.Coq_bool } (S O)))),
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool },
      (Coq_env.lookup
        (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty Coq_rpmpcfg_ent)
        (Obj.magic cfg) { Binding.name = (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_false)), EmptyString)); Binding.coq_type = Coq_ty.Coq_bool } O))))))),
      RiscvPmpBase.ty_access_type, acc)), RiscvPmpBase.ty_privilege, p)))))))

  (** val fml_pmp_nomatch_conditions :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> RiscvPmpBase.coq_Term -> coq_Formula **)

  let fml_pmp_nomatch_conditions _ a width lo hi =
    Coq_formula_or ((Coq_formula_relop ((Coq_ty.Coq_bvec xlenbits),
      (Coq_bop.Coq_bvult xlenbits), hi, lo)), (Coq_formula_or
      ((Coq_formula_and ((Coq_formula_relop ((Coq_ty.Coq_bvec xlenbits),
      (Coq_bop.Coq_bvule xlenbits), lo, hi)), (Coq_formula_relop
      ((Coq_ty.Coq_bvec xlenbits), (Coq_bop.Coq_bvule xlenbits),
      (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_bvec xlenbits),
      (Coq_ty.Coq_bvec xlenbits), (Coq_ty.Coq_bvec xlenbits),
      (Coq_bop.Coq_bvadd xlenbits), a, width)), lo)))), (Coq_formula_and
      ((Coq_formula_relop ((Coq_ty.Coq_bvec xlenbits), (Coq_bop.Coq_bvule
      xlenbits), lo, hi)), (Coq_formula_and ((Coq_formula_relop
      ((Coq_ty.Coq_bvec xlenbits), (Coq_bop.Coq_bvult xlenbits), lo,
      (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_bvec xlenbits),
      (Coq_ty.Coq_bvec xlenbits), (Coq_ty.Coq_bvec xlenbits),
      (Coq_bop.Coq_bvadd xlenbits), a, width)))), (Coq_formula_relop
      ((Coq_ty.Coq_bvec xlenbits), (Coq_bop.Coq_bvule xlenbits), hi,
      a)))))))))

  (** val fml_pmp_nomatch :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> RiscvPmpBase.coq_Term -> (Coq_ty.recordf, Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) coq_NamedEnv -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> coq_Formula -> coq_Formula **)

  let fml_pmp_nomatch _UU03a3_ a width prev_pmpaddr pmpaddr cfg _ _ cont =
    Coq_formula_and ((Coq_formula_or
      ((is_off _UU03a3_
         (Coq_env.lookup
           (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty
             Coq_rpmpcfg_ent)
           (Obj.magic cfg) { Binding.name = (String ((Ascii (Coq_true,
           Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
           Coq_false)), EmptyString)); Binding.coq_type = (Coq_ty.Coq_enum
           (Obj.magic Coq_pmpaddrmatchtype)) } (S (S (S O))))),
      (Coq_formula_and
      ((is_on _UU03a3_
         (Coq_env.lookup
           (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty
             Coq_rpmpcfg_ent)
           (Obj.magic cfg) { Binding.name = (String ((Ascii (Coq_true,
           Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
           Coq_false)), EmptyString)); Binding.coq_type = (Coq_ty.Coq_enum
           (Obj.magic Coq_pmpaddrmatchtype)) } (S (S (S O))))),
      (fml_pmp_nomatch_conditions _UU03a3_ a width prev_pmpaddr pmpaddr))))),
      cont)

  (** val cfg_to_env :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Pmpcfg_ent -> (Coq_ty.recordf, Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) coq_NamedEnv **)

  let cfg_to_env _ cfg =
    Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_pmpaddrmatchtype })),
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_pmpaddrmatchtype })),
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_pmpaddrmatchtype })),
      (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool }, (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic cfg.coq_L))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_pmpaddrmatchtype },
      (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_pmpaddrmatchtype,
      (Obj.magic cfg.coq_A))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool }, (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic cfg.coq_X))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool }, (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic cfg.coq_W))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = Coq_ty.Coq_bool }, (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic cfg.coq_R))))

  (** val simplify_pmpcheck_pure_list :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> coq_PmpEntryCfg list -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> coq_Formula **)

  let rec simplify_pmpcheck_pure_list _UU03a3_ a width lo es p acc =
    match es with
    | Coq_nil -> is_machine_mode _UU03a3_ p
    | Coq_cons (p0, es0) ->
      let Coq_pair (cfg, addr) = p0 in
      let cfg0 = cfg_to_env _UU03a3_ cfg in
      let addr0 = RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_xlenbits,
        (Obj.magic addr))
      in
      let fml = simplify_pmpcheck_pure_list _UU03a3_ a width addr0 es0 p acc
      in
      Coq_formula_or
      ((fml_pmp_nomatch _UU03a3_ a width lo addr0 cfg0 p acc fml),
      (fml_pmp_match _UU03a3_ a width lo addr0 cfg0 p acc))

  (** val simplify_pmpcheck :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_ListView ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_Formula option **)

  let rec simplify_pmpcheck _UU03a3_ _ a width lo es p acc =
    match es with
    | RiscvPmpBase.Coq_term_list_val l ->
      Some
        (simplify_pmpcheck_pure_list _UU03a3_ a width lo (Obj.magic l) p acc)
    | RiscvPmpBase.Coq_term_list_cons (pmp, t0, es0) ->
      Coq_option.bind
        (RiscvPmpBase.term_get_pair _UU03a3_ RiscvPmpBase.ty_pmpcfg_ent
          RiscvPmpBase.ty_xlenbits pmp)
        (fun pat ->
        let Coq_pair (cfg, addr) = pat in
        Coq_option.bind
          (RiscvPmpBase.term_get_record (Obj.magic Coq_rpmpcfg_ent) _UU03a3_
            cfg)
          (fun cfg0 ->
          Coq_option.bind
            (simplify_pmpcheck _UU03a3_ t0 a width addr es0 p acc)
            (fun fml -> Some (Coq_formula_or
            ((fml_pmp_nomatch _UU03a3_ a width lo addr cfg0 p acc fml),
            (fml_pmp_match _UU03a3_ a width lo addr cfg0 p acc))))))
    | _ -> None

  (** val simplify_pmpcheck_term_list :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> coq_Formula option **)

  let simplify_pmpcheck_term_list _UU03a3_ a width lo es p acc =
    simplify_pmpcheck _UU03a3_ es a width lo
      (Obj.magic RiscvPmpBase.view _UU03a3_ (Coq_ty.Coq_list
        RiscvPmpBase.ty_pmpentry) es)
      p acc

  (** val pmp_check_fml_term_aux :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> coq_Formula **)

  let pmp_check_fml_term_aux _UU03a3_ a width lo entries p acc =
    let fml = simplify_pmpcheck_term_list _UU03a3_ a width lo entries p acc in
    (match fml with
     | Some fml0 -> fml0
     | None ->
       Coq_formula_user (Coq_gen_pmp_access, (Coq_env.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
         RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
         RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
         RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
         RiscvPmpBase.ty_pmpentry))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
         (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
         (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, a)),
         RiscvPmpBase.ty_xlenbits, width)), RiscvPmpBase.ty_xlenbits, lo)),
         (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), entries)),
         RiscvPmpBase.ty_privilege, p)), RiscvPmpBase.ty_access_type, acc))))

  (** val pmp_check_fml_aux :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val
      list -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> coq_Formula **)

  let pmp_check_fml_aux _UU03a3_ a width lo entries p acc =
    let a0 = RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_xlenbits, a) in
    let width0 = RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_xlenbits, width)
    in
    let lo0 = RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_xlenbits, lo) in
    let entries0 = RiscvPmpBase.Coq_term_val ((Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry), (Obj.magic entries))
    in
    let p0 = RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_privilege, p) in
    let acc0 = RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_access_type, acc) in
    pmp_check_fml_term_aux _UU03a3_ a0 width0 lo0 entries0 p0 acc0

  (** val simplify_sub_perm :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_PathCondition
      option **)

  let simplify_sub_perm _UU03a3_ a1 a2 =
    match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_access_type a1 with
    | Some a3 ->
      (match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_access_type a2 with
       | Some a4 ->
         (match decide_sub_perm a3 a4 with
          | Coq_true -> Some Coq_ctx.Coq_nil
          | Coq_false -> None)
       | None ->
         Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
           (Coq_sub_perm, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_access_type)), (Coq_env.Coq_snoc
           (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_access_type,
           a1)), RiscvPmpBase.ty_access_type, a2)))))))
    | None ->
      Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
        (Coq_sub_perm, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        RiscvPmpBase.ty_access_type)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
        Coq_env.Coq_nil, RiscvPmpBase.ty_access_type, a1)),
        RiscvPmpBase.ty_access_type, a2))))))

  (** val simplify_access_pmp_perm :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_PathCondition
      option **)

  let simplify_access_pmp_perm _UU03a3_ a p =
    match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_access_type a with
    | Some a0 ->
      (match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_pmpcfgperm p with
       | Some p0 ->
         (match decide_access_pmp_perm (Obj.magic a0) (Obj.magic p0) with
          | Coq_true -> Some Coq_ctx.Coq_nil
          | Coq_false -> None)
       | None ->
         Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
           (Coq_access_pmp_perm, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_access_type)), (Coq_env.Coq_snoc
           (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_access_type,
           a)), RiscvPmpBase.ty_pmpcfgperm, p)))))))
    | None ->
      Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
        (Coq_access_pmp_perm, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, RiscvPmpBase.ty_access_type)), (Coq_env.Coq_snoc
        (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_access_type, a)),
        RiscvPmpBase.ty_pmpcfgperm, p))))))

  (** val simplify_gen_pmp_access :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> coq_PathCondition option **)

  let simplify_gen_pmp_access _UU03a3_ paddr width lo es p acc =
    match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_xlenbits paddr with
    | Some paddr0 ->
      (match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_xlenbits width with
       | Some width0 ->
         (match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_xlenbits lo with
          | Some lo0 ->
            (match RiscvPmpBase.term_get_val _UU03a3_ (Coq_ty.Coq_list
                     RiscvPmpBase.ty_pmpentry) es with
             | Some entries ->
               (match RiscvPmpBase.term_get_val _UU03a3_
                        RiscvPmpBase.ty_privilege p with
                | Some p0 ->
                  (match RiscvPmpBase.term_get_val _UU03a3_
                           RiscvPmpBase.ty_access_type acc with
                   | Some acc0 ->
                     (match pmp_check_aux (Obj.magic paddr0)
                              (Obj.magic width0) (Obj.magic lo0)
                              (Obj.magic entries) (Obj.magic p0)
                              (Obj.magic acc0) with
                      | Coq_true -> Some Coq_ctx.Coq_nil
                      | Coq_false -> None)
                   | None ->
                     Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                       (pmp_check_fml_term_aux _UU03a3_ paddr width lo es p
                         acc))))
                | None ->
                  Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                    (pmp_check_fml_term_aux _UU03a3_ paddr width lo es p acc))))
             | None ->
               Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 (pmp_check_fml_term_aux _UU03a3_ paddr width lo es p acc))))
          | None ->
            Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
              (pmp_check_fml_term_aux _UU03a3_ paddr width lo es p acc))))
       | None ->
         Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
           (pmp_check_fml_term_aux _UU03a3_ paddr width lo es p acc))))
    | None ->
      Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        (pmp_check_fml_term_aux _UU03a3_ paddr width lo es p acc)))

  (** val simplify_pmp_access :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_PathCondition
      option **)

  let simplify_pmp_access _UU03a3_ paddr width es p acc =
    simplify_gen_pmp_access _UU03a3_ paddr width (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_xlenbits, (Obj.magic Coq_bv.zero xlenbits))) es p acc

  (** val simplify_pmp_check_rwx :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_PathCondition
      option **)

  let simplify_pmp_check_rwx _UU03a3_ cfg acc =
    match RiscvPmpBase.term_get_record (Obj.magic Coq_rpmpcfg_ent) _UU03a3_
            cfg with
    | Some cfg' ->
      (match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_access_type
               acc with
       | Some acc' ->
         (match Obj.magic acc' with
          | Read ->
            (match RiscvPmpBase.term_get_val _UU03a3_ Coq_ty.Coq_bool
                     (Coq_env.lookup
                       (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty
                         Coq_rpmpcfg_ent)
                       (Obj.magic cfg') { Binding.name = (String ((Ascii
                       (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                       Coq_false, Coq_true, Coq_false)), EmptyString));
                       Binding.coq_type = Coq_ty.Coq_bool } O) with
             | Some v ->
               (match Obj.magic v with
                | Coq_true -> Some Coq_ctx.Coq_nil
                | Coq_false -> None)
             | None ->
               Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
                 (Coq_pmp_check_rwx, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
                 (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
                 RiscvPmpBase.ty_pmpcfg_ent, cfg)),
                 RiscvPmpBase.ty_access_type, acc)))))))
          | Write ->
            (match RiscvPmpBase.term_get_val _UU03a3_ Coq_ty.Coq_bool
                     (Coq_env.lookup
                       (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty
                         Coq_rpmpcfg_ent)
                       (Obj.magic cfg') { Binding.name = (String ((Ascii
                       (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                       Coq_false, Coq_true, Coq_false)), EmptyString));
                       Binding.coq_type = Coq_ty.Coq_bool } (S O)) with
             | Some v ->
               (match Obj.magic v with
                | Coq_true -> Some Coq_ctx.Coq_nil
                | Coq_false -> None)
             | None ->
               Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
                 (Coq_pmp_check_rwx, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
                 (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
                 RiscvPmpBase.ty_pmpcfg_ent, cfg)),
                 RiscvPmpBase.ty_access_type, acc)))))))
          | ReadWrite ->
            (match RiscvPmpBase.term_get_val _UU03a3_ Coq_ty.Coq_bool
                     (Coq_env.lookup
                       (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty
                         Coq_rpmpcfg_ent)
                       (Obj.magic cfg') { Binding.name = (String ((Ascii
                       (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                       Coq_false, Coq_true, Coq_false)), EmptyString));
                       Binding.coq_type = Coq_ty.Coq_bool } O) with
             | Some b1 ->
               (match RiscvPmpBase.term_get_val _UU03a3_ Coq_ty.Coq_bool
                        (Coq_env.lookup
                          (Obj.magic
                            RiscvPmpBase.typedefkit.Coq_ty.recordf_ty
                            Coq_rpmpcfg_ent)
                          (Obj.magic cfg') { Binding.name = (String ((Ascii
                          (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                          Coq_false, Coq_true, Coq_false)), EmptyString));
                          Binding.coq_type = Coq_ty.Coq_bool } (S O)) with
                | Some b2 ->
                  (match match Obj.magic b1 with
                         | Coq_true -> Obj.magic b2
                         | Coq_false -> Coq_false with
                   | Coq_true -> Some Coq_ctx.Coq_nil
                   | Coq_false -> None)
                | None ->
                  Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
                    (Coq_pmp_check_rwx, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
                    (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
                    (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
                    RiscvPmpBase.ty_pmpcfg_ent, cfg)),
                    RiscvPmpBase.ty_access_type, acc)))))))
             | None ->
               Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
                 (Coq_pmp_check_rwx, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
                 (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
                 RiscvPmpBase.ty_pmpcfg_ent, cfg)),
                 RiscvPmpBase.ty_access_type, acc)))))))
          | Execute ->
            (match RiscvPmpBase.term_get_val _UU03a3_ Coq_ty.Coq_bool
                     (Coq_env.lookup
                       (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty
                         Coq_rpmpcfg_ent)
                       (Obj.magic cfg') { Binding.name = (String ((Ascii
                       (Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                       Coq_false, Coq_true, Coq_false)), EmptyString));
                       Binding.coq_type = Coq_ty.Coq_bool } (S (S O))) with
             | Some v ->
               (match Obj.magic v with
                | Coq_true -> Some Coq_ctx.Coq_nil
                | Coq_false -> None)
             | None ->
               Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
                 (Coq_pmp_check_rwx, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
                 (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
                 RiscvPmpBase.ty_pmpcfg_ent, cfg)),
                 RiscvPmpBase.ty_access_type, acc))))))))
       | None ->
         Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
           (Coq_pmp_check_rwx, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)), (Coq_env.Coq_snoc
           (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent,
           cfg)), RiscvPmpBase.ty_access_type, acc)))))))
    | None ->
      Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
        (Coq_pmp_check_rwx, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)), (Coq_env.Coq_snoc
        (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent, cfg)),
        RiscvPmpBase.ty_access_type, acc))))))

  (** val simplify_pmp_check_perms :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> coq_PathCondition option **)

  let simplify_pmp_check_perms _UU03a3_ cfg acc p =
    match RiscvPmpBase.term_get_record (Obj.magic Coq_rpmpcfg_ent) _UU03a3_
            cfg with
    | Some cfg' ->
      (match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_privilege p with
       | Some v ->
         (match Obj.magic v with
          | User ->
            Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
              (Coq_pmp_check_rwx, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
              (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
              (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
              RiscvPmpBase.ty_pmpcfg_ent, cfg)), RiscvPmpBase.ty_access_type,
              acc))))))
          | Machine ->
            (match RiscvPmpBase.term_get_val _UU03a3_ Coq_ty.Coq_bool
                     (Coq_env.lookup
                       (Obj.magic RiscvPmpBase.typedefkit.Coq_ty.recordf_ty
                         Coq_rpmpcfg_ent)
                       (Obj.magic cfg') { Binding.name = (String ((Ascii
                       (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
                       Coq_false, Coq_true, Coq_false)), EmptyString));
                       Binding.coq_type = Coq_ty.Coq_bool } (S (S (S (S O))))) with
             | Some v0 ->
               (match Obj.magic v0 with
                | Coq_true ->
                  Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
                    (Coq_pmp_check_rwx, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
                    (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
                    (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
                    RiscvPmpBase.ty_pmpcfg_ent, cfg)),
                    RiscvPmpBase.ty_access_type, acc))))))
                | Coq_false -> Some Coq_ctx.Coq_nil)
             | None ->
               Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
                 (Coq_pmp_check_perms, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
                 ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)),
                 (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_pmpcfg_ent)), (Coq_env.Coq_snoc
                 (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
                 RiscvPmpBase.ty_pmpcfg_ent, cfg)),
                 RiscvPmpBase.ty_access_type, acc)),
                 RiscvPmpBase.ty_privilege, p))))))))
       | None ->
         Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
           (Coq_pmp_check_perms, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
           RiscvPmpBase.ty_access_type)), (Coq_env.Coq_snoc
           ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
           (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
           RiscvPmpBase.ty_pmpcfg_ent, cfg)), RiscvPmpBase.ty_access_type,
           acc)), RiscvPmpBase.ty_privilege, p)))))))
    | None ->
      Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
        (Coq_pmp_check_perms, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
        RiscvPmpBase.ty_access_type)), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)), (Coq_env.Coq_snoc
        (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent, cfg)),
        RiscvPmpBase.ty_access_type, acc)), RiscvPmpBase.ty_privilege, p))))))

  (** val simplify_within_cfg :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> RiscvPmpBase.coq_Term -> coq_PathCondition option **)

  let simplify_within_cfg _UU03a3_ paddr cfg prev_addr addr =
    match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_xlenbits paddr with
    | Some paddr0 ->
      (match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_pmpcfg_ent cfg with
       | Some cfg0 ->
         (match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_xlenbits
                  prev_addr with
          | Some a ->
            (match RiscvPmpBase.term_get_val _UU03a3_
                     RiscvPmpBase.ty_xlenbits addr with
             | Some a' ->
               (match decide_within_cfg paddr0 cfg0 a a' with
                | Coq_true -> Some Coq_ctx.Coq_nil
                | Coq_false -> None)
             | None ->
               Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
                 (Coq_within_cfg, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
                 ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
                 RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
                 ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
                 (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                 RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
                 (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
                 paddr)), RiscvPmpBase.ty_pmpcfg_ent, cfg)),
                 RiscvPmpBase.ty_xlenbits, prev_addr)),
                 RiscvPmpBase.ty_xlenbits, addr)))))))
          | None ->
            Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
              (Coq_within_cfg, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
              ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
              RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
              RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
              ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
              RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
              (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
              RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
              Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, paddr)),
              RiscvPmpBase.ty_pmpcfg_ent, cfg)), RiscvPmpBase.ty_xlenbits,
              prev_addr)), RiscvPmpBase.ty_xlenbits, addr)))))))
       | None ->
         Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
           (Coq_within_cfg, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
           RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
           RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
           RiscvPmpBase.ty_pmpcfg_ent)), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
           (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
           paddr)), RiscvPmpBase.ty_pmpcfg_ent, cfg)),
           RiscvPmpBase.ty_xlenbits, prev_addr)), RiscvPmpBase.ty_xlenbits,
           addr)))))))
    | None ->
      Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
        (Coq_within_cfg, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
        RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
        RiscvPmpBase.ty_pmpcfg_ent)), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
        (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, paddr)),
        RiscvPmpBase.ty_pmpcfg_ent, cfg)), RiscvPmpBase.ty_xlenbits,
        prev_addr)), RiscvPmpBase.ty_xlenbits, addr))))))

  (** val simplify_prev_addr :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> coq_PathCondition option **)

  let simplify_prev_addr _UU03a3_ cfg entries prev =
    match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_pmpcfgidx cfg with
    | Some cfg0 ->
      (match RiscvPmpBase.term_get_val _UU03a3_ (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry) entries with
       | Some entries0 ->
         (match RiscvPmpBase.term_get_val _UU03a3_ RiscvPmpBase.ty_xlenbits
                  prev with
          | Some prev0 ->
            (match decide_prev_addr cfg0 entries0 prev0 with
             | Coq_true -> Some Coq_ctx.Coq_nil
             | Coq_false -> None)
          | None ->
            Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
              (Coq_prev_addr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
              ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
              RiscvPmpBase.ty_pmpcfgidx)), (Coq_ty.Coq_list
              RiscvPmpBase.ty_pmpentry))), (Coq_env.Coq_snoc
              ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
              RiscvPmpBase.ty_pmpcfgidx)), (Coq_env.Coq_snoc
              (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_pmpcfgidx,
              cfg)), (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), entries)),
              RiscvPmpBase.ty_xlenbits, prev)))))))
       | None ->
         Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
           (Coq_prev_addr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
           (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))), (Coq_env.Coq_snoc
           ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
           (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
           RiscvPmpBase.ty_pmpcfgidx, cfg)), (Coq_ty.Coq_list
           RiscvPmpBase.ty_pmpentry), entries)), RiscvPmpBase.ty_xlenbits,
           prev)))))))
    | None ->
      Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
        (Coq_prev_addr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
        (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))), (Coq_env.Coq_snoc
        ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
        (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
        RiscvPmpBase.ty_pmpcfgidx, cfg)), (Coq_ty.Coq_list
        RiscvPmpBase.ty_pmpentry), entries)), RiscvPmpBase.ty_xlenbits,
        prev))))))

  (** val simplify_user :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      _UU1d477_ -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env ->
      coq_PathCondition option **)

  let simplify_user _UU03a3_ p e =
    match p with
    | Coq_gen_pmp_access ->
      (match e with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db) ->
         (match e0 with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e1, _, db0) ->
            (match e1 with
             | Coq_env.Coq_nil -> assert false (* absurd case *)
             | Coq_env.Coq_snoc (_, e2, _, db1) ->
               (match e2 with
                | Coq_env.Coq_nil -> assert false (* absurd case *)
                | Coq_env.Coq_snoc (_, e3, _, db2) ->
                  (match e3 with
                   | Coq_env.Coq_nil -> assert false (* absurd case *)
                   | Coq_env.Coq_snoc (_, e4, _, db3) ->
                     (match e4 with
                      | Coq_env.Coq_nil -> assert false (* absurd case *)
                      | Coq_env.Coq_snoc (_, e5, _, db4) ->
                        (match e5 with
                         | Coq_env.Coq_nil ->
                           simplify_gen_pmp_access _UU03a3_ db4 db3 db2 db1
                             db0 db
                         | Coq_env.Coq_snoc (_, _, _, _) ->
                           assert false (* absurd case *))))))))
    | Coq_pmp_access ->
      (match e with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db) ->
         (match e0 with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e1, _, db0) ->
            (match e1 with
             | Coq_env.Coq_nil -> assert false (* absurd case *)
             | Coq_env.Coq_snoc (_, e2, _, db1) ->
               (match e2 with
                | Coq_env.Coq_nil -> assert false (* absurd case *)
                | Coq_env.Coq_snoc (_, e3, _, db2) ->
                  (match e3 with
                   | Coq_env.Coq_nil -> assert false (* absurd case *)
                   | Coq_env.Coq_snoc (_, e4, _, db3) ->
                     (match e4 with
                      | Coq_env.Coq_nil ->
                        simplify_pmp_access _UU03a3_ db3 db2 db1 db0 db
                      | Coq_env.Coq_snoc (_, _, _, _) ->
                        assert false (* absurd case *)))))))
    | Coq_pmp_check_perms ->
      (match e with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db) ->
         (match e0 with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e1, _, db0) ->
            (match e1 with
             | Coq_env.Coq_nil -> assert false (* absurd case *)
             | Coq_env.Coq_snoc (_, e2, _, db1) ->
               (match e2 with
                | Coq_env.Coq_nil ->
                  simplify_pmp_check_perms _UU03a3_ db1 db0 db
                | Coq_env.Coq_snoc (_, _, _, _) ->
                  assert false (* absurd case *)))))
    | Coq_pmp_check_rwx ->
      (match e with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db) ->
         (match e0 with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e1, _, db0) ->
            (match e1 with
             | Coq_env.Coq_nil -> simplify_pmp_check_rwx _UU03a3_ db0 db
             | Coq_env.Coq_snoc (_, _, _, _) -> assert false (* absurd case *))))
    | Coq_sub_perm ->
      (match e with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db) ->
         (match e0 with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e1, _, db0) ->
            (match e1 with
             | Coq_env.Coq_nil -> simplify_sub_perm _UU03a3_ db0 db
             | Coq_env.Coq_snoc (_, _, _, _) -> assert false (* absurd case *))))
    | Coq_access_pmp_perm ->
      (match e with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db) ->
         (match e0 with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e1, _, db0) ->
            (match e1 with
             | Coq_env.Coq_nil -> simplify_access_pmp_perm _UU03a3_ db0 db
             | Coq_env.Coq_snoc (_, _, _, _) -> assert false (* absurd case *))))
    | Coq_within_cfg ->
      (match e with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db) ->
         (match e0 with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e1, _, db0) ->
            (match e1 with
             | Coq_env.Coq_nil -> assert false (* absurd case *)
             | Coq_env.Coq_snoc (_, e2, _, db1) ->
               (match e2 with
                | Coq_env.Coq_nil -> assert false (* absurd case *)
                | Coq_env.Coq_snoc (_, e3, _, db2) ->
                  (match e3 with
                   | Coq_env.Coq_nil ->
                     simplify_within_cfg _UU03a3_ db2 db1 db0 db
                   | Coq_env.Coq_snoc (_, _, _, _) ->
                     assert false (* absurd case *))))))
    | Coq_not_within_cfg ->
      (match e with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db) ->
         (match e0 with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e1, _, db0) ->
            (match e1 with
             | Coq_env.Coq_nil ->
               Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
                 (Coq_not_within_cfg, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
                 (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                 (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
                 RiscvPmpBase.ty_xlenbits, db0)), (Coq_ty.Coq_list
                 RiscvPmpBase.ty_pmpentry), db))))))
             | Coq_env.Coq_snoc (_, _, _, _) -> assert false (* absurd case *))))
    | Coq_prev_addr ->
      (match e with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db) ->
         (match e0 with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e1, _, db0) ->
            (match e1 with
             | Coq_env.Coq_nil -> assert false (* absurd case *)
             | Coq_env.Coq_snoc (_, e2, _, db1) ->
               (match e2 with
                | Coq_env.Coq_nil -> simplify_prev_addr _UU03a3_ db1 db0 db
                | Coq_env.Coq_snoc (_, _, _, _) ->
                  assert false (* absurd case *)))))
    | Coq_in_entries ->
      (match e with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db) ->
         (match e0 with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e1, _, db0) ->
            (match e1 with
             | Coq_env.Coq_nil -> assert false (* absurd case *)
             | Coq_env.Coq_snoc (_, e2, _, db1) ->
               (match e2 with
                | Coq_env.Coq_nil ->
                  Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
                    (Coq_in_entries, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
                    ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                    RiscvPmpBase.ty_pmpcfgidx)), RiscvPmpBase.ty_pmpentry)),
                    (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                    RiscvPmpBase.ty_pmpcfgidx)), (Coq_env.Coq_snoc
                    (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
                    RiscvPmpBase.ty_pmpcfgidx, db1)),
                    RiscvPmpBase.ty_pmpentry, db0)), (Coq_ty.Coq_list
                    RiscvPmpBase.ty_pmpentry), db))))))
                | Coq_env.Coq_snoc (_, _, _, _) ->
                  assert false (* absurd case *)))))
    | Coq_in_mmio bytes ->
      (match e with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e0, _, db) ->
         (match e0 with
          | Coq_env.Coq_nil ->
            Some (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_formula_user
              ((Coq_in_mmio bytes), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
              Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, db))))))
          | Coq_env.Coq_snoc (_, _, _, _) -> assert false (* absurd case *)))

  (** val solver : coq_Solver **)

  let solver =
    solveruseronly_to_solver simplify_user

  type coq_Message = { msg_function : string; msg_message : string;
                       msg_program_context : (coq_PVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx;
                       msg_localstore : RiscvPmpBase.coq_SStore;
                       msg_heap : coq_SHeap;
                       msg_pathcondition : coq_PathCondition }

  (** val msg_function :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Message -> string **)

  let msg_function _ m =
    m.msg_function

  (** val msg_message :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Message -> string **)

  let msg_message _ m =
    m.msg_message

  (** val msg_program_context :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Message -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let msg_program_context _ m =
    m.msg_program_context

  (** val msg_localstore :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Message -> RiscvPmpBase.coq_SStore **)

  let msg_localstore _ m =
    m.msg_localstore

  (** val msg_heap :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Message -> coq_SHeap **)

  let msg_heap _ m =
    m.msg_heap

  (** val msg_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Message -> coq_PathCondition **)

  let msg_pathcondition _ m =
    m.msg_pathcondition

  type coq_EMessage = { emsg_function : string; emsg_message : string;
                        emsg_program_context : (coq_PVar, Coq_ty.coq_Ty)
                                               Binding.coq_Binding
                                               Coq_ctx.coq_Ctx;
                        emsg_localstore : (coq_PVar, Coq_ty.coq_Ty,
                                          RiscvPmpBase.coq_ETerm) coq_NamedEnv;
                        emsg_heap : coq_EChunk list;
                        emsg_pathcondition : coq_EFormula list }

  (** val emsg_function : coq_EMessage -> string **)

  let emsg_function e =
    e.emsg_function

  (** val emsg_message : coq_EMessage -> string **)

  let emsg_message e =
    e.emsg_message

  (** val emsg_program_context :
      coq_EMessage -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let emsg_program_context e =
    e.emsg_program_context

  (** val emsg_localstore :
      coq_EMessage -> (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
      coq_NamedEnv **)

  let emsg_localstore e =
    e.emsg_localstore

  (** val emsg_heap : coq_EMessage -> coq_EChunk list **)

  let emsg_heap e =
    e.emsg_heap

  (** val emsg_pathcondition : coq_EMessage -> coq_EFormula list **)

  let emsg_pathcondition e =
    e.emsg_pathcondition

  (** val coq_EraseMessage :
      (coq_Message, coq_EMessage) RiscvPmpBase.coq_Erase **)

  let coq_EraseMessage _UU03a3_ pat =
    let { msg_function = f; msg_message = m; msg_program_context =
      msg_program_context0; msg_localstore = _UU03b4_; msg_heap = h;
      msg_pathcondition = pc } = pat
    in
    { emsg_function = f; emsg_message = m; emsg_program_context =
    msg_program_context0; emsg_localstore =
    (RiscvPmpBase.erase (RiscvPmpBase.coq_EraseSStore msg_program_context0)
      _UU03a3_ _UU03b4_);
    emsg_heap =
    (RiscvPmpBase.erase (RiscvPmpBase.erase_List coq_Erase_Chunk) _UU03a3_ h);
    emsg_pathcondition =
    (RiscvPmpBase.erase (RiscvPmpBase.erase_Ctx erase_Formula) _UU03a3_ pc) }

  (** val coq_SubstMessage : coq_Message RiscvPmpBase.coq_Subst **)

  let coq_SubstMessage _UU03a3_1 msg _UU03a3_2 _UU03b6_12 =
    let { msg_function = f; msg_message = m; msg_program_context = _UU0393_;
      msg_localstore = _UU03b4_; msg_heap = h; msg_pathcondition = pc } = msg
    in
    { msg_function = f; msg_message = m; msg_program_context = _UU0393_;
    msg_localstore =
    (RiscvPmpBase.subst (RiscvPmpBase.subst_localstore _UU0393_) _UU03a3_1
      _UU03b4_ _UU03a3_2 _UU03b6_12);
    msg_heap =
    (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstList coq_SubstChunk) _UU03a3_1
      h _UU03a3_2 _UU03b6_12);
    msg_pathcondition =
    (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) _UU03a3_1 pc
      _UU03a3_2 _UU03b6_12) }

  (** val coq_SubstSUMessage :
      'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_Message)
      RiscvPmpBase.coq_SubstSU **)

  let coq_SubstSUMessage h _UU03a3_1 _UU03a3_2 msg _UU03b6_12 =
    let { msg_function = f; msg_message = m; msg_program_context = _UU0393_;
      msg_localstore = _UU03b4_; msg_heap = h0; msg_pathcondition = pc } = msg
    in
    { msg_function = f; msg_message = m; msg_program_context = _UU0393_;
    msg_localstore =
    (RiscvPmpBase.substSU
      (RiscvPmpBase.coq_SubstSU_env h _UU0393_ (fun b ->
        RiscvPmpBase.coq_SubstSUTerm h b.Binding.coq_type))
      _UU03a3_1 _UU03a3_2 _UU03b4_ _UU03b6_12);
    msg_heap =
    (RiscvPmpBase.substSU (RiscvPmpBase.substSU_list (coq_SubstSUChunk h))
      _UU03a3_1 _UU03a3_2 h0 _UU03b6_12);
    msg_pathcondition =
    (RiscvPmpBase.substSU (RiscvPmpBase.substSU_ctx (subSU_formula h))
      _UU03a3_1 _UU03a3_2 pc _UU03b6_12) }

  (** val coq_SubstLawsMessage : coq_Message RiscvPmpBase.coq_SubstLaws **)

  let coq_SubstLawsMessage =
    RiscvPmpBase.Build_SubstLaws

  (** val coq_OccursCheckMessage :
      coq_Message RiscvPmpBase.coq_OccursCheck **)

  let coq_OccursCheckMessage _UU03a3_ x xIn msg =
    let { msg_function = f; msg_message = m; msg_program_context = _UU0393_;
      msg_localstore = _UU03b4_; msg_heap = h; msg_pathcondition = pc } = msg
    in
    Coq_option.bind
      (RiscvPmpBase.occurs_check
        (RiscvPmpBase.occurs_check_env (fun i ->
          RiscvPmpBase.occurs_check_term i.Binding.coq_type) _UU0393_)
        _UU03a3_ x xIn _UU03b4_)
      (fun _UU03b4_' ->
      Coq_option.bind
        (RiscvPmpBase.occurs_check
          (RiscvPmpBase.occurs_check_list coq_OccursCheckChunk) _UU03a3_ x
          xIn h)
        (fun h' ->
        Coq_option.bind
          (RiscvPmpBase.occurs_check
            (RiscvPmpBase.occurscheck_ctx coq_OccursCheckFormula) _UU03a3_ x
            xIn pc)
          (fun pc' -> Some { msg_function = f; msg_message = m;
          msg_program_context = _UU0393_; msg_localstore = _UU03b4_';
          msg_heap = h'; msg_pathcondition = pc' })))

  (** val coq_GenOccursCheckMessage :
      (RiscvPmpBase.coq_WeakensTo, coq_Message)
      RiscvPmpBase.coq_GenOccursCheck **)

  let coq_GenOccursCheckMessage _UU03a3_ d =
    let { msg_function = f; msg_message = m; msg_program_context = _UU0393_;
      msg_localstore = _UU03b4_; msg_heap = h; msg_pathcondition = pc } = d
    in
    RiscvPmpBase.liftTernOp RiscvPmpBase.substUniv_weaken
      RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
      RiscvPmpBase.substUnivMeet_weaken _UU03a3_
      (RiscvPmpBase.coq_SubstSU_env RiscvPmpBase.substUniv_weaken _UU0393_
        (fun b ->
        RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
          b.Binding.coq_type))
      (RiscvPmpBase.substSU_list
        (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken))
      (RiscvPmpBase.substSU_ctx (subSU_formula RiscvPmpBase.substUniv_weaken))
      (coq_SubstSUMessage RiscvPmpBase.substUniv_weaken) (fun _ x x0 x1 ->
      { msg_function = f; msg_message = m; msg_program_context = _UU0393_;
      msg_localstore = x; msg_heap = x0; msg_pathcondition = x1 })
      (RiscvPmpBase.gen_occurs_check RiscvPmpBase.substUniv_weaken
        (RiscvPmpBase.coq_SubstSU_env RiscvPmpBase.substUniv_weaken _UU0393_
          (fun b ->
          RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
            b.Binding.coq_type))
        (RiscvPmpBase.gen_occurs_check_env RiscvPmpBase.substUniv_weaken
          RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
          RiscvPmpBase.substUnivMeet_weaken (fun b ->
          RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
            b.Binding.coq_type)
          (fun i ->
          RiscvPmpBase.gen_occurs_check_term RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken
            RiscvPmpBase.substUnivVar_weaken RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken i.Binding.coq_type)
          _UU0393_)
        _UU03a3_ _UU03b4_)
      (RiscvPmpBase.gen_occurs_check RiscvPmpBase.substUniv_weaken
        (RiscvPmpBase.substSU_list
          (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken))
        (RiscvPmpBase.gen_occurs_check_list RiscvPmpBase.substUniv_weaken
          RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
          RiscvPmpBase.substUnivMeet_weaken
          (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken)
          coq_GenOccursCheckChunk)
        _UU03a3_ h)
      (RiscvPmpBase.gen_occurs_check RiscvPmpBase.substUniv_weaken
        (RiscvPmpBase.substSU_ctx
          (subSU_formula RiscvPmpBase.substUniv_weaken))
        (RiscvPmpBase.gen_occurscheck_ctx
          (subSU_formula RiscvPmpBase.substUniv_weaken)
          RiscvPmpBase.substUniv_weaken RiscvPmpBase.substUnivMeet_weaken
          (coq_GenOccursCheckFormula RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken
            RiscvPmpBase.substUnivVar_weaken RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken))
        _UU03a3_ pc)

  (** val coq_Error_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Message -> 'a1 **)

  let coq_Error_rect _ _ =
    assert false (* absurd case *)

  (** val coq_Error_rec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Message -> 'a1 **)

  let coq_Error_rec _ _ =
    assert false (* absurd case *)

  (** val coq_Obligation_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_Formula -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
      (__ -> 'a1) -> 'a1 **)

  let coq_Obligation_rect _ _ _ _ f =
    f __

  (** val coq_Obligation_rec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_Formula -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
      (__ -> 'a1) -> 'a1 **)

  let coq_Obligation_rec _ _ _ _ f =
    f __

  (** val coq_Debug_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 ->
      (__ -> 'a2) -> 'a2 **)

  let coq_Debug_rect _ _ f =
    f __

  (** val coq_Debug_rec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 ->
      (__ -> 'a2) -> 'a2 **)

  let coq_Debug_rec _ _ f =
    f __

  module SymProp =
   struct
    type coq_SymProp =
    | Coq_angelic_binary of coq_SymProp * coq_SymProp
    | Coq_demonic_binary of coq_SymProp * coq_SymProp
    | Coq_error of RiscvPmpBase.Coq_amsg.coq_AMessage
    | Coq_block
    | Coq_assertk of coq_Formula * RiscvPmpBase.Coq_amsg.coq_AMessage
       * coq_SymProp
    | Coq_assumek of coq_Formula * coq_SymProp
    | Coq_angelicv of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_SymProp
    | Coq_demonicv of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_SymProp
    | Coq_assert_vareq of coq_LVar * Coq_ty.coq_Ty
       * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * RiscvPmpBase.coq_Term * RiscvPmpBase.Coq_amsg.coq_AMessage
       * coq_SymProp
    | Coq_assume_vareq of coq_LVar * Coq_ty.coq_Ty
       * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * RiscvPmpBase.coq_Term * coq_SymProp
    | Coq_pattern_match of Coq_ty.coq_Ty * RiscvPmpBase.coq_Term
       * coq_LVar RiscvPmpBase.coq_Pattern
       * (coq_LVar RiscvPmpBase.coq_PatternCase -> coq_SymProp)
    | Coq_pattern_match_var of coq_LVar * Coq_ty.coq_Ty
       * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * coq_LVar RiscvPmpBase.coq_Pattern
       * (coq_LVar RiscvPmpBase.coq_PatternCase -> coq_SymProp)
    | Coq_debug of RiscvPmpBase.Coq_amsg.coq_AMessage * coq_SymProp

    (** val coq_SymProp_rect :
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> 'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
        'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> 'a1) -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1) ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp ->
        'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> coq_Formula -> coq_SymProp -> 'a1 -> 'a1) ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_SymProp -> 'a1
        -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
        coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar -> Coq_ty.coq_Ty ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.Coq_amsg.coq_AMessage ->
        coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar -> Coq_ty.coq_Ty ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
        RiscvPmpBase.coq_Term -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
        -> RiscvPmpBase.coq_Term -> coq_LVar RiscvPmpBase.coq_Pattern ->
        (coq_LVar RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> (coq_LVar
        RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar ->
        Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_In -> coq_LVar RiscvPmpBase.coq_Pattern -> (coq_LVar
        RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> (coq_LVar
        RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> 'a1 **)

    let rec coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ = function
    | Coq_angelic_binary (o1, o2) ->
      f _UU03a3_ o1
        (coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ o1)
        o2
        (coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ o2)
    | Coq_demonic_binary (o1, o2) ->
      f0 _UU03a3_ o1
        (coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ o1)
        o2
        (coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ o2)
    | Coq_error msg -> f1 _UU03a3_ msg
    | Coq_block -> f2 _UU03a3_
    | Coq_assertk (fml, msg, k) ->
      f3 _UU03a3_ fml msg k
        (coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ k)
    | Coq_assumek (fml, k) ->
      f4 _UU03a3_ fml k
        (coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ k)
    | Coq_angelicv (b, k) ->
      f5 _UU03a3_ b k
        (coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.Coq_snoc (_UU03a3_, b)) k)
    | Coq_demonicv (b, k) ->
      f6 _UU03a3_ b k
        (coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.Coq_snoc (_UU03a3_, b)) k)
    | Coq_assert_vareq (x, _UU03c3_, xIn, t, msg, k) ->
      f7 _UU03a3_ x _UU03c3_ xIn t msg k
        (coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          k)
    | Coq_assume_vareq (x, _UU03c3_, xIn, t, k) ->
      f8 _UU03a3_ x _UU03c3_ xIn t k
        (coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          k)
    | Coq_pattern_match (_UU03c3_, s0, pat, rhs) ->
      f9 _UU03a3_ _UU03c3_ s0 pat rhs (fun pc ->
        coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.cat _UU03a3_
            (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
          (rhs pc))
    | Coq_pattern_match_var (x, _UU03c3_, xIn, pat, rhs) ->
      f10 _UU03a3_ x _UU03c3_ xIn pat rhs (fun pc ->
        coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.remove
            (Coq_ctx.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            { Binding.name = x; Binding.coq_type = _UU03c3_ }
            (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
              _UU03c3_ } _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
          (rhs pc))
    | Coq_debug (b, k) ->
      f11 _UU03a3_ b k
        (coq_SymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ k)

    (** val coq_SymProp_rec :
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> 'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
        'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> 'a1) -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1) ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp ->
        'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> coq_Formula -> coq_SymProp -> 'a1 -> 'a1) ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_SymProp -> 'a1
        -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
        coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar -> Coq_ty.coq_Ty ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.Coq_amsg.coq_AMessage ->
        coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar -> Coq_ty.coq_Ty ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
        RiscvPmpBase.coq_Term -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
        -> RiscvPmpBase.coq_Term -> coq_LVar RiscvPmpBase.coq_Pattern ->
        (coq_LVar RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> (coq_LVar
        RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar ->
        Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_In -> coq_LVar RiscvPmpBase.coq_Pattern -> (coq_LVar
        RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> (coq_LVar
        RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> 'a1 **)

    let rec coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ = function
    | Coq_angelic_binary (o1, o2) ->
      f _UU03a3_ o1
        (coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ o1)
        o2
        (coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ o2)
    | Coq_demonic_binary (o1, o2) ->
      f0 _UU03a3_ o1
        (coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ o1)
        o2
        (coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ o2)
    | Coq_error msg -> f1 _UU03a3_ msg
    | Coq_block -> f2 _UU03a3_
    | Coq_assertk (fml, msg, k) ->
      f3 _UU03a3_ fml msg k
        (coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ k)
    | Coq_assumek (fml, k) ->
      f4 _UU03a3_ fml k
        (coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ k)
    | Coq_angelicv (b, k) ->
      f5 _UU03a3_ b k
        (coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.Coq_snoc (_UU03a3_, b)) k)
    | Coq_demonicv (b, k) ->
      f6 _UU03a3_ b k
        (coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.Coq_snoc (_UU03a3_, b)) k)
    | Coq_assert_vareq (x, _UU03c3_, xIn, t, msg, k) ->
      f7 _UU03a3_ x _UU03c3_ xIn t msg k
        (coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          k)
    | Coq_assume_vareq (x, _UU03c3_, xIn, t, k) ->
      f8 _UU03a3_ x _UU03c3_ xIn t k
        (coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          k)
    | Coq_pattern_match (_UU03c3_, s0, pat, rhs) ->
      f9 _UU03a3_ _UU03c3_ s0 pat rhs (fun pc ->
        coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.cat _UU03a3_
            (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
          (rhs pc))
    | Coq_pattern_match_var (x, _UU03c3_, xIn, pat, rhs) ->
      f10 _UU03a3_ x _UU03c3_ xIn pat rhs (fun pc ->
        coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
          (Coq_ctx.remove
            (Coq_ctx.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            { Binding.name = x; Binding.coq_type = _UU03c3_ }
            (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
              _UU03c3_ } _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
          (rhs pc))
    | Coq_debug (b, k) ->
      f11 _UU03a3_ b k
        (coq_SymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _UU03a3_ k)

    (** val trunc :
        nat -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
        -> coq_SymProp -> coq_SymProp **)

    let rec trunc n _UU03a3_ p =
      match n with
      | O -> Coq_block
      | S n0 ->
        (match p with
         | Coq_angelic_binary (p1, p2) ->
           Coq_angelic_binary ((trunc n0 _UU03a3_ p1), (trunc n0 _UU03a3_ p2))
         | Coq_demonic_binary (p1, p2) ->
           Coq_demonic_binary ((trunc n0 _UU03a3_ p1), (trunc n0 _UU03a3_ p2))
         | Coq_assertk (fml, msg, p0) ->
           Coq_assertk (fml, msg, (trunc n0 _UU03a3_ p0))
         | Coq_assumek (fml, p0) -> Coq_assumek (fml, (trunc n0 _UU03a3_ p0))
         | Coq_angelicv (x, p0) ->
           Coq_angelicv (x, (trunc n0 (Coq_ctx.Coq_snoc (_UU03a3_, x)) p0))
         | Coq_demonicv (x, p0) ->
           Coq_demonicv (x, (trunc n0 (Coq_ctx.Coq_snoc (_UU03a3_, x)) p0))
         | Coq_assert_vareq (xIn, _UU03c3_, xIn0, t, msg, p0) ->
           Coq_assert_vareq (xIn, _UU03c3_, xIn0, t, msg,
             (trunc n0
               (Coq_ctx.remove _UU03a3_ { Binding.name = xIn;
                 Binding.coq_type = _UU03c3_ } xIn0)
               p0))
         | Coq_assume_vareq (x, _UU03c3_, xIn, t, p0) ->
           Coq_assume_vareq (x, _UU03c3_, xIn, t,
             (trunc n0
               (Coq_ctx.remove _UU03a3_ { Binding.name = x;
                 Binding.coq_type = _UU03c3_ } xIn)
               p0))
         | Coq_pattern_match (_UU03c3_, t, pat, p0) ->
           Coq_pattern_match (_UU03c3_, t, pat, (fun pc ->
             trunc n0
               (Coq_ctx.cat _UU03a3_
                 (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
               (p0 pc)))
         | Coq_pattern_match_var (x, _UU03c3_, xIn, pat, p0) ->
           Coq_pattern_match_var (x, _UU03c3_, xIn, pat, (fun pc ->
             trunc n0
               (Coq_ctx.remove
                 (Coq_ctx.cat _UU03a3_
                   (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
                 { Binding.name = x; Binding.coq_type = _UU03c3_ }
                 (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
                   _UU03c3_ } _UU03a3_
                   (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
               (p0 pc)))
         | Coq_debug (msg, p0) -> Coq_debug (msg, (trunc n0 _UU03a3_ p0))
         | x -> x)

    (** val angelic_close0 :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> coq_SymProp **)

    let rec angelic_close0 _UU03a3_0 _UU03a3_ p =
      match _UU03a3_ with
      | Coq_ctx.Coq_nil -> p
      | Coq_ctx.Coq_snoc (_UU03a3_1, b) ->
        angelic_close0 _UU03a3_0 _UU03a3_1 (Coq_angelicv (b, p))

    (** val demonic_close0 :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> coq_SymProp **)

    let rec demonic_close0 _UU03a3_0 _UU03a3_ p =
      match _UU03a3_ with
      | Coq_ctx.Coq_nil -> p
      | Coq_ctx.Coq_snoc (_UU03a3_1, b) ->
        demonic_close0 _UU03a3_0 _UU03a3_1 (Coq_demonicv (b, p))

    (** val demonic_close :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> coq_SymProp **)

    let rec demonic_close _UU03a3_ k =
      match _UU03a3_ with
      | Coq_ctx.Coq_nil -> k
      | Coq_ctx.Coq_snoc (_UU03a3_0, b) ->
        demonic_close _UU03a3_0 (Coq_demonicv (b, k))

    (** val angelic_list' :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> ('a1 -> coq_SymProp) -> 'a1 RiscvPmpBase.coq_List ->
        coq_SymProp **)

    let rec angelic_list' _UU03a3_ d p = function
    | Coq_nil -> d
    | Coq_cons (x, xs0) ->
      Coq_angelic_binary ((p x), (angelic_list' _UU03a3_ d p xs0))

    (** val angelic_list :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> ('a1 -> coq_SymProp) -> 'a1
        RiscvPmpBase.coq_List -> coq_SymProp **)

    let angelic_list _UU03a3_ msg p = function
    | Coq_nil -> Coq_error msg
    | Coq_cons (x, xs0) -> angelic_list' _UU03a3_ (p x) p xs0

    (** val demonic_list' :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> ('a1 -> coq_SymProp) -> 'a1 RiscvPmpBase.coq_List ->
        coq_SymProp **)

    let rec demonic_list' _UU03a3_ d p = function
    | Coq_nil -> d
    | Coq_cons (x, xs0) ->
      Coq_demonic_binary ((p x), (demonic_list' _UU03a3_ d p xs0))

    (** val demonic_list :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
        -> coq_SymProp) -> 'a1 RiscvPmpBase.coq_List -> coq_SymProp **)

    let demonic_list _UU03a3_ p = function
    | Coq_nil -> Coq_block
    | Coq_cons (x, xs0) -> demonic_list' _UU03a3_ (p x) p xs0

    (** val angelic_finite :
        ('a1, 'a1) coq_RelDecision -> 'a1 coq_Finite -> (coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> ('a1 -> coq_SymProp) ->
        coq_SymProp **)

    let angelic_finite _ h _UU03a3_ msg p =
      angelic_list _UU03a3_ msg p h

    (** val demonic_finite :
        ('a1, 'a1) coq_RelDecision -> 'a1 coq_Finite -> (coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1 ->
        coq_SymProp) -> coq_SymProp **)

    let demonic_finite _ h _UU03a3_ p =
      demonic_list _UU03a3_ p h

    (** val angelic_pattern_match :
        Coq_ty.coq_Ty -> coq_LVar RiscvPmpBase.coq_Pattern -> (coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> (coq_LVar RiscvPmpBase.coq_PatternCase ->
        coq_SymProp) -> coq_SymProp **)

    let angelic_pattern_match _UU03c3_ pat _UU03a3_ s k =
      angelic_finite
        (coq_EqDecision_from_EqDec
          (RiscvPmpBase.coq_EqDec_PatternCase _UU03c3_ pat))
        (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat) _UU03a3_
        (RiscvPmpBase.Coq_amsg.empty _UU03a3_) (fun pc ->
        angelic_close0 _UU03a3_
          (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) (Coq_assertk
          ((Coq_formula_relop (_UU03c3_, (Coq_bop.Coq_eq _UU03c3_),
          (RiscvPmpBase.pattern_match_term_reverse
            (Coq_ctx.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            _UU03c3_ pat pc
            (RiscvPmpBase.sub_cat_right _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))),
          (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm _UU03c3_) _UU03a3_
            s
            (Coq_ctx.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (RiscvPmpBase.sub_cat_left _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))))),
          (RiscvPmpBase.Coq_amsg.empty
            (Coq_ctx.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))),
          (k pc))))

    (** val angelic_pattern_match_var :
        Coq_ty.coq_Ty -> coq_LVar RiscvPmpBase.coq_Pattern -> (coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
        (coq_LVar RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> coq_SymProp **)

    let angelic_pattern_match_var _UU03c3_ pat _UU03a3_ x xIn k =
      angelic_finite
        (coq_EqDecision_from_EqDec
          (RiscvPmpBase.coq_EqDec_PatternCase _UU03c3_ pat))
        (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat) _UU03a3_
        (RiscvPmpBase.Coq_amsg.empty _UU03a3_) (fun pc ->
        angelic_close0 _UU03a3_
          (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) (Coq_assert_vareq
          (x, _UU03c3_,
          (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
            _UU03c3_ } _UU03a3_
            (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn),
          (RiscvPmpBase.pattern_match_term_reverse
            (Coq_ctx.remove
              (Coq_ctx.cat _UU03a3_
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
              { Binding.name = x; Binding.coq_type = _UU03c3_ }
              (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
                _UU03c3_ } _UU03a3_
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
            _UU03c3_ pat pc
            (wmatchvar_patternvars _UU03a3_ x _UU03c3_ xIn pat pc)),
          (RiscvPmpBase.Coq_amsg.empty
            (Coq_ctx.remove
              (Coq_ctx.cat _UU03a3_
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
              { Binding.name = x; Binding.coq_type = _UU03c3_ }
              (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
                _UU03c3_ } _UU03a3_
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))),
          (k pc))))

    (** val demonic_pattern_match :
        Coq_ty.coq_Ty -> coq_LVar RiscvPmpBase.coq_Pattern -> (coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> (coq_LVar RiscvPmpBase.coq_PatternCase ->
        coq_SymProp) -> coq_SymProp **)

    let demonic_pattern_match _UU03c3_ pat _UU03a3_ s k =
      demonic_finite
        (coq_EqDecision_from_EqDec
          (RiscvPmpBase.coq_EqDec_PatternCase _UU03c3_ pat))
        (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat) _UU03a3_
        (fun pc ->
        demonic_close0 _UU03a3_
          (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) (Coq_assumek
          ((Coq_formula_relop (_UU03c3_, (Coq_bop.Coq_eq _UU03c3_),
          (RiscvPmpBase.pattern_match_term_reverse
            (Coq_ctx.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            _UU03c3_ pat pc
            (RiscvPmpBase.sub_cat_right _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))),
          (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm _UU03c3_) _UU03a3_
            s
            (Coq_ctx.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (RiscvPmpBase.sub_cat_left _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))))),
          (k pc))))

    (** val demonic_pattern_match_var :
        Coq_ty.coq_Ty -> coq_LVar RiscvPmpBase.coq_Pattern -> (coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
        (coq_LVar RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> coq_SymProp **)

    let demonic_pattern_match_var _UU03c3_ pat _UU03a3_ x xIn k =
      demonic_finite
        (coq_EqDecision_from_EqDec
          (RiscvPmpBase.coq_EqDec_PatternCase _UU03c3_ pat))
        (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat) _UU03a3_
        (fun pc ->
        demonic_close0 _UU03a3_
          (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) (Coq_assume_vareq
          (x, _UU03c3_,
          (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
            _UU03c3_ } _UU03a3_
            (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn),
          (RiscvPmpBase.pattern_match_term_reverse
            (Coq_ctx.cat
              (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
                _UU03c3_ } xIn)
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            _UU03c3_ pat pc
            (RiscvPmpBase.sub_cat_right
              (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
                _UU03c3_ } xIn)
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))),
          (k pc))))

    (** val assume_pathcondition_without_solver' :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> coq_SymProp -> coq_SymProp **)

    let rec assume_pathcondition_without_solver' _UU03a3_ c p =
      match c with
      | Coq_ctx.Coq_nil -> p
      | Coq_ctx.Coq_snoc (c0, f) ->
        assume_pathcondition_without_solver' _UU03a3_ c0 (Coq_assumek (f, p))

    (** val assert_pathcondition_without_solver' :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_PathCondition ->
        coq_SymProp -> coq_SymProp **)

    let rec assert_pathcondition_without_solver' _UU03a3_ msg c p =
      match c with
      | Coq_ctx.Coq_nil -> p
      | Coq_ctx.Coq_snoc (c0, f) ->
        assert_pathcondition_without_solver' _UU03a3_ msg c0 (Coq_assertk (f,
          msg, p))

    (** val assume_pathcondition_without_solver :
        coq_World -> coq_PathCondition -> coq_SymProp -> coq_SymProp **)

    let assume_pathcondition_without_solver w c p =
      assume_pathcondition_without_solver' w.wctx c p

    (** val assert_pathcondition_without_solver :
        coq_World -> RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_PathCondition
        -> coq_SymProp -> coq_SymProp **)

    let assert_pathcondition_without_solver w msg c p =
      assert_pathcondition_without_solver' w.wctx msg c p

    (** val assume_triangular :
        coq_World -> coq_World -> coq_Tri -> coq_SymProp -> coq_SymProp **)

    let rec assume_triangular w1 _ _UU03be_ p =
      match _UU03be_ with
      | Coq_tri_id -> p
      | Coq_tri_cons (w', x, _UU03c3_, xIn, t, _UU03be_0) ->
        Coq_assume_vareq (x, _UU03c3_, xIn, t,
          (assume_triangular (wsubst w1 x _UU03c3_ xIn t) w' _UU03be_0 p))

    (** val assert_triangular :
        coq_World -> coq_World -> RiscvPmpBase.Coq_amsg.coq_AMessage ->
        coq_Tri -> (RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp) ->
        coq_SymProp **)

    let rec assert_triangular w1 _ msg _UU03be_ p =
      match _UU03be_ with
      | Coq_tri_id -> p msg
      | Coq_tri_cons (w', x, _UU03c3_, xIn, t, _UU03be_0) ->
        let _UU03b6_ =
          RiscvPmpBase.sub_single w1.wctx { Binding.name = x;
            Binding.coq_type = _UU03c3_ } xIn t
        in
        let msg' =
          RiscvPmpBase.subst RiscvPmpBase.Coq_amsg.subst_amessage w1.wctx msg
            (Coq_ctx.remove w1.wctx { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            _UU03b6_
        in
        Coq_assert_vareq (x, _UU03c3_, xIn, t, msg',
        (assert_triangular (wsubst w1 x _UU03c3_ xIn t) w' msg' _UU03be_0 p))

    module Coq_notations =
     struct
     end

    module Statistics =
     struct
      (** val size :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_SymProp -> coq_N **)

      let rec size _UU03a3_ = function
      | Coq_angelic_binary (o1, o2) ->
        N.add (N.add (Npos Coq_xH) (size _UU03a3_ o1)) (size _UU03a3_ o2)
      | Coq_demonic_binary (o1, o2) ->
        N.add (N.add (Npos Coq_xH) (size _UU03a3_ o1)) (size _UU03a3_ o2)
      | Coq_assertk (_, _, k) -> N.add (Npos Coq_xH) (size _UU03a3_ k)
      | Coq_assumek (_, k) -> N.add (Npos Coq_xH) (size _UU03a3_ k)
      | Coq_angelicv (b, k) ->
        N.add (Npos Coq_xH) (size (Coq_ctx.Coq_snoc (_UU03a3_, b)) k)
      | Coq_demonicv (b, k) ->
        N.add (Npos Coq_xH) (size (Coq_ctx.Coq_snoc (_UU03a3_, b)) k)
      | Coq_assert_vareq (x, _UU03c3_, xIn, _, _, k) ->
        N.add (Npos Coq_xH)
          (size
            (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            k)
      | Coq_assume_vareq (x, _UU03c3_, xIn, _, k) ->
        N.add (Npos Coq_xH)
          (size
            (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            k)
      | Coq_pattern_match (_UU03c3_, _, pat, rhs) ->
        fold_right (fun pc ->
          N.add
            (size
              (Coq_ctx.cat _UU03a3_
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
              (rhs pc)))
          (Npos Coq_xH) (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat)
      | Coq_pattern_match_var (x, _UU03c3_, xIn, pat, rhs) ->
        fold_right (fun pc ->
          N.add
            (size
              (Coq_ctx.remove
                (Coq_ctx.cat _UU03a3_
                  (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
                { Binding.name = x; Binding.coq_type = _UU03c3_ }
                (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
                  _UU03c3_ } _UU03a3_
                  (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
              (rhs pc)))
          (Npos Coq_xH) (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat)
      | Coq_debug (_, k) -> N.add (Npos Coq_xH) (size _UU03a3_ k)
      | _ -> N0

      type coq_Count = { block : coq_N; error : coq_N; debug : coq_N }

      (** val block : coq_Count -> coq_N **)

      let block c =
        c.block

      (** val error : coq_Count -> coq_N **)

      let error c =
        c.error

      (** val debug : coq_Count -> coq_N **)

      let debug c =
        c.debug

      (** val empty : coq_Count **)

      let empty =
        { block = N0; error = N0; debug = N0 }

      (** val inc_block : coq_Count -> coq_Count **)

      let inc_block c =
        let { block = b; error = e; debug = d } = c in
        { block = (N.succ b); error = e; debug = d }

      (** val inc_error : coq_Count -> coq_Count **)

      let inc_error c =
        let { block = b; error = e; debug = d } = c in
        { block = b; error = (N.succ e); debug = d }

      (** val inc_debug : coq_Count -> coq_Count **)

      let inc_debug c =
        let { block = b; error = e; debug = d } = c in
        { block = b; error = e; debug = (N.succ d) }

      (** val count_nodes :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_SymProp -> coq_Count -> coq_Count **)

      let rec count_nodes _UU03a3_ s c =
        match s with
        | Coq_angelic_binary (s1, s2) ->
          count_nodes _UU03a3_ s2 (count_nodes _UU03a3_ s1 c)
        | Coq_demonic_binary (s1, s2) ->
          count_nodes _UU03a3_ s2 (count_nodes _UU03a3_ s1 c)
        | Coq_error _ -> inc_error c
        | Coq_block -> inc_block c
        | Coq_assertk (_, _, s0) -> count_nodes _UU03a3_ s0 c
        | Coq_assumek (_, s0) -> count_nodes _UU03a3_ s0 c
        | Coq_angelicv (b, s0) ->
          count_nodes (Coq_ctx.Coq_snoc (_UU03a3_, b)) s0 c
        | Coq_demonicv (b, s0) ->
          count_nodes (Coq_ctx.Coq_snoc (_UU03a3_, b)) s0 c
        | Coq_assert_vareq (x, _UU03c3_, xIn, _, _, s0) ->
          count_nodes
            (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            s0 c
        | Coq_assume_vareq (x, _UU03c3_, xIn, _, s0) ->
          count_nodes
            (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            s0 c
        | Coq_pattern_match (_UU03c3_, _, pat, rhs) ->
          fold_right (fun pc ->
            count_nodes
              (Coq_ctx.cat _UU03a3_
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
              (rhs pc))
            c (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat)
        | Coq_pattern_match_var (x, _UU03c3_, xIn, pat, rhs) ->
          fold_right (fun pc ->
            count_nodes
              (Coq_ctx.remove
                (Coq_ctx.cat _UU03a3_
                  (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
                { Binding.name = x; Binding.coq_type = _UU03c3_ }
                (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
                  _UU03c3_ } _UU03a3_
                  (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
              (rhs pc))
            c (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat)
        | Coq_debug (_, s0) -> count_nodes _UU03a3_ s0 (inc_debug c)

      (** val count_to_stats : coq_Count -> coq_Stats **)

      let count_to_stats c =
        let { block = b; error = e; debug = d } = c in
        { branches = (N.add b e); pruned = (N.sub (N.add b e) d) }
     end
   end

  module Postprocessing =
   struct
    type ('m1, 'm2) coq_AngelicBinaryFailMsg = { angelic_binary_failmsg_left : 
                                                 'm1;
                                                 angelic_binary_failmsg_right : 
                                                 'm2 }

    (** val angelic_binary_failmsg_left :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ('a1, 'a2) coq_AngelicBinaryFailMsg -> 'a1 **)

    let angelic_binary_failmsg_left _ a =
      a.angelic_binary_failmsg_left

    (** val angelic_binary_failmsg_right :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ('a1, 'a2) coq_AngelicBinaryFailMsg -> 'a2 **)

    let angelic_binary_failmsg_right _ a =
      a.angelic_binary_failmsg_right

    (** val coq_SubstAngelicBinaryFailMsg :
        'a1 RiscvPmpBase.coq_Subst -> 'a2 RiscvPmpBase.coq_Subst -> ('a1,
        'a2) coq_AngelicBinaryFailMsg RiscvPmpBase.coq_Subst **)

    let coq_SubstAngelicBinaryFailMsg h h0 _UU03a3_0 d _UU03a3_1 _UU03b6_01 =
      let { angelic_binary_failmsg_left = msg1;
        angelic_binary_failmsg_right = msg2 } = d
      in
      { angelic_binary_failmsg_left =
      (RiscvPmpBase.subst h _UU03a3_0 msg1 _UU03a3_1 _UU03b6_01);
      angelic_binary_failmsg_right =
      (RiscvPmpBase.subst h0 _UU03a3_0 msg2 _UU03a3_1 _UU03b6_01) }

    (** val coq_SubstSUAngelicBinaryFailMsg :
        ('a1, 'a2) RiscvPmpBase.coq_SubstSU -> ('a1, 'a3)
        RiscvPmpBase.coq_SubstSU -> ('a1, ('a2, 'a3)
        coq_AngelicBinaryFailMsg) RiscvPmpBase.coq_SubstSU **)

    let coq_SubstSUAngelicBinaryFailMsg h h0 _UU03a3_0 _UU03a3_1 d _UU03b6_01 =
      let { angelic_binary_failmsg_left = msg1;
        angelic_binary_failmsg_right = msg2 } = d
      in
      { angelic_binary_failmsg_left =
      (RiscvPmpBase.substSU h _UU03a3_0 _UU03a3_1 msg1 _UU03b6_01);
      angelic_binary_failmsg_right =
      (RiscvPmpBase.substSU h0 _UU03a3_0 _UU03a3_1 msg2 _UU03b6_01) }

    (** val coq_SubstLawsAngelicBinaryFailMsg :
        'a1 RiscvPmpBase.coq_Subst -> 'a1 RiscvPmpBase.coq_SubstLaws -> 'a2
        RiscvPmpBase.coq_Subst -> 'a2 RiscvPmpBase.coq_SubstLaws -> ('a1,
        'a2) coq_AngelicBinaryFailMsg RiscvPmpBase.coq_SubstLaws **)

    let coq_SubstLawsAngelicBinaryFailMsg _ _ _ _ =
      RiscvPmpBase.Build_SubstLaws

    (** val coq_OccursCheckAngelicBinaryFailMsg :
        'a1 RiscvPmpBase.coq_OccursCheck -> 'a2 RiscvPmpBase.coq_OccursCheck
        -> ('a1, 'a2) coq_AngelicBinaryFailMsg RiscvPmpBase.coq_OccursCheck **)

    let coq_OccursCheckAngelicBinaryFailMsg h h0 _UU03a3_ x xIn d =
      let { angelic_binary_failmsg_left = msg1;
        angelic_binary_failmsg_right = msg2 } = d
      in
      Coq_option.bind (RiscvPmpBase.occurs_check h _UU03a3_ x xIn msg1)
        (fun msg1' ->
        Coq_option.bind (RiscvPmpBase.occurs_check h0 _UU03a3_ x xIn msg2)
          (fun msg2' -> Some { angelic_binary_failmsg_left = msg1';
          angelic_binary_failmsg_right = msg2' }))

    (** val coq_GenOccursCheckAngelicBinaryFailMsg :
        (RiscvPmpBase.coq_WeakensTo, 'a1) RiscvPmpBase.coq_SubstSU -> 'a1
        RiscvPmpBase.coq_Subst -> (RiscvPmpBase.coq_WeakensTo, 'a2)
        RiscvPmpBase.coq_SubstSU -> 'a2 RiscvPmpBase.coq_Subst ->
        (RiscvPmpBase.coq_WeakensTo, 'a1) RiscvPmpBase.coq_GenOccursCheck ->
        (RiscvPmpBase.coq_WeakensTo, 'a2) RiscvPmpBase.coq_GenOccursCheck ->
        (RiscvPmpBase.coq_WeakensTo, ('a1, 'a2) coq_AngelicBinaryFailMsg)
        RiscvPmpBase.coq_GenOccursCheck **)

    let coq_GenOccursCheckAngelicBinaryFailMsg h _ h1 _ ocM1 ocM2 _UU03a3_ d =
      let { angelic_binary_failmsg_left = msg1;
        angelic_binary_failmsg_right = msg2 } = d
      in
      RiscvPmpBase.liftBinOp RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken _UU03a3_ h h1
        (coq_SubstSUAngelicBinaryFailMsg h h1) (fun _ x x0 ->
        { angelic_binary_failmsg_left = x; angelic_binary_failmsg_right =
        x0 })
        (RiscvPmpBase.gen_occurs_check RiscvPmpBase.substUniv_weaken h ocM1
          _UU03a3_ msg1)
        (RiscvPmpBase.gen_occurs_check RiscvPmpBase.substUniv_weaken h1 ocM2
          _UU03a3_ msg2)

    type ('mE1, 'mE2) coq_EAngelicBinaryFailMsg =
    | MkEAngelicBinaryFailMsg of 'mE1 * 'mE2

    (** val coq_EAngelicBinaryFailMsg_rect :
        ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_EAngelicBinaryFailMsg -> 'a3 **)

    let coq_EAngelicBinaryFailMsg_rect f = function
    | MkEAngelicBinaryFailMsg (m, m0) -> f m m0

    (** val coq_EAngelicBinaryFailMsg_rec :
        ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_EAngelicBinaryFailMsg -> 'a3 **)

    let coq_EAngelicBinaryFailMsg_rec f = function
    | MkEAngelicBinaryFailMsg (m, m0) -> f m m0

    (** val coq_EraseAngelicBinaryFailMsg :
        ('a1, 'a2) RiscvPmpBase.coq_Erase -> ('a3, 'a4)
        RiscvPmpBase.coq_Erase -> (('a1, 'a3) coq_AngelicBinaryFailMsg, ('a2,
        'a4) coq_EAngelicBinaryFailMsg) RiscvPmpBase.coq_Erase **)

    let coq_EraseAngelicBinaryFailMsg h h0 _UU03a3_ pat =
      let { angelic_binary_failmsg_left = msg1;
        angelic_binary_failmsg_right = msg2 } = pat
      in
      MkEAngelicBinaryFailMsg ((RiscvPmpBase.erase h _UU03a3_ msg1),
      (RiscvPmpBase.erase h0 _UU03a3_ msg2))

    (** val angelic_binary_prune :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp -> SymProp.coq_SymProp **)

    let angelic_binary_prune _ p1 p2 =
      match p1 with
      | SymProp.Coq_error msg ->
        let RiscvPmpBase.Coq_amsg.Coq_mk (subM, wkM, subLM, occM, eM, msg1) =
          msg
        in
        (match p2 with
         | SymProp.Coq_error msg0 ->
           let RiscvPmpBase.Coq_amsg.Coq_mk (subM0, wkM0, subLM0, occM0, eM0,
                                             msg2) =
             msg0
           in
           SymProp.Coq_error (RiscvPmpBase.Coq_amsg.Coq_mk
           ((Obj.magic coq_SubstAngelicBinaryFailMsg subM subM0),
           (Obj.magic coq_SubstSUAngelicBinaryFailMsg wkM wkM0),
           (Obj.magic coq_SubstLawsAngelicBinaryFailMsg subM subLM subM0
             subLM0),
           (Obj.magic coq_OccursCheckAngelicBinaryFailMsg occM occM0),
           (Obj.magic coq_EraseAngelicBinaryFailMsg eM eM0),
           (Obj.magic { angelic_binary_failmsg_left = msg1;
             angelic_binary_failmsg_right = msg2 })))
         | SymProp.Coq_block -> SymProp.Coq_block
         | _ -> p2)
      | SymProp.Coq_block -> SymProp.Coq_block
      | SymProp.Coq_assertk (_, _, _) ->
        (match p2 with
         | SymProp.Coq_error _ -> p1
         | SymProp.Coq_block -> SymProp.Coq_block
         | _ -> SymProp.Coq_angelic_binary (p1, p2))
      | SymProp.Coq_assert_vareq (_, _, _, _, _, _) ->
        (match p2 with
         | SymProp.Coq_error _ -> p1
         | SymProp.Coq_block -> SymProp.Coq_block
         | _ -> SymProp.Coq_angelic_binary (p1, p2))
      | _ ->
        (match p2 with
         | SymProp.Coq_error _ -> p1
         | SymProp.Coq_block -> SymProp.Coq_block
         | _ -> SymProp.Coq_angelic_binary (p1, p2))

    (** val demonic_binary_prune :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp -> SymProp.coq_SymProp **)

    let demonic_binary_prune _ p1 p2 =
      match p1 with
      | SymProp.Coq_error s ->
        (match p2 with
         | SymProp.Coq_block -> p1
         | _ -> SymProp.Coq_error s)
      | SymProp.Coq_block -> p2
      | _ ->
        (match p2 with
         | SymProp.Coq_error s -> SymProp.Coq_error s
         | SymProp.Coq_block -> p1
         | _ -> SymProp.Coq_demonic_binary (p1, p2))

    (** val assertk_prune :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> RiscvPmpBase.Coq_amsg.coq_AMessage ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp **)

    let assertk_prune _ fml msg p = match p with
    | SymProp.Coq_error s -> SymProp.Coq_error s
    | _ -> SymProp.Coq_assertk (fml, msg, p)

    (** val assumek_prune :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> SymProp.coq_SymProp -> SymProp.coq_SymProp **)

    let assumek_prune _ fml p = match p with
    | SymProp.Coq_block -> SymProp.Coq_block
    | _ -> SymProp.Coq_assumek (fml, p)

    (** val angelicv_prune :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> SymProp.coq_SymProp
        -> SymProp.coq_SymProp **)

    let angelicv_prune _ b p = match p with
    | SymProp.Coq_error msg0 ->
      let RiscvPmpBase.Coq_amsg.Coq_mk (subM, wkM, subLM, occM, eM, msg) =
        msg0
      in
      SymProp.Coq_error (RiscvPmpBase.Coq_amsg.Coq_mk
      ((Obj.magic RiscvPmpBase.Coq_amsg.subst_closemessage subM),
      (Obj.magic RiscvPmpBase.Coq_amsg.substSU_closemessage wkM),
      (Obj.magic RiscvPmpBase.Coq_amsg.substlaws_closemessage subM subLM),
      (Obj.magic RiscvPmpBase.Coq_amsg.occurscheck_closemessage occM),
      (Obj.magic RiscvPmpBase.Coq_amsg.erase_closemessage eM),
      (Obj.magic (RiscvPmpBase.Coq_amsg.Coq_there (b, msg)))))
    | _ -> SymProp.Coq_angelicv (b, p)

    (** val demonicv_prune :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> SymProp.coq_SymProp
        -> SymProp.coq_SymProp **)

    let demonicv_prune _ b p = match p with
    | SymProp.Coq_block -> SymProp.Coq_block
    | _ -> SymProp.Coq_demonicv (b, p)

    (** val assume_vareq_prune :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_In -> RiscvPmpBase.coq_Term ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp **)

    let assume_vareq_prune _ x _UU03c3_ xIn t k = match k with
    | SymProp.Coq_block -> SymProp.Coq_block
    | _ -> SymProp.Coq_assume_vareq (x, _UU03c3_, xIn, t, k)

    (** val assert_vareq_prune :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_In -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> SymProp.coq_SymProp ->
        SymProp.coq_SymProp **)

    let assert_vareq_prune _UU03a3_ x _UU03c3_ xIn t msg k = match k with
    | SymProp.Coq_error emsg ->
      SymProp.Coq_error
        (RiscvPmpBase.subst RiscvPmpBase.Coq_amsg.subst_amessage
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          emsg _UU03a3_
          (RiscvPmpBase.sub_shift _UU03a3_ { Binding.name = x;
            Binding.coq_type = _UU03c3_ } xIn))
    | _ -> SymProp.Coq_assert_vareq (x, _UU03c3_, xIn, t, msg, k)

    (** val prune :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp **)

    let rec prune _UU03a3_ = function
    | SymProp.Coq_angelic_binary (o1, o2) ->
      angelic_binary_prune _UU03a3_ (prune _UU03a3_ o1) (prune _UU03a3_ o2)
    | SymProp.Coq_demonic_binary (o1, o2) ->
      demonic_binary_prune _UU03a3_ (prune _UU03a3_ o1) (prune _UU03a3_ o2)
    | SymProp.Coq_assertk (fml, msg, o) ->
      assertk_prune _UU03a3_ fml msg (prune _UU03a3_ o)
    | SymProp.Coq_assumek (fml, o) ->
      assumek_prune _UU03a3_ fml (prune _UU03a3_ o)
    | SymProp.Coq_angelicv (b, o) ->
      angelicv_prune _UU03a3_ b (prune (Coq_ctx.Coq_snoc (_UU03a3_, b)) o)
    | SymProp.Coq_demonicv (b, o) ->
      demonicv_prune _UU03a3_ b (prune (Coq_ctx.Coq_snoc (_UU03a3_, b)) o)
    | SymProp.Coq_assert_vareq (x, _UU03c3_, xIn, t, msg, k) ->
      assert_vareq_prune _UU03a3_ x _UU03c3_ xIn t msg
        (prune
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          k)
    | SymProp.Coq_assume_vareq (x, _UU03c3_, xIn, t, k) ->
      assume_vareq_prune _UU03a3_ x _UU03c3_ xIn t
        (prune
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          k)
    | SymProp.Coq_pattern_match (_UU03c3_, s, pat, rhs) ->
      SymProp.Coq_pattern_match (_UU03c3_, s, pat, (fun pc ->
        prune
          (Coq_ctx.cat _UU03a3_
            (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
          (rhs pc)))
    | SymProp.Coq_pattern_match_var (x, _UU03c3_, xIn, pat, rhs) ->
      SymProp.Coq_pattern_match_var (x, _UU03c3_, xIn, pat, (fun pc ->
        prune
          (Coq_ctx.remove
            (Coq_ctx.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            { Binding.name = x; Binding.coq_type = _UU03c3_ }
            (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
              _UU03c3_ } _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
          (rhs pc)))
    | SymProp.Coq_debug (d, k) -> SymProp.Coq_debug (d, (prune _UU03a3_ k))
    | x -> x

    module SolveEvars =
     struct
      (** val assert_msgs_formulas :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (RiscvPmpBase.Coq_amsg.coq_AMessage, coq_Formula)
          RiscvPmpBase.coq_Pair Coq_ctx.coq_Ctx -> SymProp.coq_SymProp ->
          SymProp.coq_SymProp **)

      let rec assert_msgs_formulas _UU03a3_ mfs p =
        match mfs with
        | Coq_ctx.Coq_nil -> p
        | Coq_ctx.Coq_snoc (mfs0, b) ->
          let Coq_pair (msg, fml) = b in
          assert_msgs_formulas _UU03a3_ mfs0 (SymProp.Coq_assertk (fml, msg,
            p))

      type coq_ECtx =
      | Coq_ectx of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                    Coq_ctx.coq_Ctx
         * (RiscvPmpBase.Coq_amsg.coq_AMessage, coq_Formula)
           RiscvPmpBase.coq_Pair Coq_ctx.coq_Ctx

      (** val coq_ECtx_rect :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (RiscvPmpBase.Coq_amsg.coq_AMessage, coq_Formula)
          RiscvPmpBase.coq_Pair Coq_ctx.coq_Ctx -> 'a1) -> (coq_LVar,
          Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
          'a1 **)

      let coq_ECtx_rect _ f _ = function
      | Coq_ectx (_UU03a3_e, mfs) -> f _UU03a3_e mfs

      (** val coq_ECtx_rec :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (RiscvPmpBase.Coq_amsg.coq_AMessage, coq_Formula)
          RiscvPmpBase.coq_Pair Coq_ctx.coq_Ctx -> 'a1) -> (coq_LVar,
          Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
          'a1 **)

      let coq_ECtx_rec _ f _ = function
      | Coq_ectx (_UU03a3_e, mfs) -> f _UU03a3_e mfs

      (** val ectx_refl :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_ECtx **)

      let ectx_refl _ =
        Coq_ectx (Coq_ctx.Coq_nil, Coq_ctx.Coq_nil)

      (** val ectx_formula :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_ECtx -> RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_Formula ->
          coq_ECtx **)

      let ectx_formula _ _ e msg fml =
        let Coq_ectx (_UU03a3_e, mfs) = e in
        Coq_ectx (_UU03a3_e, (Coq_ctx.Coq_snoc (mfs, (Coq_pair (msg, fml)))))

      (** val ectx_snoc :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_ECtx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
          coq_ECtx **)

      let ectx_snoc _UU03a3_1 _ e b =
        let Coq_ectx (_UU03a3_e, mfs) = e in
        Coq_ectx ((Coq_ctx.Coq_snoc (_UU03a3_e, b)),
        (RiscvPmpBase.subst
          (RiscvPmpBase.subst_ctx
            (RiscvPmpBase.coq_SubstPair RiscvPmpBase.Coq_amsg.subst_amessage
              sub_formula))
          (Coq_ctx.cat _UU03a3_1 _UU03a3_e) mfs (Coq_ctx.Coq_snoc
          ((Coq_ctx.cat _UU03a3_1 _UU03a3_e), b))
          (RiscvPmpBase.sub_wk1 (Coq_ctx.cat _UU03a3_1 _UU03a3_e) b)))

      (** val ectx_subst :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_ECtx -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
          Binding.coq_Binding Coq_ctx.coq_In -> RiscvPmpBase.coq_Term ->
          coq_ECtx option **)

      let ectx_subst _UU03a3_1 _ e x _UU03c3_ xIn t =
        let Coq_ectx (_UU03a3_e, mfs) = e in
        (match Coq_ctx.catView _UU03a3_1 _UU03a3_e { Binding.name = x;
                 Binding.coq_type = _UU03c3_ } xIn with
         | Coq_ctx.Coq_isCatLeft _ -> None
         | Coq_ctx.Coq_isCatRight bIn ->
           let _UU03b6_ =
             RiscvPmpBase.sub_single (Coq_ctx.cat _UU03a3_1 _UU03a3_e)
               { Binding.name = x; Binding.coq_type = _UU03c3_ }
               (Coq_ctx.in_cat_right { Binding.name = x; Binding.coq_type =
                 _UU03c3_ } _UU03a3_1 _UU03a3_e bIn)
               t
           in
           Some (Coq_ectx
           ((Coq_ctx.remove _UU03a3_e { Binding.name = x; Binding.coq_type =
              _UU03c3_ } bIn),
           (RiscvPmpBase.subst
             (RiscvPmpBase.subst_ctx
               (RiscvPmpBase.coq_SubstPair
                 RiscvPmpBase.Coq_amsg.subst_amessage sub_formula))
             (Coq_ctx.cat _UU03a3_1 _UU03a3_e) mfs
             (Coq_ctx.cat _UU03a3_1
               (Coq_ctx.remove _UU03a3_e { Binding.name = x;
                 Binding.coq_type = _UU03c3_ } bIn))
             _UU03b6_))))

      (** val plug :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_ECtx -> SymProp.coq_SymProp -> SymProp.coq_SymProp **)

      let plug _UU03a3_1 _ e p =
        let Coq_ectx (_UU03a3_e, mfs) = e in
        SymProp.angelic_close0 _UU03a3_1 _UU03a3_e
          (assert_msgs_formulas (Coq_ctx.cat _UU03a3_1 _UU03a3_e) mfs p)

      (** val plug_msg :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_ECtx -> RiscvPmpBase.Coq_amsg.coq_AMessage ->
          RiscvPmpBase.Coq_amsg.coq_AMessage **)

      let plug_msg _UU03a3_1 _ = function
      | Coq_ectx (_UU03a3_e, _) ->
        RiscvPmpBase.Coq_amsg.close _UU03a3_1 _UU03a3_e

      (** val push :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_ECtx -> SymProp.coq_SymProp -> SymProp.coq_SymProp **)

      let rec push _UU03a3_1 _UU03a3_2 ec = function
      | SymProp.Coq_angelic_binary (p1, p2) ->
        SymProp.Coq_angelic_binary ((push _UU03a3_1 _UU03a3_2 ec p1),
          (push _UU03a3_1 _UU03a3_2 ec p2))
      | SymProp.Coq_demonic_binary (p1, p2) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_demonic_binary
          ((push _UU03a3_2 _UU03a3_2 (ectx_refl _UU03a3_2) p1),
          (push _UU03a3_2 _UU03a3_2 (ectx_refl _UU03a3_2) p2)))
      | SymProp.Coq_error msg ->
        SymProp.Coq_error (plug_msg _UU03a3_1 _UU03a3_2 ec msg)
      | SymProp.Coq_block -> plug _UU03a3_1 _UU03a3_2 ec SymProp.Coq_block
      | SymProp.Coq_assertk (fml, msg, p0) ->
        push _UU03a3_1 _UU03a3_2
          (ectx_formula _UU03a3_1 _UU03a3_2 ec msg fml) p0
      | SymProp.Coq_assumek (fml, p0) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_assumek (fml,
          (push _UU03a3_2 _UU03a3_2 (ectx_refl _UU03a3_2) p0)))
      | SymProp.Coq_angelicv (b, p0) ->
        push _UU03a3_1 (Coq_ctx.Coq_snoc (_UU03a3_2, b))
          (ectx_snoc _UU03a3_1 _UU03a3_2 ec b) p0
      | SymProp.Coq_demonicv (b, p0) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_demonicv (b,
          (push (Coq_ctx.Coq_snoc (_UU03a3_2, b)) (Coq_ctx.Coq_snoc
            (_UU03a3_2, b)) (ectx_refl (Coq_ctx.Coq_snoc (_UU03a3_2, b))) p0)))
      | SymProp.Coq_assert_vareq (x, _UU03c3_, xIn, t, msg, p0) ->
        (match ectx_subst _UU03a3_1 _UU03a3_2 ec x _UU03c3_ xIn t with
         | Some e' ->
           push _UU03a3_1
             (Coq_ctx.remove _UU03a3_2 { Binding.name = x; Binding.coq_type =
               _UU03c3_ } xIn)
             e' p0
         | None ->
           plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_assert_vareq (x,
             _UU03c3_, xIn, t, msg,
             (push
               (Coq_ctx.remove _UU03a3_2 { Binding.name = x;
                 Binding.coq_type = _UU03c3_ } xIn)
               (Coq_ctx.remove _UU03a3_2 { Binding.name = x;
                 Binding.coq_type = _UU03c3_ } xIn)
               (ectx_refl
                 (Coq_ctx.remove _UU03a3_2 { Binding.name = x;
                   Binding.coq_type = _UU03c3_ } xIn))
               p0))))
      | SymProp.Coq_assume_vareq (x, _UU03c3_, xIn, t, p0) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_assume_vareq (x, _UU03c3_,
          xIn, t,
          (push
            (Coq_ctx.remove _UU03a3_2 { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            (Coq_ctx.remove _UU03a3_2 { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            (ectx_refl
              (Coq_ctx.remove _UU03a3_2 { Binding.name = x;
                Binding.coq_type = _UU03c3_ } xIn))
            p0)))
      | SymProp.Coq_pattern_match (_UU03c3_, s, pat, rhs) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_pattern_match (_UU03c3_, s,
          pat, (fun pc ->
          push
            (Coq_ctx.cat _UU03a3_2
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (Coq_ctx.cat _UU03a3_2
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (ectx_refl
              (Coq_ctx.cat _UU03a3_2
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc)))
            (rhs pc))))
      | SymProp.Coq_pattern_match_var (x, _UU03c3_, xIn, pat, rhs) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_pattern_match_var (x,
          _UU03c3_, xIn, pat, (fun pc ->
          push
            (Coq_ctx.remove
              (Coq_ctx.cat _UU03a3_2
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
              { Binding.name = x; Binding.coq_type = _UU03c3_ }
              (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
                _UU03c3_ } _UU03a3_2
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
            (Coq_ctx.remove
              (Coq_ctx.cat _UU03a3_2
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
              { Binding.name = x; Binding.coq_type = _UU03c3_ }
              (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
                _UU03c3_ } _UU03a3_2
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
            (ectx_refl
              (Coq_ctx.remove
                (Coq_ctx.cat _UU03a3_2
                  (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
                { Binding.name = x; Binding.coq_type = _UU03c3_ }
                (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
                  _UU03c3_ } _UU03a3_2
                  (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn)))
            (rhs pc))))
      | SymProp.Coq_debug (b, p0) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_debug (b,
          (push _UU03a3_2 _UU03a3_2 (ectx_refl _UU03a3_2) p0)))
     end

    (** val solve_evars :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp **)

    let solve_evars _UU03a3_ p =
      SolveEvars.push _UU03a3_ _UU03a3_ (SolveEvars.ectx_refl _UU03a3_) p

    module SolveUvars =
     struct
      (** val assume_pathcondition :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_PathCondition -> SymProp.coq_SymProp -> SymProp.coq_SymProp **)

      let rec assume_pathcondition _UU03a3_ c p =
        match c with
        | Coq_ctx.Coq_nil -> p
        | Coq_ctx.Coq_snoc (c0, f) ->
          assume_pathcondition _UU03a3_ c0 (SymProp.Coq_assumek (f, p))

      type coq_UCtx =
      | Coq_uctx of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                    Coq_ctx.coq_Ctx
         * coq_PathCondition

      (** val coq_UCtx_rect :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_PathCondition -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
          Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx -> 'a1 **)

      let coq_UCtx_rect _ f _ = function
      | Coq_uctx (_UU03a3_u, mfs) -> f _UU03a3_u mfs

      (** val coq_UCtx_rec :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_PathCondition -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
          Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx -> 'a1 **)

      let coq_UCtx_rec _ f _ = function
      | Coq_uctx (_UU03a3_u, mfs) -> f _UU03a3_u mfs

      (** val uctx_refl :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_UCtx **)

      let uctx_refl _ =
        Coq_uctx (Coq_ctx.Coq_nil, Coq_ctx.Coq_nil)

      (** val uctx_formula :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_UCtx -> coq_Formula -> coq_UCtx **)

      let uctx_formula _ _ e f =
        let Coq_uctx (_UU03a3_u, c) = e in
        Coq_uctx (_UU03a3_u, (Coq_ctx.Coq_snoc (c, f)))

      (** val uctx_snoc :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_UCtx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
          coq_UCtx **)

      let uctx_snoc _UU03a3_1 _ e b =
        let Coq_uctx (_UU03a3_u, c) = e in
        Coq_uctx ((Coq_ctx.Coq_snoc (_UU03a3_u, b)),
        (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula)
          (Coq_ctx.cat _UU03a3_1 _UU03a3_u) c (Coq_ctx.Coq_snoc
          ((Coq_ctx.cat _UU03a3_1 _UU03a3_u), b))
          (RiscvPmpBase.sub_wk1 (Coq_ctx.cat _UU03a3_1 _UU03a3_u) b)))

      (** val uctx_subst :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_UCtx -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
          Binding.coq_Binding Coq_ctx.coq_In -> RiscvPmpBase.coq_Term ->
          coq_UCtx option **)

      let uctx_subst _UU03a3_1 _ e x _UU03c3_ xIn t =
        let Coq_uctx (_UU03a3_u, mfs) = e in
        (match Coq_ctx.catView _UU03a3_1 _UU03a3_u { Binding.name = x;
                 Binding.coq_type = _UU03c3_ } xIn with
         | Coq_ctx.Coq_isCatLeft _ -> None
         | Coq_ctx.Coq_isCatRight bIn ->
           let _UU03b6_ =
             RiscvPmpBase.sub_single (Coq_ctx.cat _UU03a3_1 _UU03a3_u)
               { Binding.name = x; Binding.coq_type = _UU03c3_ }
               (Coq_ctx.in_cat_right { Binding.name = x; Binding.coq_type =
                 _UU03c3_ } _UU03a3_1 _UU03a3_u bIn)
               t
           in
           Some (Coq_uctx
           ((Coq_ctx.remove _UU03a3_u { Binding.name = x; Binding.coq_type =
              _UU03c3_ } bIn),
           (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula)
             (Coq_ctx.cat _UU03a3_1 _UU03a3_u) mfs
             (Coq_ctx.cat _UU03a3_1
               (Coq_ctx.remove _UU03a3_u { Binding.name = x;
                 Binding.coq_type = _UU03c3_ } bIn))
             _UU03b6_))))

      (** val plug :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_UCtx -> SymProp.coq_SymProp -> SymProp.coq_SymProp **)

      let plug _UU03a3_1 _ e p =
        let Coq_uctx (_UU03a3_u, c) = e in
        SymProp.demonic_close0 _UU03a3_1 _UU03a3_u
          (assume_pathcondition (Coq_ctx.cat _UU03a3_1 _UU03a3_u) c p)

      (** val plug_error :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_UCtx -> RiscvPmpBase.Coq_amsg.coq_AMessage ->
          SymProp.coq_SymProp **)

      let plug_error _UU03a3_1 _ ec msg =
        let Coq_uctx (_UU03a3_u, c) = ec in
        (match c with
         | Coq_ctx.Coq_nil ->
           SymProp.Coq_error
             (RiscvPmpBase.Coq_amsg.close _UU03a3_1 _UU03a3_u msg)
         | Coq_ctx.Coq_snoc (_, _) ->
           plug _UU03a3_1 (Coq_ctx.cat _UU03a3_1 _UU03a3_u) (Coq_uctx
             (_UU03a3_u, c)) (SymProp.Coq_error msg))

      (** val push :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_UCtx -> SymProp.coq_SymProp -> SymProp.coq_SymProp **)

      let rec push _UU03a3_1 _UU03a3_2 ec = function
      | SymProp.Coq_angelic_binary (p1, p2) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_angelic_binary
          ((push _UU03a3_2 _UU03a3_2 (uctx_refl _UU03a3_2) p1),
          (push _UU03a3_2 _UU03a3_2 (uctx_refl _UU03a3_2) p2)))
      | SymProp.Coq_demonic_binary (p1, p2) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_demonic_binary
          ((push _UU03a3_2 _UU03a3_2 (uctx_refl _UU03a3_2) p1),
          (push _UU03a3_2 _UU03a3_2 (uctx_refl _UU03a3_2) p2)))
      | SymProp.Coq_error msg -> plug_error _UU03a3_1 _UU03a3_2 ec msg
      | SymProp.Coq_block -> SymProp.Coq_block
      | SymProp.Coq_assertk (fml, msg, p0) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_assertk (fml, msg,
          (push _UU03a3_2 _UU03a3_2 (uctx_refl _UU03a3_2) p0)))
      | SymProp.Coq_assumek (fml, p0) ->
        push _UU03a3_1 _UU03a3_2 (uctx_formula _UU03a3_1 _UU03a3_2 ec fml) p0
      | SymProp.Coq_angelicv (b, p0) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_angelicv (b,
          (push (Coq_ctx.Coq_snoc (_UU03a3_2, b)) (Coq_ctx.Coq_snoc
            (_UU03a3_2, b)) (uctx_refl (Coq_ctx.Coq_snoc (_UU03a3_2, b))) p0)))
      | SymProp.Coq_demonicv (b, p0) ->
        push _UU03a3_1 (Coq_ctx.Coq_snoc (_UU03a3_2, b))
          (uctx_snoc _UU03a3_1 _UU03a3_2 ec b) p0
      | SymProp.Coq_assert_vareq (x, _UU03c3_, xIn, t, msg, p0) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_assert_vareq (x, _UU03c3_,
          xIn, t, msg,
          (push
            (Coq_ctx.remove _UU03a3_2 { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            (Coq_ctx.remove _UU03a3_2 { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            (uctx_refl
              (Coq_ctx.remove _UU03a3_2 { Binding.name = x;
                Binding.coq_type = _UU03c3_ } xIn))
            p0)))
      | SymProp.Coq_assume_vareq (x, _UU03c3_, xIn, t, p0) ->
        (match uctx_subst _UU03a3_1 _UU03a3_2 ec x _UU03c3_ xIn t with
         | Some e' ->
           push _UU03a3_1
             (Coq_ctx.remove _UU03a3_2 { Binding.name = x; Binding.coq_type =
               _UU03c3_ } xIn)
             e' p0
         | None ->
           plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_assume_vareq (x,
             _UU03c3_, xIn, t,
             (push
               (Coq_ctx.remove _UU03a3_2 { Binding.name = x;
                 Binding.coq_type = _UU03c3_ } xIn)
               (Coq_ctx.remove _UU03a3_2 { Binding.name = x;
                 Binding.coq_type = _UU03c3_ } xIn)
               (uctx_refl
                 (Coq_ctx.remove _UU03a3_2 { Binding.name = x;
                   Binding.coq_type = _UU03c3_ } xIn))
               p0))))
      | SymProp.Coq_pattern_match (_UU03c3_, s, pat, rhs) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_pattern_match (_UU03c3_, s,
          pat, (fun pc ->
          push
            (Coq_ctx.cat _UU03a3_2
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (Coq_ctx.cat _UU03a3_2
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (uctx_refl
              (Coq_ctx.cat _UU03a3_2
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc)))
            (rhs pc))))
      | SymProp.Coq_pattern_match_var (x, _UU03c3_, xIn, pat, rhs) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_pattern_match_var (x,
          _UU03c3_, xIn, pat, (fun pc ->
          push
            (Coq_ctx.remove
              (Coq_ctx.cat _UU03a3_2
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
              { Binding.name = x; Binding.coq_type = _UU03c3_ }
              (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
                _UU03c3_ } _UU03a3_2
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
            (Coq_ctx.remove
              (Coq_ctx.cat _UU03a3_2
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
              { Binding.name = x; Binding.coq_type = _UU03c3_ }
              (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
                _UU03c3_ } _UU03a3_2
                (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
            (uctx_refl
              (Coq_ctx.remove
                (Coq_ctx.cat _UU03a3_2
                  (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
                { Binding.name = x; Binding.coq_type = _UU03c3_ }
                (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
                  _UU03c3_ } _UU03a3_2
                  (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn)))
            (rhs pc))))
      | SymProp.Coq_debug (b, p0) ->
        plug _UU03a3_1 _UU03a3_2 ec (SymProp.Coq_debug (b,
          (push _UU03a3_2 _UU03a3_2 (uctx_refl _UU03a3_2) p0)))
     end

    (** val solve_uvars :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp **)

    let solve_uvars _UU03a3_ p =
      SolveUvars.push _UU03a3_ _UU03a3_ (SolveUvars.uctx_refl _UU03a3_) p

    module Experimental =
     struct
      type coq_Ephemeral = (SolveEvars.coq_ECtx, SolveUvars.coq_UCtx) sum

      type coq_EProp =
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Ephemeral -> SymProp.coq_SymProp

      (** val angelic_binary :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_EProp -> coq_EProp -> coq_EProp **)

      let angelic_binary _UU03a3_ p q _UU03a3_0 eph = match eph with
      | Coq_inl _ ->
        SymProp.Coq_angelic_binary ((p _UU03a3_0 eph), (q _UU03a3_0 eph))
      | Coq_inr uc ->
        let eph' = Coq_inl (SolveEvars.ectx_refl _UU03a3_) in
        SolveUvars.plug _UU03a3_0 _UU03a3_ uc (SymProp.Coq_angelic_binary
          ((p _UU03a3_ eph'), (q _UU03a3_ eph')))

      (** val angelicv :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_EProp ->
          coq_EProp **)

      let angelicv _UU03a3_ b p _UU03a3_0 = function
      | Coq_inl ec ->
        p _UU03a3_0 (Coq_inl (SolveEvars.ectx_snoc _UU03a3_0 _UU03a3_ ec b))
      | Coq_inr uc ->
        let eph' = Coq_inl
          (SolveEvars.ectx_refl (Coq_ctx.Coq_snoc (_UU03a3_, b)))
        in
        SolveUvars.plug _UU03a3_0 _UU03a3_ uc (SymProp.Coq_angelicv (b,
          (p (Coq_ctx.Coq_snoc (_UU03a3_, b)) eph')))

      (** val demonic_binary :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          coq_EProp -> coq_EProp -> coq_EProp **)

      let demonic_binary _UU03a3_ p q _UU03a3_0 eph = match eph with
      | Coq_inl ec ->
        let eph' = Coq_inr (SolveUvars.uctx_refl _UU03a3_) in
        SolveEvars.plug _UU03a3_0 _UU03a3_ ec (SymProp.Coq_demonic_binary
          ((p _UU03a3_ eph'), (q _UU03a3_ eph')))
      | Coq_inr _ ->
        SymProp.Coq_demonic_binary ((p _UU03a3_0 eph), (q _UU03a3_0 eph))

      (** val error :
          (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_EProp **)

      let error _UU03a3_ msg _UU03a3_0 = function
      | Coq_inl ec ->
        SymProp.Coq_error (SolveEvars.plug_msg _UU03a3_0 _UU03a3_ ec msg)
      | Coq_inr uc ->
        SolveUvars.plug _UU03a3_0 _UU03a3_ uc (SymProp.Coq_error msg)
     end

    (** val weaken_symprop :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_WeakensTo -> SymProp.coq_SymProp **)

    let rec weaken_symprop _UU03a3_1 p _UU03a3_2 _UU03b6_ =
      match p with
      | SymProp.Coq_angelic_binary (p1, p2) ->
        SymProp.Coq_angelic_binary
          ((weaken_symprop _UU03a3_1 p1 _UU03a3_2 _UU03b6_),
          (weaken_symprop _UU03a3_1 p2 _UU03a3_2 _UU03b6_))
      | SymProp.Coq_demonic_binary (p1, p2) ->
        SymProp.Coq_demonic_binary
          ((weaken_symprop _UU03a3_1 p1 _UU03a3_2 _UU03b6_),
          (weaken_symprop _UU03a3_1 p2 _UU03a3_2 _UU03b6_))
      | SymProp.Coq_error msg ->
        SymProp.Coq_error
          (RiscvPmpBase.substSU RiscvPmpBase.Coq_amsg.substSU_amessage
            _UU03a3_1 _UU03a3_2 msg _UU03b6_)
      | SymProp.Coq_block -> SymProp.Coq_block
      | SymProp.Coq_assertk (fml, msg, p0) ->
        SymProp.Coq_assertk
          ((RiscvPmpBase.substSU
             (subSU_formula RiscvPmpBase.substUniv_weaken) _UU03a3_1
             _UU03a3_2 fml _UU03b6_),
          (RiscvPmpBase.substSU RiscvPmpBase.Coq_amsg.substSU_amessage
            _UU03a3_1 _UU03a3_2 msg _UU03b6_),
          (weaken_symprop _UU03a3_1 p0 _UU03a3_2 _UU03b6_))
      | SymProp.Coq_assumek (fml, p0) ->
        SymProp.Coq_assumek
          ((RiscvPmpBase.substSU
             (subSU_formula RiscvPmpBase.substUniv_weaken) _UU03a3_1
             _UU03a3_2 fml _UU03b6_),
          (weaken_symprop _UU03a3_1 p0 _UU03a3_2 _UU03b6_))
      | SymProp.Coq_angelicv (b, p0) ->
        SymProp.Coq_angelicv (b,
          (weaken_symprop (Coq_ctx.Coq_snoc (_UU03a3_1, b)) p0
            (Coq_ctx.Coq_snoc (_UU03a3_2, b))
            (RiscvPmpBase.upSU RiscvPmpBase.substUniv_weaken
              RiscvPmpBase.substUnivMeet_weaken
              RiscvPmpBase.substUnivVar_weaken
              RiscvPmpBase.substUnivVarUp_weaken _UU03a3_1 _UU03a3_2 b
              _UU03b6_)))
      | SymProp.Coq_demonicv (b, p0) ->
        SymProp.Coq_demonicv (b,
          (weaken_symprop (Coq_ctx.Coq_snoc (_UU03a3_1, b)) p0
            (Coq_ctx.Coq_snoc (_UU03a3_2, b))
            (RiscvPmpBase.upSU RiscvPmpBase.substUniv_weaken
              RiscvPmpBase.substUnivMeet_weaken
              RiscvPmpBase.substUnivVar_weaken
              RiscvPmpBase.substUnivVarUp_weaken _UU03a3_1 _UU03a3_2 b
              _UU03b6_)))
      | SymProp.Coq_assert_vareq (x, _UU03c3_, xIn, t, msg, p0) ->
        let _UU03b6_' =
          RiscvPmpBase.weakenRemovePres _UU03a3_1 _UU03a3_2 _UU03b6_
            { Binding.name = x; Binding.coq_type = _UU03c3_ } xIn
        in
        let t' =
          RiscvPmpBase.substSU
            (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
              _UU03c3_)
            (Coq_ctx.remove _UU03a3_1 { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            (Coq_ctx.remove _UU03a3_2 { Binding.name = x; Binding.coq_type =
              _UU03c3_ }
              (RiscvPmpBase.weakenIn _UU03a3_1 _UU03a3_2 _UU03b6_
                { Binding.name = x; Binding.coq_type = _UU03c3_ } xIn))
            t _UU03b6_'
        in
        SymProp.Coq_assert_vareq (x, _UU03c3_,
        (RiscvPmpBase.weakenIn _UU03a3_1 _UU03a3_2 _UU03b6_ { Binding.name =
          x; Binding.coq_type = _UU03c3_ } xIn),
        t',
        (RiscvPmpBase.substSU RiscvPmpBase.Coq_amsg.substSU_amessage
          (Coq_ctx.remove _UU03a3_1 { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          (Coq_ctx.remove _UU03a3_2 { Binding.name = x; Binding.coq_type =
            _UU03c3_ }
            (RiscvPmpBase.weakenIn _UU03a3_1 _UU03a3_2 _UU03b6_
              { Binding.name = x; Binding.coq_type = _UU03c3_ } xIn))
          msg _UU03b6_'),
        (weaken_symprop
          (Coq_ctx.remove _UU03a3_1 { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          p0
          (Coq_ctx.remove _UU03a3_2 { Binding.name = x; Binding.coq_type =
            _UU03c3_ }
            (RiscvPmpBase.weakenIn _UU03a3_1 _UU03a3_2 _UU03b6_
              { Binding.name = x; Binding.coq_type = _UU03c3_ } xIn))
          _UU03b6_'))
      | SymProp.Coq_assume_vareq (x, _UU03c3_, xIn, t, p0) ->
        let _UU03b6_' =
          RiscvPmpBase.weakenRemovePres _UU03a3_1 _UU03a3_2 _UU03b6_
            { Binding.name = x; Binding.coq_type = _UU03c3_ } xIn
        in
        SymProp.Coq_assume_vareq (x, _UU03c3_,
        (RiscvPmpBase.weakenIn _UU03a3_1 _UU03a3_2 _UU03b6_ { Binding.name =
          x; Binding.coq_type = _UU03c3_ } xIn),
        (RiscvPmpBase.substSU
          (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
            _UU03c3_)
          (Coq_ctx.remove _UU03a3_1 { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          (Coq_ctx.remove _UU03a3_2 { Binding.name = x; Binding.coq_type =
            _UU03c3_ }
            (RiscvPmpBase.weakenIn _UU03a3_1 _UU03a3_2 _UU03b6_
              { Binding.name = x; Binding.coq_type = _UU03c3_ } xIn))
          t _UU03b6_'),
        (weaken_symprop
          (Coq_ctx.remove _UU03a3_1 { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          p0
          (Coq_ctx.remove _UU03a3_2 { Binding.name = x; Binding.coq_type =
            _UU03c3_ }
            (RiscvPmpBase.weakenIn _UU03a3_1 _UU03a3_2 _UU03b6_
              { Binding.name = x; Binding.coq_type = _UU03c3_ } xIn))
          _UU03b6_'))
      | SymProp.Coq_pattern_match (_UU03c3_, t, pat, k) ->
        SymProp.Coq_pattern_match (_UU03c3_,
          (RiscvPmpBase.substSU
            (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
              _UU03c3_)
            _UU03a3_1 _UU03a3_2 t _UU03b6_),
          pat, (fun pc ->
          weaken_symprop
            (Coq_ctx.cat _UU03a3_1
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (k pc)
            (Coq_ctx.cat _UU03a3_2
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (RiscvPmpBase.wkKeepCtx _UU03a3_1 _UU03a3_2 _UU03b6_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))))
      | SymProp.Coq_pattern_match_var (_, _, _, _, _) ->
        SymProp.Coq_error (RiscvPmpBase.Coq_amsg.Coq_mk
          ((Obj.magic RiscvPmpBase.coq_SubstUnit),
          RiscvPmpBase.substSU_Const,
          (Obj.magic RiscvPmpBase.coq_SubstLawsUnit),
          (Obj.magic RiscvPmpBase.occurs_check_unit),
          RiscvPmpBase.erase_Const, (Obj.magic Coq_tt)))
      | SymProp.Coq_debug (msg, p0) ->
        SymProp.Coq_debug
          ((RiscvPmpBase.substSU RiscvPmpBase.Coq_amsg.substSU_amessage
             _UU03a3_1 _UU03a3_2 msg _UU03b6_),
          (weaken_symprop _UU03a3_1 p0 _UU03a3_2 _UU03b6_))

    (** val coq_SubstSU_SymProp :
        (RiscvPmpBase.coq_WeakensTo, SymProp.coq_SymProp)
        RiscvPmpBase.coq_SubstSU **)

    let coq_SubstSU_SymProp _UU03a3_1 _UU03a3_2 p _UU03c3_ =
      weaken_symprop _UU03a3_1 p _UU03a3_2 _UU03c3_

    type coq_UQSymProp =
      (RiscvPmpBase.coq_WeakensTo, SymProp.coq_SymProp)
      RiscvPmpBase.coq_Weakened

    (** val from_uqSymProp :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_UQSymProp -> SymProp.coq_SymProp **)

    let from_uqSymProp _UU03a3_ =
      RiscvPmpBase.unWeaken _UU03a3_ RiscvPmpBase.substUniv_weaken
        coq_SubstSU_SymProp

    (** val uq_angelic_binary :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_UQSymProp -> coq_UQSymProp -> coq_UQSymProp **)

    let uq_angelic_binary _UU03a3_ =
      RiscvPmpBase.liftBinOp RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken _UU03a3_ coq_SubstSU_SymProp
        coq_SubstSU_SymProp coq_SubstSU_SymProp (fun _ p1' p2' ->
        SymProp.Coq_angelic_binary (p1', p2'))

    (** val uq_demonic_binary :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_UQSymProp -> coq_UQSymProp -> coq_UQSymProp **)

    let uq_demonic_binary _UU03a3_ =
      RiscvPmpBase.liftBinOp RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken _UU03a3_ coq_SubstSU_SymProp
        coq_SubstSU_SymProp coq_SubstSU_SymProp (fun _ p1' p2' ->
        SymProp.Coq_demonic_binary (p1', p2'))

    (** val uq_error :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_UQSymProp **)

    let uq_error _UU03a3_ msg =
      RiscvPmpBase.weakenInit RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken coq_SubstSU_SymProp
        RiscvPmpBase.substUniv_weaken RiscvPmpBase.substUnivMeet_weaken
        _UU03a3_ (SymProp.Coq_error
        (RiscvPmpBase.Coq_amsg.boxMsg _UU03a3_ Coq_ctx.Coq_nil msg))

    (** val uq_block :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_UQSymProp **)

    let uq_block _UU03a3_ =
      RiscvPmpBase.weakenInit RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken coq_SubstSU_SymProp
        RiscvPmpBase.substUniv_weaken RiscvPmpBase.substUnivMeet_weaken
        _UU03a3_ SymProp.Coq_block

    (** val uq_assertk :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_UQSymProp ->
        coq_UQSymProp **)

    let uq_assertk _UU03a3_ fml msg =
      RiscvPmpBase.liftBinOp RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken _UU03a3_
        (subSU_formula RiscvPmpBase.substUniv_weaken) coq_SubstSU_SymProp
        coq_SubstSU_SymProp (fun _UU03a3_' fml' kP' -> SymProp.Coq_assertk
        (fml', (RiscvPmpBase.Coq_amsg.boxMsg _UU03a3_ _UU03a3_' msg), kP'))
        (RiscvPmpBase.gen_occurs_check RiscvPmpBase.substUniv_weaken
          (subSU_formula RiscvPmpBase.substUniv_weaken)
          (coq_GenOccursCheckFormula RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken
            RiscvPmpBase.substUnivVar_weaken RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken)
          _UU03a3_ fml)

    (** val uq_assumek :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> coq_UQSymProp -> coq_UQSymProp **)

    let uq_assumek _UU03a3_ fml =
      RiscvPmpBase.liftBinOp RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
        RiscvPmpBase.substUnivMeet_weaken _UU03a3_
        (subSU_formula RiscvPmpBase.substUniv_weaken) coq_SubstSU_SymProp
        coq_SubstSU_SymProp (fun _ fml' kP' -> SymProp.Coq_assumek (fml',
        kP'))
        (RiscvPmpBase.gen_occurs_check RiscvPmpBase.substUniv_weaken
          (subSU_formula RiscvPmpBase.substUniv_weaken)
          (coq_GenOccursCheckFormula RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken
            RiscvPmpBase.substUnivVar_weaken RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
            RiscvPmpBase.substUnivMeet_weaken)
          _UU03a3_ fml)

    (** val uq_angelicv :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_UQSymProp ->
        coq_UQSymProp **)

    let uq_angelicv _UU03a3_ b kP =
      RiscvPmpBase.elimWeakenedVarZero coq_SubstSU_SymProp _UU03a3_ b
        (fun _UU03a3_0 kP' ->
        let filtered_var =
          Coq_ty.inhabit RiscvPmpBase.typedeclkit RiscvPmpBase.typedenotekit
            b.Binding.coq_type
        in
        (match filtered_var with
         | Some _ -> kP'
         | None ->
           SymProp.Coq_angelicv (b,
             (RiscvPmpBase.substSU coq_SubstSU_SymProp
               (Coq_ctx.remove (Coq_ctx.Coq_snoc (_UU03a3_0, b)) b
                 (Coq_ctx.in_zero b _UU03a3_0))
               (Coq_ctx.Coq_snoc (_UU03a3_0, b)) kP'
               (RiscvPmpBase.wkRemove (Coq_ctx.Coq_snoc (_UU03a3_0, b)) b
                 (Coq_ctx.in_zero b _UU03a3_0))))))
        (fun _ x -> SymProp.Coq_angelicv (b, x)) kP

    (** val uq_demonicv :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_UQSymProp ->
        coq_UQSymProp **)

    let uq_demonicv _UU03a3_ b kP =
      RiscvPmpBase.elimWeakenedVarZero coq_SubstSU_SymProp _UU03a3_ b
        (fun _UU03a3_0 kP' ->
        let filtered_var =
          Coq_ty.inhabit RiscvPmpBase.typedeclkit RiscvPmpBase.typedenotekit
            b.Binding.coq_type
        in
        (match filtered_var with
         | Some _ -> kP'
         | None ->
           SymProp.Coq_demonicv (b,
             (RiscvPmpBase.substSU coq_SubstSU_SymProp _UU03a3_0
               (Coq_ctx.Coq_snoc (_UU03a3_0, b)) kP'
               (RiscvPmpBase.wkRemove (Coq_ctx.Coq_snoc (_UU03a3_0, b)) b
                 (Coq_ctx.in_zero b _UU03a3_0))))))
        (fun _ x -> SymProp.Coq_demonicv (b, x)) kP

    (** val uq_assert_vareq :
        coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_In -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_UQSymProp -> coq_UQSymProp **)

    let uq_assert_vareq x _UU03c3_ _UU03a3_ xIn t msg p =
      RiscvPmpBase.elimWeakenedVar
        (RiscvPmpBase.substSU_pair
          (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
            _UU03c3_)
          coq_SubstSU_SymProp)
        coq_SubstSU_SymProp _UU03a3_ { Binding.name = x; Binding.coq_type =
        _UU03c3_ } xIn (fun _UU03a3_0 xIn' pat ->
        let Coq_pair (t', kP') = pat in
        SymProp.Coq_assert_vareq (x, _UU03c3_, xIn', t',
        (RiscvPmpBase.Coq_amsg.boxMsg
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          (Coq_ctx.remove _UU03a3_0 { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn')
          msg),
        kP'))
        (RiscvPmpBase.liftBinOp RiscvPmpBase.substUniv_weaken
          RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
          RiscvPmpBase.substUnivMeet_weaken
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
            _UU03c3_)
          coq_SubstSU_SymProp
          (RiscvPmpBase.substSU_pair
            (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
              _UU03c3_)
            coq_SubstSU_SymProp)
          (fun _ x0 x1 -> Coq_pair (x0, x1))
          (RiscvPmpBase.gen_occurs_check RiscvPmpBase.substUniv_weaken
            (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
              _UU03c3_)
            (RiscvPmpBase.gen_occurs_check_term RiscvPmpBase.substUniv_weaken
              RiscvPmpBase.substUnivMeet_weaken
              RiscvPmpBase.substUnivVar_weaken RiscvPmpBase.substUniv_weaken
              RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
              RiscvPmpBase.substUnivMeet_weaken _UU03c3_)
            (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            t)
          p)

    (** val uq_assume_vareq :
        coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_In -> RiscvPmpBase.coq_Term ->
        coq_UQSymProp -> coq_UQSymProp **)

    let uq_assume_vareq x _UU03c3_ _UU03a3_ xIn t p =
      RiscvPmpBase.elimWeakenedVar
        (RiscvPmpBase.substSU_pair
          (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
            _UU03c3_)
          coq_SubstSU_SymProp)
        coq_SubstSU_SymProp _UU03a3_ { Binding.name = x; Binding.coq_type =
        _UU03c3_ } xIn (fun _ xIn' pat ->
        let Coq_pair (t', kP') = pat in
        SymProp.Coq_assume_vareq (x, _UU03c3_, xIn', t', kP'))
        (RiscvPmpBase.liftBinOp RiscvPmpBase.substUniv_weaken
          RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
          RiscvPmpBase.substUnivMeet_weaken
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
            _UU03c3_)
          coq_SubstSU_SymProp
          (RiscvPmpBase.substSU_pair
            (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
              _UU03c3_)
            coq_SubstSU_SymProp)
          (fun _ x0 x1 -> Coq_pair (x0, x1))
          (RiscvPmpBase.gen_occurs_check RiscvPmpBase.substUniv_weaken
            (RiscvPmpBase.coq_SubstSUTerm RiscvPmpBase.substUniv_weaken
              _UU03c3_)
            (RiscvPmpBase.gen_occurs_check_term RiscvPmpBase.substUniv_weaken
              RiscvPmpBase.substUnivMeet_weaken
              RiscvPmpBase.substUnivVar_weaken RiscvPmpBase.substUniv_weaken
              RiscvPmpBase.substUnivMeet_weaken RiscvPmpBase.substUniv_weaken
              RiscvPmpBase.substUnivMeet_weaken _UU03c3_)
            (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            t)
          p)

    (** val uq_debug :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_UQSymProp -> coq_UQSymProp **)

    let uq_debug _UU03a3_ msg =
      RiscvPmpBase.liftUnOp RiscvPmpBase.substUniv_weaken _UU03a3_
        coq_SubstSU_SymProp coq_SubstSU_SymProp (fun _UU03a3_' p' ->
        SymProp.Coq_debug
        ((RiscvPmpBase.Coq_amsg.boxMsg _UU03a3_ _UU03a3_' msg), p'))

    (** val to_uqSymProp :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> coq_UQSymProp **)

    let rec to_uqSymProp _UU03a3_ = function
    | SymProp.Coq_angelic_binary (p1, p2) ->
      uq_angelic_binary _UU03a3_ (to_uqSymProp _UU03a3_ p1)
        (to_uqSymProp _UU03a3_ p2)
    | SymProp.Coq_demonic_binary (p1, p2) ->
      uq_demonic_binary _UU03a3_ (to_uqSymProp _UU03a3_ p1)
        (to_uqSymProp _UU03a3_ p2)
    | SymProp.Coq_error msg -> uq_error _UU03a3_ msg
    | SymProp.Coq_assertk (fml, msg, kP) ->
      uq_assertk _UU03a3_ fml msg (to_uqSymProp _UU03a3_ kP)
    | SymProp.Coq_assumek (fml, kP) ->
      uq_assumek _UU03a3_ fml (to_uqSymProp _UU03a3_ kP)
    | SymProp.Coq_angelicv (b, p0) ->
      uq_angelicv _UU03a3_ b
        (to_uqSymProp (Coq_ctx.Coq_snoc (_UU03a3_, b)) p0)
    | SymProp.Coq_demonicv (b, p0) ->
      uq_demonicv _UU03a3_ b
        (to_uqSymProp (Coq_ctx.Coq_snoc (_UU03a3_, b)) p0)
    | SymProp.Coq_assert_vareq (x, _UU03c3_, xIn, t, msg, p0) ->
      uq_assert_vareq x _UU03c3_ _UU03a3_ xIn t msg
        (to_uqSymProp
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          p0)
    | SymProp.Coq_assume_vareq (x, _UU03c3_, xIn, t, p0) ->
      uq_assume_vareq x _UU03c3_ _UU03a3_ xIn t
        (to_uqSymProp
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          p0)
    | SymProp.Coq_debug (msg, p0) ->
      uq_debug _UU03a3_ msg (to_uqSymProp _UU03a3_ p0)
    | _ -> uq_block _UU03a3_

    (** val unquantify :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp **)

    let unquantify _UU03a3_ p =
      from_uqSymProp _UU03a3_ (to_uqSymProp _UU03a3_ p)

    (** val weakenWorld :
        coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_WeakensTo -> coq_World **)

    let weakenWorld w _UU03a3_' _UU03b6_ =
      { wctx = _UU03a3_'; wco =
        (RiscvPmpBase.substSU
          (RiscvPmpBase.substSU_ctx
            (subSU_formula RiscvPmpBase.substUniv_weaken))
          w.wctx _UU03a3_' w.wco _UU03b6_) }

    (** val weakenWorld_acc :
        coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_WeakensTo -> coq_Acc **)

    let weakenWorld_acc w _UU03a3_' _UU03b6_ =
      Coq_acc_sub ((weakenWorld w _UU03a3_' _UU03b6_),
        (RiscvPmpBase.interpWk w.wctx _UU03a3_' _UU03b6_))
   end

  (** val postprocess :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp **)

  let postprocess _UU03a3_ p =
    Postprocessing.prune _UU03a3_
      (Postprocessing.solve_uvars _UU03a3_
        (Postprocessing.prune _UU03a3_
          (Postprocessing.solve_evars _UU03a3_
            (Postprocessing.prune _UU03a3_ p))))

  (** val postprocess2 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp **)

  let postprocess2 _UU03a3_ p =
    Postprocessing.unquantify _UU03a3_ (postprocess _UU03a3_ p)

  module Erasure =
   struct
    type coq_ESymProp =
    | Coq_eangelic_binary of coq_ESymProp * coq_ESymProp
    | Coq_edemonic_binary of coq_ESymProp * coq_ESymProp
    | Coq_eerror of RiscvPmpBase.Coq_amsg.coq_EAMessage
    | Coq_eblock
    | Coq_eassertk of coq_EFormula * coq_ESymProp
    | Coq_eassumek of coq_EFormula * coq_ESymProp
    | Coq_eangelicv of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_ESymProp
    | Coq_edemonicv of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_ESymProp
    | Coq_eassert_vareq of coq_LVar * Coq_ty.coq_Ty * nat
       * RiscvPmpBase.coq_ETerm * coq_ESymProp
    | Coq_eassume_vareq of coq_LVar * Coq_ty.coq_Ty * nat
       * RiscvPmpBase.coq_ETerm * coq_ESymProp
    | Coq_epattern_match of Coq_ty.coq_Ty * RiscvPmpBase.coq_ETerm
       * coq_LVar RiscvPmpBase.coq_Pattern
       * (coq_LVar RiscvPmpBase.coq_PatternCase -> coq_ESymProp)
    | Coq_epattern_match_var of coq_LVar * Coq_ty.coq_Ty * nat
       * coq_LVar RiscvPmpBase.coq_Pattern
       * (coq_LVar RiscvPmpBase.coq_PatternCase -> coq_ESymProp)
    | Coq_edebug of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                    Coq_ctx.coq_Ctx
       * RiscvPmpBase.Coq_amsg.coq_AMessage * coq_ESymProp

    (** val coq_ESymProp_rect :
        (coq_ESymProp -> 'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_ESymProp
        -> 'a1 -> coq_ESymProp -> 'a1 -> 'a1) ->
        (RiscvPmpBase.Coq_amsg.coq_EAMessage -> 'a1) -> 'a1 -> (coq_EFormula
        -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_EFormula -> coq_ESymProp ->
        'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
        coq_ESymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_LVar ->
        Coq_ty.coq_Ty -> nat -> RiscvPmpBase.coq_ETerm -> coq_ESymProp -> 'a1
        -> 'a1) -> (coq_LVar -> Coq_ty.coq_Ty -> nat ->
        RiscvPmpBase.coq_ETerm -> coq_ESymProp -> 'a1 -> 'a1) ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_ETerm -> coq_LVar
        RiscvPmpBase.coq_Pattern -> (coq_LVar RiscvPmpBase.coq_PatternCase ->
        coq_ESymProp) -> (coq_LVar RiscvPmpBase.coq_PatternCase -> 'a1) ->
        'a1) -> (coq_LVar -> Coq_ty.coq_Ty -> nat -> coq_LVar
        RiscvPmpBase.coq_Pattern -> (coq_LVar RiscvPmpBase.coq_PatternCase ->
        coq_ESymProp) -> (coq_LVar RiscvPmpBase.coq_PatternCase -> 'a1) ->
        'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_ESymProp
        -> 'a1 -> 'a1) -> coq_ESymProp -> 'a1 **)

    let rec coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
    | Coq_eangelic_binary (o1, o2) ->
      f o1 (coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 o1) o2
        (coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 o2)
    | Coq_edemonic_binary (o1, o2) ->
      f0 o1 (coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 o1) o2
        (coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 o2)
    | Coq_eerror msg -> f1 msg
    | Coq_eblock -> f2
    | Coq_eassertk (fml, k) ->
      f3 fml k (coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_eassumek (fml, k) ->
      f4 fml k (coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_eangelicv (b, k) ->
      f5 b k (coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_edemonicv (b, k) ->
      f6 b k (coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_eassert_vareq (x, _UU03c3_, n, t, k) ->
      f7 x _UU03c3_ n t k
        (coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_eassume_vareq (x, _UU03c3_, n, t, k) ->
      f8 x _UU03c3_ n t k
        (coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_epattern_match (_UU03c3_, s, pat, rhs) ->
      f9 _UU03c3_ s pat rhs (fun p ->
        coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 (rhs p))
    | Coq_epattern_match_var (x, _UU03c3_, n, pat, rhs) ->
      f10 x _UU03c3_ n pat rhs (fun p ->
        coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 (rhs p))
    | Coq_edebug (_UU03a3_, b, k) ->
      f11 _UU03a3_ b k
        (coq_ESymProp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)

    (** val coq_ESymProp_rec :
        (coq_ESymProp -> 'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_ESymProp
        -> 'a1 -> coq_ESymProp -> 'a1 -> 'a1) ->
        (RiscvPmpBase.Coq_amsg.coq_EAMessage -> 'a1) -> 'a1 -> (coq_EFormula
        -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_EFormula -> coq_ESymProp ->
        'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
        coq_ESymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_LVar ->
        Coq_ty.coq_Ty -> nat -> RiscvPmpBase.coq_ETerm -> coq_ESymProp -> 'a1
        -> 'a1) -> (coq_LVar -> Coq_ty.coq_Ty -> nat ->
        RiscvPmpBase.coq_ETerm -> coq_ESymProp -> 'a1 -> 'a1) ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_ETerm -> coq_LVar
        RiscvPmpBase.coq_Pattern -> (coq_LVar RiscvPmpBase.coq_PatternCase ->
        coq_ESymProp) -> (coq_LVar RiscvPmpBase.coq_PatternCase -> 'a1) ->
        'a1) -> (coq_LVar -> Coq_ty.coq_Ty -> nat -> coq_LVar
        RiscvPmpBase.coq_Pattern -> (coq_LVar RiscvPmpBase.coq_PatternCase ->
        coq_ESymProp) -> (coq_LVar RiscvPmpBase.coq_PatternCase -> 'a1) ->
        'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_ESymProp
        -> 'a1 -> 'a1) -> coq_ESymProp -> 'a1 **)

    let rec coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
    | Coq_eangelic_binary (o1, o2) ->
      f o1 (coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 o1) o2
        (coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 o2)
    | Coq_edemonic_binary (o1, o2) ->
      f0 o1 (coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 o1) o2
        (coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 o2)
    | Coq_eerror msg -> f1 msg
    | Coq_eblock -> f2
    | Coq_eassertk (fml, k) ->
      f3 fml k (coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_eassumek (fml, k) ->
      f4 fml k (coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_eangelicv (b, k) ->
      f5 b k (coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_edemonicv (b, k) ->
      f6 b k (coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_eassert_vareq (x, _UU03c3_, n, t, k) ->
      f7 x _UU03c3_ n t k
        (coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_eassume_vareq (x, _UU03c3_, n, t, k) ->
      f8 x _UU03c3_ n t k
        (coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)
    | Coq_epattern_match (_UU03c3_, s, pat, rhs) ->
      f9 _UU03c3_ s pat rhs (fun p ->
        coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 (rhs p))
    | Coq_epattern_match_var (x, _UU03c3_, n, pat, rhs) ->
      f10 x _UU03c3_ n pat rhs (fun p ->
        coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 (rhs p))
    | Coq_edebug (_UU03a3_, b, k) ->
      f11 _UU03a3_ b k
        (coq_ESymProp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 k)

    (** val erase_symprop :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> coq_ESymProp **)

    let rec erase_symprop _UU03a3_ = function
    | SymProp.Coq_angelic_binary (o1, o2) ->
      Coq_eangelic_binary ((erase_symprop _UU03a3_ o1),
        (erase_symprop _UU03a3_ o2))
    | SymProp.Coq_demonic_binary (o1, o2) ->
      Coq_edemonic_binary ((erase_symprop _UU03a3_ o1),
        (erase_symprop _UU03a3_ o2))
    | SymProp.Coq_error msg0 ->
      let RiscvPmpBase.Coq_amsg.Coq_mk (_, _, _, _, eM, msg) = msg0 in
      Coq_eerror (RiscvPmpBase.erase eM _UU03a3_ msg)
    | SymProp.Coq_block -> Coq_eblock
    | SymProp.Coq_assertk (fml, _, k) ->
      Coq_eassertk ((erase_formula _UU03a3_ fml), (erase_symprop _UU03a3_ k))
    | SymProp.Coq_assumek (fml, k) ->
      Coq_eassumek ((erase_formula _UU03a3_ fml), (erase_symprop _UU03a3_ k))
    | SymProp.Coq_angelicv (b, k) ->
      Coq_eangelicv (b, (erase_symprop (Coq_ctx.Coq_snoc (_UU03a3_, b)) k))
    | SymProp.Coq_demonicv (b, k) ->
      Coq_edemonicv (b, (erase_symprop (Coq_ctx.Coq_snoc (_UU03a3_, b)) k))
    | SymProp.Coq_assert_vareq (x, _UU03c3_, xIn, t, _, k) ->
      Coq_eassert_vareq (x, _UU03c3_, xIn,
        (RiscvPmpBase.erase_term
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          _UU03c3_ t),
        (erase_symprop
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          k))
    | SymProp.Coq_assume_vareq (x, _UU03c3_, xIn, t, k) ->
      Coq_eassume_vareq (x, _UU03c3_, xIn,
        (RiscvPmpBase.erase_term
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          _UU03c3_ t),
        (erase_symprop
          (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
            _UU03c3_ } xIn)
          k))
    | SymProp.Coq_pattern_match (_UU03c3_, s, pat, rhs) ->
      Coq_epattern_match (_UU03c3_,
        (RiscvPmpBase.erase_term _UU03a3_ _UU03c3_ s), pat, (fun pc ->
        erase_symprop
          (Coq_ctx.cat _UU03a3_
            (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
          (rhs pc)))
    | SymProp.Coq_pattern_match_var (x, _UU03c3_, xIn, pat, rhs) ->
      Coq_epattern_match_var (x, _UU03c3_, xIn, pat, (fun pc ->
        erase_symprop
          (Coq_ctx.remove
            (Coq_ctx.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            { Binding.name = x; Binding.coq_type = _UU03c3_ }
            (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type =
              _UU03c3_ } _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) xIn))
          (rhs pc)))
    | SymProp.Coq_debug (b, k) ->
      Coq_edebug (_UU03a3_, b, (erase_symprop _UU03a3_ k))

    (** val erase_SymProp :
        (SymProp.coq_SymProp, coq_ESymProp) RiscvPmpBase.coq_Erase **)

    let erase_SymProp =
      erase_symprop

    (** val erase_valuation :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
        Coq_env.coq_Env -> (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list **)

    let rec erase_valuation _ = function
    | Coq_env.Coq_nil -> Coq_nil
    | Coq_env.Coq_snoc (_UU0393_, _UU03b9_0, b, v) ->
      Coq_cons ((Coq_existT (b.Binding.coq_type, v)),
        (erase_valuation _UU0393_ _UU03b9_0))

    (** val erase_Valuation :
        (((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
        Coq_env.coq_Env, (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list)
        RiscvPmpBase.coq_Erase **)

    let erase_Valuation =
      erase_valuation

    (** val inst_env' :
        (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> (Coq_ty.coq_Ty ->
        RiscvPmpBase.coq_ETerm -> Coq_ty.coq_Val option) -> Coq_ty.coq_Ty
        Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
        Coq_env.coq_Env -> (Coq_ty.coq_Ty, Coq_ty.coq_Val) Coq_env.coq_Env
        option **)

    let rec inst_env' _UU03b9_ inst_eterm0 _ = function
    | Coq_env.Coq_nil -> Some Coq_env.Coq_nil
    | Coq_env.Coq_snoc (_UU0393_, e0, _UU03c3_, t) ->
      Coq_option.bind (inst_eterm0 _UU03c3_ t) (fun v ->
        Coq_option.bind (inst_env' _UU03b9_ inst_eterm0 _UU0393_ e0)
          (fun vs -> Some (Coq_env.Coq_snoc (_UU0393_, vs, _UU03c3_, v))))

    (** val inst_namedenv' :
        (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> (Coq_ty.coq_Ty ->
        RiscvPmpBase.coq_ETerm -> Coq_ty.coq_Val option) -> ('a1,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
        Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) coq_NamedEnv -> ('a1,
        Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv option **)

    let rec inst_namedenv' _UU03b9_ inst_eterm0 _ = function
    | Coq_env.Coq_nil -> Some Coq_env.Coq_nil
    | Coq_env.Coq_snoc (_UU0393_, e0, b, t) ->
      let _UU2113_ = b.Binding.name in
      let _UU03c3_ = b.Binding.coq_type in
      Coq_option.bind (inst_eterm0 _UU03c3_ t) (fun v ->
        Coq_option.bind (inst_namedenv' _UU03b9_ inst_eterm0 _UU0393_ e0)
          (fun vs -> Some (Coq_env.Coq_snoc (_UU0393_, vs, { Binding.name =
          _UU2113_; Binding.coq_type = _UU03c3_ }, v))))

    (** val inst_eterm :
        (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> Coq_ty.coq_Ty ->
        RiscvPmpBase.coq_ETerm -> Coq_ty.coq_Val option **)

    let rec inst_eterm _UU03b9_ _ = function
    | RiscvPmpBase.Coq_eterm_var (_, _UU03c4_, n) ->
      Coq_option.bind (nth_error _UU03b9_ n) (fun pat ->
        let Coq_existT (_UU03c3_, v) = pat in
        (match eq_dec
                 (Coq_ty.coq_Ty_eq_dec RiscvPmpBase.typedeclkit
                   RiscvPmpBase.typedenotekit RiscvPmpBase.typedefkit)
                 _UU03c3_ _UU03c4_ with
         | Coq_left -> Some v
         | Coq_right -> None))
    | RiscvPmpBase.Coq_eterm_val (_, v) -> Some v
    | RiscvPmpBase.Coq_eterm_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1,
                                    t2) ->
      Coq_option.bind (inst_eterm _UU03b9_ _UU03c3_1 t1) (fun v1 ->
        Coq_option.bind (inst_eterm _UU03b9_ _UU03c3_2 t2) (fun v2 -> Some
          (Coq_bop.eval RiscvPmpBase.typedeclkit RiscvPmpBase.typedenotekit
            RiscvPmpBase.typedefkit _UU03c3_1 _UU03c3_2 _UU03c3_3 op v1 v2)))
    | RiscvPmpBase.Coq_eterm_unop (_UU03c3_1, _UU03c3_2, op, t0) ->
      Coq_option.map
        (Coq_uop.eval RiscvPmpBase.typedeclkit RiscvPmpBase.typedenotekit
          _UU03c3_1 _UU03c3_2 op)
        (inst_eterm _UU03b9_ _UU03c3_1 t0)
    | RiscvPmpBase.Coq_eterm_tuple (_UU03c3_s, ts) ->
      Coq_option.map (Coq_envrec.of_env _UU03c3_s)
        (inst_env' _UU03b9_ (inst_eterm _UU03b9_) _UU03c3_s ts)
    | RiscvPmpBase.Coq_eterm_union (u, k, t0) ->
      Coq_option.bind
        (inst_eterm _UU03b9_ (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty u k)
          t0)
        (fun v -> Some
        (RiscvPmpBase.typedefkit.Coq_ty.unionv_fold u (Coq_existT (k, v))))
    | RiscvPmpBase.Coq_eterm_record (r, ts) ->
      Coq_option.map (RiscvPmpBase.typedefkit.Coq_ty.recordv_fold r)
        (inst_namedenv' _UU03b9_ (inst_eterm _UU03b9_)
          (RiscvPmpBase.typedefkit.Coq_ty.recordf_ty r) ts)

    (** val inst_namedenv :
        (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> ('a1, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty,
        RiscvPmpBase.coq_ETerm) coq_NamedEnv -> ('a1, Coq_ty.coq_Ty,
        Coq_ty.coq_Val) coq_NamedEnv option **)

    let inst_namedenv _UU03b9_ _UU0394_ =
      inst_namedenv' _UU03b9_ (inst_eterm _UU03b9_) _UU0394_

    (** val inst_env :
        (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> Coq_ty.coq_Ty
        Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
        Coq_env.coq_Env -> (Coq_ty.coq_Ty, Coq_ty.coq_Val) Coq_env.coq_Env
        option **)

    let rec inst_env _UU03b9_ _ = function
    | Coq_env.Coq_nil -> Some Coq_env.Coq_nil
    | Coq_env.Coq_snoc (_UU0393_, e0, _UU03c3_, t) ->
      Coq_option.bind (inst_eterm _UU03b9_ _UU03c3_ t) (fun v ->
        Coq_option.bind (inst_env _UU03b9_ _UU0393_ e0) (fun vs -> Some
          (Coq_env.Coq_snoc (_UU0393_, vs, _UU03c3_, v))))

    (** val inst_eformula :
        (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> coq_EFormula -> __ option **)

    let rec inst_eformula _UU03b9_ = function
    | Coq_eformula_user (p, ts) ->
      Coq_option.bind
        (inst_env _UU03b9_
          (match p with
           | Coq_gen_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_check_perms ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_privilege)
           | Coq_pmp_check_rwx ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)
           | Coq_sub_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_access_type)
           | Coq_access_pmp_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_pmpcfgperm)
           | Coq_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)
           | Coq_not_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_prev_addr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_xlenbits)
           | Coq_in_entries ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               RiscvPmpBase.ty_pmpentry)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_in_mmio _ ->
             Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits))
          ts)
        (fun _ -> Some __)
    | Coq_eformula_bool t ->
      Coq_option.bind (inst_eterm _UU03b9_ Coq_ty.Coq_bool t) (fun _ -> Some
        __)
    | Coq_eformula_prop (_UU03a3_', _UU03b6_, _) ->
      Coq_option.bind (inst_namedenv _UU03b9_ _UU03a3_' _UU03b6_) (fun _ ->
        Some __)
    | Coq_eformula_relop (_UU03c3_, _, t1, t2) ->
      Coq_option.bind (inst_eterm _UU03b9_ _UU03c3_ t1) (fun _ ->
        Coq_option.bind (inst_eterm _UU03b9_ _UU03c3_ t2) (fun _ -> Some __))
    | Coq_eformula_and (f1, f2) ->
      Coq_option.bind (inst_eformula _UU03b9_ f1) (fun _ ->
        Coq_option.bind (inst_eformula _UU03b9_ f2) (fun _ -> Some __))
    | Coq_eformula_or (f1, f2) ->
      Coq_option.bind (inst_eformula _UU03b9_ f1) (fun _ ->
        Coq_option.bind (inst_eformula _UU03b9_ f2) (fun _ -> Some __))
    | _ -> Some __

    (** val list_remove : 'a1 list -> nat -> 'a1 list **)

    let rec list_remove xs n =
      match xs with
      | Coq_nil -> Coq_nil
      | Coq_cons (x, xs0) ->
        (match n with
         | O -> xs0
         | S n0 -> Coq_cons (x, (list_remove xs0 n0)))

    module Coq_notations =
     struct
     end
   end

  module Coq_notations =
   struct
   end

  (** val modality_assuming :
      coq_World -> coq_World -> coq_Acc -> modality **)

  let modality_assuming w1 _ _ =
    { modality_car = (Obj.magic __); modality_intuitionistic_action =
      (MIEnvTransform (bi_pred w1)); modality_spatial_action =
      (MIEnvTransform (bi_pred w1)) }

  (** val modality_forgetting :
      coq_World -> coq_World -> coq_Acc -> modality **)

  let modality_forgetting _ w2 _ =
    { modality_car = (Obj.magic __); modality_intuitionistic_action =
      (MIEnvTransform (bi_pred w2)); modality_spatial_action =
      (MIEnvTransform (bi_pred w2)) }

  module Coq_logicalrelation =
   struct
    type ('aT, 'a) coq_Rel =
      'a -> ('aT, coq_Pred) coq_Impl coq_Valid
      (* singleton inductive, whose constructor was MkRel *)

    (** val coq_RInst :
        ('a1, 'a2) RiscvPmpBase.coq_Inst -> ('a1, 'a2) coq_Rel **)

    let coq_RInst _ =
      Obj.magic __

    (** val coq_RInstPropIff : 'a1 coq_InstPred -> ('a1, __) coq_Rel **)

    let coq_RInstPropIff _ =
      Obj.magic __

    (** val coq_RBox : ('a1, 'a2) coq_Rel -> ('a1 coq_Box, 'a2) coq_Rel **)

    let coq_RBox _ =
      Obj.magic __

    (** val coq_RImpl :
        ('a1, 'a2) coq_Rel -> ('a3, 'a4) coq_Rel -> (('a1, 'a3) coq_Impl, 'a2
        -> 'a4) coq_Rel **)

    let coq_RImpl _ _ =
      Obj.magic __

    (** val coq_RForall :
        ('a1 -> ('a2, 'a3) coq_Rel) -> (('a1, 'a2) coq_Forall, 'a1 -> 'a3)
        coq_Rel **)

    let coq_RForall _ =
      Obj.magic __

    (** val coq_RVal :
        Coq_ty.coq_Ty -> (RiscvPmpBase.coq_Term, Coq_ty.coq_Val) coq_Rel **)

    let coq_RVal _UU03c3_ =
      coq_RInst (RiscvPmpBase.inst_term _UU03c3_)

    (** val coq_RNEnv :
        ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (('a1,
        Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) coq_NamedEnv, ('a1,
        Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv) coq_Rel **)

    let coq_RNEnv _UU0394_ =
      coq_RInst
        (RiscvPmpBase.inst_env (fun _UU03c4_ ->
          RiscvPmpBase.inst_term _UU03c4_.Binding.coq_type) _UU0394_)

    (** val coq_REnv :
        Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ((Coq_ty.coq_Ty,
        RiscvPmpBase.coq_Term) Coq_env.coq_Env, (Coq_ty.coq_Ty,
        Coq_ty.coq_Val) Coq_env.coq_Env) coq_Rel **)

    let coq_REnv _UU0394_ =
      coq_RInst (RiscvPmpBase.inst_env RiscvPmpBase.inst_term _UU0394_)

    (** val coq_RUnit : (RiscvPmpBase.coq_Unit, coq_unit) coq_Rel **)

    let coq_RUnit =
      coq_RInst RiscvPmpBase.inst_unit

    (** val coq_RPathCondition : (coq_PathCondition, __) coq_Rel **)

    let coq_RPathCondition =
      coq_RInstPropIff (instpred_ctx_inst instpred_inst_formula)

    (** val coq_RFormula : (coq_Formula, __) coq_Rel **)

    let coq_RFormula =
      coq_RInstPropIff instpred_inst_formula

    (** val coq_RChunk : (coq_Chunk, coq_SCChunk) coq_Rel **)

    let coq_RChunk =
      coq_RInst inst_chunk

    (** val coq_RMsg :
        ('a2, 'a3) coq_Rel -> (('a1, 'a2) coq_Impl, 'a3) coq_Rel **)

    let coq_RMsg _ =
      Obj.magic __

    (** val coq_RList : ('a1, 'a2) coq_Rel -> ('a1 list, 'a2 list) coq_Rel **)

    let coq_RList _ =
      Obj.magic __

    (** val coq_RHeap : (coq_SHeap, coq_SCHeap) coq_Rel **)

    let coq_RHeap =
      coq_RInst inst_heap

    (** val coq_RConst : ('a1 RiscvPmpBase.coq_Const, 'a1) coq_Rel **)

    let coq_RConst =
      coq_RInst RiscvPmpBase.inst_const

    (** val coq_RProd :
        ('a1, 'a2) coq_Rel -> ('a3, 'a4) coq_Rel -> (('a1, 'a3) prod, ('a2,
        'a4) prod) coq_Rel **)

    let coq_RProd _ _ =
      Obj.magic __

    (** val coq_RMatchResult :
        Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern -> ('a1
        RiscvPmpBase.coq_SMatchResult, 'a1 RiscvPmpBase.coq_MatchResult)
        coq_Rel **)

    let coq_RMatchResult _ _ =
      Obj.magic __

    (** val coq_RIn :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In, Coq_ty.coq_Val)
        coq_Rel **)

    let coq_RIn _ =
      Obj.magic __

    module Coq_notations =
     struct
     end
   end

  module RSolve =
   struct
   end

  module AutorewriteUnifLogic =
   struct
   end

  module LogicalSoundness =
   struct
    (** val coq_RProp :
        (SymProp.coq_SymProp, __) Coq_logicalrelation.coq_Rel **)

    let coq_RProp =
      Obj.magic __
   end

  module Coq_asn =
   struct
    type coq_Assertion =
    | Coq_formula of coq_Formula
    | Coq_chunk of coq_Chunk
    | Coq_chunk_angelic of coq_Chunk
    | Coq_pattern_match of Coq_ty.coq_Ty * RiscvPmpBase.coq_Term
       * coq_LVar RiscvPmpBase.coq_Pattern
       * (coq_LVar RiscvPmpBase.coq_PatternCase -> coq_Assertion)
    | Coq_sep of coq_Assertion * coq_Assertion
    | Coq_or of coq_Assertion * coq_Assertion
    | Coq_exist of coq_LVar * Coq_ty.coq_Ty * coq_Assertion
    | Coq_debug

    (** val coq_Assertion_rect :
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> coq_LVar
        RiscvPmpBase.coq_Pattern -> (coq_LVar RiscvPmpBase.coq_PatternCase ->
        coq_Assertion) -> (coq_LVar RiscvPmpBase.coq_PatternCase -> 'a1) ->
        'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 -> coq_Assertion -> 'a1 ->
        'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 -> coq_Assertion -> 'a1 ->
        'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> coq_LVar -> Coq_ty.coq_Ty -> coq_Assertion -> 'a1
        -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 **)

    let rec coq_Assertion_rect f f0 f1 f2 f3 f4 f5 f6 _UU03a3_ = function
    | Coq_formula fml -> f _UU03a3_ fml
    | Coq_chunk c -> f0 _UU03a3_ c
    | Coq_chunk_angelic c -> f1 _UU03a3_ c
    | Coq_pattern_match (_UU03c3_, s, pat, rhs) ->
      f2 _UU03a3_ _UU03c3_ s pat rhs (fun pc ->
        coq_Assertion_rect f f0 f1 f2 f3 f4 f5 f6
          (Coq_ctx.cat _UU03a3_
            (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
          (rhs pc))
    | Coq_sep (a1, a2) ->
      f3 _UU03a3_ a1 (coq_Assertion_rect f f0 f1 f2 f3 f4 f5 f6 _UU03a3_ a1)
        a2 (coq_Assertion_rect f f0 f1 f2 f3 f4 f5 f6 _UU03a3_ a2)
    | Coq_or (a1, a2) ->
      f4 _UU03a3_ a1 (coq_Assertion_rect f f0 f1 f2 f3 f4 f5 f6 _UU03a3_ a1)
        a2 (coq_Assertion_rect f f0 f1 f2 f3 f4 f5 f6 _UU03a3_ a2)
    | Coq_exist (_UU03c2_, _UU03c4_, a0) ->
      f5 _UU03a3_ _UU03c2_ _UU03c4_ a0
        (coq_Assertion_rect f f0 f1 f2 f3 f4 f5 f6 (Coq_ctx.Coq_snoc
          (_UU03a3_, { Binding.name = _UU03c2_; Binding.coq_type =
          _UU03c4_ })) a0)
    | Coq_debug -> f6 _UU03a3_

    (** val coq_Assertion_rec :
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> coq_LVar
        RiscvPmpBase.coq_Pattern -> (coq_LVar RiscvPmpBase.coq_PatternCase ->
        coq_Assertion) -> (coq_LVar RiscvPmpBase.coq_PatternCase -> 'a1) ->
        'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 -> coq_Assertion -> 'a1 ->
        'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 -> coq_Assertion -> 'a1 ->
        'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> coq_LVar -> Coq_ty.coq_Ty -> coq_Assertion -> 'a1
        -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 **)

    let rec coq_Assertion_rec f f0 f1 f2 f3 f4 f5 f6 _UU03a3_ = function
    | Coq_formula fml -> f _UU03a3_ fml
    | Coq_chunk c -> f0 _UU03a3_ c
    | Coq_chunk_angelic c -> f1 _UU03a3_ c
    | Coq_pattern_match (_UU03c3_, s, pat, rhs) ->
      f2 _UU03a3_ _UU03c3_ s pat rhs (fun pc ->
        coq_Assertion_rec f f0 f1 f2 f3 f4 f5 f6
          (Coq_ctx.cat _UU03a3_
            (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
          (rhs pc))
    | Coq_sep (a1, a2) ->
      f3 _UU03a3_ a1 (coq_Assertion_rec f f0 f1 f2 f3 f4 f5 f6 _UU03a3_ a1)
        a2 (coq_Assertion_rec f f0 f1 f2 f3 f4 f5 f6 _UU03a3_ a2)
    | Coq_or (a1, a2) ->
      f4 _UU03a3_ a1 (coq_Assertion_rec f f0 f1 f2 f3 f4 f5 f6 _UU03a3_ a1)
        a2 (coq_Assertion_rec f f0 f1 f2 f3 f4 f5 f6 _UU03a3_ a2)
    | Coq_exist (_UU03c2_, _UU03c4_, a0) ->
      f5 _UU03a3_ _UU03c2_ _UU03c4_ a0
        (coq_Assertion_rec f f0 f1 f2 f3 f4 f5 f6 (Coq_ctx.Coq_snoc
          (_UU03a3_, { Binding.name = _UU03c2_; Binding.coq_type =
          _UU03c4_ })) a0)
    | Coq_debug -> f6 _UU03a3_

    (** val match_bool :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> coq_Assertion -> coq_Assertion ->
        coq_Assertion **)

    let match_bool _ b a1 a2 =
      Coq_pattern_match (Coq_ty.Coq_bool, b, RiscvPmpBase.Coq_pat_bool,
        (fun v -> match Obj.magic v with
                  | Coq_true -> a1
                  | Coq_false -> a2))

    (** val match_enum :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.enumi -> RiscvPmpBase.coq_Term -> (Coq_ty.enumt ->
        coq_Assertion) -> coq_Assertion **)

    let match_enum _ e k alts =
      Coq_pattern_match ((Coq_ty.Coq_enum e), k, (RiscvPmpBase.Coq_pat_enum
        e), alts)

    (** val match_sum :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> coq_LVar
        -> coq_Assertion -> coq_LVar -> coq_Assertion -> coq_Assertion **)

    let match_sum _ _UU03c3_ _UU03c4_ s xl al xr ar =
      Coq_pattern_match ((Coq_ty.Coq_sum (_UU03c3_, _UU03c4_)), s,
        (RiscvPmpBase.Coq_pat_sum (_UU03c3_, _UU03c4_, xl, xr)), (fun b ->
        match Obj.magic b with
        | Coq_true -> al
        | Coq_false -> ar))

    (** val match_list :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> coq_Assertion -> coq_LVar
        -> coq_LVar -> coq_Assertion -> coq_Assertion **)

    let match_list _ _UU03c3_ s anil xh xt acons =
      Coq_pattern_match ((Coq_ty.Coq_list _UU03c3_), s,
        (RiscvPmpBase.Coq_pat_list (_UU03c3_, xh, xt)), (fun b ->
        match Obj.magic b with
        | Coq_true -> anil
        | Coq_false -> acons))

    (** val match_prod :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> coq_LVar
        -> coq_LVar -> coq_Assertion -> coq_Assertion **)

    let match_prod _ _UU03c3_1 _UU03c3_2 s xl xr rhs =
      Coq_pattern_match ((Coq_ty.Coq_prod (_UU03c3_1, _UU03c3_2)), s,
        (RiscvPmpBase.Coq_pat_pair (xl, xr, _UU03c3_1, _UU03c3_2)), (fun _ ->
        rhs))

    (** val match_tuple :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Term ->
        coq_LVar RiscvPmpBase.coq_TuplePat -> coq_Assertion -> coq_Assertion **)

    let match_tuple _ _UU03c3_s _UU0394_ s p rhs =
      Coq_pattern_match ((Coq_ty.Coq_tuple _UU03c3_s), s,
        (RiscvPmpBase.Coq_pat_tuple (_UU03c3_s, _UU0394_, p)), (fun _ -> rhs))

    (** val match_record :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.recordi -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Term -> coq_LVar
        RiscvPmpBase.coq_RecordPat -> coq_Assertion -> coq_Assertion **)

    let match_record _ r _UU0394_ s p rhs =
      Coq_pattern_match ((Coq_ty.Coq_record r), s,
        (RiscvPmpBase.Coq_pat_record (r, _UU0394_, p)), (fun _ -> rhs))

    (** val match_union_alt :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.unioni -> RiscvPmpBase.coq_Term -> (Coq_ty.unionk ->
        (coq_LVar, coq_Assertion) RiscvPmpBase.coq_Alternative) ->
        coq_Assertion **)

    let match_union_alt _UU03a3_ u t alts =
      Coq_pattern_match ((Coq_ty.Coq_union u), t, (RiscvPmpBase.Coq_pat_union
        (u, (fun k -> (alts k).RiscvPmpBase.alt_pat))), (fun pat ->
        let Coq_existT (k, pc) = Obj.magic pat in
        RiscvPmpBase.of_pattern_case_curried _UU03a3_
          (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty u k)
          (alts k).RiscvPmpBase.alt_pat (alts k).RiscvPmpBase.alt_rhs pc))

    (** val exs :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Assertion -> coq_Assertion **)

    let rec exs _UU03a3_ = function
    | Coq_ctx.Coq_nil -> (fun a -> a)
    | Coq_ctx.Coq_snoc (_UU0393_, b) ->
      let x = b.Binding.name in
      let _UU03c4_ = b.Binding.coq_type in
      (fun a -> exs _UU03a3_ _UU0393_ (Coq_exist (x, _UU03c4_, a)))

    (** val sub_assertion :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Assertion -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Sub -> coq_Assertion **)

    let rec sub_assertion _UU03a3_1 a _UU03a3_2 _UU03b6_ =
      match a with
      | Coq_formula fml ->
        Coq_formula
          (RiscvPmpBase.subst sub_formula _UU03a3_1 fml _UU03a3_2 _UU03b6_)
      | Coq_chunk c ->
        Coq_chunk
          (RiscvPmpBase.subst coq_SubstChunk _UU03a3_1 c _UU03a3_2 _UU03b6_)
      | Coq_chunk_angelic c ->
        Coq_chunk_angelic
          (RiscvPmpBase.subst coq_SubstChunk _UU03a3_1 c _UU03a3_2 _UU03b6_)
      | Coq_pattern_match (_UU03c3_, s, pat, rhs) ->
        Coq_pattern_match (_UU03c3_,
          (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm _UU03c3_) _UU03a3_1
            s _UU03a3_2 _UU03b6_),
          pat, (fun pc ->
          sub_assertion
            (Coq_ctx.cat _UU03a3_1
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (rhs pc)
            (Coq_ctx.cat _UU03a3_2
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (RiscvPmpBase.sub_up _UU03a3_1 _UU03a3_2 _UU03b6_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))))
      | Coq_sep (a1, a2) ->
        Coq_sep ((sub_assertion _UU03a3_1 a1 _UU03a3_2 _UU03b6_),
          (sub_assertion _UU03a3_1 a2 _UU03a3_2 _UU03b6_))
      | Coq_or (a1, a2) ->
        Coq_sep ((sub_assertion _UU03a3_1 a1 _UU03a3_2 _UU03b6_),
          (sub_assertion _UU03a3_1 a2 _UU03a3_2 _UU03b6_))
      | Coq_exist (_UU03c2_, _UU03c4_, a0) ->
        Coq_exist (_UU03c2_, _UU03c4_,
          (sub_assertion (Coq_ctx.Coq_snoc (_UU03a3_1, { Binding.name =
            _UU03c2_; Binding.coq_type = _UU03c4_ })) a0 (Coq_ctx.Coq_snoc
            (_UU03a3_2, { Binding.name = _UU03c2_; Binding.coq_type =
            _UU03c4_ }))
            (RiscvPmpBase.sub_up1 _UU03a3_1 _UU03a3_2 _UU03b6_
              { Binding.name = _UU03c2_; Binding.coq_type = _UU03c4_ })))
      | Coq_debug -> Coq_debug

    (** val coq_OccursCheckAssertion :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Assertion ->
        coq_Assertion option **)

    let rec coq_OccursCheckAssertion _UU03a3_ b bIn = function
    | Coq_formula fml ->
      Coq_option.map (fun x -> Coq_formula x)
        (RiscvPmpBase.occurs_check coq_OccursCheckFormula _UU03a3_ b bIn fml)
    | Coq_chunk c ->
      Coq_option.map (fun x -> Coq_chunk x)
        (RiscvPmpBase.occurs_check coq_OccursCheckChunk _UU03a3_ b bIn c)
    | Coq_chunk_angelic c ->
      Coq_option.map (fun x -> Coq_chunk_angelic x)
        (RiscvPmpBase.occurs_check coq_OccursCheckChunk _UU03a3_ b bIn c)
    | Coq_pattern_match (_UU03c3_, s, _, _) ->
      Coq_option.bind
        (RiscvPmpBase.occurs_check (RiscvPmpBase.occurs_check_term _UU03c3_)
          _UU03a3_ b bIn s)
        (fun _ -> None)
    | Coq_sep (a1, a2) ->
      Coq_option.bind (coq_OccursCheckAssertion _UU03a3_ b bIn a1)
        (fun a1' ->
        Coq_option.bind (coq_OccursCheckAssertion _UU03a3_ b bIn a2)
          (fun a2' -> Some (Coq_sep (a1', a2'))))
    | Coq_or (a1, a2) ->
      Coq_option.bind (coq_OccursCheckAssertion _UU03a3_ b bIn a1)
        (fun a1' ->
        Coq_option.bind (coq_OccursCheckAssertion _UU03a3_ b bIn a2)
          (fun a2' -> Some (Coq_or (a1', a2'))))
    | Coq_exist (_UU03c2_, _UU03c4_, a) ->
      option_map (fun x -> Coq_exist (_UU03c2_, _UU03c4_, x))
        (coq_OccursCheckAssertion (Coq_ctx.Coq_snoc (_UU03a3_,
          { Binding.name = _UU03c2_; Binding.coq_type = _UU03c4_ })) b
          (Coq_ctx.in_succ b _UU03a3_ { Binding.name = _UU03c2_;
            Binding.coq_type = _UU03c4_ } bIn)
          a)
    | Coq_debug -> Some Coq_debug

    (** val is_pure :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Assertion -> bool **)

    let rec is_pure _UU03a3_ = function
    | Coq_formula _ -> Coq_true
    | Coq_pattern_match (_UU03c3_, _, pat, rhs) ->
      forallb (fun pc ->
        is_pure
          (Coq_ctx.cat _UU03a3_
            (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
          (rhs pc))
        (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat)
    | Coq_sep (a1, a2) ->
      (match is_pure _UU03a3_ a1 with
       | Coq_true -> is_pure _UU03a3_ a2
       | Coq_false -> Coq_false)
    | Coq_or (a1, a2) ->
      (match is_pure _UU03a3_ a1 with
       | Coq_true -> is_pure _UU03a3_ a2
       | Coq_false -> Coq_false)
    | Coq_exist (_UU03c2_, _UU03c4_, a0) ->
      is_pure (Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name = _UU03c2_;
        Binding.coq_type = _UU03c4_ })) a0
    | Coq_debug -> Coq_true
    | _ -> Coq_false

    (** val interpret :
        bi -> coq_PredicateDef -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> ((coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env
        -> __ **)

    let rec interpret pROP pI _UU03a3_ a _UU03b9_ =
      match a with
      | Coq_formula _ -> pROP.bi_and (pROP.bi_pure __) pROP.bi_emp
      | Coq_chunk c -> interpret_chunk pROP pI _UU03a3_ c _UU03b9_
      | Coq_chunk_angelic c -> interpret_chunk pROP pI _UU03a3_ c _UU03b9_
      | Coq_pattern_match (_UU03c3_, s, pat, rhs) ->
        let v =
          RiscvPmpBase.inst (RiscvPmpBase.inst_term _UU03c3_) _UU03a3_ s
            _UU03b9_
        in
        let Coq_existT (pc, _UU03b4_pc) =
          RiscvPmpBase.pattern_match_val _UU03c3_ pat v
        in
        interpret pROP pI
          (Coq_ctx.cat _UU03a3_
            (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
          (rhs pc)
          (Coq_env.cat _UU03a3_
            (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) _UU03b9_
            _UU03b4_pc)
      | Coq_sep (a1, a2) ->
        pROP.bi_sep (interpret pROP pI _UU03a3_ a1 _UU03b9_)
          (interpret pROP pI _UU03a3_ a2 _UU03b9_)
      | Coq_or (a1, a2) ->
        pROP.bi_or (interpret pROP pI _UU03a3_ a1 _UU03b9_)
          (interpret pROP pI _UU03a3_ a2 _UU03b9_)
      | Coq_exist (_UU03c2_, _UU03c4_, a0) ->
        pROP.bi_exist __ (fun v ->
          interpret pROP pI (Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name =
            _UU03c2_; Binding.coq_type = _UU03c4_ })) a0 (Coq_env.Coq_snoc
            (_UU03a3_, _UU03b9_, { Binding.name = _UU03c2_;
            Binding.coq_type = _UU03c4_ }, v)))
      | Coq_debug -> pROP.bi_emp

    module Coq_notations =
     struct
     end
   end

  type coq_SepContract = { sep_contract_logic_variables : (coq_LVar,
                                                          Coq_ty.coq_Ty)
                                                          Binding.coq_Binding
                                                          Coq_ctx.coq_Ctx;
                           sep_contract_localstore : RiscvPmpBase.coq_SStore;
                           sep_contract_precondition : Coq_asn.coq_Assertion;
                           sep_contract_result : coq_LVar;
                           sep_contract_postcondition : Coq_asn.coq_Assertion }

  (** val sep_contract_logic_variables :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContract -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx **)

  let sep_contract_logic_variables _ _ s =
    s.sep_contract_logic_variables

  (** val sep_contract_localstore :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContract -> RiscvPmpBase.coq_SStore **)

  let sep_contract_localstore _ _ s =
    s.sep_contract_localstore

  (** val sep_contract_precondition :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContract -> Coq_asn.coq_Assertion **)

  let sep_contract_precondition _ _ s =
    s.sep_contract_precondition

  (** val sep_contract_result :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContract -> coq_LVar **)

  let sep_contract_result _ _ s =
    s.sep_contract_result

  (** val sep_contract_postcondition :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContract -> Coq_asn.coq_Assertion **)

  let sep_contract_postcondition _ _ s =
    s.sep_contract_postcondition

  type coq_Lemma = { lemma_logic_variables : (coq_LVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx;
                     lemma_patterns : RiscvPmpBase.coq_SStore;
                     lemma_precondition : Coq_asn.coq_Assertion;
                     lemma_postcondition : Coq_asn.coq_Assertion }

  (** val lemma_logic_variables :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Lemma -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let lemma_logic_variables _ l =
    l.lemma_logic_variables

  (** val lemma_patterns :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Lemma -> RiscvPmpBase.coq_SStore **)

  let lemma_patterns _ l =
    l.lemma_patterns

  (** val lemma_precondition :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Lemma -> Coq_asn.coq_Assertion **)

  let lemma_precondition _ l =
    l.lemma_precondition

  (** val lemma_postcondition :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Lemma -> Coq_asn.coq_Assertion **)

  let lemma_postcondition _ l =
    l.lemma_postcondition

  (** val lint_assertion :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      Coq_asn.coq_Assertion -> bool **)

  let rec lint_assertion _UU03a3_ b bIn = function
  | Coq_asn.Coq_formula fml ->
    Coq_option.isNone
      (RiscvPmpBase.occurs_check coq_OccursCheckFormula _UU03a3_ b bIn fml)
  | Coq_asn.Coq_chunk c ->
    Coq_option.isNone
      (Coq_option.map (fun x -> Coq_asn.Coq_chunk x)
        (RiscvPmpBase.occurs_check coq_OccursCheckChunk _UU03a3_ b bIn c))
  | Coq_asn.Coq_chunk_angelic c ->
    Coq_option.isNone
      (Coq_option.map (fun x -> Coq_asn.Coq_chunk_angelic x)
        (RiscvPmpBase.occurs_check coq_OccursCheckChunk _UU03a3_ b bIn c))
  | Coq_asn.Coq_pattern_match (_UU03c3_, s, pat, rhs) ->
    (match Coq_option.isNone
             (RiscvPmpBase.occurs_check
               (RiscvPmpBase.occurs_check_term _UU03c3_) _UU03a3_ b bIn s) with
     | Coq_true -> Coq_true
     | Coq_false ->
       existsb (fun pc ->
         lint_assertion
           (Coq_ctx.cat _UU03a3_
             (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
           b
           (Coq_ctx.in_cat_left b _UU03a3_
             (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc) bIn)
           (rhs pc))
         (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat))
  | Coq_asn.Coq_sep (a1, a2) ->
    (match lint_assertion _UU03a3_ b bIn a1 with
     | Coq_true -> Coq_true
     | Coq_false -> lint_assertion _UU03a3_ b bIn a2)
  | Coq_asn.Coq_or (a1, a2) ->
    (match lint_assertion _UU03a3_ b bIn a1 with
     | Coq_true -> Coq_true
     | Coq_false -> lint_assertion _UU03a3_ b bIn a2)
  | Coq_asn.Coq_exist (_UU03c2_, _UU03c4_, a) ->
    lint_assertion (Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name = _UU03c2_;
      Binding.coq_type = _UU03c4_ })) b
      (Coq_ctx.in_succ b _UU03a3_ { Binding.name = _UU03c2_;
        Binding.coq_type = _UU03c4_ } bIn)
      a
  | Coq_asn.Coq_debug -> Coq_false

  (** val lint_contract :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContract -> bool **)

  let lint_contract _UU0394_ _ c =
    let { sep_contract_logic_variables = _UU03a3_; sep_contract_localstore =
      _UU03b4_; sep_contract_precondition = pre; sep_contract_result = _;
      sep_contract_postcondition = _ } = c
    in
    Coq_ctx.forallb _UU03a3_ (fun b bIn ->
      match Coq_option.isNone
              (RiscvPmpBase.occurs_check
                (RiscvPmpBase.occurs_check_env (fun i ->
                  RiscvPmpBase.occurs_check_term i.Binding.coq_type) _UU0394_)
                _UU03a3_ b bIn _UU03b4_) with
      | Coq_true -> Coq_true
      | Coq_false -> lint_assertion _UU03a3_ b bIn pre)

  (** val lint_lemma :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Lemma -> bool **)

  let lint_lemma _UU0394_ l =
    let { lemma_logic_variables = _UU03a3_; lemma_patterns = _UU03b4_;
      lemma_precondition = pre; lemma_postcondition = _ } = l
    in
    Coq_ctx.forallb _UU03a3_ (fun b bIn ->
      match Coq_option.isNone
              (RiscvPmpBase.occurs_check
                (RiscvPmpBase.occurs_check_env (fun i ->
                  RiscvPmpBase.occurs_check_term i.Binding.coq_type) _UU0394_)
                _UU03a3_ b bIn _UU03b4_) with
      | Coq_true -> Coq_true
      | Coq_false -> lint_assertion _UU03a3_ b bIn pre)

  (** val sep_contract_pun_logvars :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx **)

  let sep_contract_pun_logvars _UU0394_ _UU03a3_ =
    Coq_ctx.cat
      (Coq_ctx.map (fun pat ->
        let x = pat.Binding.name in
        let _UU03c3_ = pat.Binding.coq_type in
        { Binding.name = (RiscvPmpBase.varkit.coq_PVartoLVar x);
        Binding.coq_type = _UU03c3_ }) _UU0394_)
      _UU03a3_

  type coq_SepContractPun = { sep_contract_pun_logic_variables : (coq_LVar,
                                                                 Coq_ty.coq_Ty)
                                                                 Binding.coq_Binding
                                                                 Coq_ctx.coq_Ctx;
                              sep_contract_pun_precondition : Coq_asn.coq_Assertion;
                              sep_contract_pun_result : coq_LVar;
                              sep_contract_pun_postcondition : Coq_asn.coq_Assertion }

  (** val sep_contract_pun_logic_variables :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContractPun -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx **)

  let sep_contract_pun_logic_variables _ _ s =
    s.sep_contract_pun_logic_variables

  (** val sep_contract_pun_precondition :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContractPun -> Coq_asn.coq_Assertion **)

  let sep_contract_pun_precondition _ _ s =
    s.sep_contract_pun_precondition

  (** val sep_contract_pun_result :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContractPun -> coq_LVar **)

  let sep_contract_pun_result _ _ s =
    s.sep_contract_pun_result

  (** val sep_contract_pun_postcondition :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContractPun -> Coq_asn.coq_Assertion **)

  let sep_contract_pun_postcondition _ _ s =
    s.sep_contract_pun_postcondition

  (** val sep_contract_pun_to_sep_contract :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContractPun -> coq_SepContract **)

  let sep_contract_pun_to_sep_contract _UU0394_ _ c =
    let { sep_contract_pun_logic_variables = _UU03a3_;
      sep_contract_pun_precondition = req; sep_contract_pun_result = result;
      sep_contract_pun_postcondition = ens } = c
    in
    { sep_contract_logic_variables =
    (sep_contract_pun_logvars _UU0394_ _UU03a3_); sep_contract_localstore =
    (Coq_env.tabulate _UU0394_ (fun pat ->
      let x = pat.Binding.name in
      let _UU03c3_ = pat.Binding.coq_type in
      (fun xIn -> RiscvPmpBase.Coq_term_var
      ((RiscvPmpBase.varkit.coq_PVartoLVar x), _UU03c3_,
      (Coq_ctx.in_cat_left { Binding.name =
        (RiscvPmpBase.varkit.coq_PVartoLVar x); Binding.coq_type = _UU03c3_ }
        (Coq_ctx.map (fun pat0 -> { Binding.name =
          (RiscvPmpBase.varkit.coq_PVartoLVar pat0.Binding.name);
          Binding.coq_type = pat0.Binding.coq_type }) _UU0394_)
        _UU03a3_
        (Coq_ctx.in_map (fun pat0 ->
          let y = pat0.Binding.name in
          let _UU03c4_ = pat0.Binding.coq_type in
          { Binding.name = (RiscvPmpBase.varkit.coq_PVartoLVar y);
          Binding.coq_type = _UU03c4_ }) { Binding.name = x;
          Binding.coq_type = _UU03c3_ } _UU0394_ xIn))))));
    sep_contract_precondition = req; sep_contract_result = result;
    sep_contract_postcondition = ens }

  (** val inst_contract_localstore :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContract -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> (coq_PVar,
      Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv **)

  let inst_contract_localstore _UU0394_ _ c _UU03b9_ =
    RiscvPmpBase.inst (RiscvPmpBase.inst_store _UU0394_)
      c.sep_contract_logic_variables c.sep_contract_localstore _UU03b9_

  (** val interpret_contract_precondition :
      bi -> coq_PredicateDef -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_SepContract -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
      __ **)

  let interpret_contract_precondition pROP pI _ _ c _UU03b9_ =
    Coq_asn.interpret pROP pI c.sep_contract_logic_variables
      c.sep_contract_precondition _UU03b9_

  (** val interpret_contract_postcondition :
      bi -> coq_PredicateDef -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_SepContract -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
      Coq_ty.coq_Val -> __ **)

  let interpret_contract_postcondition pROP pI _ _UU03c4_ c _UU03b9_ result =
    Coq_asn.interpret pROP pI (Coq_ctx.Coq_snoc
      (c.sep_contract_logic_variables, { Binding.name =
      c.sep_contract_result; Binding.coq_type = _UU03c4_ }))
      c.sep_contract_postcondition (Coq_env.Coq_snoc
      (c.sep_contract_logic_variables, _UU03b9_, { Binding.name =
      c.sep_contract_result; Binding.coq_type = _UU03c4_ }, result))

  module GenericSolver =
   struct
    (** val simplify_bool :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let rec simplify_bool _UU03a3_ t =
      RiscvPmpBase.coq_Term_bool_case _UU03a3_ (fun _UU03c2_ lIn ->
        DList.singleton _UU03a3_ (Coq_formula_bool (RiscvPmpBase.Coq_term_var
          (_UU03c2_, Coq_ty.Coq_bool, lIn))))
        (fun b ->
        match Obj.magic b with
        | Coq_true -> DList.empty _UU03a3_
        | Coq_false -> DList.error _UU03a3_) (fun t1 t2 ->
        DList.cat _UU03a3_ (simplify_bool _UU03a3_ t1)
          (simplify_bool _UU03a3_ t2))
        (fun t1 t2 ->
        DList.singleton _UU03a3_ (Coq_formula_bool
          (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool,
          Coq_ty.Coq_bool, Coq_bop.Coq_or, t1, t2))))
        (fun _UU03c3_ op t1 t2 ->
        DList.singleton _UU03a3_ (Coq_formula_relop (_UU03c3_, op, t1, t2)))
        (fun t1 -> simplify_bool_neg _UU03a3_ t1) t

    (** val simplify_bool_neg :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    and simplify_bool_neg _UU03a3_ t =
      RiscvPmpBase.coq_Term_bool_case _UU03a3_ (fun _UU03c2_ lIn ->
        DList.singleton _UU03a3_ (Coq_formula_bool
          (RiscvPmpBase.Coq_term_unop (Coq_ty.Coq_bool, Coq_ty.Coq_bool,
          Coq_uop.Coq_not, (RiscvPmpBase.Coq_term_var (_UU03c2_,
          Coq_ty.Coq_bool, lIn))))))
        (fun b ->
        match Obj.magic b with
        | Coq_true -> DList.error _UU03a3_
        | Coq_false -> DList.empty _UU03a3_) (fun t1 t2 ->
        DList.singleton _UU03a3_ (Coq_formula_bool
          (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool,
          Coq_ty.Coq_bool, Coq_bop.Coq_or, (RiscvPmpBase.Coq_term_unop
          (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_uop.Coq_not, t1)),
          (RiscvPmpBase.Coq_term_unop (Coq_ty.Coq_bool, Coq_ty.Coq_bool,
          Coq_uop.Coq_not, t2))))))
        (fun t1 t2 ->
        DList.cat _UU03a3_ (simplify_bool_neg _UU03a3_ t1)
          (simplify_bool_neg _UU03a3_ t2))
        (fun _UU03c3_ op t1 t2 ->
        DList.singleton _UU03a3_
          (formula_relop_neg _UU03a3_ _UU03c3_ op t1 t2))
        (fun t1 -> simplify_bool _UU03a3_ t1) t

    (** val simplify_eqb :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList **)

    let simplify_eqb _UU03a3_ _UU03c3_ t1 t2 =
      let num = fun t ->
        match t with
        | RiscvPmpBase.Coq_term_var (_, _, _) -> Coq_xH
        | RiscvPmpBase.Coq_term_val (_, _) -> Coq_xO Coq_xH
        | RiscvPmpBase.Coq_term_binop (_, _, _, _, _, _) -> Coq_xI Coq_xH
        | RiscvPmpBase.Coq_term_unop (_, _, _, _) -> Coq_xO (Coq_xO Coq_xH)
        | RiscvPmpBase.Coq_term_tuple (_, _) -> Coq_xI (Coq_xO Coq_xH)
        | RiscvPmpBase.Coq_term_union (_, _, _) -> Coq_xO (Coq_xI Coq_xH)
        | RiscvPmpBase.Coq_term_record (_, _) -> Coq_xI (Coq_xI Coq_xH)
      in
      (match RiscvPmpBase.coq_Term_eqb _UU03a3_ _UU03c3_ t1 t2 with
       | Coq_true -> DList.empty _UU03a3_
       | Coq_false ->
         (match Pos.leb (num t1) (num t2) with
          | Coq_true ->
            DList.singleton _UU03a3_ (Coq_formula_relop (_UU03c3_,
              (Coq_bop.Coq_eq _UU03c3_), t1, t2))
          | Coq_false ->
            DList.singleton _UU03a3_ (Coq_formula_relop (_UU03c3_,
              (Coq_bop.Coq_eq _UU03c3_), t2, t1))))

    (** val simplify_eq_binop_default_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
        -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val
        -> DList.coq_DList **)

    let simplify_eq_binop_default_val _UU03a3_ _UU03c3_1 _UU03c3_2 _UU03c3_ op t1 t2 v =
      DList.singleton _UU03a3_ (Coq_formula_relop (_UU03c3_, (Coq_bop.Coq_eq
        _UU03c3_), (RiscvPmpBase.Coq_term_val (_UU03c3_, v)),
        (RiscvPmpBase.Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_, op, t1,
        t2))))

    (** val simplify_eq_unop_default_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
        RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList **)

    let simplify_eq_unop_default_val _UU03a3_ _UU03c3_1 _UU03c3_2 op t v =
      DList.singleton _UU03a3_ (Coq_formula_relop (_UU03c3_2, (Coq_bop.Coq_eq
        _UU03c3_2), (RiscvPmpBase.Coq_term_val (_UU03c3_2, v)),
        (RiscvPmpBase.Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t))))

    (** val simplify_eq_binop_and_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList **)

    let simplify_eq_binop_and_val _UU03a3_ t1 t2 v =
      match Obj.magic v with
      | Coq_true ->
        simplify_bool _UU03a3_ (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_bool,
          Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_bop.Coq_and, t1, t2))
      | Coq_false ->
        simplify_bool_neg _UU03a3_ (RiscvPmpBase.Coq_term_binop
          (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
          Coq_bop.Coq_and, t1, t2))

    (** val simplify_eq_binop_or_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList **)

    let simplify_eq_binop_or_val _UU03a3_ t1 t2 v =
      match Obj.magic v with
      | Coq_true ->
        simplify_bool _UU03a3_ (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_bool,
          Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_bop.Coq_or, t1, t2))
      | Coq_false ->
        simplify_bool_neg _UU03a3_ (RiscvPmpBase.Coq_term_binop
          (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_bop.Coq_or,
          t1, t2))

    (** val simplify_eq_unop_not_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList **)

    let simplify_eq_unop_not_val _UU03a3_ t v =
      match Obj.magic v with
      | Coq_true -> simplify_bool_neg _UU03a3_ t
      | Coq_false -> simplify_bool _UU03a3_ t

    (** val simplify_eq_binop_relop_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList **)

    let simplify_eq_binop_relop_val _UU03a3_ _UU03c3_ op t1 t2 v =
      match Obj.magic v with
      | Coq_true ->
        DList.singleton _UU03a3_ (Coq_formula_relop (_UU03c3_, op, t1, t2))
      | Coq_false ->
        DList.singleton _UU03a3_
          (formula_relop_neg _UU03a3_ _UU03c3_ op t1 t2)

    (** val simplify_eq_binop_pair_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList **)

    let simplify_eq_binop_pair_val _UU03a3_ simplify_eq_val0 _UU03c3_1 _UU03c3_2 t1 t2 v =
      let Coq_pair (v1, v2) = Obj.magic v in
      DList.cat _UU03a3_ (simplify_eq_val0 _UU03c3_1 t1 v1)
        (simplify_eq_val0 _UU03c3_2 t2 v2)

    (** val simplify_eq_binop_cons_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList **)

    let simplify_eq_binop_cons_val _UU03a3_ simplify_eq_val0 _UU03c3_ t1 t2 v =
      match Obj.magic v with
      | Coq_nil -> DList.error _UU03a3_
      | Coq_cons (vh, vl) ->
        DList.cat _UU03a3_ (simplify_eq_val0 _UU03c3_ t1 vh)
          (Obj.magic simplify_eq_val0 (Coq_ty.Coq_list _UU03c3_) t2 vl)

    (** val simplify_eq_binop_bvapp_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> nat -> nat -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList **)

    let simplify_eq_binop_bvapp_val _UU03a3_ simplify_eq_val0 m n t1 t2 v =
      let Coq_bv.Coq_isapp (v1, v2) = Coq_bv.appView m n (Obj.magic v) in
      DList.cat _UU03a3_
        (Obj.magic simplify_eq_val0 (Coq_ty.Coq_bvec m) t1 v1)
        (Obj.magic simplify_eq_val0 (Coq_ty.Coq_bvec n) t2 v2)

    (** val simplify_eq_binop_bvcons_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList **)

    let simplify_eq_binop_bvcons_val _UU03a3_ simplify_eq_val0 m t1 t2 v =
      let Coq_bv.Coq_cvcons (v1, v2) = Obj.magic Coq_bv.view (S m) v in
      DList.cat _UU03a3_ (Obj.magic simplify_eq_val0 Coq_ty.Coq_bool t1 v1)
        (Obj.magic simplify_eq_val0 (Coq_ty.Coq_bvec m) t2 v2)

    (** val simplify_eq_binop_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
        -> Coq_bop.coq_BinOp -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList **)

    let simplify_eq_binop_val _UU03a3_ simplify_eq_val0 _ _ _ = function
    | Coq_bop.Coq_and -> simplify_eq_binop_and_val _UU03a3_
    | Coq_bop.Coq_or -> simplify_eq_binop_or_val _UU03a3_
    | Coq_bop.Coq_pair (_UU03c3_0, _UU03c3_3) ->
      simplify_eq_binop_pair_val _UU03a3_ simplify_eq_val0 _UU03c3_0 _UU03c3_3
    | Coq_bop.Coq_cons _UU03c3_0 ->
      simplify_eq_binop_cons_val _UU03a3_ simplify_eq_val0 _UU03c3_0
    | Coq_bop.Coq_append _UU03c3_0 ->
      simplify_eq_binop_default_val _UU03a3_ (Coq_ty.Coq_list _UU03c3_0)
        (Coq_ty.Coq_list _UU03c3_0) (Coq_ty.Coq_list _UU03c3_0)
        (Coq_bop.Coq_append _UU03c3_0)
    | Coq_bop.Coq_shiftr (m, n) ->
      simplify_eq_binop_default_val _UU03a3_ (Coq_ty.Coq_bvec m)
        (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec m) (Coq_bop.Coq_shiftr (m, n))
    | Coq_bop.Coq_shiftl (m, n) ->
      simplify_eq_binop_default_val _UU03a3_ (Coq_ty.Coq_bvec m)
        (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec m) (Coq_bop.Coq_shiftl (m, n))
    | Coq_bop.Coq_bvadd n ->
      simplify_eq_binop_default_val _UU03a3_ (Coq_ty.Coq_bvec n)
        (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvadd n)
    | Coq_bop.Coq_bvsub n ->
      simplify_eq_binop_default_val _UU03a3_ (Coq_ty.Coq_bvec n)
        (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvsub n)
    | Coq_bop.Coq_bvmul n ->
      simplify_eq_binop_default_val _UU03a3_ (Coq_ty.Coq_bvec n)
        (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvmul n)
    | Coq_bop.Coq_bvand n ->
      simplify_eq_binop_default_val _UU03a3_ (Coq_ty.Coq_bvec n)
        (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvand n)
    | Coq_bop.Coq_bvor n ->
      simplify_eq_binop_default_val _UU03a3_ (Coq_ty.Coq_bvec n)
        (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvor n)
    | Coq_bop.Coq_bvxor n ->
      simplify_eq_binop_default_val _UU03a3_ (Coq_ty.Coq_bvec n)
        (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvxor n)
    | Coq_bop.Coq_bvapp (m, n) ->
      simplify_eq_binop_bvapp_val _UU03a3_ simplify_eq_val0 m n
    | Coq_bop.Coq_bvcons m ->
      simplify_eq_binop_bvcons_val _UU03a3_ simplify_eq_val0 m
    | Coq_bop.Coq_update_vector_subrange (n, s, l) ->
      simplify_eq_binop_default_val _UU03a3_ (Coq_ty.Coq_bvec n)
        (Coq_ty.Coq_bvec l) (Coq_ty.Coq_bvec n)
        (Coq_bop.Coq_update_vector_subrange (n, s, l))
    | Coq_bop.Coq_relop (_UU03c3_0, op0) ->
      simplify_eq_binop_relop_val _UU03a3_ _UU03c3_0 op0
    | x ->
      simplify_eq_binop_default_val _UU03a3_ Coq_ty.Coq_int Coq_ty.Coq_int
        Coq_ty.Coq_int x

    (** val simplify_eq_unop_inl_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
        RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList **)

    let simplify_eq_unop_inl_val _UU03a3_ simplify_eq_val0 _UU03c3_1 _ t v =
      match Obj.magic v with
      | Coq_inl vl -> simplify_eq_val0 _UU03c3_1 t vl
      | Coq_inr _ -> DList.error _UU03a3_

    (** val simplify_eq_unop_inr_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
        RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList **)

    let simplify_eq_unop_inr_val _UU03a3_ simplify_eq_val0 _ _UU03c3_2 t v =
      match Obj.magic v with
      | Coq_inl _ -> DList.error _UU03a3_
      | Coq_inr vr -> simplify_eq_val0 _UU03c3_2 t vr

    (** val simplify_eq_unop_neg_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList **)

    let simplify_eq_unop_neg_val _ simplify_eq_val0 t v =
      Obj.magic simplify_eq_val0 Coq_ty.Coq_int t (Z.opp (Obj.magic v))

    (** val simplify_eq_unop_signed_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList **)

    let simplify_eq_unop_signed_val _UU03a3_ simplify_eq_val0 n t v =
      match match Z.leb (Z.opp (Z.pow (Zpos (Coq_xO Coq_xH)) (Z.of_nat n)))
                    (Z.mul (Zpos (Coq_xO Coq_xH)) (Obj.magic v)) with
            | Coq_true ->
              Z.ltb (Z.mul (Zpos (Coq_xO Coq_xH)) (Obj.magic v))
                (Z.pow (Zpos (Coq_xO Coq_xH)) (Z.of_nat n))
            | Coq_false -> Coq_false with
      | Coq_true ->
        Obj.magic simplify_eq_val0 (Coq_ty.Coq_bvec n) t
          (Coq_bv.of_Z n (Obj.magic v))
      | Coq_false -> DList.error _UU03a3_

    (** val simplify_eq_unop_unsigned_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList **)

    let simplify_eq_unop_unsigned_val _UU03a3_ simplify_eq_val0 n t v =
      match match Z.leb Z0 (Obj.magic v) with
            | Coq_true ->
              Z.ltb (Obj.magic v) (Z.pow (Zpos (Coq_xO Coq_xH)) (Z.of_nat n))
            | Coq_false -> Coq_false with
      | Coq_true ->
        Obj.magic simplify_eq_val0 (Coq_ty.Coq_bvec n) t
          (Coq_bv.of_Z n (Obj.magic v))
      | Coq_false -> DList.error _UU03a3_

    (** val simplify_eq_unop_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
        Coq_uop.coq_UnOp -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList **)

    let simplify_eq_unop_val _UU03a3_ simplify_eq_val0 _ _ = function
    | Coq_uop.Coq_inl (_UU03c3_0, _UU03c3_3) ->
      simplify_eq_unop_inl_val _UU03a3_ simplify_eq_val0 _UU03c3_0 _UU03c3_3
    | Coq_uop.Coq_inr (_UU03c3_0, _UU03c3_3) ->
      simplify_eq_unop_inr_val _UU03a3_ simplify_eq_val0 _UU03c3_0 _UU03c3_3
    | Coq_uop.Coq_neg -> simplify_eq_unop_neg_val _UU03a3_ simplify_eq_val0
    | Coq_uop.Coq_not -> simplify_eq_unop_not_val _UU03a3_
    | Coq_uop.Coq_rev _UU03c3_ ->
      simplify_eq_unop_default_val _UU03a3_ (Coq_ty.Coq_list _UU03c3_)
        (Coq_ty.Coq_list _UU03c3_) (Coq_uop.Coq_rev _UU03c3_)
    | Coq_uop.Coq_sext (m, n) ->
      simplify_eq_unop_default_val _UU03a3_ (Coq_ty.Coq_bvec m)
        (Coq_ty.Coq_bvec n) (Coq_uop.Coq_sext (m, n))
    | Coq_uop.Coq_zext (m, n) ->
      simplify_eq_unop_default_val _UU03a3_ (Coq_ty.Coq_bvec m)
        (Coq_ty.Coq_bvec n) (Coq_uop.Coq_zext (m, n))
    | Coq_uop.Coq_get_slice_int n ->
      simplify_eq_unop_default_val _UU03a3_ Coq_ty.Coq_int (Coq_ty.Coq_bvec
        n) (Coq_uop.Coq_get_slice_int n)
    | Coq_uop.Coq_signed n ->
      simplify_eq_unop_signed_val _UU03a3_ simplify_eq_val0 n
    | Coq_uop.Coq_unsigned n ->
      simplify_eq_unop_unsigned_val _UU03a3_ simplify_eq_val0 n
    | Coq_uop.Coq_truncate (n, m) ->
      simplify_eq_unop_default_val _UU03a3_ (Coq_ty.Coq_bvec n)
        (Coq_ty.Coq_bvec m) (Coq_uop.Coq_truncate (n, m))
    | Coq_uop.Coq_vector_subrange (n, s, l) ->
      simplify_eq_unop_default_val _UU03a3_ (Coq_ty.Coq_bvec n)
        (Coq_ty.Coq_bvec l) (Coq_uop.Coq_vector_subrange (n, s, l))
    | Coq_uop.Coq_bvnot n ->
      simplify_eq_unop_default_val _UU03a3_ (Coq_ty.Coq_bvec n)
        (Coq_ty.Coq_bvec n) (Coq_uop.Coq_bvnot n)
    | Coq_uop.Coq_bvdrop (m, n) ->
      simplify_eq_unop_default_val _UU03a3_ (Coq_ty.Coq_bvec (add m n))
        (Coq_ty.Coq_bvec n) (Coq_uop.Coq_bvdrop (m, n))
    | Coq_uop.Coq_bvtake (m, n) ->
      simplify_eq_unop_default_val _UU03a3_ (Coq_ty.Coq_bvec (add m n))
        (Coq_ty.Coq_bvec m) (Coq_uop.Coq_bvtake (m, n))
    | Coq_uop.Coq_negate n ->
      simplify_eq_unop_default_val _UU03a3_ (Coq_ty.Coq_bvec n)
        (Coq_ty.Coq_bvec n) (Coq_uop.Coq_negate n)

    (** val simplify_eq_tuple_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty,
        RiscvPmpBase.coq_Term) Coq_env.coq_Env -> Coq_ty.coq_Val ->
        DList.coq_DList **)

    let rec simplify_eq_tuple_val _UU03a3_ simplify_eq_val0 _ ts vs =
      match ts with
      | Coq_env.Coq_nil -> DList.empty _UU03a3_
      | Coq_env.Coq_snoc (_UU0393_, e, b, db) ->
        let Coq_pair (v_UU03c4_s, v_UU03c4_) = Obj.magic vs in
        DList.cat _UU03a3_
          (simplify_eq_tuple_val _UU03a3_ simplify_eq_val0 _UU0393_ e
            v_UU03c4_s)
          (simplify_eq_val0 b db v_UU03c4_)

    (** val simplify_eq_union_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> Coq_ty.unioni -> Coq_ty.unionk ->
        RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList **)

    let simplify_eq_union_val _UU03a3_ simplify_eq_val0 u k1 t1 v2 =
      let Coq_existT (k2, v3) =
        RiscvPmpBase.typedefkit.Coq_ty.unionv_unfold u v2
      in
      (match eq_dec (RiscvPmpBase.typedefkit.Coq_ty.unionk_eqdec u) k1 k2 with
       | Coq_left ->
         simplify_eq_val0 (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty u k1) t1
           v3
       | Coq_right -> DList.error _UU03a3_)

    (** val simplify_eq_record_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList) -> Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty,
        RiscvPmpBase.coq_Term) coq_NamedEnv -> Coq_ty.coq_Val ->
        DList.coq_DList **)

    let simplify_eq_record_val _UU03a3_ simplify_eq_val0 r ts v =
      let rec f _ e x =
        match e with
        | Coq_env.Coq_nil -> DList.empty _UU03a3_
        | Coq_env.Coq_snoc (_UU0393_, e0, b, db) ->
          let Coq_env.Coq_isSnoc (vs_UU0394_, vb) =
            Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (_UU0393_, b)) x
          in
          DList.cat _UU03a3_ (f _UU0393_ e0 vs_UU0394_)
            (simplify_eq_val0 b.Binding.coq_type db vb)
      in f (RiscvPmpBase.typedefkit.Coq_ty.recordf_ty r) ts
           (RiscvPmpBase.typedefkit.Coq_ty.recordv_unfold r v)

    (** val simplify_eq_val :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
        DList.coq_DList **)

    let rec simplify_eq_val _UU03a3_ _UU03c3_ t v =
      match t with
      | RiscvPmpBase.Coq_term_var (_, _, _) ->
        DList.singleton _UU03a3_ (Coq_formula_relop (_UU03c3_,
          (Coq_bop.Coq_eq _UU03c3_), t, (RiscvPmpBase.Coq_term_val (_UU03c3_,
          v))))
      | RiscvPmpBase.Coq_term_val (_UU03c3_0, v0) ->
        (match eq_dec
                 (Coq_ty.coq_Val_eq_dec RiscvPmpBase.typedeclkit
                   RiscvPmpBase.typedenotekit RiscvPmpBase.typedefkit
                   _UU03c3_0)
                 v0 v with
         | Coq_left -> DList.empty _UU03a3_
         | Coq_right -> DList.error _UU03a3_)
      | RiscvPmpBase.Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1,
                                     t2) ->
        simplify_eq_binop_val _UU03a3_ (simplify_eq_val _UU03a3_) _UU03c3_3
          _UU03c3_1 _UU03c3_2 op t1 t2 v
      | RiscvPmpBase.Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t0) ->
        simplify_eq_unop_val _UU03a3_ (simplify_eq_val _UU03a3_) _UU03c3_1
          _UU03c3_2 op t0 v
      | RiscvPmpBase.Coq_term_tuple (_UU03c3_s, ts) ->
        simplify_eq_tuple_val _UU03a3_ (simplify_eq_val _UU03a3_) _UU03c3_s
          ts v
      | RiscvPmpBase.Coq_term_union (u, k, t0) ->
        simplify_eq_union_val _UU03a3_ (simplify_eq_val _UU03a3_) u k t0 v
      | RiscvPmpBase.Coq_term_record (r, ts) ->
        simplify_eq_record_val _UU03a3_ (simplify_eq_val _UU03a3_) r ts v

    (** val simplify_eq_binop_default :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
        -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop_default _UU03a3_ _UU03c3_1 _UU03c3_2 _UU03c3_ op t1 t2 t =
      DList.singleton _UU03a3_ (Coq_formula_relop (_UU03c3_, (Coq_bop.Coq_eq
        _UU03c3_), (RiscvPmpBase.Coq_term_binop (_UU03c3_1, _UU03c3_2,
        _UU03c3_, op, t1, t2)), t))

    (** val simplify_eq_binop_minus :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop_minus _UU03a3_ tl1 tl2 tr =
      DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_int,
        (Coq_bop.Coq_eq Coq_ty.Coq_int), (RiscvPmpBase.Coq_term_val
        (Coq_ty.Coq_int, (Obj.magic Z.of_nat O))),
        (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
        Coq_ty.Coq_int, Coq_bop.Coq_minus, tr, (RiscvPmpBase.Coq_term_binop
        (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_bop.Coq_minus,
        tl1, tl2))))))

    (** val simplify_eq_binop_times :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop_times _UU03a3_ tl1 tl2 tr =
      DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_int,
        (Coq_bop.Coq_eq Coq_ty.Coq_int), (RiscvPmpBase.Coq_term_val
        (Coq_ty.Coq_int, (Obj.magic Z.of_nat O))),
        (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
        Coq_ty.Coq_int, Coq_bop.Coq_minus, tr, (RiscvPmpBase.Coq_term_binop
        (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_bop.Coq_times,
        tl1, tl2))))))

    (** val simplify_eq_unop_default :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_unop_default _UU03a3_ _UU03c3_1 _UU03c3_2 op t1 t =
      DList.singleton _UU03a3_ (Coq_formula_relop (_UU03c3_2, (Coq_bop.Coq_eq
        _UU03c3_2), (RiscvPmpBase.Coq_term_unop (_UU03c3_1, _UU03c3_2, op,
        t1)), t))

    (** val simplify_eq_binop_plus :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop_plus _UU03a3_ simplify_eq0 tl1 tl2 tr =
      let default =
        DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_int,
          (Coq_bop.Coq_eq Coq_ty.Coq_int), (RiscvPmpBase.Coq_term_val
          (Coq_ty.Coq_int, (Obj.magic Z.of_nat O))),
          (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
          Coq_ty.Coq_int, Coq_bop.Coq_minus, tr, (RiscvPmpBase.Coq_term_binop
          (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_bop.Coq_plus,
          tl1, tl2))))))
      in
      RiscvPmpBase.coq_Term_int_case _UU03a3_ (fun _ _ -> default) (fun v ->
        simplify_eq_val _UU03a3_ Coq_ty.Coq_int (RiscvPmpBase.Coq_term_binop
          (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_bop.Coq_plus,
          tl1, tl2)) v)
        (fun tr1 tr2 ->
        match RiscvPmpBase.coq_Term_eqb _UU03a3_ Coq_ty.Coq_int tl1 tr1 with
        | Coq_true -> simplify_eq0 Coq_ty.Coq_int tl2 tr2
        | Coq_false ->
          (match RiscvPmpBase.coq_Term_eqb _UU03a3_ Coq_ty.Coq_int tl2 tr2 with
           | Coq_true -> simplify_eq0 Coq_ty.Coq_int tl1 tr1
           | Coq_false ->
             (match RiscvPmpBase.coq_Term_eqb _UU03a3_ Coq_ty.Coq_int tl1 tr2 with
              | Coq_true -> simplify_eq0 Coq_ty.Coq_int tl2 tr1
              | Coq_false ->
                (match RiscvPmpBase.coq_Term_eqb _UU03a3_ Coq_ty.Coq_int tl2
                         tr1 with
                 | Coq_true -> simplify_eq0 Coq_ty.Coq_int tl1 tr2
                 | Coq_false -> default))))
        (fun tr1 tr2 ->
        match RiscvPmpBase.coq_Term_eqb _UU03a3_ Coq_ty.Coq_int tl1 tr1 with
        | Coq_true ->
          simplify_eq0 Coq_ty.Coq_int tl2 (RiscvPmpBase.Coq_term_unop
            (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_uop.Coq_neg, tr2))
        | Coq_false ->
          (match RiscvPmpBase.coq_Term_eqb _UU03a3_ Coq_ty.Coq_int tl2 tr1 with
           | Coq_true ->
             simplify_eq0 Coq_ty.Coq_int tl1 (RiscvPmpBase.Coq_term_unop
               (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_uop.Coq_neg, tr2))
           | Coq_false -> default))
        (fun _ _ -> default) (fun _ _ -> default) (fun _ -> default)
        (fun _ _ -> default) (fun _ _ -> default) tr

    (** val simplify_eq_binop_and :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop_and _UU03a3_ tl1 tl2 tr =
      let tl = RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool,
        Coq_ty.Coq_bool, Coq_bop.Coq_and, tl1, tl2)
      in
      let default =
        DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_bool,
          (Coq_bop.Coq_eq Coq_ty.Coq_bool), tl, tr))
      in
      RiscvPmpBase.coq_Term_bool_case _UU03a3_ (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_bool,
          (Coq_bop.Coq_eq Coq_ty.Coq_bool), tr, tl)))
        (fun v -> simplify_eq_val _UU03a3_ Coq_ty.Coq_bool tl v)
        (fun tr1 tr2 ->
        match match RiscvPmpBase.coq_Term_eqb _UU03a3_ Coq_ty.Coq_bool tl1 tr1 with
              | Coq_true ->
                RiscvPmpBase.coq_Term_eqb _UU03a3_ Coq_ty.Coq_bool tl2 tr2
              | Coq_false -> Coq_false with
        | Coq_true -> DList.empty _UU03a3_
        | Coq_false -> default) (fun _ _ -> default) (fun _ _ _ _ -> default)
        (fun _ -> default) tr

    (** val simplify_eq_binop_or :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop_or _UU03a3_ tl1 tl2 tr =
      let tl = RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool,
        Coq_ty.Coq_bool, Coq_bop.Coq_or, tl1, tl2)
      in
      let default =
        DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_bool,
          (Coq_bop.Coq_eq Coq_ty.Coq_bool), tl, tr))
      in
      RiscvPmpBase.coq_Term_bool_case _UU03a3_ (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_bool,
          (Coq_bop.Coq_eq Coq_ty.Coq_bool), tr, tl)))
        (fun v -> simplify_eq_val _UU03a3_ Coq_ty.Coq_bool tl v) (fun _ _ ->
        default) (fun tr1 tr2 ->
        match match RiscvPmpBase.coq_Term_eqb _UU03a3_ Coq_ty.Coq_bool tl1 tr1 with
              | Coq_true ->
                RiscvPmpBase.coq_Term_eqb _UU03a3_ Coq_ty.Coq_bool tl2 tr2
              | Coq_false -> Coq_false with
        | Coq_true -> DList.empty _UU03a3_
        | Coq_false -> default) (fun _ _ _ _ -> default) (fun _ -> default) tr

    (** val simplify_eq_binop_pair :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop_pair _UU03a3_ simplify_eq0 _UU03c3_1 _UU03c3_2 t1 t2 t =
      RiscvPmpBase.coq_Term_prod_case _UU03a3_ _UU03c3_1 _UU03c3_2
        (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_prod
          (_UU03c3_1, _UU03c3_2)), (Coq_bop.Coq_eq (Coq_ty.Coq_prod
          (_UU03c3_1, _UU03c3_2))), t, (RiscvPmpBase.Coq_term_binop
          (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_prod (_UU03c3_1, _UU03c3_2)),
          (Coq_bop.Coq_pair (_UU03c3_1, _UU03c3_2)), t1, t2)))))
        (fun v ->
        simplify_eq_val _UU03a3_ (Coq_ty.Coq_prod (_UU03c3_1, _UU03c3_2))
          (RiscvPmpBase.Coq_term_binop (_UU03c3_1, _UU03c3_2,
          (Coq_ty.Coq_prod (_UU03c3_1, _UU03c3_2)), (Coq_bop.Coq_pair
          (_UU03c3_1, _UU03c3_2)), t1, t2)) v)
        (fun t1' t2' ->
        DList.cat _UU03a3_ (simplify_eq0 _UU03c3_1 t1 t1')
          (simplify_eq0 _UU03c3_2 t2 t2'))
        t

    (** val simplify_eq_binop_cons :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop_cons _UU03a3_ simplify_eq0 _UU03c3_ t1 t2 t =
      RiscvPmpBase.coq_Term_list_case _UU03a3_ _UU03c3_ (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_list
          _UU03c3_), (Coq_bop.Coq_eq (Coq_ty.Coq_list _UU03c3_)), t,
          (RiscvPmpBase.Coq_term_binop (_UU03c3_, (Coq_ty.Coq_list _UU03c3_),
          (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_cons _UU03c3_), t1, t2)))))
        (fun v ->
        simplify_eq_val _UU03a3_ (Coq_ty.Coq_list _UU03c3_)
          (RiscvPmpBase.Coq_term_binop (_UU03c3_, (Coq_ty.Coq_list _UU03c3_),
          (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_cons _UU03c3_), t1, t2)) v)
        (fun t1' t2' ->
        DList.cat _UU03a3_ (simplify_eq0 _UU03c3_ t1 t1')
          (simplify_eq0 (Coq_ty.Coq_list _UU03c3_) t2 t2'))
        (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_list
          _UU03c3_), (Coq_bop.Coq_eq (Coq_ty.Coq_list _UU03c3_)),
          (RiscvPmpBase.Coq_term_binop (_UU03c3_, (Coq_ty.Coq_list _UU03c3_),
          (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_cons _UU03c3_), t1, t2)),
          t)))
        (fun _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_list
          _UU03c3_), (Coq_bop.Coq_eq (Coq_ty.Coq_list _UU03c3_)),
          (RiscvPmpBase.Coq_term_binop (_UU03c3_, (Coq_ty.Coq_list _UU03c3_),
          (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_cons _UU03c3_), t1, t2)),
          t)))
        t

    (** val simplify_eq_binop_append :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop_append _UU03a3_ simplify_eq0 _UU03c3_ tl1 tl2 tr =
      RiscvPmpBase.coq_Term_list_case _UU03a3_ _UU03c3_ (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_list
          _UU03c3_), (Coq_bop.Coq_eq (Coq_ty.Coq_list _UU03c3_)), tr,
          (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_list _UU03c3_),
          (Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list _UU03c3_),
          (Coq_bop.Coq_append _UU03c3_), tl1, tl2)))))
        (fun v ->
        simplify_eq_val _UU03a3_ (Coq_ty.Coq_list _UU03c3_)
          (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_list _UU03c3_),
          (Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list _UU03c3_),
          (Coq_bop.Coq_append _UU03c3_), tl1, tl2)) v)
        (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_list
          _UU03c3_), (Coq_bop.Coq_eq (Coq_ty.Coq_list _UU03c3_)), tr,
          (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_list _UU03c3_),
          (Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list _UU03c3_),
          (Coq_bop.Coq_append _UU03c3_), tl1, tl2)))))
        (fun tr1 tr2 ->
        match RiscvPmpBase.coq_Term_eqb _UU03a3_ (Coq_ty.Coq_list _UU03c3_)
                tl1 tr1 with
        | Coq_true -> simplify_eq0 (Coq_ty.Coq_list _UU03c3_) tl2 tr2
        | Coq_false ->
          (match RiscvPmpBase.coq_Term_eqb _UU03a3_ (Coq_ty.Coq_list
                   _UU03c3_) tl2 tr2 with
           | Coq_true -> simplify_eq0 (Coq_ty.Coq_list _UU03c3_) tl1 tr1
           | Coq_false ->
             DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_list
               _UU03c3_), (Coq_bop.Coq_eq (Coq_ty.Coq_list _UU03c3_)),
               (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_list _UU03c3_),
               (Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list _UU03c3_),
               (Coq_bop.Coq_append _UU03c3_), tl1, tl2)), tr))))
        (fun _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_list
          _UU03c3_), (Coq_bop.Coq_eq (Coq_ty.Coq_list _UU03c3_)),
          (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_list _UU03c3_),
          (Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list _UU03c3_),
          (Coq_bop.Coq_append _UU03c3_), tl1, tl2)), tr)))
        tr

    (** val simplify_eq_binop_bvapp' :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> nat -> nat -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> nat -> RiscvPmpBase.coq_Term ->
        DList.coq_DList **)

    let simplify_eq_binop_bvapp' _UU03a3_ simplify_eq0 m n t1 t2 mn t =
      let default = fun _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_bvec
          (add m n)), (Coq_bop.Coq_eq (Coq_ty.Coq_bvec (add m n))),
          (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec
          n), (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)), t1,
          t2)), t))
      in
      RiscvPmpBase.coq_Term_bvec_case _UU03a3_ (fun _ _ _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_bvec
          (add m n)), (Coq_bop.Coq_eq (Coq_ty.Coq_bvec (add m n))), t,
          (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec
          n), (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)), t1,
          t2)))))
        (fun _ v _ ->
        simplify_eq_val _UU03a3_ (Coq_ty.Coq_bvec (add m n))
          (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec
          n), (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)), t1,
          t2)) v)
        (fun n0 _ _ _ -> default n0) (fun n0 _ _ _ -> default n0)
        (fun n0 _ _ _ -> default n0) (fun n0 _ _ _ -> default n0)
        (fun n0 _ _ _ -> default n0) (fun n0 _ _ _ -> default n0)
        (fun n0 _ _ _ _ -> default n0) (fun n0 _ _ _ _ -> default n0)
        (fun m' n' t1' t2' _ ->
        match eq_dec nat_EqDec m m' with
        | Coq_left ->
          DList.cat _UU03a3_ (simplify_eq0 (Coq_ty.Coq_bvec m) t1 t1')
            (simplify_eq0 (Coq_ty.Coq_bvec n) t2 t2')
        | Coq_right -> default (add m' n')) (fun n0 _ _ _ -> default (S n0))
        (fun n0 _ _ _ _ _ _ -> default n0) (fun n0 _ _ -> default n0)
        (fun n0 _ _ -> default n0) (fun n0 _ _ _ _ -> default n0)
        (fun n0 _ _ _ _ -> default n0) (fun n0 _ _ -> default n0)
        (fun n0 _ _ _ _ -> default n0) (fun _ l _ _ _ _ -> default l)
        (fun _ n0 _ _ -> default n0) (fun m0 _ _ _ -> default m0) mn t __

    (** val simplify_eq_binop_bvapp :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> nat -> nat -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop_bvapp _UU03a3_ simplify_eq0 m n t1 t2 t =
      simplify_eq_binop_bvapp' _UU03a3_ simplify_eq0 m n t1 t2 (add m n) t

    (** val simplify_eq_binop_bvcons' :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> nat -> RiscvPmpBase.coq_Term ->
        DList.coq_DList **)

    let simplify_eq_binop_bvcons' _UU03a3_ simplify_eq0 m t1 t2 sm t =
      let default = fun _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_bvec (S m)),
          (Coq_bop.Coq_eq (Coq_ty.Coq_bvec (S m))),
          (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m),
          (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvcons m), t1, t2)), t))
      in
      RiscvPmpBase.coq_Term_bvec_case _UU03a3_ (fun _ _ _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_bvec (S m)),
          (Coq_bop.Coq_eq (Coq_ty.Coq_bvec (S m))), t,
          (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m),
          (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvcons m), t1, t2)))))
        (fun _ v _ ->
        simplify_eq_val _UU03a3_ (Coq_ty.Coq_bvec (S m))
          (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m),
          (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvcons m), t1, t2)) v)
        (fun n _ _ _ -> default n) (fun n _ _ _ -> default n) (fun n _ _ _ ->
        default n) (fun n _ _ _ -> default n) (fun n _ _ _ -> default n)
        (fun n _ _ _ -> default n) (fun n _ _ _ _ -> default n)
        (fun n _ _ _ _ -> default n) (fun n1 n2 _ _ _ -> default (add n1 n2))
        (fun _ t1' t2' _ ->
        DList.cat _UU03a3_ (simplify_eq0 Coq_ty.Coq_bool t1 t1')
          (simplify_eq0 (Coq_ty.Coq_bvec m) t2 t2'))
        (fun n _ _ _ _ _ _ -> default n) (fun n _ _ -> default n)
        (fun n _ _ -> default n) (fun n _ _ _ _ -> default n)
        (fun n _ _ _ _ -> default n) (fun n _ _ -> default n)
        (fun n _ _ _ _ -> default n) (fun _ l _ _ _ _ -> default l)
        (fun _ n _ _ -> default n) (fun m0 _ _ _ -> default m0) sm t __

    (** val simplify_eq_binop_bvcons :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop_bvcons _UU03a3_ simplify_eq0 m t1 t2 t =
      simplify_eq_binop_bvcons' _UU03a3_ simplify_eq0 m t1 t2 (S m) t

    (** val simplify_eq_relop :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let rec simplify_eq_relop _UU03a3_ _UU03c3_ op tl1 tl2 tr =
      let tl = RiscvPmpBase.Coq_term_binop (_UU03c3_, _UU03c3_,
        Coq_ty.Coq_bool, (Coq_bop.Coq_relop (_UU03c3_, op)), tl1, tl2)
      in
      RiscvPmpBase.coq_Term_bool_case _UU03a3_ (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_bool,
          (Coq_bop.Coq_eq Coq_ty.Coq_bool), tr, tl)))
        (fun v -> simplify_eq_val _UU03a3_ Coq_ty.Coq_bool tl v) (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_bool,
          (Coq_bop.Coq_eq Coq_ty.Coq_bool), tl, tr)))
        (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_bool,
          (Coq_bop.Coq_eq Coq_ty.Coq_bool), tl, tr)))
        (fun _ _ _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_bool,
          (Coq_bop.Coq_eq Coq_ty.Coq_bool), tl, tr)))
        (fun tr' ->
        match op with
        | Coq_bop.Coq_eq _UU03c3_0 ->
          simplify_eq_relop _UU03a3_ _UU03c3_0 (Coq_bop.Coq_neq _UU03c3_0)
            tl1 tl2 tr'
        | Coq_bop.Coq_neq _UU03c3_0 ->
          simplify_eq_relop _UU03a3_ _UU03c3_0 (Coq_bop.Coq_eq _UU03c3_0) tl1
            tl2 tr'
        | Coq_bop.Coq_le ->
          simplify_eq_relop _UU03a3_ Coq_ty.Coq_int Coq_bop.Coq_lt tl2 tl1 tr'
        | Coq_bop.Coq_lt ->
          simplify_eq_relop _UU03a3_ Coq_ty.Coq_int Coq_bop.Coq_le tl2 tl1 tr'
        | Coq_bop.Coq_bvsle n ->
          simplify_eq_relop _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvslt
            n) tl2 tl1 tr'
        | Coq_bop.Coq_bvslt n ->
          simplify_eq_relop _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvsle
            n) tl2 tl1 tr'
        | Coq_bop.Coq_bvule n ->
          simplify_eq_relop _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvult
            n) tl2 tl1 tr'
        | Coq_bop.Coq_bvult n ->
          simplify_eq_relop _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvule
            n) tl2 tl1 tr')
        tr

    (** val simplify_eq_binop :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
        -> Coq_bop.coq_BinOp -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_binop _UU03a3_ simplify_eq0 _ _ _ = function
    | Coq_bop.Coq_plus -> simplify_eq_binop_plus _UU03a3_ simplify_eq0
    | Coq_bop.Coq_minus -> simplify_eq_binop_minus _UU03a3_
    | Coq_bop.Coq_times -> simplify_eq_binop_times _UU03a3_
    | Coq_bop.Coq_land ->
      simplify_eq_binop_default _UU03a3_ Coq_ty.Coq_int Coq_ty.Coq_int
        Coq_ty.Coq_int Coq_bop.Coq_land
    | Coq_bop.Coq_and -> simplify_eq_binop_and _UU03a3_
    | Coq_bop.Coq_or -> simplify_eq_binop_or _UU03a3_
    | Coq_bop.Coq_pair (_UU03c3_0, _UU03c3_3) ->
      simplify_eq_binop_pair _UU03a3_ simplify_eq0 _UU03c3_0 _UU03c3_3
    | Coq_bop.Coq_cons _UU03c3_0 ->
      simplify_eq_binop_cons _UU03a3_ simplify_eq0 _UU03c3_0
    | Coq_bop.Coq_append _UU03c3_0 ->
      simplify_eq_binop_append _UU03a3_ simplify_eq0 _UU03c3_0
    | Coq_bop.Coq_shiftr (m, n) ->
      simplify_eq_binop_default _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec
        n) (Coq_ty.Coq_bvec m) (Coq_bop.Coq_shiftr (m, n))
    | Coq_bop.Coq_shiftl (m, n) ->
      simplify_eq_binop_default _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec
        n) (Coq_ty.Coq_bvec m) (Coq_bop.Coq_shiftl (m, n))
    | Coq_bop.Coq_bvadd n ->
      simplify_eq_binop_default _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec
        n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvadd n)
    | Coq_bop.Coq_bvsub n ->
      simplify_eq_binop_default _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec
        n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvsub n)
    | Coq_bop.Coq_bvmul n ->
      simplify_eq_binop_default _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec
        n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvmul n)
    | Coq_bop.Coq_bvand n ->
      simplify_eq_binop_default _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec
        n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvand n)
    | Coq_bop.Coq_bvor n ->
      simplify_eq_binop_default _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec
        n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvor n)
    | Coq_bop.Coq_bvxor n ->
      simplify_eq_binop_default _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec
        n) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvxor n)
    | Coq_bop.Coq_bvapp (m, n) ->
      simplify_eq_binop_bvapp _UU03a3_ simplify_eq0 m n
    | Coq_bop.Coq_bvcons m -> simplify_eq_binop_bvcons _UU03a3_ simplify_eq0 m
    | Coq_bop.Coq_update_vector_subrange (n, s, l) ->
      simplify_eq_binop_default _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec
        l) (Coq_ty.Coq_bvec n) (Coq_bop.Coq_update_vector_subrange (n, s, l))
    | Coq_bop.Coq_relop (_UU03c3_0, rop) ->
      simplify_eq_relop _UU03a3_ _UU03c3_0 rop

    (** val simplify_eq_unop_inl :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_unop_inl _UU03a3_ simplify_eq0 _UU03c3_1 _UU03c3_2 t1 t =
      RiscvPmpBase.coq_Term_sum_case _UU03a3_ _UU03c3_1 _UU03c3_2 (fun _ _ ->
        simplify_eq_unop_default _UU03a3_ _UU03c3_1 (Coq_ty.Coq_sum
          (_UU03c3_1, _UU03c3_2)) (Coq_uop.Coq_inl (_UU03c3_1, _UU03c3_2)) t1
          t)
        (fun v ->
        simplify_eq_val _UU03a3_ (Coq_ty.Coq_sum (_UU03c3_1, _UU03c3_2))
          (RiscvPmpBase.Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_sum (_UU03c3_1,
          _UU03c3_2)), (Coq_uop.Coq_inl (_UU03c3_1, _UU03c3_2)), t1)) v)
        (fun t1' -> simplify_eq0 _UU03c3_1 t1 t1') (fun _ ->
        DList.error _UU03a3_) t

    (** val simplify_eq_unop_inr :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_unop_inr _UU03a3_ simplify_eq0 _UU03c3_1 _UU03c3_2 t2 t =
      RiscvPmpBase.coq_Term_sum_case _UU03a3_ _UU03c3_1 _UU03c3_2 (fun _ _ ->
        simplify_eq_unop_default _UU03a3_ _UU03c3_2 (Coq_ty.Coq_sum
          (_UU03c3_1, _UU03c3_2)) (Coq_uop.Coq_inr (_UU03c3_1, _UU03c3_2)) t2
          t)
        (fun v ->
        simplify_eq_val _UU03a3_ (Coq_ty.Coq_sum (_UU03c3_1, _UU03c3_2))
          (RiscvPmpBase.Coq_term_unop (_UU03c3_2, (Coq_ty.Coq_sum (_UU03c3_1,
          _UU03c3_2)), (Coq_uop.Coq_inr (_UU03c3_1, _UU03c3_2)), t2)) v)
        (fun _ -> DList.error _UU03a3_) (fun t2' ->
        simplify_eq0 _UU03c3_2 t2 t2') t

    (** val simplify_eq_unop_get_slice_int :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat
        -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_unop_get_slice_int _UU03a3_ m tl tr =
      let tl0 = RiscvPmpBase.Coq_term_unop (Coq_ty.Coq_int, (Coq_ty.Coq_bvec
        m), (Coq_uop.Coq_get_slice_int m), tl)
      in
      (match RiscvPmpBase.coq_Term_eqb _UU03a3_ (Coq_ty.Coq_bvec m) tl0 tr with
       | Coq_true -> DList.empty _UU03a3_
       | Coq_false ->
         DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_bvec m),
           (Coq_bop.Coq_eq (Coq_ty.Coq_bvec m)), tl0, tr)))

    (** val simplify_eq_unop_signed :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_unop_signed _UU03a3_ simplify_eq0 m tl tr =
      let default =
        DList.singleton _UU03a3_ (Coq_formula_relop (Coq_ty.Coq_int,
          (Coq_bop.Coq_eq Coq_ty.Coq_int), (RiscvPmpBase.Coq_term_val
          (Coq_ty.Coq_int, (Obj.magic Z.of_nat O))),
          (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
          Coq_ty.Coq_int, Coq_bop.Coq_minus, tr, (RiscvPmpBase.Coq_term_unop
          ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int, (Coq_uop.Coq_signed m),
          tl))))))
      in
      RiscvPmpBase.coq_Term_int_case _UU03a3_ (fun _ _ -> default) (fun v ->
        simplify_eq_val _UU03a3_ Coq_ty.Coq_int (RiscvPmpBase.Coq_term_unop
          ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int, (Coq_uop.Coq_signed m), tl)) v)
        (fun _ _ -> default) (fun _ _ -> default) (fun _ _ -> default)
        (fun _ _ -> default) (fun _ -> default) (fun n ->
        match eq_dec nat_EqDec m n with
        | Coq_left -> simplify_eq0 (Coq_ty.Coq_bvec m) tl
        | Coq_right -> (fun _ -> default)) (fun _ _ -> default) tr

    (** val simplify_eq_unop :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
        Coq_uop.coq_UnOp -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList **)

    let simplify_eq_unop _UU03a3_ simplify_eq0 _ _ = function
    | Coq_uop.Coq_inl (_UU03c3_0, _UU03c3_3) ->
      simplify_eq_unop_inl _UU03a3_ simplify_eq0 _UU03c3_0 _UU03c3_3
    | Coq_uop.Coq_inr (_UU03c3_0, _UU03c3_3) ->
      simplify_eq_unop_inr _UU03a3_ simplify_eq0 _UU03c3_0 _UU03c3_3
    | Coq_uop.Coq_neg ->
      simplify_eq_unop_default _UU03a3_ Coq_ty.Coq_int Coq_ty.Coq_int
        Coq_uop.Coq_neg
    | Coq_uop.Coq_not ->
      simplify_eq_unop_default _UU03a3_ Coq_ty.Coq_bool Coq_ty.Coq_bool
        Coq_uop.Coq_not
    | Coq_uop.Coq_rev _UU03c3_ ->
      simplify_eq_unop_default _UU03a3_ (Coq_ty.Coq_list _UU03c3_)
        (Coq_ty.Coq_list _UU03c3_) (Coq_uop.Coq_rev _UU03c3_)
    | Coq_uop.Coq_sext (m, n) ->
      simplify_eq_unop_default _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec
        n) (Coq_uop.Coq_sext (m, n))
    | Coq_uop.Coq_zext (m, n) ->
      simplify_eq_unop_default _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec
        n) (Coq_uop.Coq_zext (m, n))
    | Coq_uop.Coq_get_slice_int n -> simplify_eq_unop_get_slice_int _UU03a3_ n
    | Coq_uop.Coq_signed n -> simplify_eq_unop_signed _UU03a3_ simplify_eq0 n
    | Coq_uop.Coq_unsigned n ->
      simplify_eq_unop_default _UU03a3_ (Coq_ty.Coq_bvec n) Coq_ty.Coq_int
        (Coq_uop.Coq_unsigned n)
    | Coq_uop.Coq_truncate (n0, n) ->
      simplify_eq_unop_default _UU03a3_ (Coq_ty.Coq_bvec n0) (Coq_ty.Coq_bvec
        n) (Coq_uop.Coq_truncate (n0, n))
    | Coq_uop.Coq_vector_subrange (n, s, l) ->
      simplify_eq_unop_default _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec
        l) (Coq_uop.Coq_vector_subrange (n, s, l))
    | Coq_uop.Coq_bvnot n ->
      simplify_eq_unop_default _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec
        n) (Coq_uop.Coq_bvnot n)
    | Coq_uop.Coq_bvdrop (m, n) ->
      simplify_eq_unop_default _UU03a3_ (Coq_ty.Coq_bvec (add m n))
        (Coq_ty.Coq_bvec n) (Coq_uop.Coq_bvdrop (m, n))
    | Coq_uop.Coq_bvtake (m, n) ->
      simplify_eq_unop_default _UU03a3_ (Coq_ty.Coq_bvec (add m n))
        (Coq_ty.Coq_bvec m) (Coq_uop.Coq_bvtake (m, n))
    | Coq_uop.Coq_negate n ->
      simplify_eq_unop_default _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec
        n) (Coq_uop.Coq_negate n)

    (** val formula_eqs_ctx :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty,
        RiscvPmpBase.coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
        RiscvPmpBase.coq_Term) Coq_env.coq_Env -> DList.coq_DList **)

    let rec formula_eqs_ctx _UU03a3_ simplify_eq0 _ _UU03b4_ _UU03b4_' =
      match _UU03b4_ with
      | Coq_env.Coq_nil ->
        (match _UU03b4_' with
         | Coq_env.Coq_nil -> DList.empty _UU03a3_
         | Coq_env.Coq_snoc (_, _, _, _) -> assert false (* absurd case *))
      | Coq_env.Coq_snoc (_UU0393_, e, b, db) ->
        (match _UU03b4_' with
         | Coq_env.Coq_nil -> assert false (* absurd case *)
         | Coq_env.Coq_snoc (_, e0, _, db0) ->
           DList.cat _UU03a3_
             (formula_eqs_ctx _UU03a3_ simplify_eq0 _UU0393_ e e0)
             (simplify_eq0 b db db0))

    (** val formula_eqs_nctx :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
        coq_NamedEnv -> ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
        coq_NamedEnv -> DList.coq_DList **)

    let rec formula_eqs_nctx _UU03a3_ simplify_eq0 _ _UU03b4_ _UU03b4_' =
      match _UU03b4_ with
      | Coq_env.Coq_nil ->
        (match _UU03b4_' with
         | Coq_env.Coq_nil -> DList.empty _UU03a3_
         | Coq_env.Coq_snoc (_, _, _, _) -> assert false (* absurd case *))
      | Coq_env.Coq_snoc (_UU0393_, e, b, db) ->
        (match _UU03b4_' with
         | Coq_env.Coq_nil -> assert false (* absurd case *)
         | Coq_env.Coq_snoc (_, e0, _, db0) ->
           DList.cat _UU03a3_
             (formula_eqs_nctx _UU03a3_ simplify_eq0 _UU0393_ e e0)
             (simplify_eq0 b.Binding.coq_type db db0))

    (** val simplify_eq_tuple :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty,
        RiscvPmpBase.coq_Term) Coq_env.coq_Env -> RiscvPmpBase.coq_Term ->
        DList.coq_DList **)

    let simplify_eq_tuple _UU03a3_ simplify_eq0 _UU03c3_s tls tr =
      RiscvPmpBase.coq_Term_tuple_case _UU03a3_ _UU03c3_s (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_tuple
          _UU03c3_s), (Coq_bop.Coq_eq (Coq_ty.Coq_tuple _UU03c3_s)),
          (RiscvPmpBase.Coq_term_tuple (_UU03c3_s, tls)), tr)))
        (fun v ->
        simplify_eq_val _UU03a3_ (Coq_ty.Coq_tuple _UU03c3_s)
          (RiscvPmpBase.Coq_term_tuple (_UU03c3_s, tls)) v)
        (fun trs -> formula_eqs_ctx _UU03a3_ simplify_eq0 _UU03c3_s tls trs)
        tr

    (** val simplify_eq_record :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty,
        RiscvPmpBase.coq_Term) coq_NamedEnv -> RiscvPmpBase.coq_Term ->
        DList.coq_DList **)

    let simplify_eq_record _UU03a3_ simplify_eq0 r tls tr =
      RiscvPmpBase.coq_Term_record_case _UU03a3_ r (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_record r),
          (Coq_bop.Coq_eq (Coq_ty.Coq_record r)), tr,
          (RiscvPmpBase.Coq_term_record (r, tls)))))
        (fun v ->
        simplify_eq_record_val _UU03a3_ (simplify_eq_val _UU03a3_) r tls v)
        (fun trs ->
        formula_eqs_nctx _UU03a3_ simplify_eq0
          (RiscvPmpBase.typedefkit.Coq_ty.recordf_ty r) tls trs)
        tr

    (** val simplify_eq_union :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList) -> Coq_ty.unioni -> Coq_ty.unionk ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_eq_union _UU03a3_ simplify_eq0 u k1 t1 t2 =
      RiscvPmpBase.coq_Term_union_case _UU03a3_ u (fun _ _ ->
        DList.singleton _UU03a3_ (Coq_formula_relop ((Coq_ty.Coq_union u),
          (Coq_bop.Coq_eq (Coq_ty.Coq_union u)), t2,
          (RiscvPmpBase.Coq_term_union (u, k1, t1)))))
        (fun v ->
        simplify_eq_val _UU03a3_ (Coq_ty.Coq_union u)
          (RiscvPmpBase.Coq_term_union (u, k1, t1)) v)
        (fun k2 t3 ->
        match eq_dec (RiscvPmpBase.typedefkit.Coq_ty.unionk_eqdec u) k1 k2 with
        | Coq_left ->
          simplify_eq0 (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty u k1) t1 t3
        | Coq_right -> DList.error _UU03a3_) t2

    (** val simplify_eq :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
        DList.coq_DList **)

    let rec simplify_eq _UU03a3_ _UU03c3_ tl tr =
      match tl with
      | RiscvPmpBase.Coq_term_var (_, _, _) ->
        simplify_eqb _UU03a3_ _UU03c3_ tl tr
      | RiscvPmpBase.Coq_term_val (_UU03c3_0, v) ->
        simplify_eq_val _UU03a3_ _UU03c3_0 tr v
      | RiscvPmpBase.Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1,
                                     t2) ->
        simplify_eq_binop _UU03a3_ (simplify_eq _UU03a3_) _UU03c3_1 _UU03c3_2
          _UU03c3_3 op t1 t2 tr
      | RiscvPmpBase.Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t1) ->
        simplify_eq_unop _UU03a3_ (simplify_eq _UU03a3_) _UU03c3_1 _UU03c3_2
          op t1 tr
      | RiscvPmpBase.Coq_term_tuple (_UU03c3_s, tls) ->
        simplify_eq_tuple _UU03a3_ (simplify_eq _UU03a3_) _UU03c3_s tls tr
      | RiscvPmpBase.Coq_term_union (u, k, tl0) ->
        simplify_eq_union _UU03a3_ (simplify_eq _UU03a3_) u k tl0 tr
      | RiscvPmpBase.Coq_term_record (r, tls) ->
        simplify_eq_record _UU03a3_ (simplify_eq _UU03a3_) r tls tr

    (** val simplify_relopb :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_relopb _UU03a3_ _UU03c3_ op t1 t2 =
      match RiscvPmpBase.term_get_val _UU03a3_ _UU03c3_ t1 with
      | Some v1 ->
        (match RiscvPmpBase.term_get_val _UU03a3_ _UU03c3_ t2 with
         | Some v2 ->
           (match Coq_bop.eval_relop_val RiscvPmpBase.typedeclkit
                    RiscvPmpBase.typedenotekit RiscvPmpBase.typedefkit
                    _UU03c3_ op v1 v2 with
            | Coq_true -> DList.empty _UU03a3_
            | Coq_false -> DList.error _UU03a3_)
         | None ->
           DList.singleton _UU03a3_ (Coq_formula_relop (_UU03c3_, op, t1, t2)))
      | None ->
        DList.singleton _UU03a3_ (Coq_formula_relop (_UU03c3_, op, t1, t2))

    (** val peval_formula_le' :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> coq_Formula **)

    let peval_formula_le' _UU03a3_ t =
      let default = Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
        (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int, (Obj.magic Z0))), t)
      in
      RiscvPmpBase.coq_Term_int_case _UU03a3_ (fun _ _ -> default) (fun v ->
        match Z.leb Z0 (Obj.magic v) with
        | Coq_true -> Coq_formula_true
        | Coq_false -> Coq_formula_false) (fun _ _ -> default) (fun _ _ ->
        default) (fun _ _ -> default) (fun _ _ -> default) (fun _ -> default)
        (fun _ _ -> default) (fun _ _ -> Coq_formula_true) t

    (** val peval_formula_le :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_Formula **)

    let peval_formula_le _UU03a3_ t1 t2 =
      peval_formula_le' _UU03a3_
        (RiscvPmpBase.peval _UU03a3_ Coq_ty.Coq_int
          (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
          Coq_ty.Coq_int, Coq_bop.Coq_minus, t2, t1)))

    (** val peval_formula_lt :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_Formula **)

    let peval_formula_lt _UU03a3_ t1 t2 =
      peval_formula_le _UU03a3_ (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int,
        Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_bop.Coq_plus, t1,
        (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
        (Obj.magic (Zpos Coq_xH)))))) t2

    (** val peval_formula_relop_neg :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> coq_Formula **)

    let peval_formula_relop_neg _UU03a3_ _ = function
    | Coq_bop.Coq_eq _UU03c3_0 ->
      (fun x x0 -> Coq_formula_relop (_UU03c3_0, (Coq_bop.Coq_neq _UU03c3_0),
        x, x0))
    | Coq_bop.Coq_neq _UU03c3_0 ->
      (fun x x0 -> Coq_formula_relop (_UU03c3_0, (Coq_bop.Coq_eq _UU03c3_0),
        x, x0))
    | Coq_bop.Coq_le -> flip (peval_formula_lt _UU03a3_)
    | Coq_bop.Coq_lt -> flip (peval_formula_le _UU03a3_)
    | Coq_bop.Coq_bvsle n ->
      flip (fun x x0 -> Coq_formula_relop ((Coq_ty.Coq_bvec n),
        (Coq_bop.Coq_bvslt n), x, x0))
    | Coq_bop.Coq_bvslt n ->
      flip (fun x x0 -> Coq_formula_relop ((Coq_ty.Coq_bvec n),
        (Coq_bop.Coq_bvsle n), x, x0))
    | Coq_bop.Coq_bvule n ->
      flip (fun x x0 -> Coq_formula_relop ((Coq_ty.Coq_bvec n),
        (Coq_bop.Coq_bvult n), x, x0))
    | Coq_bop.Coq_bvult n ->
      flip (fun x x0 -> Coq_formula_relop ((Coq_ty.Coq_bvec n),
        (Coq_bop.Coq_bvule n), x, x0))

    (** val simplify_le :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_le _UU03a3_ t1 t2 =
      DList.singleton _UU03a3_ (peval_formula_le _UU03a3_ t1 t2)

    (** val simplify_bvule :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat
        -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_bvule _UU03a3_ n t1 t2 =
      let default = fun _ ->
        simplify_relopb _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvule n)
          (RiscvPmpBase.peval _UU03a3_ (Coq_ty.Coq_bvec n) t1)
          (RiscvPmpBase.peval _UU03a3_ (Coq_ty.Coq_bvec n) t2)
      in
      (match RiscvPmpBase.term_get_val _UU03a3_ (Coq_ty.Coq_bvec n) t1 with
       | Some v ->
         (match Coq_bv.eqb n (Obj.magic v) (Coq_bv.zero n) with
          | Coq_true -> DList.empty _UU03a3_
          | Coq_false -> default Coq_tt)
       | None -> default Coq_tt)

    (** val simplify_bvult :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat
        -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_bvult _UU03a3_ n t1 t2 =
      let default = fun _ ->
        simplify_relopb _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvult n)
          (RiscvPmpBase.peval _UU03a3_ (Coq_ty.Coq_bvec n) t1)
          (RiscvPmpBase.peval _UU03a3_ (Coq_ty.Coq_bvec n) t2)
      in
      (match RiscvPmpBase.term_get_val _UU03a3_ (Coq_ty.Coq_bvec n) t2 with
       | Some v ->
         (match Coq_bv.eqb n (Obj.magic v) (Coq_bv.zero n) with
          | Coq_true -> DList.singleton _UU03a3_ Coq_formula_false
          | Coq_false -> default Coq_tt)
       | None -> default Coq_tt)

    (** val simplify_lt :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_lt _UU03a3_ t1 t2 =
      DList.singleton _UU03a3_ (peval_formula_lt _UU03a3_ t1 t2)

    (** val simplify_relop :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> DList.coq_DList **)

    let simplify_relop _UU03a3_ _ = function
    | Coq_bop.Coq_eq _UU03c3_0 ->
      (fun t1 t2 ->
        simplify_eq _UU03a3_ _UU03c3_0
          (RiscvPmpBase.peval _UU03a3_ _UU03c3_0 t1)
          (RiscvPmpBase.peval _UU03a3_ _UU03c3_0 t2))
    | Coq_bop.Coq_neq _UU03c3_0 ->
      (fun t1 t2 ->
        simplify_relopb _UU03a3_ _UU03c3_0 (Coq_bop.Coq_neq _UU03c3_0)
          (RiscvPmpBase.peval _UU03a3_ _UU03c3_0 t1)
          (RiscvPmpBase.peval _UU03a3_ _UU03c3_0 t2))
    | Coq_bop.Coq_le -> simplify_le _UU03a3_
    | Coq_bop.Coq_lt -> simplify_lt _UU03a3_
    | Coq_bop.Coq_bvsle n ->
      (fun t1 t2 ->
        simplify_relopb _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvsle n)
          (RiscvPmpBase.peval _UU03a3_ (Coq_ty.Coq_bvec n) t1)
          (RiscvPmpBase.peval _UU03a3_ (Coq_ty.Coq_bvec n) t2))
    | Coq_bop.Coq_bvslt n ->
      (fun t1 t2 ->
        simplify_relopb _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvslt n)
          (RiscvPmpBase.peval _UU03a3_ (Coq_ty.Coq_bvec n) t1)
          (RiscvPmpBase.peval _UU03a3_ (Coq_ty.Coq_bvec n) t2))
    | Coq_bop.Coq_bvule n -> simplify_bvule _UU03a3_ n
    | Coq_bop.Coq_bvult n -> simplify_bvult _UU03a3_ n

    (** val smart_and :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> coq_Formula -> coq_Formula **)

    let smart_and _ f1 f2 =
      match f1 with
      | Coq_formula_true -> f2
      | Coq_formula_false ->
        (match f2 with
         | Coq_formula_true -> f1
         | _ -> Coq_formula_false)
      | _ ->
        (match f2 with
         | Coq_formula_true -> f1
         | Coq_formula_false -> Coq_formula_false
         | _ -> Coq_formula_and (f1, f2))

    (** val coq_PathCondition_to_Formula :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> coq_Formula **)

    let rec coq_PathCondition_to_Formula _UU03a3_ = function
    | Coq_ctx.Coq_nil -> Coq_formula_true
    | Coq_ctx.Coq_snoc (_UU0393_, b) ->
      smart_and _UU03a3_ (coq_PathCondition_to_Formula _UU03a3_ _UU0393_) b

    (** val coq_PathCondition_to_DList :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> DList.coq_DList **)

    let coq_PathCondition_to_DList _ pc k =
      Some (Coq_ctx.cat pc k)

    (** val simplify_formula :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> DList.coq_DList **)

    let rec simplify_formula _UU03a3_ fml = match fml with
    | Coq_formula_user (p, ts) ->
      DList.singleton _UU03a3_ (Coq_formula_user (p,
        (RiscvPmpBase.pevals _UU03a3_
          (match p with
           | Coq_gen_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_check_perms ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_privilege)
           | Coq_pmp_check_rwx ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)
           | Coq_sub_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_access_type)
           | Coq_access_pmp_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_pmpcfgperm)
           | Coq_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)
           | Coq_not_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_prev_addr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_xlenbits)
           | Coq_in_entries ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               RiscvPmpBase.ty_pmpentry)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_in_mmio _ ->
             Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits))
          ts)))
    | Coq_formula_bool t ->
      simplify_bool _UU03a3_ (RiscvPmpBase.peval _UU03a3_ Coq_ty.Coq_bool t)
    | Coq_formula_prop (_, _, _) -> DList.singleton _UU03a3_ fml
    | Coq_formula_relop (_UU03c3_, op, t1, t2) ->
      simplify_relop _UU03a3_ _UU03c3_ op t1 t2
    | Coq_formula_true -> DList.empty _UU03a3_
    | Coq_formula_false -> DList.error _UU03a3_
    | Coq_formula_and (f1, f2) ->
      DList.cat _UU03a3_ (simplify_formula _UU03a3_ f1)
        (simplify_formula _UU03a3_ f2)
    | Coq_formula_or (f1, f2) ->
      (match DList.run _UU03a3_ (simplify_formula _UU03a3_ f1) with
       | Some f1' ->
         (match f1' with
          | Coq_ctx.Coq_nil -> DList.empty _UU03a3_
          | Coq_ctx.Coq_snoc (_, _) ->
            (match DList.run _UU03a3_ (simplify_formula _UU03a3_ f2) with
             | Some f2' ->
               (match f2' with
                | Coq_ctx.Coq_nil -> DList.empty _UU03a3_
                | Coq_ctx.Coq_snoc (_, _) ->
                  DList.singleton _UU03a3_ (Coq_formula_or
                    ((coq_PathCondition_to_Formula _UU03a3_ f1'),
                    (coq_PathCondition_to_Formula _UU03a3_ f2'))))
             | None -> coq_PathCondition_to_DList _UU03a3_ f1'))
       | None -> simplify_formula _UU03a3_ f2)

    (** val simplify_pathcondition :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> DList.coq_DList **)

    let rec simplify_pathcondition _UU03a3_ = function
    | Coq_ctx.Coq_nil -> DList.empty _UU03a3_
    | Coq_ctx.Coq_snoc (c0, f) ->
      DList.cat _UU03a3_ (simplify_pathcondition _UU03a3_ c0)
        (simplify_formula _UU03a3_ f)

    (** val occurs_check_lt :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term option **)

    let occurs_check_lt _UU03a3_ x xIn _UU03c3_ t = match t with
    | RiscvPmpBase.Coq_term_var (_, _, yIn) ->
      (match PeanoNat.Nat.ltb xIn yIn with
       | Coq_true ->
         RiscvPmpBase.occurs_check (RiscvPmpBase.occurs_check_term _UU03c3_)
           _UU03a3_ x xIn t
       | Coq_false -> None)
    | _ ->
      RiscvPmpBase.occurs_check (RiscvPmpBase.occurs_check_term _UU03c3_)
        _UU03a3_ x xIn t

    (** val try_unify_bool :
        coq_World -> RiscvPmpBase.coq_Term -> (coq_World, coq_Tri) sigT option **)

    let try_unify_bool w = function
    | RiscvPmpBase.Coq_term_var (l, _, lIn) ->
      Some (Coq_existT
        ((wsubst w l Coq_ty.Coq_bool lIn (RiscvPmpBase.Coq_term_val
           (Coq_ty.Coq_bool, (Obj.magic Coq_true)))),
        (Coq_tri_cons
        ((wsubst w l Coq_ty.Coq_bool lIn (RiscvPmpBase.Coq_term_val
           (Coq_ty.Coq_bool, (Obj.magic Coq_true)))),
        l, Coq_ty.Coq_bool, lIn, (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_bool,
        (Obj.magic Coq_true))), Coq_tri_id))))
    | RiscvPmpBase.Coq_term_val (_, _) -> None
    | RiscvPmpBase.Coq_term_binop (_, _, _, _, _, _) -> None
    | RiscvPmpBase.Coq_term_unop (_, _, op, t0) ->
      (match op with
       | Coq_uop.Coq_not ->
         (match t0 with
          | RiscvPmpBase.Coq_term_var (l, _, lIn) ->
            Some (Coq_existT
              ((wsubst w l Coq_ty.Coq_bool lIn (RiscvPmpBase.Coq_term_val
                 (Coq_ty.Coq_bool, (Obj.magic Coq_false)))),
              (Coq_tri_cons
              ((wsubst w l Coq_ty.Coq_bool lIn (RiscvPmpBase.Coq_term_val
                 (Coq_ty.Coq_bool, (Obj.magic Coq_false)))),
              l, Coq_ty.Coq_bool, lIn, (RiscvPmpBase.Coq_term_val
              (Coq_ty.Coq_bool, (Obj.magic Coq_false))), Coq_tri_id))))
          | RiscvPmpBase.Coq_term_val (_, _) -> None
          | RiscvPmpBase.Coq_term_binop (_, _, _, _, _, _) -> None
          | RiscvPmpBase.Coq_term_unop (_, _, _, _) -> None
          | _ -> assert false (* absurd case *))
       | _ -> assert false (* absurd case *))
    | _ -> assert false (* absurd case *)

    (** val try_unify_eq :
        coq_World -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term ->
        RiscvPmpBase.coq_Term -> (coq_World, coq_Tri) sigT option **)

    let try_unify_eq w _ t1 t2 =
      match t1 with
      | RiscvPmpBase.Coq_term_var (_UU03c2_, _UU03c3_, _UU03c2_In_UU03a3_) ->
        (match occurs_check_lt w.wctx { Binding.name = _UU03c2_;
                 Binding.coq_type = _UU03c3_ } _UU03c2_In_UU03a3_ _UU03c3_ t2 with
         | Some t ->
           Some (Coq_existT
             ((wsubst w _UU03c2_ _UU03c3_ _UU03c2_In_UU03a3_ t),
             (Coq_tri_cons
             ((wsubst w _UU03c2_ _UU03c3_ _UU03c2_In_UU03a3_ t), _UU03c2_,
             _UU03c3_, _UU03c2_In_UU03a3_, t, Coq_tri_id))))
         | None -> None)
      | _ -> None

    (** val try_unify_formula :
        coq_World -> coq_Formula -> (coq_World, coq_Tri) sigT option **)

    let try_unify_formula w = function
    | Coq_formula_bool t -> try_unify_bool w t
    | Coq_formula_relop (_, rop, t1, t2) ->
      (match rop with
       | Coq_bop.Coq_eq _UU03c3_0 ->
         (match try_unify_eq w _UU03c3_0 t1 t2 with
          | Some r -> Some r
          | None -> try_unify_eq w _UU03c3_0 t2 t1)
       | _ -> None)
    | _ -> None

    (** val unify_formula :
        coq_World -> coq_Formula -> (coq_World, (coq_Tri, coq_PathCondition)
        prod) sigT **)

    let unify_formula w0 f =
      match try_unify_formula w0 f with
      | Some s ->
        let Coq_existT (w1, _UU03bd_01) = s in
        Coq_existT (w1, (Coq_pair (_UU03bd_01, Coq_ctx.Coq_nil)))
      | None ->
        Coq_existT (w0, (Coq_pair (Coq_tri_id, (Coq_ctx.Coq_snoc
          (Coq_ctx.Coq_nil, f)))))

    (** val unify_pathcondition :
        coq_World -> coq_PathCondition -> (coq_World, (coq_Tri,
        coq_PathCondition) prod) sigT **)

    let rec unify_pathcondition w0 = function
    | Coq_ctx.Coq_nil ->
      Coq_existT (w0, (Coq_pair (Coq_tri_id, Coq_ctx.Coq_nil)))
    | Coq_ctx.Coq_snoc (_UU0393_, b) ->
      let s = unify_pathcondition w0 _UU0393_ in
      let Coq_existT (x, p) = s in
      let Coq_pair (t, p0) = p in
      let s0 =
        unify_formula x
          (persist (persistent_subst sub_formula) w0 b x
            (acc_triangular w0 x t))
      in
      let Coq_existT (x0, p1) = s0 in
      let Coq_pair (t0, p2) = p1 in
      Coq_existT (x0, (Coq_pair ((tri_comp w0 x x0 t t0),
      (Coq_ctx.cat
        (persist (persistent_subst (RiscvPmpBase.subst_ctx sub_formula)) x p0
          x0 (acc_triangular x x0 t0))
        p2))))

    (** val formula_eqb_clause_3 :
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> coq_Formula -> bool) -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_PurePredicate ->
        (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env ->
        coq_PurePredicate -> sumbool -> (Coq_ty.coq_Ty,
        RiscvPmpBase.coq_Term) Coq_env.coq_Env -> bool **)

    let formula_eqb_clause_3 _ _UU03a3_ p ts1 _ refine ts2 =
      match refine with
      | Coq_left ->
        Coq_env.eqb_hom (RiscvPmpBase.coq_Term_eqb _UU03a3_)
          (match p with
           | Coq_gen_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_access ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
           | Coq_pmp_check_perms ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_privilege)
           | Coq_pmp_check_rwx ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_pmpcfg_ent)), RiscvPmpBase.ty_access_type)
           | Coq_sub_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_access_type)
           | Coq_access_pmp_perm ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_pmpcfgperm)
           | Coq_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_pmpcfg_ent)),
               RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)
           | Coq_not_within_cfg ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
               RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_prev_addr ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
               RiscvPmpBase.ty_xlenbits)
           | Coq_in_entries ->
             Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
               (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
               RiscvPmpBase.ty_pmpentry)), (Coq_ty.Coq_list
               RiscvPmpBase.ty_pmpentry))
           | Coq_in_mmio _ ->
             Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits))
          ts1 ts2
      | Coq_right -> Coq_false

    (** val formula_eqb_clause_2 :
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> coq_Formula -> bool) -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
        Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
        -> Coq_ty.coq_Ty -> sumbool -> Coq_bop.coq_RelOp ->
        RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> bool **)

    let formula_eqb_clause_2 _ _UU03a3_ _UU03c3_ op1 t11 t12 _ refine op2 t21 t22 =
      match refine with
      | Coq_left ->
        (match match eq_dec
                       (Coq_bop.coq_RelOp_EqDec RiscvPmpBase.typedeclkit
                         _UU03c3_)
                       op1 op2 with
               | Coq_left ->
                 RiscvPmpBase.coq_Term_eqb _UU03a3_ _UU03c3_ t11 t21
               | Coq_right -> Coq_false with
         | Coq_true -> RiscvPmpBase.coq_Term_eqb _UU03a3_ _UU03c3_ t12 t22
         | Coq_false -> Coq_false)
      | Coq_right -> Coq_false

    (** val formula_eqb :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> coq_Formula -> bool **)

    let rec formula_eqb _UU03a3_ f1 f2 =
      match f1 with
      | Coq_formula_user (p, ts) ->
        (match f2 with
         | Coq_formula_user (p0, ts0) ->
           (match _UU1d477__eq_dec p p0 with
            | Coq_left ->
              Coq_env.eqb_hom (RiscvPmpBase.coq_Term_eqb _UU03a3_)
                (match p with
                 | Coq_gen_pmp_access ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                     ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                     (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                     RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
                     (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                     RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
                 | Coq_pmp_access ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                     ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)),
                     (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                     RiscvPmpBase.ty_privilege)), RiscvPmpBase.ty_access_type)
                 | Coq_pmp_check_perms ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                     (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfg_ent)),
                     RiscvPmpBase.ty_access_type)), RiscvPmpBase.ty_privilege)
                 | Coq_pmp_check_rwx ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_pmpcfg_ent)),
                     RiscvPmpBase.ty_access_type)
                 | Coq_sub_perm ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_access_type)),
                     RiscvPmpBase.ty_access_type)
                 | Coq_access_pmp_perm ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_access_type)),
                     RiscvPmpBase.ty_pmpcfgperm)
                 | Coq_within_cfg ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                     ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)),
                     RiscvPmpBase.ty_pmpcfg_ent)),
                     RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_xlenbits)
                 | Coq_not_within_cfg ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
                     RiscvPmpBase.ty_pmpentry))
                 | Coq_prev_addr ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                     (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
                     (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                     RiscvPmpBase.ty_xlenbits)
                 | Coq_in_entries ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                     (Coq_ctx.Coq_nil, RiscvPmpBase.ty_pmpcfgidx)),
                     RiscvPmpBase.ty_pmpentry)), (Coq_ty.Coq_list
                     RiscvPmpBase.ty_pmpentry))
                 | Coq_in_mmio _ ->
                   Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits))
                ts ts0
            | Coq_right -> Coq_false)
         | _ -> Coq_false)
      | Coq_formula_bool t ->
        (match f2 with
         | Coq_formula_bool t0 ->
           RiscvPmpBase.coq_Term_eqb _UU03a3_ Coq_ty.Coq_bool t t0
         | _ -> Coq_false)
      | Coq_formula_prop (_, _, _) -> Coq_false
      | Coq_formula_relop (_UU03c3_, rop, t1, t2) ->
        (match f2 with
         | Coq_formula_relop (_UU03c3_0, rop0, t3, t4) ->
           (match eq_dec
                    (Coq_ty.coq_Ty_eq_dec RiscvPmpBase.typedeclkit
                      RiscvPmpBase.typedenotekit RiscvPmpBase.typedefkit)
                    _UU03c3_ _UU03c3_0 with
            | Coq_left ->
              (match match eq_dec
                             (Coq_bop.coq_RelOp_EqDec
                               RiscvPmpBase.typedeclkit _UU03c3_)
                             rop rop0 with
                     | Coq_left ->
                       RiscvPmpBase.coq_Term_eqb _UU03a3_ _UU03c3_ t1 t3
                     | Coq_right -> Coq_false with
               | Coq_true -> RiscvPmpBase.coq_Term_eqb _UU03a3_ _UU03c3_ t2 t4
               | Coq_false -> Coq_false)
            | Coq_right -> Coq_false)
         | _ -> Coq_false)
      | Coq_formula_true ->
        (match f2 with
         | Coq_formula_true -> Coq_true
         | _ -> Coq_false)
      | Coq_formula_false ->
        (match f2 with
         | Coq_formula_false -> Coq_true
         | _ -> Coq_false)
      | Coq_formula_and (f3, f4) ->
        (match f2 with
         | Coq_formula_and (f5, f6) ->
           (match formula_eqb _UU03a3_ f3 f5 with
            | Coq_true -> formula_eqb _UU03a3_ f4 f6
            | Coq_false -> Coq_false)
         | _ -> Coq_false)
      | Coq_formula_or (f3, f4) ->
        (match f2 with
         | Coq_formula_or (f5, f6) ->
           (match formula_eqb _UU03a3_ f3 f5 with
            | Coq_true -> formula_eqb _UU03a3_ f4 f6
            | Coq_false -> Coq_false)
         | _ -> Coq_false)

    (** val smart_or :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> coq_Formula -> coq_Formula **)

    let smart_or _ f1 f2 =
      match f1 with
      | Coq_formula_true ->
        (match f2 with
         | Coq_formula_false -> f1
         | _ -> Coq_formula_true)
      | Coq_formula_false -> f2
      | _ ->
        (match f2 with
         | Coq_formula_true -> Coq_formula_true
         | Coq_formula_false -> f1
         | _ -> Coq_formula_or (f1, f2))

    (** val formula_simplifies :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Formula -> coq_Formula -> coq_Formula option **)

    let rec formula_simplifies _UU03a3_ hyp fact =
      match formula_eqb _UU03a3_ hyp fact with
      | Coq_true -> Some Coq_formula_true
      | Coq_false ->
        (match hyp with
         | Coq_formula_relop (_UU03c3_, op, t1, t2) ->
           let hyp' = peval_formula_relop_neg _UU03a3_ _UU03c3_ op t1 t2 in
           (match formula_eqb _UU03a3_ hyp' fact with
            | Coq_true -> Some Coq_formula_false
            | Coq_false -> None)
         | Coq_formula_and (hyp1, hyp2) ->
           (match formula_simplifies _UU03a3_ hyp1 fact with
            | Some hyp1' ->
              (match formula_simplifies _UU03a3_ hyp2 fact with
               | Some hyp2' -> Some (smart_and _UU03a3_ hyp1' hyp2')
               | None -> Some (smart_and _UU03a3_ hyp1' hyp2))
            | None ->
              (match formula_simplifies _UU03a3_ hyp2 fact with
               | Some hyp2' -> Some (smart_and _UU03a3_ hyp1 hyp2')
               | None -> None))
         | Coq_formula_or (hyp1, hyp2) ->
           (match formula_simplifies _UU03a3_ hyp1 fact with
            | Some hyp1' ->
              (match formula_simplifies _UU03a3_ hyp2 fact with
               | Some hyp2' -> Some (smart_or _UU03a3_ hyp1' hyp2')
               | None -> Some (smart_or _UU03a3_ hyp1' hyp2))
            | None ->
              (match formula_simplifies _UU03a3_ hyp2 fact with
               | Some hyp2' -> Some (smart_or _UU03a3_ hyp1 hyp2')
               | None -> None))
         | _ -> None)

    (** val assumption_formula :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> coq_Formula -> coq_PathCondition ->
        coq_PathCondition **)

    let rec assumption_formula _UU03a3_ c f k =
      match c with
      | Coq_ctx.Coq_nil -> Coq_ctx.Coq_snoc (k, f)
      | Coq_ctx.Coq_snoc (c0, f') ->
        (match formula_simplifies _UU03a3_ f f' with
         | Some f2 -> assumption_formula _UU03a3_ c0 f2 k
         | None -> assumption_formula _UU03a3_ c0 f k)

    (** val assumption_pathcondition :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> coq_PathCondition -> coq_PathCondition ->
        coq_PathCondition **)

    let rec assumption_pathcondition _UU03a3_ c fs k =
      match fs with
      | Coq_ctx.Coq_nil -> k
      | Coq_ctx.Coq_snoc (fs0, f) ->
        assumption_formula _UU03a3_ c f
          (assumption_pathcondition _UU03a3_ c fs0 k)

    (** val solver_generic : coq_Solver **)

    let solver_generic w0 c0 =
      match DList.run w0.wctx (simplify_pathcondition w0.wctx c0) with
      | Some c1 ->
        Some
          (unify_pathcondition w0
            (assumption_pathcondition w0.wctx w0.wco c1 Coq_ctx.Coq_nil))
      | None -> None
   end

  (** val combined_solver : coq_Solver **)

  let combined_solver =
    let gg =
      solver_compose GenericSolver.solver_generic GenericSolver.solver_generic
    in
    let ggu = solver_compose gg solver in
    solver_compose ggu (solver_compose ggu gg)

  type 'a coq_CPureSpec = __

  module CPureSpec =
   struct
    module Coq_notations =
     struct
     end
   end

  type 'a coq_CHeapSpec = __

  module CHeapSpec =
   struct
    module Coq_notations =
     struct
     end
   end

  module CStatistics =
   struct
    type coq_PropShape =
    | Coq_psfork of coq_PropShape * coq_PropShape
    | Coq_psquant of coq_PropShape
    | Coq_pspruned
    | Coq_psfinish
    | Coq_psother

    (** val coq_PropShape_rect :
        (coq_PropShape -> 'a1 -> coq_PropShape -> 'a1 -> 'a1) ->
        (coq_PropShape -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_PropShape
        -> 'a1 **)

    let rec coq_PropShape_rect f f0 f1 f2 f3 = function
    | Coq_psfork (p0, q) ->
      f p0 (coq_PropShape_rect f f0 f1 f2 f3 p0) q
        (coq_PropShape_rect f f0 f1 f2 f3 q)
    | Coq_psquant p0 -> f0 p0 (coq_PropShape_rect f f0 f1 f2 f3 p0)
    | Coq_pspruned -> f1
    | Coq_psfinish -> f2
    | Coq_psother -> f3

    (** val coq_PropShape_rec :
        (coq_PropShape -> 'a1 -> coq_PropShape -> 'a1 -> 'a1) ->
        (coq_PropShape -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_PropShape
        -> 'a1 **)

    let rec coq_PropShape_rec f f0 f1 f2 f3 = function
    | Coq_psfork (p0, q) ->
      f p0 (coq_PropShape_rec f f0 f1 f2 f3 p0) q
        (coq_PropShape_rec f f0 f1 f2 f3 q)
    | Coq_psquant p0 -> f0 p0 (coq_PropShape_rec f f0 f1 f2 f3 p0)
    | Coq_pspruned -> f1
    | Coq_psfinish -> f2
    | Coq_psother -> f3

    (** val shape_to_stats : coq_PropShape -> coq_Stats **)

    let rec shape_to_stats = function
    | Coq_psfork (p, q) -> plus_stats (shape_to_stats p) (shape_to_stats q)
    | Coq_psquant p -> shape_to_stats p
    | Coq_pspruned -> { branches = (Npos Coq_xH); pruned = (Npos Coq_xH) }
    | Coq_psfinish -> { branches = (Npos Coq_xH); pruned = N0 }
    | Coq_psother -> { branches = N0; pruned = N0 }

    type coq_ShallowStats = coq_Stats

    (** val stats : coq_ShallowStats -> coq_Stats **)

    let stats shallowStats =
      shallowStats

    (** val stats_true : coq_ShallowStats **)

    let stats_true =
      { branches = (Npos Coq_xH); pruned = (Npos Coq_xH) }

    (** val stats_false : coq_ShallowStats **)

    let stats_false =
      { branches = (Npos Coq_xH); pruned = (Npos Coq_xH) }

    (** val stats_finish : coq_ShallowStats **)

    let stats_finish =
      { branches = (Npos Coq_xH); pruned = N0 }

    (** val stats_true' : coq_ShallowStats **)

    let stats_true' =
      { branches = N0; pruned = N0 }

    (** val stats_false' : coq_ShallowStats **)

    let stats_false' =
      { branches = N0; pruned = N0 }

    (** val stats_eq : 'a1 -> 'a1 -> coq_ShallowStats **)

    let stats_eq _ _ =
      { branches = N0; pruned = N0 }

    (** val stats_zle : coq_Z -> coq_Z -> coq_ShallowStats **)

    let stats_zle _ _ =
      { branches = N0; pruned = N0 }

    (** val stats_and :
        coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats **)

    let stats_and h h0 =
      plus_stats (stats h) (stats h0)

    (** val stats_or :
        coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats **)

    let stats_or h h0 =
      plus_stats (stats h) (stats h0)

    (** val stats_impl :
        coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats **)

    let stats_impl h h0 =
      plus_stats (stats h) (stats h0)

    (** val stats_forall :
        (__ -> __) -> ('a1 -> coq_ShallowStats) -> coq_ShallowStats **)

    let stats_forall undefined sP =
      Obj.magic sP (undefined __)

    (** val stats_exists :
        (__ -> __) -> ('a1 -> coq_ShallowStats) -> coq_ShallowStats **)

    let stats_exists undefined sP =
      Obj.magic sP (undefined __)
   end

  type coq_DebugAsn = { debug_asn_pathcondition : coq_PathCondition;
                        debug_asn_heap : coq_SHeap }

  (** val debug_asn_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugAsn -> coq_PathCondition **)

  let debug_asn_pathcondition _ d =
    d.debug_asn_pathcondition

  (** val debug_asn_heap :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugAsn -> coq_SHeap **)

  let debug_asn_heap _ d =
    d.debug_asn_heap

  (** val coq_SubstDebugAsn : coq_DebugAsn RiscvPmpBase.coq_Subst **)

  let coq_SubstDebugAsn _UU03a3_0 d _UU03a3_1 _UU03b6_01 =
    let { debug_asn_pathcondition = pc; debug_asn_heap = h } = d in
    { debug_asn_pathcondition =
    (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) _UU03a3_0 pc
      _UU03a3_1 _UU03b6_01);
    debug_asn_heap =
    (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstList coq_SubstChunk) _UU03a3_0
      h _UU03a3_1 _UU03b6_01) }

  (** val coq_SubstSUDebugAsn :
      (RiscvPmpBase.coq_WeakensTo, coq_DebugAsn) RiscvPmpBase.coq_SubstSU **)

  let coq_SubstSUDebugAsn _UU03a3_0 _UU03a3_1 d _UU03b6_01 =
    let { debug_asn_pathcondition = pc; debug_asn_heap = h } = d in
    { debug_asn_pathcondition =
    (RiscvPmpBase.substSU
      (RiscvPmpBase.substSU_ctx (subSU_formula RiscvPmpBase.substUniv_weaken))
      _UU03a3_0 _UU03a3_1 pc _UU03b6_01);
    debug_asn_heap =
    (RiscvPmpBase.substSU
      (RiscvPmpBase.substSU_list
        (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken))
      _UU03a3_0 _UU03a3_1 h _UU03b6_01) }

  (** val coq_SubstLawsDebugAsn : coq_DebugAsn RiscvPmpBase.coq_SubstLaws **)

  let coq_SubstLawsDebugAsn =
    RiscvPmpBase.Build_SubstLaws

  (** val coq_OccursCheckDebugAsn :
      coq_DebugAsn RiscvPmpBase.coq_OccursCheck **)

  let coq_OccursCheckDebugAsn _UU03a3_ x xIn d =
    let { debug_asn_pathcondition = pc; debug_asn_heap = h } = d in
    Coq_option.bind
      (RiscvPmpBase.occurs_check
        (RiscvPmpBase.occurscheck_ctx coq_OccursCheckFormula) _UU03a3_ x xIn
        pc)
      (fun pc' ->
      Coq_option.bind
        (RiscvPmpBase.occurs_check
          (RiscvPmpBase.occurs_check_list coq_OccursCheckChunk) _UU03a3_ x
          xIn h)
        (fun h' -> Some { debug_asn_pathcondition = pc'; debug_asn_heap =
        h' }))

  type coq_DebugConsumeChunk = { debug_consume_chunk_pathcondition : 
                                 coq_PathCondition;
                                 debug_consume_chunk_heap : coq_SHeap;
                                 debug_consume_chunk_chunk : coq_Chunk }

  (** val debug_consume_chunk_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugConsumeChunk -> coq_PathCondition **)

  let debug_consume_chunk_pathcondition _ d =
    d.debug_consume_chunk_pathcondition

  (** val debug_consume_chunk_heap :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugConsumeChunk -> coq_SHeap **)

  let debug_consume_chunk_heap _ d =
    d.debug_consume_chunk_heap

  (** val debug_consume_chunk_chunk :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugConsumeChunk -> coq_Chunk **)

  let debug_consume_chunk_chunk _ d =
    d.debug_consume_chunk_chunk

  type coq_EDebugConsumeChunk = { edebug_consume_chunk_pathcondition : 
                                  coq_EFormula list;
                                  edebug_consume_chunk_heap : coq_EChunk list;
                                  edebug_consume_chunk_chunk : coq_EChunk }

  (** val edebug_consume_chunk_pathcondition :
      coq_EDebugConsumeChunk -> coq_EFormula list **)

  let edebug_consume_chunk_pathcondition e =
    e.edebug_consume_chunk_pathcondition

  (** val edebug_consume_chunk_heap :
      coq_EDebugConsumeChunk -> coq_EChunk list **)

  let edebug_consume_chunk_heap e =
    e.edebug_consume_chunk_heap

  (** val edebug_consume_chunk_chunk :
      coq_EDebugConsumeChunk -> coq_EChunk **)

  let edebug_consume_chunk_chunk e =
    e.edebug_consume_chunk_chunk

  (** val coq_Erase_DebugConsumeChunk :
      (coq_DebugConsumeChunk, coq_EDebugConsumeChunk) RiscvPmpBase.coq_Erase **)

  let coq_Erase_DebugConsumeChunk _UU03a3_ pat =
    let { debug_consume_chunk_pathcondition = pc; debug_consume_chunk_heap =
      h; debug_consume_chunk_chunk = c } = pat
    in
    { edebug_consume_chunk_pathcondition =
    (RiscvPmpBase.erase (RiscvPmpBase.erase_Ctx erase_Formula) _UU03a3_ pc);
    edebug_consume_chunk_heap =
    (RiscvPmpBase.erase (RiscvPmpBase.erase_List coq_Erase_Chunk) _UU03a3_ h);
    edebug_consume_chunk_chunk =
    (RiscvPmpBase.erase coq_Erase_Chunk _UU03a3_ c) }

  (** val coq_SubstDebugConsumeChunk :
      coq_DebugConsumeChunk RiscvPmpBase.coq_Subst **)

  let coq_SubstDebugConsumeChunk _UU03a3_0 d _UU03a3_1 _UU03b6_01 =
    let { debug_consume_chunk_pathcondition = pc; debug_consume_chunk_heap =
      h; debug_consume_chunk_chunk = c } = d
    in
    { debug_consume_chunk_pathcondition =
    (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) _UU03a3_0 pc
      _UU03a3_1 _UU03b6_01);
    debug_consume_chunk_heap =
    (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstList coq_SubstChunk) _UU03a3_0
      h _UU03a3_1 _UU03b6_01);
    debug_consume_chunk_chunk =
    (RiscvPmpBase.subst coq_SubstChunk _UU03a3_0 c _UU03a3_1 _UU03b6_01) }

  (** val coq_SubstSUDebugConsumeChunk :
      'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugConsumeChunk)
      RiscvPmpBase.coq_SubstSU **)

  let coq_SubstSUDebugConsumeChunk h _UU03a3_0 _UU03a3_1 d _UU03b6_01 =
    let { debug_consume_chunk_pathcondition = pc; debug_consume_chunk_heap =
      h0; debug_consume_chunk_chunk = c } = d
    in
    { debug_consume_chunk_pathcondition =
    (RiscvPmpBase.substSU (RiscvPmpBase.substSU_ctx (subSU_formula h))
      _UU03a3_0 _UU03a3_1 pc _UU03b6_01);
    debug_consume_chunk_heap =
    (RiscvPmpBase.substSU (RiscvPmpBase.substSU_list (coq_SubstSUChunk h))
      _UU03a3_0 _UU03a3_1 h0 _UU03b6_01);
    debug_consume_chunk_chunk =
    (RiscvPmpBase.substSU (coq_SubstSUChunk h) _UU03a3_0 _UU03a3_1 c
      _UU03b6_01) }

  (** val coq_SubstLawsDebugConsumeChunk :
      coq_DebugConsumeChunk RiscvPmpBase.coq_SubstLaws **)

  let coq_SubstLawsDebugConsumeChunk =
    RiscvPmpBase.Build_SubstLaws

  (** val coq_OccursCheckDebugConsumeChunk :
      coq_DebugConsumeChunk RiscvPmpBase.coq_OccursCheck **)

  let coq_OccursCheckDebugConsumeChunk _UU03a3_ x xIn d =
    let { debug_consume_chunk_pathcondition = pc; debug_consume_chunk_heap =
      h; debug_consume_chunk_chunk = c } = d
    in
    Coq_option.bind
      (RiscvPmpBase.occurs_check
        (RiscvPmpBase.occurscheck_ctx coq_OccursCheckFormula) _UU03a3_ x xIn
        pc)
      (fun pc' ->
      Coq_option.bind
        (RiscvPmpBase.occurs_check
          (RiscvPmpBase.occurs_check_list coq_OccursCheckChunk) _UU03a3_ x
          xIn h)
        (fun h' ->
        Coq_option.bind
          (RiscvPmpBase.occurs_check coq_OccursCheckChunk _UU03a3_ x xIn c)
          (fun c' -> Some { debug_consume_chunk_pathcondition = pc';
          debug_consume_chunk_heap = h'; debug_consume_chunk_chunk = c' })))

  type coq_DebugReadRegister = { debug_read_register_pathcondition : 
                                 coq_PathCondition;
                                 debug_read_register_heap : coq_SHeap;
                                 debug_read_register_type : Coq_ty.coq_Ty;
                                 debug_read_register_register : RiscvPmpBase.coq_Reg }

  (** val debug_read_register_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugReadRegister -> coq_PathCondition **)

  let debug_read_register_pathcondition _ d =
    d.debug_read_register_pathcondition

  (** val debug_read_register_heap :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugReadRegister -> coq_SHeap **)

  let debug_read_register_heap _ d =
    d.debug_read_register_heap

  (** val debug_read_register_type :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugReadRegister -> Coq_ty.coq_Ty **)

  let debug_read_register_type _ d =
    d.debug_read_register_type

  (** val debug_read_register_register :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugReadRegister -> RiscvPmpBase.coq_Reg **)

  let debug_read_register_register _ d =
    d.debug_read_register_register

  type coq_EDebugReadRegister = { edebug_read_register_pathcondition : 
                                  coq_EFormula list;
                                  edebug_read_register_heap : coq_EChunk list;
                                  edebug_read_register_type : Coq_ty.coq_Ty;
                                  edebug_read_register_register : RiscvPmpBase.coq_Reg }

  (** val edebug_read_register_pathcondition :
      coq_EDebugReadRegister -> coq_EFormula list **)

  let edebug_read_register_pathcondition e =
    e.edebug_read_register_pathcondition

  (** val edebug_read_register_heap :
      coq_EDebugReadRegister -> coq_EChunk list **)

  let edebug_read_register_heap e =
    e.edebug_read_register_heap

  (** val edebug_read_register_type :
      coq_EDebugReadRegister -> Coq_ty.coq_Ty **)

  let edebug_read_register_type e =
    e.edebug_read_register_type

  (** val edebug_read_register_register :
      coq_EDebugReadRegister -> RiscvPmpBase.coq_Reg **)

  let edebug_read_register_register e =
    e.edebug_read_register_register

  (** val coq_EraseDebugReadRegister :
      (coq_DebugReadRegister, coq_EDebugReadRegister) RiscvPmpBase.coq_Erase **)

  let coq_EraseDebugReadRegister _UU03a3_ pat =
    let { debug_read_register_pathcondition = pc; debug_read_register_heap =
      h; debug_read_register_type = debug_read_register_type0;
      debug_read_register_register = r } = pat
    in
    { edebug_read_register_pathcondition =
    (RiscvPmpBase.erase (RiscvPmpBase.erase_Ctx erase_Formula) _UU03a3_ pc);
    edebug_read_register_heap =
    (RiscvPmpBase.erase (RiscvPmpBase.erase_List coq_Erase_Chunk) _UU03a3_ h);
    edebug_read_register_type = debug_read_register_type0;
    edebug_read_register_register = r }

  (** val coq_SubstDebugReadRegister :
      coq_DebugReadRegister RiscvPmpBase.coq_Subst **)

  let coq_SubstDebugReadRegister _UU03a3_0 d _UU03a3_1 _UU03b6_01 =
    let { debug_read_register_pathcondition = pc; debug_read_register_heap =
      h; debug_read_register_type = debug_read_register_type0;
      debug_read_register_register = r } = d
    in
    { debug_read_register_pathcondition =
    (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) _UU03a3_0 pc
      _UU03a3_1 _UU03b6_01);
    debug_read_register_heap =
    (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstList coq_SubstChunk) _UU03a3_0
      h _UU03a3_1 _UU03b6_01);
    debug_read_register_type = debug_read_register_type0;
    debug_read_register_register = r }

  (** val coq_SubstSUDebugReadRegister :
      'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugReadRegister)
      RiscvPmpBase.coq_SubstSU **)

  let coq_SubstSUDebugReadRegister h _UU03a3_0 _UU03a3_1 d _UU03b6_01 =
    let { debug_read_register_pathcondition = pc; debug_read_register_heap =
      h0; debug_read_register_type = debug_read_register_type0;
      debug_read_register_register = r } = d
    in
    { debug_read_register_pathcondition =
    (RiscvPmpBase.substSU (RiscvPmpBase.substSU_ctx (subSU_formula h))
      _UU03a3_0 _UU03a3_1 pc _UU03b6_01);
    debug_read_register_heap =
    (RiscvPmpBase.substSU (RiscvPmpBase.substSU_list (coq_SubstSUChunk h))
      _UU03a3_0 _UU03a3_1 h0 _UU03b6_01);
    debug_read_register_type = debug_read_register_type0;
    debug_read_register_register = r }

  (** val coq_SubstLawsDebugReadRegister :
      coq_DebugReadRegister RiscvPmpBase.coq_SubstLaws **)

  let coq_SubstLawsDebugReadRegister =
    RiscvPmpBase.Build_SubstLaws

  (** val coq_OccursCheckDebugReadRegister :
      coq_DebugReadRegister RiscvPmpBase.coq_OccursCheck **)

  let coq_OccursCheckDebugReadRegister _UU03a3_ x xIn d =
    let { debug_read_register_pathcondition = pc; debug_read_register_heap =
      h; debug_read_register_type = debug_read_register_type0;
      debug_read_register_register = r } = d
    in
    Coq_option.bind
      (RiscvPmpBase.occurs_check
        (RiscvPmpBase.occurscheck_ctx coq_OccursCheckFormula) _UU03a3_ x xIn
        pc)
      (fun pc' ->
      Coq_option.bind
        (RiscvPmpBase.occurs_check
          (RiscvPmpBase.occurs_check_list coq_OccursCheckChunk) _UU03a3_ x
          xIn h)
        (fun h' -> Some { debug_read_register_pathcondition = pc';
        debug_read_register_heap = h'; debug_read_register_type =
        debug_read_register_type0; debug_read_register_register = r }))

  type coq_DebugWriteRegister = { debug_write_register_pathcondition : 
                                  coq_PathCondition;
                                  debug_write_register_heap : coq_SHeap;
                                  debug_write_register_type : Coq_ty.coq_Ty;
                                  debug_write_register_register : RiscvPmpBase.coq_Reg;
                                  debug_write_register_value : RiscvPmpBase.coq_Term }

  (** val debug_write_register_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugWriteRegister -> coq_PathCondition **)

  let debug_write_register_pathcondition _ d =
    d.debug_write_register_pathcondition

  (** val debug_write_register_heap :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugWriteRegister -> coq_SHeap **)

  let debug_write_register_heap _ d =
    d.debug_write_register_heap

  (** val debug_write_register_type :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugWriteRegister -> Coq_ty.coq_Ty **)

  let debug_write_register_type _ d =
    d.debug_write_register_type

  (** val debug_write_register_register :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugWriteRegister -> RiscvPmpBase.coq_Reg **)

  let debug_write_register_register _ d =
    d.debug_write_register_register

  (** val debug_write_register_value :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugWriteRegister -> RiscvPmpBase.coq_Term **)

  let debug_write_register_value _ d =
    d.debug_write_register_value

  type coq_EDebugWriteRegister = { edebug_write_register_pathcondition : 
                                   coq_EFormula list;
                                   edebug_write_register_heap : coq_EChunk
                                                                list;
                                   edebug_write_register_type : Coq_ty.coq_Ty;
                                   edebug_write_register_register : RiscvPmpBase.coq_Reg;
                                   edebug_write_register_value : RiscvPmpBase.coq_ETerm }

  (** val edebug_write_register_pathcondition :
      coq_EDebugWriteRegister -> coq_EFormula list **)

  let edebug_write_register_pathcondition e =
    e.edebug_write_register_pathcondition

  (** val edebug_write_register_heap :
      coq_EDebugWriteRegister -> coq_EChunk list **)

  let edebug_write_register_heap e =
    e.edebug_write_register_heap

  (** val edebug_write_register_type :
      coq_EDebugWriteRegister -> Coq_ty.coq_Ty **)

  let edebug_write_register_type e =
    e.edebug_write_register_type

  (** val edebug_write_register_register :
      coq_EDebugWriteRegister -> RiscvPmpBase.coq_Reg **)

  let edebug_write_register_register e =
    e.edebug_write_register_register

  (** val edebug_write_register_value :
      coq_EDebugWriteRegister -> RiscvPmpBase.coq_ETerm **)

  let edebug_write_register_value e =
    e.edebug_write_register_value

  (** val coq_EraseDebugWriteRegister :
      (coq_DebugWriteRegister, coq_EDebugWriteRegister) RiscvPmpBase.coq_Erase **)

  let coq_EraseDebugWriteRegister _UU03a3_ pat =
    let { debug_write_register_pathcondition = pc;
      debug_write_register_heap = h; debug_write_register_type =
      debug_write_register_type0; debug_write_register_register = r;
      debug_write_register_value = t } = pat
    in
    { edebug_write_register_pathcondition =
    (RiscvPmpBase.erase (RiscvPmpBase.erase_Ctx erase_Formula) _UU03a3_ pc);
    edebug_write_register_heap =
    (RiscvPmpBase.erase (RiscvPmpBase.erase_List coq_Erase_Chunk) _UU03a3_ h);
    edebug_write_register_type = debug_write_register_type0;
    edebug_write_register_register = r; edebug_write_register_value =
    (RiscvPmpBase.erase (RiscvPmpBase.erase_Term debug_write_register_type0)
      _UU03a3_ t) }

  (** val coq_SubstDebugWriteRegister :
      coq_DebugWriteRegister RiscvPmpBase.coq_Subst **)

  let coq_SubstDebugWriteRegister _UU03a3_0 d _UU03a3_1 _UU03b6_01 =
    let { debug_write_register_pathcondition = pc;
      debug_write_register_heap = h; debug_write_register_type =
      debug_write_register_type0; debug_write_register_register = r;
      debug_write_register_value = t } = d
    in
    { debug_write_register_pathcondition =
    (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) _UU03a3_0 pc
      _UU03a3_1 _UU03b6_01);
    debug_write_register_heap =
    (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstList coq_SubstChunk) _UU03a3_0
      h _UU03a3_1 _UU03b6_01);
    debug_write_register_type = debug_write_register_type0;
    debug_write_register_register = r; debug_write_register_value =
    (RiscvPmpBase.subst
      (RiscvPmpBase.coq_SubstTerm debug_write_register_type0) _UU03a3_0 t
      _UU03a3_1 _UU03b6_01) }

  (** val coq_SubstSUDebugWriteRegister :
      'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugWriteRegister)
      RiscvPmpBase.coq_SubstSU **)

  let coq_SubstSUDebugWriteRegister h _UU03a3_0 _UU03a3_1 d _UU03b6_01 =
    let { debug_write_register_pathcondition = pc;
      debug_write_register_heap = h0; debug_write_register_type =
      debug_write_register_type0; debug_write_register_register = r;
      debug_write_register_value = t } = d
    in
    { debug_write_register_pathcondition =
    (RiscvPmpBase.substSU (RiscvPmpBase.substSU_ctx (subSU_formula h))
      _UU03a3_0 _UU03a3_1 pc _UU03b6_01);
    debug_write_register_heap =
    (RiscvPmpBase.substSU (RiscvPmpBase.substSU_list (coq_SubstSUChunk h))
      _UU03a3_0 _UU03a3_1 h0 _UU03b6_01);
    debug_write_register_type = debug_write_register_type0;
    debug_write_register_register = r; debug_write_register_value =
    (RiscvPmpBase.substSU
      (RiscvPmpBase.coq_SubstSUTerm h debug_write_register_type0) _UU03a3_0
      _UU03a3_1 t _UU03b6_01) }

  (** val coq_SubstLawsDebugWriteRegister :
      coq_DebugWriteRegister RiscvPmpBase.coq_SubstLaws **)

  let coq_SubstLawsDebugWriteRegister =
    RiscvPmpBase.Build_SubstLaws

  (** val coq_OccursCheckDebugWriteRegister :
      coq_DebugWriteRegister RiscvPmpBase.coq_OccursCheck **)

  let coq_OccursCheckDebugWriteRegister _UU03a3_ x xIn d =
    let { debug_write_register_pathcondition = pc;
      debug_write_register_heap = h; debug_write_register_type =
      debug_write_register_type0; debug_write_register_register = r;
      debug_write_register_value = t } = d
    in
    Coq_option.bind
      (RiscvPmpBase.occurs_check
        (RiscvPmpBase.occurscheck_ctx coq_OccursCheckFormula) _UU03a3_ x xIn
        pc)
      (fun pc' ->
      Coq_option.bind
        (RiscvPmpBase.occurs_check
          (RiscvPmpBase.occurs_check_list coq_OccursCheckChunk) _UU03a3_ x
          xIn h)
        (fun h' ->
        Coq_option.bind
          (RiscvPmpBase.occurs_check
            (RiscvPmpBase.occurs_check_term debug_write_register_type0)
            _UU03a3_ x xIn t)
          (fun t' -> Some { debug_write_register_pathcondition = pc';
          debug_write_register_heap = h'; debug_write_register_type =
          debug_write_register_type0; debug_write_register_register = r;
          debug_write_register_value = t' })))

  type coq_DebugString = { debug_string_pathcondition : coq_PathCondition;
                           debug_string_message : string }

  (** val debug_string_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugString -> coq_PathCondition **)

  let debug_string_pathcondition _ d =
    d.debug_string_pathcondition

  (** val debug_string_message :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugString -> string **)

  let debug_string_message _ d =
    d.debug_string_message

  type coq_EDebugString = { edebug_string_pathcondition : coq_EFormula list;
                            edebug_string_message : string }

  (** val edebug_string_pathcondition :
      coq_EDebugString -> coq_EFormula list **)

  let edebug_string_pathcondition e =
    e.edebug_string_pathcondition

  (** val edebug_string_message : coq_EDebugString -> string **)

  let edebug_string_message e =
    e.edebug_string_message

  (** val coq_EraseDebugString :
      (coq_DebugString, coq_EDebugString) RiscvPmpBase.coq_Erase **)

  let coq_EraseDebugString _UU03a3_ pat =
    let { debug_string_pathcondition = pc; debug_string_message = s } = pat in
    { edebug_string_pathcondition =
    (RiscvPmpBase.erase (RiscvPmpBase.erase_Ctx erase_Formula) _UU03a3_ pc);
    edebug_string_message = s }

  (** val coq_SubstDebugString : coq_DebugString RiscvPmpBase.coq_Subst **)

  let coq_SubstDebugString _UU03a3_0 d _UU03a3_1 _UU03b6_01 =
    let { debug_string_pathcondition = pc; debug_string_message = s } = d in
    { debug_string_pathcondition =
    (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) _UU03a3_0 pc
      _UU03a3_1 _UU03b6_01);
    debug_string_message = s }

  (** val coq_SubstSUDebugString :
      (RiscvPmpBase.coq_WeakensTo, coq_DebugString) RiscvPmpBase.coq_SubstSU **)

  let coq_SubstSUDebugString _UU03a3_0 _UU03a3_1 d _UU03b6_01 =
    let { debug_string_pathcondition = pc; debug_string_message = s } = d in
    { debug_string_pathcondition =
    (RiscvPmpBase.substSU
      (RiscvPmpBase.substSU_ctx (subSU_formula RiscvPmpBase.substUniv_weaken))
      _UU03a3_0 _UU03a3_1 pc _UU03b6_01);
    debug_string_message = s }

  (** val coq_SubstLawsDebugString :
      coq_DebugString RiscvPmpBase.coq_SubstLaws **)

  let coq_SubstLawsDebugString =
    RiscvPmpBase.Build_SubstLaws

  (** val coq_OccursCheckDebugString :
      coq_DebugString RiscvPmpBase.coq_OccursCheck **)

  let coq_OccursCheckDebugString _UU03a3_ x xIn d =
    let { debug_string_pathcondition = pc; debug_string_message = s } = d in
    Coq_option.bind
      (RiscvPmpBase.occurs_check
        (RiscvPmpBase.occurscheck_ctx coq_OccursCheckFormula) _UU03a3_ x xIn
        pc)
      (fun pc' -> Some { debug_string_pathcondition = pc';
      debug_string_message = s })

  type coq_DebugAssertFormula = { debug_assert_formula_pathcondition : 
                                  coq_PathCondition;
                                  debug_assert_formula_heap : coq_SHeap;
                                  debug_assert_formula_formula : coq_Formula }

  (** val debug_assert_formula_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugAssertFormula -> coq_PathCondition **)

  let debug_assert_formula_pathcondition _ d =
    d.debug_assert_formula_pathcondition

  (** val debug_assert_formula_heap :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugAssertFormula -> coq_SHeap **)

  let debug_assert_formula_heap _ d =
    d.debug_assert_formula_heap

  (** val debug_assert_formula_formula :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugAssertFormula -> coq_Formula **)

  let debug_assert_formula_formula _ d =
    d.debug_assert_formula_formula

  (** val coq_SubstDebugAssertFormula :
      coq_DebugAssertFormula RiscvPmpBase.coq_Subst **)

  let coq_SubstDebugAssertFormula _UU03a3_0 d _UU03a3_1 _UU03b6_01 =
    let { debug_assert_formula_pathcondition = pc;
      debug_assert_formula_heap = h; debug_assert_formula_formula = fml } = d
    in
    { debug_assert_formula_pathcondition =
    (RiscvPmpBase.subst (RiscvPmpBase.subst_ctx sub_formula) _UU03a3_0 pc
      _UU03a3_1 _UU03b6_01);
    debug_assert_formula_heap =
    (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstList coq_SubstChunk) _UU03a3_0
      h _UU03a3_1 _UU03b6_01);
    debug_assert_formula_formula =
    (RiscvPmpBase.subst sub_formula _UU03a3_0 fml _UU03a3_1 _UU03b6_01) }

  (** val coq_SubstSUDebugAssertFormula :
      (RiscvPmpBase.coq_WeakensTo, coq_DebugAssertFormula)
      RiscvPmpBase.coq_SubstSU **)

  let coq_SubstSUDebugAssertFormula _UU03a3_0 _UU03a3_1 d _UU03b6_01 =
    let { debug_assert_formula_pathcondition = pc;
      debug_assert_formula_heap = h; debug_assert_formula_formula = fml } = d
    in
    { debug_assert_formula_pathcondition =
    (RiscvPmpBase.substSU
      (RiscvPmpBase.substSU_ctx (subSU_formula RiscvPmpBase.substUniv_weaken))
      _UU03a3_0 _UU03a3_1 pc _UU03b6_01);
    debug_assert_formula_heap =
    (RiscvPmpBase.substSU
      (RiscvPmpBase.substSU_list
        (coq_SubstSUChunk RiscvPmpBase.substUniv_weaken))
      _UU03a3_0 _UU03a3_1 h _UU03b6_01);
    debug_assert_formula_formula =
    (RiscvPmpBase.substSU (subSU_formula RiscvPmpBase.substUniv_weaken)
      _UU03a3_0 _UU03a3_1 fml _UU03b6_01) }

  (** val coq_SubstLawsDebugAssertFormula :
      coq_DebugAssertFormula RiscvPmpBase.coq_SubstLaws **)

  let coq_SubstLawsDebugAssertFormula =
    RiscvPmpBase.Build_SubstLaws

  (** val coq_OccursCheckDebugAssertFormula :
      coq_DebugAssertFormula RiscvPmpBase.coq_OccursCheck **)

  let coq_OccursCheckDebugAssertFormula _UU03a3_ x xIn d =
    let { debug_assert_formula_pathcondition = pc;
      debug_assert_formula_heap = h; debug_assert_formula_formula = fml } = d
    in
    Coq_option.bind
      (RiscvPmpBase.occurs_check
        (RiscvPmpBase.occurscheck_ctx coq_OccursCheckFormula) _UU03a3_ x xIn
        pc)
      (fun pc' ->
      Coq_option.bind
        (RiscvPmpBase.occurs_check
          (RiscvPmpBase.occurs_check_list coq_OccursCheckChunk) _UU03a3_ x
          xIn h)
        (fun h' ->
        Coq_option.bind
          (RiscvPmpBase.occurs_check coq_OccursCheckFormula _UU03a3_ x xIn
            fml)
          (fun fml' -> Some { debug_assert_formula_pathcondition = pc';
          debug_assert_formula_heap = h'; debug_assert_formula_formula =
          fml' })))

  type 'a coq_SPureSpec =
    (('a, SymProp.coq_SymProp) coq_Impl coq_Box, SymProp.coq_SymProp) coq_Impl

  module SPureSpec =
   struct
    (** val run :
        (RiscvPmpBase.coq_Unit coq_SPureSpec, SymProp.coq_SymProp) coq_Impl
        coq_Valid **)

    let run _ m =
      m (fun _ _ _ -> SymProp.Coq_block)

    (** val pure : ('a1, 'a1 coq_SPureSpec) coq_Impl coq_Valid **)

    let pure w0 a _UU03a6_ =
      coq_T w0 _UU03a6_ a

    (** val bind :
        ('a1 coq_SPureSpec, (('a1, 'a2 coq_SPureSpec) coq_Impl coq_Box, 'a2
        coq_SPureSpec) coq_Impl) coq_Impl coq_Valid **)

    let bind w0 m f _UU03a6_ =
      m (fun w1 _UU03c9_01 a1 ->
        f w1 _UU03c9_01 a1 (four w0 _UU03a6_ w1 _UU03c9_01))

    module Coq_notations =
     struct
     end

    (** val block : 'a1 coq_SPureSpec coq_Valid **)

    let block _ _ =
      SymProp.Coq_block

    (** val error :
        (RiscvPmpBase.Coq_amsg.coq_AMessage, 'a1 coq_SPureSpec) coq_Impl
        coq_Valid **)

    let error _ msg _ =
      SymProp.Coq_error msg

    (** val angelic :
        coq_LVar option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term
        coq_SPureSpec) coq_Forall coq_Valid **)

    let angelic x w _UU03c3_ _UU03a6_ =
      let y = fresh_lvar RiscvPmpBase.varkit w.wctx x in
      SymProp.Coq_angelicv ({ Binding.name = y; Binding.coq_type =
      _UU03c3_ },
      (_UU03a6_ (wsnoc w { Binding.name = y; Binding.coq_type = _UU03c3_ })
        (acc_snoc_right w { Binding.name = y; Binding.coq_type = _UU03c3_ })
        (RiscvPmpBase.Coq_term_var (y, _UU03c3_,
        (Coq_ctx.in_zero { Binding.name = y; Binding.coq_type = _UU03c3_ }
          w.wctx)))))

    (** val demonic :
        coq_LVar option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term
        coq_SPureSpec) coq_Forall coq_Valid **)

    let demonic x w _UU03c3_ _UU03a6_ =
      let y = fresh_lvar RiscvPmpBase.varkit w.wctx x in
      SymProp.Coq_demonicv ({ Binding.name = y; Binding.coq_type =
      _UU03c3_ },
      (_UU03a6_ (wsnoc w { Binding.name = y; Binding.coq_type = _UU03c3_ })
        (acc_snoc_right w { Binding.name = y; Binding.coq_type = _UU03c3_ })
        (RiscvPmpBase.Coq_term_var (y, _UU03c3_,
        (Coq_ctx.in_zero { Binding.name = y; Binding.coq_type = _UU03c3_ }
          w.wctx)))))

    (** val angelic_ctx :
        ('a1 -> coq_LVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
        coq_NamedEnv coq_SPureSpec) coq_Forall coq_Valid **)

    let rec angelic_ctx n w = function
    | Coq_ctx.Coq_nil -> pure w Coq_env.Coq_nil
    | Coq_ctx.Coq_snoc (_UU0393_, b) ->
      let x = b.Binding.name in
      let _UU03c3_ = b.Binding.coq_type in
      bind w (angelic_ctx n w _UU0393_) (fun w1 _ t_UU0394_ ->
        bind w1 (angelic (Some (n x)) w1 _UU03c3_)
          (fun w2 _UU03c9_2 t_UU03c3_ ->
          pure w2 (Coq_env.Coq_snoc (_UU0393_,
            (persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b0 ->
                  RiscvPmpBase.coq_SubstTerm b0.Binding.coq_type) _UU0393_))
              w1 t_UU0394_ w2 _UU03c9_2),
            { Binding.name = x; Binding.coq_type = _UU03c3_ }, t_UU03c3_))))

    (** val demonic_ctx :
        ('a1 -> coq_LVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
        coq_NamedEnv coq_SPureSpec) coq_Forall coq_Valid **)

    let rec demonic_ctx n w = function
    | Coq_ctx.Coq_nil -> pure w Coq_env.Coq_nil
    | Coq_ctx.Coq_snoc (_UU0394_0, b) ->
      let x = b.Binding.name in
      let _UU03c3_ = b.Binding.coq_type in
      bind w (demonic_ctx n w _UU0394_0) (fun w1 _ t_UU0394_ ->
        bind w1 (demonic (Some (n x)) w1 _UU03c3_)
          (fun w2 _UU03c9_2 t_UU03c3_ ->
          pure w2 (Coq_env.Coq_snoc (_UU0394_0,
            (persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b0 ->
                  RiscvPmpBase.coq_SubstTerm b0.Binding.coq_type) _UU0394_0))
              w1 t_UU0394_ w2 _UU03c9_2),
            { Binding.name = x; Binding.coq_type = _UU03c3_ }, t_UU03c3_))))

    (** val assert_pathcondition :
        (RiscvPmpBase.Coq_amsg.coq_AMessage, (coq_PathCondition,
        RiscvPmpBase.coq_Unit coq_SPureSpec) coq_Impl) coq_Impl coq_Valid **)

    let assert_pathcondition w msg c pOST =
      match combined_solver w c with
      | Some s ->
        let Coq_existT (w1, p) = s in
        let Coq_pair (_UU03bd_, c1) = p in
        SymProp.assert_triangular w w1 msg _UU03bd_ (fun msg' ->
          SymProp.assert_pathcondition_without_solver w1 msg' c1
            (pOST (wpathcondition w1 c1)
              (acc_trans w w1 (wpathcondition w1 c1)
                (acc_triangular w w1 _UU03bd_)
                (acc_pathcondition_right w1 c1))
              Coq_tt))
      | None -> SymProp.Coq_error msg

    (** val assume_pathcondition :
        (coq_PathCondition, RiscvPmpBase.coq_Unit coq_SPureSpec) coq_Impl
        coq_Valid **)

    let assume_pathcondition w c pOST =
      match combined_solver w c with
      | Some s ->
        let Coq_existT (w1, p) = s in
        let Coq_pair (_UU03bd_, c1) = p in
        SymProp.assume_triangular w w1 _UU03bd_
          (SymProp.assume_pathcondition_without_solver w1 c1
            (pOST (wpathcondition w1 c1)
              (acc_trans w w1 (wpathcondition w1 c1)
                (acc_triangular w w1 _UU03bd_)
                (acc_pathcondition_right w1 c1))
              Coq_tt))
      | None -> SymProp.Coq_block

    (** val assert_formula :
        (RiscvPmpBase.Coq_amsg.coq_AMessage, (coq_Formula,
        RiscvPmpBase.coq_Unit coq_SPureSpec) coq_Impl) coq_Impl coq_Valid **)

    let assert_formula w0 msg fml0 =
      assert_pathcondition w0 msg (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, fml0))

    (** val assume_formula :
        (coq_Formula, RiscvPmpBase.coq_Unit coq_SPureSpec) coq_Impl coq_Valid **)

    let assume_formula w f =
      assume_pathcondition w (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, f))

    (** val angelic_binary :
        ('a1 coq_SPureSpec, ('a1 coq_SPureSpec, 'a1 coq_SPureSpec) coq_Impl)
        coq_Impl coq_Valid **)

    let angelic_binary _ m1 m2 pOST =
      SymProp.Coq_angelic_binary ((m1 pOST), (m2 pOST))

    (** val demonic_binary :
        ('a1 coq_SPureSpec, ('a1 coq_SPureSpec, 'a1 coq_SPureSpec) coq_Impl)
        coq_Impl coq_Valid **)

    let demonic_binary _ m1 m2 pOST =
      SymProp.Coq_demonic_binary ((m1 pOST), (m2 pOST))

    (** val angelic_list' :
        ('a1, ('a1 list, 'a1 coq_SPureSpec) coq_Impl) coq_Impl coq_Valid **)

    let rec angelic_list' w d = function
    | Coq_nil -> pure w d
    | Coq_cons (x, xs0) -> angelic_binary w (pure w d) (angelic_list' w x xs0)

    (** val angelic_list :
        (RiscvPmpBase.Coq_amsg.coq_AMessage, ('a1 list, 'a1 coq_SPureSpec)
        coq_Impl) coq_Impl coq_Valid **)

    let angelic_list w msg = function
    | Coq_nil -> error w msg
    | Coq_cons (x, xs0) -> angelic_list' w x xs0

    (** val demonic_list' :
        ('a1, ('a1 list, 'a1 coq_SPureSpec) coq_Impl) coq_Impl coq_Valid **)

    let rec demonic_list' w d = function
    | Coq_nil -> pure w d
    | Coq_cons (x, xs0) -> demonic_binary w (pure w d) (demonic_list' w x xs0)

    (** val demonic_list :
        ('a1 list, 'a1 coq_SPureSpec) coq_Impl coq_Valid **)

    let demonic_list w = function
    | Coq_nil -> block w
    | Coq_cons (x, xs0) -> demonic_list' w x xs0

    (** val angelic_finite :
        ('a1, 'a1) coq_RelDecision -> 'a1 coq_Finite ->
        (RiscvPmpBase.Coq_amsg.coq_AMessage, 'a1 RiscvPmpBase.coq_Const
        coq_SPureSpec) coq_Impl coq_Valid **)

    let angelic_finite _ h w msg =
      angelic_list w msg h

    (** val demonic_finite :
        ('a1, 'a1) coq_RelDecision -> 'a1 coq_Finite -> 'a1
        RiscvPmpBase.coq_Const coq_SPureSpec coq_Valid **)

    let demonic_finite _ h w =
      demonic_list w h

    (** val angelic_pattern_match' :
        ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
        (RiscvPmpBase.Coq_amsg.coq_AMessage, (RiscvPmpBase.coq_Term, 'a1
        RiscvPmpBase.coq_SMatchResult coq_SPureSpec) coq_Impl) coq_Impl
        coq_Valid **)

    let angelic_pattern_match' n _UU03c3_ pat w0 msg t =
      bind w0
        (angelic_finite
          (coq_EqDecision_from_EqDec
            (RiscvPmpBase.coq_EqDec_PatternCase _UU03c3_ pat))
          (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat) w0 msg)
        (fun w1 _UU03b8_1 pc ->
        bind w1
          (angelic_ctx n w1 (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
          (fun w2 _UU03b8_2 ts ->
          let _UU03b8_12 = acc_trans w0 w1 w2 _UU03b8_1 _UU03b8_2 in
          bind w2
            (assert_formula w2
              (persist
                (persistent_subst RiscvPmpBase.Coq_amsg.subst_amessage) w0
                msg w2 _UU03b8_12)
              (Coq_formula_relop (_UU03c3_, (Coq_bop.Coq_eq _UU03c3_),
              (RiscvPmpBase.pattern_match_term_reverse w2.wctx _UU03c3_ pat
                pc ts),
              (persist
                (persistent_subst (RiscvPmpBase.coq_SubstTerm _UU03c3_)) w0 t
                w2 _UU03b8_12))))
            (fun w3 _UU03b8_3 _ ->
            pure w3 (Coq_existT (pc,
              (persist
                (persistent_subst
                  (RiscvPmpBase.coq_SubstEnv (fun b ->
                    RiscvPmpBase.coq_SubstTerm b.Binding.coq_type)
                    (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc)))
                w2 ts w3 _UU03b8_3))))))

    (** val angelic_pattern_match :
        ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
        (RiscvPmpBase.Coq_amsg.coq_AMessage, (RiscvPmpBase.coq_Term, 'a1
        RiscvPmpBase.coq_SMatchResult coq_SPureSpec) coq_Impl) coq_Impl
        coq_Valid **)

    let rec angelic_pattern_match n _ pat w0 msg scr =
      match pat with
      | RiscvPmpBase.Coq_pat_var (x, _UU03c3_0) ->
        pure w0 (Coq_existT ((Obj.magic Coq_tt), (Coq_env.Coq_snoc
          (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x;
          Binding.coq_type = _UU03c3_0 }, scr))))
      | RiscvPmpBase.Coq_pat_bool ->
        (match RiscvPmpBase.term_get_val w0.wctx Coq_ty.Coq_bool scr with
         | Some v -> pure w0 (Coq_existT (v, Coq_env.Coq_nil))
         | None ->
           angelic_pattern_match' n Coq_ty.Coq_bool RiscvPmpBase.Coq_pat_bool
             w0 msg scr)
      | RiscvPmpBase.Coq_pat_list (_UU03c3_0, x, y) ->
        angelic_pattern_match' n (Coq_ty.Coq_list _UU03c3_0)
          (RiscvPmpBase.Coq_pat_list (_UU03c3_0, x, y)) w0 msg scr
      | RiscvPmpBase.Coq_pat_pair (x, y, _UU03c3_0, _UU03c4_) ->
        (match RiscvPmpBase.term_get_pair w0.wctx _UU03c3_0 _UU03c4_ scr with
         | Some p ->
           let Coq_pair (tl, tr) = p in
           pure w0 (Coq_existT ((Obj.magic Coq_tt), (Coq_env.Coq_snoc
             ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name = x;
             Binding.coq_type = _UU03c3_0 })), (Coq_env.Coq_snoc
             (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x;
             Binding.coq_type = _UU03c3_0 }, tl)), { Binding.name = y;
             Binding.coq_type = _UU03c4_ }, tr))))
         | None ->
           angelic_pattern_match' n (Coq_ty.Coq_prod (_UU03c3_0, _UU03c4_))
             (RiscvPmpBase.Coq_pat_pair (x, y, _UU03c3_0, _UU03c4_)) w0 msg
             scr)
      | RiscvPmpBase.Coq_pat_sum (_UU03c3_0, _UU03c4_, x, y) ->
        (match RiscvPmpBase.term_get_sum w0.wctx _UU03c3_0 _UU03c4_ scr with
         | Some s ->
           (match s with
            | Coq_inl tl ->
              pure w0 (Coq_existT ((Obj.magic Coq_true), (Coq_env.Coq_snoc
                (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x;
                Binding.coq_type = _UU03c3_0 }, tl))))
            | Coq_inr tr ->
              pure w0 (Coq_existT ((Obj.magic Coq_false), (Coq_env.Coq_snoc
                (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = y;
                Binding.coq_type = _UU03c4_ }, tr)))))
         | None ->
           angelic_pattern_match' n (Coq_ty.Coq_sum (_UU03c3_0, _UU03c4_))
             (RiscvPmpBase.Coq_pat_sum (_UU03c3_0, _UU03c4_, x, y)) w0 msg scr)
      | RiscvPmpBase.Coq_pat_unit ->
        pure w0 (Coq_existT ((Obj.magic Coq_tt), Coq_env.Coq_nil))
      | RiscvPmpBase.Coq_pat_enum e ->
        (match RiscvPmpBase.term_get_val w0.wctx (Coq_ty.Coq_enum e) scr with
         | Some v -> pure w0 (Coq_existT (v, Coq_env.Coq_nil))
         | None ->
           angelic_pattern_match' n (Coq_ty.Coq_enum e)
             (RiscvPmpBase.Coq_pat_enum e) w0 msg scr)
      | RiscvPmpBase.Coq_pat_bvec_split (m, n0, x, y) ->
        angelic_pattern_match' n (Coq_ty.Coq_bvec (add m n0))
          (RiscvPmpBase.Coq_pat_bvec_split (m, n0, x, y)) w0 msg scr
      | RiscvPmpBase.Coq_pat_bvec_exhaustive m ->
        (match RiscvPmpBase.term_get_val w0.wctx (Coq_ty.Coq_bvec m) scr with
         | Some v -> pure w0 (Coq_existT (v, Coq_env.Coq_nil))
         | None ->
           angelic_pattern_match' n (Coq_ty.Coq_bvec m)
             (RiscvPmpBase.Coq_pat_bvec_exhaustive m) w0 msg scr)
      | RiscvPmpBase.Coq_pat_tuple (_UU03c3_s, _UU0394_, p) ->
        (match RiscvPmpBase.term_get_tuple _UU03c3_s w0.wctx scr with
         | Some a ->
           pure w0 (Coq_existT ((Obj.magic Coq_tt),
             (RiscvPmpBase.tuple_pattern_match_env _UU03c3_s _UU0394_ p a)))
         | None ->
           angelic_pattern_match' n (Coq_ty.Coq_tuple _UU03c3_s)
             (RiscvPmpBase.Coq_pat_tuple (_UU03c3_s, _UU0394_, p)) w0 msg scr)
      | RiscvPmpBase.Coq_pat_record (r, _UU0394_, p) ->
        (match RiscvPmpBase.term_get_record r w0.wctx scr with
         | Some a ->
           pure w0 (Coq_existT ((Obj.magic Coq_tt),
             (RiscvPmpBase.record_pattern_match_env
               (RiscvPmpBase.typedefkit.Coq_ty.recordf_ty r) _UU0394_ p a)))
         | None ->
           angelic_pattern_match' n (Coq_ty.Coq_record r)
             (RiscvPmpBase.Coq_pat_record (r, _UU0394_, p)) w0 msg scr)
      | RiscvPmpBase.Coq_pat_union (u, p) ->
        (match RiscvPmpBase.term_get_union w0.wctx u scr with
         | Some s ->
           let Coq_existT (k, scr') = s in
           bind w0
             (angelic_pattern_match n
               (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty u k) (p k) w0 msg
               scr')
             (fun w1 _ res ->
             let Coq_existT (pc, _UU03b4_pc) = res in
             pure w1 (Coq_existT ((Obj.magic (Coq_existT (k, pc))),
               _UU03b4_pc)))
         | None ->
           angelic_pattern_match' n (Coq_ty.Coq_union u)
             (RiscvPmpBase.Coq_pat_union (u, p)) w0 msg scr)

    (** val demonic_pattern_match' :
        ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
        (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
        coq_SPureSpec) coq_Impl coq_Valid **)

    let demonic_pattern_match' n _UU03c3_ pat w0 t =
      bind w0
        (demonic_finite
          (coq_EqDecision_from_EqDec
            (RiscvPmpBase.coq_EqDec_PatternCase _UU03c3_ pat))
          (RiscvPmpBase.coq_Finite_PatternCase _UU03c3_ pat) w0)
        (fun w1 _UU03b8_1 pc ->
        bind w1
          (demonic_ctx n w1 (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
          (fun w2 _UU03b8_2 ts ->
          let _UU03b8_12 = acc_trans w0 w1 w2 _UU03b8_1 _UU03b8_2 in
          bind w2
            (assume_formula w2 (Coq_formula_relop (_UU03c3_, (Coq_bop.Coq_eq
              _UU03c3_),
              (RiscvPmpBase.pattern_match_term_reverse w2.wctx _UU03c3_ pat
                pc ts),
              (persist
                (persistent_subst (RiscvPmpBase.coq_SubstTerm _UU03c3_)) w0 t
                w2 _UU03b8_12))))
            (fun w3 _UU03b8_3 _ ->
            pure w3 (Coq_existT (pc,
              (persist
                (persistent_subst
                  (RiscvPmpBase.coq_SubstEnv (fun b ->
                    RiscvPmpBase.coq_SubstTerm b.Binding.coq_type)
                    (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc)))
                w2 ts w3 _UU03b8_3))))))

    (** val demonic_pattern_match :
        ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
        (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
        coq_SPureSpec) coq_Impl coq_Valid **)

    let rec demonic_pattern_match n _ pat w0 scr =
      match pat with
      | RiscvPmpBase.Coq_pat_var (x, _UU03c3_0) ->
        pure w0 (Coq_existT ((Obj.magic Coq_tt), (Coq_env.Coq_snoc
          (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x;
          Binding.coq_type = _UU03c3_0 }, scr))))
      | RiscvPmpBase.Coq_pat_bool ->
        (match RiscvPmpBase.term_get_val w0.wctx Coq_ty.Coq_bool scr with
         | Some v -> pure w0 (Coq_existT (v, Coq_env.Coq_nil))
         | None ->
           demonic_pattern_match' n Coq_ty.Coq_bool RiscvPmpBase.Coq_pat_bool
             w0 scr)
      | RiscvPmpBase.Coq_pat_list (_UU03c3_0, x, y) ->
        demonic_pattern_match' n (Coq_ty.Coq_list _UU03c3_0)
          (RiscvPmpBase.Coq_pat_list (_UU03c3_0, x, y)) w0 scr
      | RiscvPmpBase.Coq_pat_pair (x, y, _UU03c3_0, _UU03c4_) ->
        (match RiscvPmpBase.term_get_pair w0.wctx _UU03c3_0 _UU03c4_ scr with
         | Some p ->
           let Coq_pair (tl, tr) = p in
           pure w0 (Coq_existT ((Obj.magic Coq_tt), (Coq_env.Coq_snoc
             ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name = x;
             Binding.coq_type = _UU03c3_0 })), (Coq_env.Coq_snoc
             (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x;
             Binding.coq_type = _UU03c3_0 }, tl)), { Binding.name = y;
             Binding.coq_type = _UU03c4_ }, tr))))
         | None ->
           demonic_pattern_match' n (Coq_ty.Coq_prod (_UU03c3_0, _UU03c4_))
             (RiscvPmpBase.Coq_pat_pair (x, y, _UU03c3_0, _UU03c4_)) w0 scr)
      | RiscvPmpBase.Coq_pat_sum (_UU03c3_0, _UU03c4_, x, y) ->
        (match RiscvPmpBase.term_get_sum w0.wctx _UU03c3_0 _UU03c4_ scr with
         | Some s ->
           (match s with
            | Coq_inl tl ->
              pure w0 (Coq_existT ((Obj.magic Coq_true), (Coq_env.Coq_snoc
                (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x;
                Binding.coq_type = _UU03c3_0 }, tl))))
            | Coq_inr tr ->
              pure w0 (Coq_existT ((Obj.magic Coq_false), (Coq_env.Coq_snoc
                (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = y;
                Binding.coq_type = _UU03c4_ }, tr)))))
         | None ->
           demonic_pattern_match' n (Coq_ty.Coq_sum (_UU03c3_0, _UU03c4_))
             (RiscvPmpBase.Coq_pat_sum (_UU03c3_0, _UU03c4_, x, y)) w0 scr)
      | RiscvPmpBase.Coq_pat_unit ->
        pure w0 (Coq_existT ((Obj.magic Coq_tt), Coq_env.Coq_nil))
      | RiscvPmpBase.Coq_pat_enum e ->
        (match RiscvPmpBase.term_get_val w0.wctx (Coq_ty.Coq_enum e) scr with
         | Some v -> pure w0 (Coq_existT (v, Coq_env.Coq_nil))
         | None ->
           demonic_pattern_match' n (Coq_ty.Coq_enum e)
             (RiscvPmpBase.Coq_pat_enum e) w0 scr)
      | RiscvPmpBase.Coq_pat_bvec_split (m, n0, x, y) ->
        demonic_pattern_match' n (Coq_ty.Coq_bvec (add m n0))
          (RiscvPmpBase.Coq_pat_bvec_split (m, n0, x, y)) w0 scr
      | RiscvPmpBase.Coq_pat_bvec_exhaustive m ->
        (match RiscvPmpBase.term_get_val w0.wctx (Coq_ty.Coq_bvec m) scr with
         | Some v -> pure w0 (Coq_existT (v, Coq_env.Coq_nil))
         | None ->
           demonic_pattern_match' n (Coq_ty.Coq_bvec m)
             (RiscvPmpBase.Coq_pat_bvec_exhaustive m) w0 scr)
      | RiscvPmpBase.Coq_pat_tuple (_UU03c3_s, _UU0394_, p) ->
        (match RiscvPmpBase.term_get_tuple _UU03c3_s w0.wctx scr with
         | Some a ->
           pure w0 (Coq_existT ((Obj.magic Coq_tt),
             (RiscvPmpBase.tuple_pattern_match_env _UU03c3_s _UU0394_ p a)))
         | None ->
           demonic_pattern_match' n (Coq_ty.Coq_tuple _UU03c3_s)
             (RiscvPmpBase.Coq_pat_tuple (_UU03c3_s, _UU0394_, p)) w0 scr)
      | RiscvPmpBase.Coq_pat_record (r, _UU0394_, p) ->
        (match RiscvPmpBase.term_get_record r w0.wctx scr with
         | Some a ->
           pure w0 (Coq_existT ((Obj.magic Coq_tt),
             (RiscvPmpBase.record_pattern_match_env
               (RiscvPmpBase.typedefkit.Coq_ty.recordf_ty r) _UU0394_ p a)))
         | None ->
           demonic_pattern_match' n (Coq_ty.Coq_record r)
             (RiscvPmpBase.Coq_pat_record (r, _UU0394_, p)) w0 scr)
      | RiscvPmpBase.Coq_pat_union (u, p) ->
        (match RiscvPmpBase.term_get_union w0.wctx u scr with
         | Some s ->
           let Coq_existT (k, scr') = s in
           bind w0
             (demonic_pattern_match n
               (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty u k) (p k) w0 scr')
             (fun w1 _ res ->
             let Coq_existT (pc, _UU03b4_pc) = res in
             pure w1 (Coq_existT ((Obj.magic (Coq_existT (k, pc))),
               _UU03b4_pc)))
         | None ->
           demonic_pattern_match' n (Coq_ty.Coq_union u)
             (RiscvPmpBase.Coq_pat_union (u, p)) w0 scr)

    (** val new_pattern_match_regular :
        ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
        (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
        coq_SPureSpec) coq_Impl coq_Valid **)

    let new_pattern_match_regular n _UU03c3_ pat w0 scr pOST =
      SymProp.Coq_pattern_match (_UU03c3_, scr,
        (RiscvPmpBase.freshen_pattern n w0.wctx _UU03c3_ pat), (fun pc ->
        let w1 =
          wmatch w0 _UU03c3_ scr
            (RiscvPmpBase.freshen_pattern n w0.wctx _UU03c3_ pat) pc
        in
        let r1 =
          acc_match_right w0 _UU03c3_ scr
            (RiscvPmpBase.freshen_pattern n w0.wctx _UU03c3_ pat) pc
        in
        pOST w1 r1 (Coq_existT
          ((RiscvPmpBase.unfreshen_patterncase n w0.wctx _UU03c3_ pat pc),
          (RiscvPmpBase.unfreshen_patterncaseenv n w0.wctx _UU03c3_ pat pc
            (RiscvPmpBase.sub_cat_right w0.wctx
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_
                (RiscvPmpBase.freshen_pattern n w0.wctx _UU03c3_ pat) pc)))))))

    (** val new_pattern_match_var :
        ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> coq_LVar -> 'a1
        RiscvPmpBase.coq_Pattern -> ((coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_In, 'a1 RiscvPmpBase.coq_SMatchResult
        coq_SPureSpec) coq_Impl coq_Valid **)

    let new_pattern_match_var n _UU03c3_ x pat w0 xIn pOST =
      let pat' = RiscvPmpBase.freshen_pattern n w0.wctx _UU03c3_ pat in
      SymProp.Coq_pattern_match_var (x, _UU03c3_, xIn, pat', (fun pc ->
      pOST (wmatchvar w0 x _UU03c3_ xIn pat' pc)
        (acc_matchvar_right w0 x _UU03c3_ xIn pat' pc) (Coq_existT
        ((RiscvPmpBase.unfreshen_patterncase n w0.wctx _UU03c3_ pat pc),
        (RiscvPmpBase.unfreshen_patterncaseenv n w0.wctx _UU03c3_ pat pc
          (wmatchvar_patternvars w0.wctx x _UU03c3_ xIn pat' pc))))))

    (** val new_pattern_match' :
        ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
        (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
        coq_SPureSpec) coq_Impl coq_Valid **)

    let new_pattern_match' n _ pat w0 = function
    | RiscvPmpBase.Coq_term_var (x, _UU03c3_, xIn) ->
      new_pattern_match_var n _UU03c3_ x pat w0 xIn
    | RiscvPmpBase.Coq_term_val (_UU03c3_0, v) ->
      new_pattern_match_regular n _UU03c3_0 pat w0 (RiscvPmpBase.Coq_term_val
        (_UU03c3_0, v))
    | RiscvPmpBase.Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1, t2) ->
      new_pattern_match_regular n _UU03c3_3 pat w0
        (RiscvPmpBase.Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op,
        t1, t2))
    | RiscvPmpBase.Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t0) ->
      new_pattern_match_regular n _UU03c3_2 pat w0
        (RiscvPmpBase.Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t0))
    | RiscvPmpBase.Coq_term_tuple (_UU03c3_s, ts) ->
      new_pattern_match_regular n (Coq_ty.Coq_tuple _UU03c3_s) pat w0
        (RiscvPmpBase.Coq_term_tuple (_UU03c3_s, ts))
    | RiscvPmpBase.Coq_term_union (u, k, t0) ->
      new_pattern_match_regular n (Coq_ty.Coq_union u) pat w0
        (RiscvPmpBase.Coq_term_union (u, k, t0))
    | RiscvPmpBase.Coq_term_record (r, ts) ->
      new_pattern_match_regular n (Coq_ty.Coq_record r) pat w0
        (RiscvPmpBase.Coq_term_record (r, ts))

    (** val new_pattern_match :
        ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
        (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
        coq_SPureSpec) coq_Impl coq_Valid **)

    let rec new_pattern_match n _ pat w0 scr =
      match pat with
      | RiscvPmpBase.Coq_pat_var (x, _UU03c3_0) ->
        pure w0 (Coq_existT ((Obj.magic Coq_tt), (Coq_env.Coq_snoc
          (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x;
          Binding.coq_type = _UU03c3_0 }, scr))))
      | RiscvPmpBase.Coq_pat_bool ->
        (match RiscvPmpBase.term_get_val w0.wctx Coq_ty.Coq_bool scr with
         | Some a -> pure w0 (Coq_existT (a, Coq_env.Coq_nil))
         | None ->
           new_pattern_match' n Coq_ty.Coq_bool RiscvPmpBase.Coq_pat_bool w0
             scr)
      | RiscvPmpBase.Coq_pat_list (_UU03c3_, x, y) ->
        new_pattern_match' n (Coq_ty.Coq_list _UU03c3_)
          (RiscvPmpBase.Coq_pat_list (_UU03c3_, x, y)) w0 scr
      | RiscvPmpBase.Coq_pat_pair (x, y, _UU03c3_0, _UU03c4_) ->
        (match RiscvPmpBase.term_get_pair w0.wctx _UU03c3_0 _UU03c4_ scr with
         | Some p ->
           let Coq_pair (a, b) = p in
           pure w0 (Coq_existT ((Obj.magic Coq_tt), (Coq_env.Coq_snoc
             ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name = x;
             Binding.coq_type = _UU03c3_0 })), (Coq_env.Coq_snoc
             (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x;
             Binding.coq_type = _UU03c3_0 }, a)), { Binding.name = y;
             Binding.coq_type = _UU03c4_ }, b))))
         | None ->
           new_pattern_match' n (Coq_ty.Coq_prod (_UU03c3_0, _UU03c4_))
             (RiscvPmpBase.Coq_pat_pair (x, y, _UU03c3_0, _UU03c4_)) w0 scr)
      | RiscvPmpBase.Coq_pat_sum (_UU03c3_, _UU03c4_, x, y) ->
        (match RiscvPmpBase.term_get_sum w0.wctx _UU03c3_ _UU03c4_ scr with
         | Some s ->
           (match s with
            | Coq_inl a ->
              pure w0 (Coq_existT ((Obj.magic Coq_true), (Coq_env.Coq_snoc
                (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x;
                Binding.coq_type = _UU03c3_ }, a))))
            | Coq_inr b ->
              pure w0 (Coq_existT ((Obj.magic Coq_false), (Coq_env.Coq_snoc
                (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = y;
                Binding.coq_type = _UU03c4_ }, b)))))
         | None ->
           new_pattern_match' n (Coq_ty.Coq_sum (_UU03c3_, _UU03c4_))
             (RiscvPmpBase.Coq_pat_sum (_UU03c3_, _UU03c4_, x, y)) w0 scr)
      | RiscvPmpBase.Coq_pat_unit ->
        pure w0 (Coq_existT ((Obj.magic Coq_tt), Coq_env.Coq_nil))
      | RiscvPmpBase.Coq_pat_enum e ->
        (match RiscvPmpBase.term_get_val w0.wctx (Coq_ty.Coq_enum e) scr with
         | Some a -> pure w0 (Coq_existT (a, Coq_env.Coq_nil))
         | None ->
           new_pattern_match' n (Coq_ty.Coq_enum e)
             (RiscvPmpBase.Coq_pat_enum e) w0 scr)
      | RiscvPmpBase.Coq_pat_bvec_split (m, k, x, y) ->
        new_pattern_match' n (Coq_ty.Coq_bvec (add m k))
          (RiscvPmpBase.Coq_pat_bvec_split (m, k, x, y)) w0 scr
      | RiscvPmpBase.Coq_pat_bvec_exhaustive m ->
        (match RiscvPmpBase.term_get_val w0.wctx (Coq_ty.Coq_bvec m) scr with
         | Some a -> pure w0 (Coq_existT (a, Coq_env.Coq_nil))
         | None ->
           new_pattern_match' n (Coq_ty.Coq_bvec m)
             (RiscvPmpBase.Coq_pat_bvec_exhaustive m) w0 scr)
      | RiscvPmpBase.Coq_pat_tuple (_UU03c3_s, _UU0394_, p) ->
        (match RiscvPmpBase.term_get_tuple _UU03c3_s w0.wctx scr with
         | Some a ->
           pure w0 (Coq_existT ((Obj.magic Coq_tt),
             (RiscvPmpBase.tuple_pattern_match_env _UU03c3_s _UU0394_ p a)))
         | None ->
           new_pattern_match' n (Coq_ty.Coq_tuple _UU03c3_s)
             (RiscvPmpBase.Coq_pat_tuple (_UU03c3_s, _UU0394_, p)) w0 scr)
      | RiscvPmpBase.Coq_pat_record (r, _UU0394_, p) ->
        (match RiscvPmpBase.term_get_record r w0.wctx scr with
         | Some a ->
           pure w0 (Coq_existT ((Obj.magic Coq_tt),
             (RiscvPmpBase.record_pattern_match_env
               (RiscvPmpBase.typedefkit.Coq_ty.recordf_ty r) _UU0394_ p a)))
         | None ->
           new_pattern_match' n (Coq_ty.Coq_record r)
             (RiscvPmpBase.Coq_pat_record (r, _UU0394_, p)) w0 scr)
      | RiscvPmpBase.Coq_pat_union (u, p) ->
        (match RiscvPmpBase.term_get_union w0.wctx u scr with
         | Some s ->
           let Coq_existT (k, scr') = s in
           bind w0
             (new_pattern_match n
               (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty u k) (p k) w0 scr')
             (fun w1 _ pat0 ->
             let Coq_existT (pc, ts) = pat0 in
             pure w1 (Coq_existT ((Obj.magic (Coq_existT (k, pc))), ts)))
         | None ->
           new_pattern_match' n (Coq_ty.Coq_union u)
             (RiscvPmpBase.Coq_pat_union (u, p)) w0 scr)

    (** val debug :
        (RiscvPmpBase.Coq_amsg.coq_AMessage, ('a1 coq_SPureSpec, 'a1
        coq_SPureSpec) coq_Impl) coq_Impl coq_Valid **)

    let debug _ msg m _UU03a6_ =
      SymProp.Coq_debug (msg, (m _UU03a6_))

    (** val assert_eq_env :
        (Coq_ty.coq_Ty Coq_ctx.coq_Ctx, (RiscvPmpBase.Coq_amsg.coq_AMessage,
        ((Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env,
        ((Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env,
        RiscvPmpBase.coq_Unit coq_SPureSpec) coq_Impl) coq_Impl) coq_Impl)
        coq_Forall coq_Valid **)

    let rec assert_eq_env w _ a e e0 =
      match e with
      | Coq_env.Coq_nil ->
        (match e0 with
         | Coq_env.Coq_nil -> pure w Coq_tt
         | Coq_env.Coq_snoc (_, _, _, _) -> assert false (* absurd case *))
      | Coq_env.Coq_snoc (_UU0393_, e1, b, db) ->
        (match e0 with
         | Coq_env.Coq_nil -> assert false (* absurd case *)
         | Coq_env.Coq_snoc (_, e2, _, db0) ->
           bind w (assert_eq_env w _UU0393_ a e1 e2) (fun w1 _UU03b8_ _ ->
             assert_formula w1
               (persist
                 (persistent_subst RiscvPmpBase.Coq_amsg.subst_amessage) w a
                 w1 _UU03b8_)
               (persist (persistent_subst sub_formula) w (Coq_formula_relop
                 (b, (Coq_bop.Coq_eq b), db, db0)) w1 _UU03b8_)))

    (** val assert_eq_nenv :
        (('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx,
        (RiscvPmpBase.Coq_amsg.coq_AMessage, (('a1, Coq_ty.coq_Ty,
        RiscvPmpBase.coq_Term) coq_NamedEnv, (('a1, Coq_ty.coq_Ty,
        RiscvPmpBase.coq_Term) coq_NamedEnv, RiscvPmpBase.coq_Unit
        coq_SPureSpec) coq_Impl) coq_Impl) coq_Impl) coq_Forall coq_Valid **)

    let rec assert_eq_nenv w _ a n n0 =
      match n with
      | Coq_env.Coq_nil ->
        (match n0 with
         | Coq_env.Coq_nil -> pure w Coq_tt
         | Coq_env.Coq_snoc (_, _, _, _) -> assert false (* absurd case *))
      | Coq_env.Coq_snoc (_UU0393_, e, b, db) ->
        (match n0 with
         | Coq_env.Coq_nil -> assert false (* absurd case *)
         | Coq_env.Coq_snoc (_, e0, _, db0) ->
           bind w (assert_eq_nenv w _UU0393_ a e e0) (fun w1 _UU03b8_ _ ->
             assert_formula w1
               (persist
                 (persistent_subst RiscvPmpBase.Coq_amsg.subst_amessage) w a
                 w1 _UU03b8_)
               (persist (persistent_subst sub_formula) w (Coq_formula_relop
                 (b.Binding.coq_type, (Coq_bop.Coq_eq b.Binding.coq_type),
                 db, db0)) w1 _UU03b8_)))

    (** val assert_eq_chunk :
        (RiscvPmpBase.Coq_amsg.coq_AMessage, (coq_Chunk, (coq_Chunk,
        RiscvPmpBase.coq_Unit coq_SPureSpec coq_Box) coq_Impl) coq_Impl)
        coq_Impl coq_Valid **)

    let rec assert_eq_chunk w0 msg c1 c2 w1 _UU03b8_1 =
      match c1 with
      | Coq_chunk_user (p1, vs1) ->
        (match c2 with
         | Coq_chunk_user (p2, vs2) ->
           (match eq_dec _UU1d46f__eq_dec p1 p2 with
            | Coq_left ->
              assert_eq_env w1
                (match p2 with
                 | Coq_pmp_entries ->
                   Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
                     RiscvPmpBase.ty_pmpentry))
                 | Coq_pmp_addr_access ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                     RiscvPmpBase.ty_privilege)
                 | Coq_pmp_addr_access_without _ ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                     (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                     (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
                     RiscvPmpBase.ty_privilege)
                 | Coq_gprs -> Coq_ctx.Coq_nil
                 | Coq_ptstomem_readonly width ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                     (mul width byte)))
                 | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
                 | Coq_mmio_checked_write width ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                     (mul width byte)))
                 | Coq_encodes_instr ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_word)), RiscvPmpBase.ty_ast)
                 | Coq_ptstomem width ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_bvec
                     (mul width byte)))
                 | Coq_ptstoinstr ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_ast)
                 | _ ->
                   Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                     RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_byte))
                (persist
                  (persistent_subst RiscvPmpBase.Coq_amsg.subst_amessage) w0
                  msg w1 _UU03b8_1)
                (persist
                  (persistent_subst
                    (RiscvPmpBase.coq_SubstEnv RiscvPmpBase.coq_SubstTerm
                      (match p1 with
                       | Coq_pmp_entries ->
                         Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
                           RiscvPmpBase.ty_pmpentry))
                       | Coq_pmp_addr_access ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
                           RiscvPmpBase.ty_pmpentry))),
                           RiscvPmpBase.ty_privilege)
                       | Coq_pmp_addr_access_without _ ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                           RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
                           RiscvPmpBase.ty_pmpentry))),
                           RiscvPmpBase.ty_privilege)
                       | Coq_gprs -> Coq_ctx.Coq_nil
                       | Coq_ptstomem_readonly width ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                           (Coq_ty.Coq_bvec (mul width byte)))
                       | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
                       | Coq_mmio_checked_write width ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                           (Coq_ty.Coq_bvec (mul width byte)))
                       | Coq_encodes_instr ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_word)),
                           RiscvPmpBase.ty_ast)
                       | Coq_ptstomem width ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                           (Coq_ty.Coq_bvec (mul width byte)))
                       | Coq_ptstoinstr ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                           RiscvPmpBase.ty_ast)
                       | _ ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                           RiscvPmpBase.ty_byte))))
                  w0 vs1 w1 _UU03b8_1)
                (persist
                  (persistent_subst
                    (RiscvPmpBase.coq_SubstEnv RiscvPmpBase.coq_SubstTerm
                      (match p2 with
                       | Coq_pmp_entries ->
                         Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
                           RiscvPmpBase.ty_pmpentry))
                       | Coq_pmp_addr_access ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, (Coq_ty.Coq_list
                           RiscvPmpBase.ty_pmpentry))),
                           RiscvPmpBase.ty_privilege)
                       | Coq_pmp_addr_access_without _ ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                           RiscvPmpBase.ty_xlenbits)), (Coq_ty.Coq_list
                           RiscvPmpBase.ty_pmpentry))),
                           RiscvPmpBase.ty_privilege)
                       | Coq_gprs -> Coq_ctx.Coq_nil
                       | Coq_ptstomem_readonly width ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                           (Coq_ty.Coq_bvec (mul width byte)))
                       | Coq_inv_mmio _ -> Coq_ctx.Coq_nil
                       | Coq_mmio_checked_write width ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                           (Coq_ty.Coq_bvec (mul width byte)))
                       | Coq_encodes_instr ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_word)),
                           RiscvPmpBase.ty_ast)
                       | Coq_ptstomem width ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                           (Coq_ty.Coq_bvec (mul width byte)))
                       | Coq_ptstoinstr ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                           RiscvPmpBase.ty_ast)
                       | _ ->
                         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
                           (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
                           RiscvPmpBase.ty_byte))))
                  w0 vs2 w1 _UU03b8_1)
            | Coq_right ->
              error w1
                (persist
                  (persistent_subst RiscvPmpBase.Coq_amsg.subst_amessage) w0
                  msg w1 _UU03b8_1))
         | _ ->
           error w1
             (persist (persistent_subst RiscvPmpBase.Coq_amsg.subst_amessage)
               w0 msg w1 _UU03b8_1))
      | Coq_chunk_ptsreg (_UU03c3_, r1, v1) ->
        (match c2 with
         | Coq_chunk_ptsreg (_UU03c3_0, r2, v2) ->
           (match eq_dec_het RiscvPmpBase._UU1d479__UU1d46c__UU1d46e__eq_dec
                    _UU03c3_ _UU03c3_0 r1 r2 with
            | Coq_left ->
              assert_formula w1
                (persist
                  (persistent_subst RiscvPmpBase.Coq_amsg.subst_amessage) w0
                  msg w1 _UU03b8_1)
                (Coq_formula_relop ((projT1 (Coq_existT (_UU03c3_0, r2))),
                (Coq_bop.Coq_eq (projT1 (Coq_existT (_UU03c3_0, r2)))),
                (persist
                  (persistent_subst
                    (RiscvPmpBase.coq_SubstTerm
                      (projT1 (Coq_existT (_UU03c3_, r1)))))
                  w0 v1 w1 _UU03b8_1),
                (persist
                  (persistent_subst (RiscvPmpBase.coq_SubstTerm _UU03c3_0))
                  w0 v2 w1 _UU03b8_1)))
            | Coq_right ->
              error w1
                (persist
                  (persistent_subst RiscvPmpBase.Coq_amsg.subst_amessage) w0
                  msg w1 _UU03b8_1))
         | _ ->
           error w1
             (persist (persistent_subst RiscvPmpBase.Coq_amsg.subst_amessage)
               w0 msg w1 _UU03b8_1))
      | Coq_chunk_conj (c11, c12) ->
        (match c2 with
         | Coq_chunk_conj (c21, c22) ->
           bind w1 (assert_eq_chunk w0 msg c11 c21 w1 _UU03b8_1)
             (fun w2 _UU03b8_2 _ ->
             assert_eq_chunk w0 msg c12 c22 w2
               (acc_trans w0 w1 w2 _UU03b8_1 _UU03b8_2))
         | _ ->
           error w1
             (persist (persistent_subst RiscvPmpBase.Coq_amsg.subst_amessage)
               w0 msg w1 _UU03b8_1))
      | Coq_chunk_wand (c11, c12) ->
        (match c2 with
         | Coq_chunk_wand (c21, c22) ->
           bind w1 (assert_eq_chunk w0 msg c11 c21 w1 _UU03b8_1)
             (fun w2 _UU03b8_2 _ ->
             assert_eq_chunk w0 msg c12 c22 w2
               (acc_trans w0 w1 w2 _UU03b8_1 _UU03b8_2))
         | _ ->
           error w1
             (persist (persistent_subst RiscvPmpBase.Coq_amsg.subst_amessage)
               w0 msg w1 _UU03b8_1))

    (** val replay_aux :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> (RiscvPmpBase.coq_Sub, RiscvPmpBase.coq_Unit
        coq_SPureSpec) coq_Impl coq_Valid **)

    let rec replay_aux _UU03a3_ s w0 _UU03b4_ =
      match s with
      | SymProp.Coq_angelic_binary (o1, o2) ->
        angelic_binary w0 (replay_aux _UU03a3_ o1 w0 _UU03b4_)
          (replay_aux _UU03a3_ o2 w0 _UU03b4_)
      | SymProp.Coq_demonic_binary (o1, o2) ->
        demonic_binary w0 (replay_aux _UU03a3_ o1 w0 _UU03b4_)
          (replay_aux _UU03a3_ o2 w0 _UU03b4_)
      | SymProp.Coq_error msg ->
        error w0
          (RiscvPmpBase.subst RiscvPmpBase.Coq_amsg.subst_amessage _UU03a3_
            msg w0.wctx _UU03b4_)
      | SymProp.Coq_block -> block w0
      | SymProp.Coq_assertk (fml, msg, k) ->
        bind w0
          (assert_formula w0
            (RiscvPmpBase.subst RiscvPmpBase.Coq_amsg.subst_amessage _UU03a3_
              msg w0.wctx _UU03b4_)
            (RiscvPmpBase.subst sub_formula _UU03a3_ fml w0.wctx _UU03b4_))
          (fun w1 _UU03b8_ _ ->
          replay_aux _UU03a3_ k w1
            (persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b ->
                  RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_))
              w0 _UU03b4_ w1 _UU03b8_))
      | SymProp.Coq_assumek (fml, k) ->
        bind w0
          (assume_formula w0
            (RiscvPmpBase.subst sub_formula _UU03a3_ fml w0.wctx _UU03b4_))
          (fun w1 _UU03b8_ _ ->
          replay_aux _UU03a3_ k w1
            (persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b ->
                  RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_))
              w0 _UU03b4_ w1 _UU03b8_))
      | SymProp.Coq_angelicv (b, k) ->
        bind w0 (angelic (Some b.Binding.name) w0 b.Binding.coq_type)
          (fun w1 _UU03b8_ t ->
          replay_aux (Coq_ctx.Coq_snoc (_UU03a3_, b)) k w1 (Coq_env.Coq_snoc
            (_UU03a3_,
            (persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b0 ->
                  RiscvPmpBase.coq_SubstTerm b0.Binding.coq_type) _UU03a3_))
              w0 _UU03b4_ w1 _UU03b8_),
            b, t)))
      | SymProp.Coq_demonicv (b, k) ->
        bind w0 (demonic (Some b.Binding.name) w0 b.Binding.coq_type)
          (fun w1 _UU03b8_ t ->
          replay_aux (Coq_ctx.Coq_snoc (_UU03a3_, b)) k w1 (Coq_env.Coq_snoc
            (_UU03a3_,
            (persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b0 ->
                  RiscvPmpBase.coq_SubstTerm b0.Binding.coq_type) _UU03a3_))
              w0 _UU03b4_ w1 _UU03b8_),
            b, t)))
      | SymProp.Coq_assert_vareq (x, _UU03c3_, xIn, t, msg, k) ->
        let _UU03b6_ =
          RiscvPmpBase.sub_shift _UU03a3_ { Binding.name = x;
            Binding.coq_type = _UU03c3_ } xIn
        in
        let msg0 =
          RiscvPmpBase.subst RiscvPmpBase.Coq_amsg.subst_amessage
            (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            msg _UU03a3_ _UU03b6_
        in
        let fml = Coq_formula_relop (_UU03c3_, (Coq_bop.Coq_eq _UU03c3_),
          (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm _UU03c3_)
            (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            t _UU03a3_ _UU03b6_),
          (RiscvPmpBase.Coq_term_var (x, _UU03c3_, xIn)))
        in
        bind w0
          (assert_formula w0
            (RiscvPmpBase.subst RiscvPmpBase.Coq_amsg.subst_amessage _UU03a3_
              msg0 w0.wctx _UU03b4_)
            (RiscvPmpBase.subst sub_formula _UU03a3_ fml w0.wctx _UU03b4_))
          (fun w1 _UU03b8_ _ ->
          replay_aux
            (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            k w1
            (Coq_env.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ }
              (persist
                (persistent_subst
                  (RiscvPmpBase.coq_SubstEnv (fun b ->
                    RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_))
                w0 _UU03b4_ w1 _UU03b8_)
              xIn))
      | SymProp.Coq_assume_vareq (x, _UU03c3_, xIn, t, k) ->
        let _UU03b6_ =
          RiscvPmpBase.sub_shift _UU03a3_ { Binding.name = x;
            Binding.coq_type = _UU03c3_ } xIn
        in
        let fml = Coq_formula_relop (_UU03c3_, (Coq_bop.Coq_eq _UU03c3_),
          (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm _UU03c3_)
            (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            t _UU03a3_ _UU03b6_),
          (RiscvPmpBase.Coq_term_var (x, _UU03c3_, xIn)))
        in
        bind w0
          (assume_formula w0
            (RiscvPmpBase.subst sub_formula _UU03a3_ fml w0.wctx _UU03b4_))
          (fun w1 _UU03b8_ _ ->
          replay_aux
            (Coq_ctx.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ } xIn)
            k w1
            (Coq_env.remove _UU03a3_ { Binding.name = x; Binding.coq_type =
              _UU03c3_ }
              (persist
                (persistent_subst
                  (RiscvPmpBase.coq_SubstEnv (fun b ->
                    RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_))
                w0 _UU03b4_ w1 _UU03b8_)
              xIn))
      | SymProp.Coq_pattern_match (_, _, _, _) ->
        error w0 (RiscvPmpBase.Coq_amsg.Coq_mk (RiscvPmpBase.coq_SubstConst,
          RiscvPmpBase.substSU_Const, RiscvPmpBase.coq_SubstLawsConst,
          RiscvPmpBase.coq_OccursCheck_Const, RiscvPmpBase.erase_Const,
          (Obj.magic { debug_string_pathcondition = w0.wco;
            debug_string_message = (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) })))
      | SymProp.Coq_pattern_match_var (_, _, _, _, _) ->
        error w0 (RiscvPmpBase.Coq_amsg.Coq_mk (RiscvPmpBase.coq_SubstConst,
          RiscvPmpBase.substSU_Const, RiscvPmpBase.coq_SubstLawsConst,
          RiscvPmpBase.coq_OccursCheck_Const, RiscvPmpBase.erase_Const,
          (Obj.magic { debug_string_pathcondition = w0.wco;
            debug_string_message = (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) })))
      | SymProp.Coq_debug (msg, k) ->
        debug w0
          (RiscvPmpBase.subst RiscvPmpBase.Coq_amsg.subst_amessage _UU03a3_
            msg w0.wctx _UU03b4_)
          (replay_aux _UU03a3_ k w0 _UU03b4_)

    (** val replay :
        (SymProp.coq_SymProp, SymProp.coq_SymProp) coq_Impl coq_Valid **)

    let replay w p =
      run w (replay_aux w.wctx p w (RiscvPmpBase.sub_id w.wctx))

    (** val produce_chunk :
        (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
        coq_Valid **)

    let produce_chunk w0 c h =
      pure w0 (Coq_cons ((peval_chunk w0.wctx c), h))

    (** val consume_chunk :
        (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
        coq_Valid **)

    let consume_chunk w0 c h =
      let c1 = peval_chunk w0.wctx c in
      (match try_consume_chunk_exact w0.wctx h c1 with
       | Some h' -> pure w0 h'
       | None ->
         (match try_consume_chunk_precise w0.wctx h c1 with
          | Some p ->
            let Coq_pair (h', fs) = p in
            bind w0
              (assert_pathcondition w0 (RiscvPmpBase.Coq_amsg.Coq_mk
                ((Obj.magic coq_SubstDebugConsumeChunk),
                (Obj.magic coq_SubstSUDebugConsumeChunk
                  RiscvPmpBase.substUniv_weaken),
                (Obj.magic coq_SubstLawsDebugConsumeChunk),
                (Obj.magic coq_OccursCheckDebugConsumeChunk),
                (Obj.magic coq_Erase_DebugConsumeChunk),
                (Obj.magic { debug_consume_chunk_pathcondition = w0.wco;
                  debug_consume_chunk_heap = h; debug_consume_chunk_chunk =
                  c1 })))
                fs)
              (fun w1 _UU03b8_ _ ->
              pure w1
                (persist
                  (persistent_subst
                    (RiscvPmpBase.coq_SubstList coq_SubstChunk))
                  w0 h' w1 _UU03b8_))
          | None ->
            error w0 (RiscvPmpBase.Coq_amsg.Coq_mk
              ((Obj.magic coq_SubstDebugConsumeChunk),
              (Obj.magic coq_SubstSUDebugConsumeChunk
                RiscvPmpBase.substUniv_weaken),
              (Obj.magic coq_SubstLawsDebugConsumeChunk),
              (Obj.magic coq_OccursCheckDebugConsumeChunk),
              (Obj.magic coq_Erase_DebugConsumeChunk),
              (Obj.magic { debug_consume_chunk_pathcondition = w0.wco;
                debug_consume_chunk_heap = h; debug_consume_chunk_chunk =
                c1 })))))

    (** val consume_chunk_angelic :
        (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
        coq_Valid **)

    let consume_chunk_angelic w0 c h =
      let c1 = peval_chunk w0.wctx c in
      (match try_consume_chunk_exact w0.wctx h c1 with
       | Some h' -> pure w0 h'
       | None ->
         (match try_consume_chunk_precise w0.wctx h c1 with
          | Some p ->
            let Coq_pair (h', fs) = p in
            bind w0
              (assert_pathcondition w0 (RiscvPmpBase.Coq_amsg.Coq_mk
                ((Obj.magic coq_SubstDebugConsumeChunk),
                (Obj.magic coq_SubstSUDebugConsumeChunk
                  RiscvPmpBase.substUniv_weaken),
                (Obj.magic coq_SubstLawsDebugConsumeChunk),
                (Obj.magic coq_OccursCheckDebugConsumeChunk),
                (Obj.magic coq_Erase_DebugConsumeChunk),
                (Obj.magic { debug_consume_chunk_pathcondition = w0.wco;
                  debug_consume_chunk_heap = h; debug_consume_chunk_chunk =
                  c1 })))
                fs)
              (fun w1 _UU03b8_ _ ->
              pure w1
                (persist
                  (persistent_subst
                    (RiscvPmpBase.coq_SubstList coq_SubstChunk))
                  w0 h' w1 _UU03b8_))
          | None ->
            bind w0
              (angelic_list w0 (RiscvPmpBase.Coq_amsg.Coq_mk
                ((Obj.magic coq_SubstDebugConsumeChunk),
                (Obj.magic coq_SubstSUDebugConsumeChunk
                  RiscvPmpBase.substUniv_weaken),
                (Obj.magic coq_SubstLawsDebugConsumeChunk),
                (Obj.magic coq_OccursCheckDebugConsumeChunk),
                (Obj.magic coq_Erase_DebugConsumeChunk),
                (Obj.magic { debug_consume_chunk_pathcondition = w0.wco;
                  debug_consume_chunk_heap = h; debug_consume_chunk_chunk =
                  c1 })))
                (heap_extractions chunk_isdup h))
              (fun w1 _UU03b8_2 pat ->
              let Coq_pair (c', h') = pat in
              let c2 =
                persist (persistent_subst coq_SubstChunk) w0 c1 w1 _UU03b8_2
              in
              bind w1
                (assert_eq_chunk w1 (RiscvPmpBase.Coq_amsg.Coq_mk
                  ((Obj.magic coq_SubstDebugConsumeChunk),
                  (Obj.magic coq_SubstSUDebugConsumeChunk
                    RiscvPmpBase.substUniv_weaken),
                  (Obj.magic coq_SubstLawsDebugConsumeChunk),
                  (Obj.magic coq_OccursCheckDebugConsumeChunk),
                  (Obj.magic coq_Erase_DebugConsumeChunk),
                  (Obj.magic { debug_consume_chunk_pathcondition = w1.wco;
                    debug_consume_chunk_heap =
                    (persist
                      (persistent_subst
                        (RiscvPmpBase.coq_SubstList coq_SubstChunk))
                      w0 h w1 _UU03b8_2);
                    debug_consume_chunk_chunk = c2 })))
                  c2 c' w1 Coq_acc_refl)
                (fun w2 _UU03b8_3 _ ->
                pure w2
                  (persist
                    (persistent_subst
                      (RiscvPmpBase.coq_SubstList coq_SubstChunk))
                    w1 h' w2 _UU03b8_3)))))

    (** val read_register :
        Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> (coq_SHeap,
        (RiscvPmpBase.coq_Term, coq_SHeap) RiscvPmpBase.coq_Pair
        coq_SPureSpec) coq_Impl coq_Valid **)

    let read_register _UU03c4_ reg w h =
      match find_chunk_ptsreg_precise w.wctx _UU03c4_ reg h with
      | Some p ->
        let Coq_pair (t', h') = p in
        pure w (Coq_pair (t', (Coq_cons ((Coq_chunk_ptsreg (_UU03c4_, reg,
          t')), h'))))
      | None ->
        error w (RiscvPmpBase.Coq_amsg.Coq_mk
          ((Obj.magic coq_SubstDebugReadRegister),
          (Obj.magic coq_SubstSUDebugReadRegister
            RiscvPmpBase.substUniv_weaken),
          (Obj.magic coq_SubstLawsDebugReadRegister),
          (Obj.magic coq_OccursCheckDebugReadRegister),
          (Obj.magic coq_EraseDebugReadRegister),
          (Obj.magic { debug_read_register_pathcondition = w.wco;
            debug_read_register_heap = h; debug_read_register_type =
            _UU03c4_; debug_read_register_register = reg })))

    (** val write_register :
        Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> (RiscvPmpBase.coq_Term,
        (coq_SHeap, (RiscvPmpBase.coq_Term, coq_SHeap) RiscvPmpBase.coq_Pair
        coq_SPureSpec) coq_Impl) coq_Impl coq_Valid **)

    let write_register _UU03c4_ reg w t h =
      match find_chunk_ptsreg_precise w.wctx _UU03c4_ reg h with
      | Some p ->
        let Coq_pair (_, h') = p in
        pure w (Coq_pair (t, (Coq_cons ((Coq_chunk_ptsreg (_UU03c4_, reg,
          t)), h'))))
      | None ->
        error w (RiscvPmpBase.Coq_amsg.Coq_mk
          ((Obj.magic coq_SubstDebugWriteRegister),
          (Obj.magic coq_SubstSUDebugWriteRegister
            RiscvPmpBase.substUniv_weaken),
          (Obj.magic coq_SubstLawsDebugWriteRegister),
          (Obj.magic coq_OccursCheckDebugWriteRegister),
          (Obj.magic coq_EraseDebugWriteRegister),
          (Obj.magic { debug_write_register_pathcondition = w.wco;
            debug_write_register_heap = h; debug_write_register_type =
            _UU03c4_; debug_write_register_register = reg;
            debug_write_register_value = t })))
   end

  type 'a coq_SHeapSpec =
    (('a, (coq_SHeap, SymProp.coq_SymProp) coq_Impl) coq_Impl coq_Box,
    (coq_SHeap, SymProp.coq_SymProp) coq_Impl) coq_Impl

  module SHeapSpec =
   struct
    (** val run :
        (RiscvPmpBase.coq_Unit coq_SHeapSpec, SymProp.coq_SymProp) coq_Impl
        coq_Valid **)

    let run _ m =
      m (fun _ _ _ _ -> SymProp.Coq_block) Coq_nil

    (** val lift_purespec :
        ('a1 coq_SPureSpec, 'a1 coq_SHeapSpec) coq_Impl coq_Valid **)

    let lift_purespec w0 m _UU03a6_ h0 =
      m (fun w1 _UU03c9_01 a1 ->
        _UU03a6_ w1 _UU03c9_01 a1
          (persist
            (persistent_subst (RiscvPmpBase.coq_SubstList coq_SubstChunk)) w0
            h0 w1 _UU03c9_01))

    (** val pure : ('a1, 'a1 coq_SHeapSpec) coq_Impl coq_Valid **)

    let pure w a _UU03a6_ h =
      coq_T w _UU03a6_ a h

    (** val bind :
        ('a1 coq_SHeapSpec, (('a1, 'a2 coq_SHeapSpec) coq_Impl coq_Box, 'a2
        coq_SHeapSpec) coq_Impl) coq_Impl coq_Valid **)

    let bind w m f _UU03a6_ =
      m (fun w1 _UU03b8_1 a1 ->
        f w1 _UU03b8_1 a1 (four w _UU03a6_ w1 _UU03b8_1))

    module Coq_notations =
     struct
     end

    (** val error :
        ((coq_SHeap, RiscvPmpBase.Coq_amsg.coq_AMessage) coq_Impl, 'a1
        coq_SHeapSpec) coq_Impl coq_Valid **)

    let error _ msg _ h =
      SymProp.Coq_error (msg h)

    (** val angelic :
        coq_LVar option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term
        coq_SHeapSpec) coq_Forall coq_Valid **)

    let angelic x w _UU03c3_ =
      lift_purespec w (SPureSpec.angelic x w _UU03c3_)

    (** val demonic :
        coq_LVar option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term
        coq_SHeapSpec) coq_Forall coq_Valid **)

    let demonic x w _UU03c3_ =
      lift_purespec w (SPureSpec.demonic x w _UU03c3_)

    (** val angelic_ctx :
        ('a1 -> coq_LVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
        coq_NamedEnv coq_SHeapSpec) coq_Forall coq_Valid **)

    let angelic_ctx n w _UU0394_ =
      lift_purespec w (SPureSpec.angelic_ctx n w _UU0394_)

    (** val demonic_ctx :
        ('a1 -> coq_LVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
        coq_NamedEnv coq_SHeapSpec) coq_Forall coq_Valid **)

    let demonic_ctx n w _UU0394_ =
      lift_purespec w (SPureSpec.demonic_ctx n w _UU0394_)

    (** val angelic_binary :
        ('a1 coq_SHeapSpec, ('a1 coq_SHeapSpec, 'a1 coq_SHeapSpec) coq_Impl)
        coq_Impl coq_Valid **)

    let angelic_binary _ m1 m2 _UU03a6_ h =
      SymProp.Coq_angelic_binary ((m1 _UU03a6_ h), (m2 _UU03a6_ h))

    (** val demonic_binary :
        ('a1 coq_SHeapSpec, ('a1 coq_SHeapSpec, 'a1 coq_SHeapSpec) coq_Impl)
        coq_Impl coq_Valid **)

    let demonic_binary _ m1 m2 _UU03a6_ h =
      SymProp.Coq_demonic_binary ((m1 _UU03a6_ h), (m2 _UU03a6_ h))

    (** val debug :
        ((coq_SHeap, RiscvPmpBase.Coq_amsg.coq_AMessage) coq_Impl, ('a1
        coq_SHeapSpec, 'a1 coq_SHeapSpec) coq_Impl) coq_Impl coq_Valid **)

    let debug _ msg m _UU03a6_ h =
      SymProp.Coq_debug ((msg h), (m _UU03a6_ h))

    (** val assert_formula :
        ((coq_SHeap, RiscvPmpBase.Coq_amsg.coq_AMessage) coq_Impl,
        (coq_Formula, RiscvPmpBase.coq_Unit coq_SHeapSpec) coq_Impl) coq_Impl
        coq_Valid **)

    let assert_formula w msg c _UU03a6_ h =
      SPureSpec.assert_formula w (msg h) c (fun w1 _UU03b8_1 x ->
        _UU03a6_ w1 _UU03b8_1 x
          (persist
            (persistent_subst (RiscvPmpBase.coq_SubstList coq_SubstChunk)) w
            h w1 _UU03b8_1))

    (** val assume_formula :
        (coq_Formula, RiscvPmpBase.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid **)

    let assume_formula w fml =
      lift_purespec w (SPureSpec.assume_formula w fml)

    (** val produce_chunk :
        (coq_Chunk, RiscvPmpBase.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid **)

    let produce_chunk w0 c _UU03a6_ h =
      SPureSpec.produce_chunk w0 c h (fun w1 _UU03b8_1 ->
        _UU03a6_ w1 _UU03b8_1 Coq_tt)

    (** val consume_chunk :
        (coq_Chunk, RiscvPmpBase.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid **)

    let consume_chunk w0 c _UU03a6_ h =
      SPureSpec.consume_chunk w0 c h (fun w1 _UU03b8_1 ->
        _UU03a6_ w1 _UU03b8_1 Coq_tt)

    (** val consume_chunk_angelic :
        (coq_Chunk, RiscvPmpBase.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid **)

    let consume_chunk_angelic w0 c _UU03a6_ h =
      SPureSpec.consume_chunk_angelic w0 c h (fun w1 _UU03b8_1 ->
        _UU03a6_ w1 _UU03b8_1 Coq_tt)

    (** val read_register :
        Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> RiscvPmpBase.coq_Term
        coq_SHeapSpec coq_Valid **)

    let read_register _UU03c4_ reg w0 _UU03a6_ h =
      SPureSpec.read_register _UU03c4_ reg w0 h (fun w1 _UU03b8_1 pat ->
        let Coq_pair (t, h') = pat in _UU03a6_ w1 _UU03b8_1 t h')

    (** val write_register :
        Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> (RiscvPmpBase.coq_Term,
        RiscvPmpBase.coq_Term coq_SHeapSpec) coq_Impl coq_Valid **)

    let write_register _UU03c4_ reg w0 t _UU03a6_ h =
      SPureSpec.write_register _UU03c4_ reg w0 t h (fun w1 _UU03b8_1 pat ->
        let Coq_pair (t', h') = pat in _UU03a6_ w1 _UU03b8_1 t' h')

    (** val produce :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_asn.coq_Assertion -> (RiscvPmpBase.coq_Sub, RiscvPmpBase.coq_Unit
        coq_SHeapSpec) coq_Impl coq_Valid **)

    let rec produce _UU03a3_ asn w _UU03b6_ =
      match asn with
      | Coq_asn.Coq_formula fml ->
        assume_formula w
          (RiscvPmpBase.subst sub_formula _UU03a3_ fml w.wctx _UU03b6_)
      | Coq_asn.Coq_chunk c ->
        produce_chunk w
          (RiscvPmpBase.subst coq_SubstChunk _UU03a3_ c w.wctx _UU03b6_)
      | Coq_asn.Coq_chunk_angelic c ->
        produce_chunk w
          (RiscvPmpBase.subst coq_SubstChunk _UU03a3_ c w.wctx _UU03b6_)
      | Coq_asn.Coq_pattern_match (_UU03c3_, s, pat, rhs) ->
        bind w
          (lift_purespec w
            (SPureSpec.demonic_pattern_match id _UU03c3_ pat w
              (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm _UU03c3_)
                _UU03a3_ s w.wctx _UU03b6_)))
          (fun w1 _UU03b8_ pat0 ->
          let Coq_existT (pc, _UU03b4_pc) = pat0 in
          produce
            (Coq_ctx.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (rhs pc) w1
            (Coq_env.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc)
              (persist
                (persistent_subst
                  (RiscvPmpBase.coq_SubstEnv (fun b ->
                    RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_))
                w _UU03b6_ w1 _UU03b8_)
              _UU03b4_pc))
      | Coq_asn.Coq_sep (a1, a2) ->
        bind w (produce _UU03a3_ a1 w _UU03b6_) (fun w1 _UU03b8_ _ ->
          produce _UU03a3_ a2 w1
            (persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b ->
                  RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_))
              w _UU03b6_ w1 _UU03b8_))
      | Coq_asn.Coq_or (a1, a2) ->
        demonic_binary w (produce _UU03a3_ a1 w _UU03b6_)
          (produce _UU03a3_ a2 w _UU03b6_)
      | Coq_asn.Coq_exist (_UU03c2_, _UU03c4_, a) ->
        bind w (demonic (Some _UU03c2_) w _UU03c4_) (fun w1 _UU03b8_ t ->
          produce (Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name = _UU03c2_;
            Binding.coq_type = _UU03c4_ })) a w1 (Coq_env.Coq_snoc (_UU03a3_,
            (persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b ->
                  RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_))
              w _UU03b6_ w1 _UU03b8_),
            { Binding.name = _UU03c2_; Binding.coq_type = _UU03c4_ }, t)))
      | Coq_asn.Coq_debug ->
        debug w (fun h1 -> RiscvPmpBase.Coq_amsg.Coq_mk
          (RiscvPmpBase.coq_SubstConst, RiscvPmpBase.substSU_Const,
          RiscvPmpBase.coq_SubstLawsConst,
          RiscvPmpBase.coq_OccursCheck_Const, RiscvPmpBase.erase_Const,
          (Obj.magic { debug_asn_pathcondition = w.wco; debug_asn_heap = h1 })))
          (pure w Coq_tt)

    (** val consume :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_asn.coq_Assertion -> (RiscvPmpBase.coq_Sub, RiscvPmpBase.coq_Unit
        coq_SHeapSpec) coq_Impl coq_Valid **)

    let rec consume _UU03a3_ asn w _UU03b6_ =
      match asn with
      | Coq_asn.Coq_formula fml ->
        let fml0 = RiscvPmpBase.subst sub_formula _UU03a3_ fml w.wctx _UU03b6_
        in
        assert_formula w (fun h -> RiscvPmpBase.Coq_amsg.Coq_mk
          (RiscvPmpBase.coq_SubstConst, RiscvPmpBase.substSU_Const,
          RiscvPmpBase.coq_SubstLawsConst,
          RiscvPmpBase.coq_OccursCheck_Const, RiscvPmpBase.erase_Const,
          (Obj.magic { debug_assert_formula_pathcondition = w.wco;
            debug_assert_formula_heap = h; debug_assert_formula_formula =
            fml0 })))
          fml0
      | Coq_asn.Coq_chunk c ->
        consume_chunk w
          (RiscvPmpBase.subst coq_SubstChunk _UU03a3_ c w.wctx _UU03b6_)
      | Coq_asn.Coq_chunk_angelic c ->
        consume_chunk_angelic w
          (RiscvPmpBase.subst coq_SubstChunk _UU03a3_ c w.wctx _UU03b6_)
      | Coq_asn.Coq_pattern_match (_UU03c3_, s, pat, rhs) ->
        bind w
          (lift_purespec w
            (SPureSpec.angelic_pattern_match id _UU03c3_ pat w
              (RiscvPmpBase.Coq_amsg.Coq_mk (RiscvPmpBase.coq_SubstConst,
              RiscvPmpBase.substSU_Const, RiscvPmpBase.coq_SubstLawsConst,
              RiscvPmpBase.coq_OccursCheck_Const, RiscvPmpBase.erase_Const,
              (Obj.magic { debug_string_pathcondition = w.wco;
                debug_string_message = (String ((Ascii (Coq_true, Coq_true,
                Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
                Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
                Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
                ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
                Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
                ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false,
                Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
                ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
                Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                Coq_true, Coq_false)),
                EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) })))
              (RiscvPmpBase.subst (RiscvPmpBase.coq_SubstTerm _UU03c3_)
                _UU03a3_ s w.wctx _UU03b6_)))
          (fun w1 _UU03b8_ pat0 ->
          let Coq_existT (pc, _UU03b4_pc) = pat0 in
          consume
            (Coq_ctx.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc))
            (rhs pc) w1
            (Coq_env.cat _UU03a3_
              (RiscvPmpBase.coq_PatternCaseCtx _UU03c3_ pat pc)
              (persist
                (persistent_subst
                  (RiscvPmpBase.coq_SubstEnv (fun b ->
                    RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_))
                w _UU03b6_ w1 _UU03b8_)
              _UU03b4_pc))
      | Coq_asn.Coq_sep (a1, a2) ->
        bind w (consume _UU03a3_ a1 w _UU03b6_) (fun w1 _UU03b8_ _ ->
          consume _UU03a3_ a2 w1
            (persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b ->
                  RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_))
              w _UU03b6_ w1 _UU03b8_))
      | Coq_asn.Coq_or (a1, a2) ->
        angelic_binary w (consume _UU03a3_ a1 w _UU03b6_)
          (consume _UU03a3_ a2 w _UU03b6_)
      | Coq_asn.Coq_exist (_UU03c2_, _UU03c4_, a) ->
        bind w (angelic (Some _UU03c2_) w _UU03c4_) (fun w1 _UU03b8_ t ->
          consume (Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name = _UU03c2_;
            Binding.coq_type = _UU03c4_ })) a w1 (Coq_env.Coq_snoc (_UU03a3_,
            (persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b ->
                  RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_))
              w _UU03b6_ w1 _UU03b8_),
            { Binding.name = _UU03c2_; Binding.coq_type = _UU03c4_ }, t)))
      | Coq_asn.Coq_debug ->
        debug w (fun h1 -> RiscvPmpBase.Coq_amsg.Coq_mk
          (RiscvPmpBase.coq_SubstConst, RiscvPmpBase.substSU_Const,
          RiscvPmpBase.coq_SubstLawsConst,
          RiscvPmpBase.coq_OccursCheck_Const, RiscvPmpBase.erase_Const,
          (Obj.magic { debug_asn_pathcondition = w.wco; debug_asn_heap = h1 })))
          (pure w Coq_tt)

    (** val call_contract :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> coq_SepContract -> (RiscvPmpBase.coq_SStore,
        RiscvPmpBase.coq_Term coq_SHeapSpec) coq_Impl coq_Valid **)

    let call_contract _UU0394_ _UU03c4_ c w0 args =
      let { sep_contract_logic_variables = _UU03a3_e;
        sep_contract_localstore = _UU03b4_e; sep_contract_precondition = req;
        sep_contract_result = result; sep_contract_postcondition = ens } = c
      in
      bind w0 (lift_purespec w0 (SPureSpec.angelic_ctx id w0 _UU03a3_e))
        (fun w1 _UU03b8_1 evars ->
        bind w1
          (lift_purespec w1
            (SPureSpec.assert_eq_nenv w1 _UU0394_
              (RiscvPmpBase.Coq_amsg.Coq_mk (RiscvPmpBase.coq_SubstConst,
              RiscvPmpBase.substSU_Const, RiscvPmpBase.coq_SubstLawsConst,
              RiscvPmpBase.coq_OccursCheck_Const, RiscvPmpBase.erase_Const,
              (Obj.magic { debug_string_pathcondition = w0.wco;
                debug_string_message = (String ((Ascii (Coq_true, Coq_true,
                Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
                Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
                Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
                Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
                ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
                Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
                ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                Coq_false)),
                EmptyString)))))))))))))))))))))))))))))))))))))))))))))) })))
              (RiscvPmpBase.subst (RiscvPmpBase.subst_localstore _UU0394_)
                _UU03a3_e _UU03b4_e w1.wctx evars)
              (persist
                (persistent_subst (RiscvPmpBase.subst_localstore _UU0394_))
                w0 args w1 _UU03b8_1)))
          (fun w2 _UU03b8_2 _ ->
          let evars2 =
            persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b ->
                  RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_e))
              w1 evars w2 _UU03b8_2
          in
          bind w2 (consume _UU03a3_e req w2 evars2) (fun w3 _UU03b8_3 _ ->
            bind w3 (demonic (Some result) w3 _UU03c4_)
              (fun w4 _UU03b8_4 res ->
              let evars4 =
                persist
                  (persistent_subst
                    (RiscvPmpBase.coq_SubstEnv (fun b ->
                      RiscvPmpBase.coq_SubstTerm b.Binding.coq_type)
                      _UU03a3_e))
                  w2 evars2 w4 (acc_trans w2 w3 w4 _UU03b8_3 _UU03b8_4)
              in
              bind w4
                (produce (Coq_ctx.Coq_snoc (_UU03a3_e, { Binding.name =
                  result; Binding.coq_type = _UU03c4_ })) ens w4
                  (RiscvPmpBase.sub_snoc _UU03a3_e w4.wctx evars4
                    { Binding.name = result; Binding.coq_type = _UU03c4_ }
                    res))
                (fun w5 _UU03b8_5 _ ->
                pure w5
                  (persist
                    (persistent_subst (RiscvPmpBase.coq_SubstTerm _UU03c4_))
                    w4 res w5 _UU03b8_5))))))

    (** val call_lemma :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Lemma -> (RiscvPmpBase.coq_SStore, RiscvPmpBase.coq_Unit
        coq_SHeapSpec) coq_Impl coq_Valid **)

    let call_lemma _UU0394_ lem w0 args =
      let { lemma_logic_variables = _UU03a3_e; lemma_patterns = _UU03b4_e;
        lemma_precondition = req; lemma_postcondition = ens } = lem
      in
      bind w0 (lift_purespec w0 (SPureSpec.angelic_ctx id w0 _UU03a3_e))
        (fun w1 _UU03b8_1 evars ->
        bind w1
          (lift_purespec w1
            (SPureSpec.assert_eq_nenv w1 _UU0394_
              (RiscvPmpBase.Coq_amsg.Coq_mk (RiscvPmpBase.coq_SubstConst,
              RiscvPmpBase.substSU_Const, RiscvPmpBase.coq_SubstLawsConst,
              RiscvPmpBase.coq_OccursCheck_Const, RiscvPmpBase.erase_Const,
              (Obj.magic { debug_string_pathcondition = w0.wco;
                debug_string_message = (String ((Ascii (Coq_true, Coq_true,
                Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
                Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
                Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
                Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
                Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
                ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
                Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
                ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
                Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
                Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
                ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                Coq_false, Coq_true, Coq_true, Coq_false)),
                EmptyString)))))))))))))))))))))))))))))))))))))))) })))
              (RiscvPmpBase.subst (RiscvPmpBase.subst_localstore _UU0394_)
                _UU03a3_e _UU03b4_e w1.wctx evars)
              (persist
                (persistent_subst (RiscvPmpBase.subst_localstore _UU0394_))
                w0 args w1 _UU03b8_1)))
          (fun w2 _UU03b8_2 _ ->
          let evars2 =
            persist
              (persistent_subst
                (RiscvPmpBase.coq_SubstEnv (fun b ->
                  RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_e))
              w1 evars w2 _UU03b8_2
          in
          bind w2 (consume _UU03a3_e req w2 evars2) (fun w3 _UU03b8_3 _ ->
            let evars3 =
              persist
                (persistent_subst
                  (RiscvPmpBase.coq_SubstEnv (fun b ->
                    RiscvPmpBase.coq_SubstTerm b.Binding.coq_type) _UU03a3_e))
                w2 evars2 w3 _UU03b8_3
            in
            produce _UU03a3_e ens w3 evars3)))
   end

  (** val coq_RPureSpec :
      ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SPureSpec, 'a2
      coq_CPureSpec) Coq_logicalrelation.coq_Rel **)

  let coq_RPureSpec rA =
    Obj.magic Coq_logicalrelation.coq_RImpl
      (Coq_logicalrelation.coq_RBox
        (Coq_logicalrelation.coq_RImpl rA LogicalSoundness.coq_RProp))
      LogicalSoundness.coq_RProp

  module PureSpec =
   struct
    (** val coq_RPureSpec :
        ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SPureSpec, 'a2
        coq_CPureSpec) Coq_logicalrelation.coq_Rel **)

    let coq_RPureSpec rA =
      Obj.magic Coq_logicalrelation.coq_RImpl
        (Coq_logicalrelation.coq_RBox
          (Coq_logicalrelation.coq_RImpl rA LogicalSoundness.coq_RProp))
        LogicalSoundness.coq_RProp
   end

  (** val coq_RHeapSpec :
      ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SHeapSpec, 'a2
      coq_CHeapSpec) Coq_logicalrelation.coq_Rel **)

  let coq_RHeapSpec rA =
    Obj.magic Coq_logicalrelation.coq_RImpl
      (Coq_logicalrelation.coq_RBox
        (Coq_logicalrelation.coq_RImpl rA
          (Coq_logicalrelation.coq_RImpl Coq_logicalrelation.coq_RHeap
            LogicalSoundness.coq_RProp)))
      (Coq_logicalrelation.coq_RImpl Coq_logicalrelation.coq_RHeap
        LogicalSoundness.coq_RProp)

  module HeapSpec =
   struct
   end

  (** val z_term :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Z
      -> RiscvPmpBase.coq_Term **)

  let z_term _ =
    Obj.magic (fun x -> RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int, x))

  (** val sep_contract_logvars :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx **)

  let sep_contract_logvars _UU0394_ _UU03a3_ =
    Coq_ctx.cat
      (Coq_ctx.map (fun pat ->
        let x = pat.Binding.name in
        let _UU03c3_ = pat.Binding.coq_type in
        { Binding.name = x; Binding.coq_type = _UU03c3_ }) _UU0394_)
      _UU03a3_

  (** val create_localstore :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_SStore **)

  let create_localstore _UU0394_ _UU03a3_ =
    Coq_env.tabulate _UU0394_ (fun pat ->
      let x = pat.Binding.name in
      let _UU03c3_ = pat.Binding.coq_type in
      (fun xIn -> RiscvPmpBase.Coq_term_var (x, _UU03c3_,
      (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type = _UU03c3_ }
        (Coq_ctx.map (fun pat0 -> { Binding.name = pat0.Binding.name;
          Binding.coq_type = pat0.Binding.coq_type }) _UU0394_)
        _UU03a3_
        (Coq_ctx.in_map (fun pat0 ->
          let y = pat0.Binding.name in
          let _UU03c4_ = pat0.Binding.coq_type in
          { Binding.name = y; Binding.coq_type = _UU03c4_ }) { Binding.name =
          x; Binding.coq_type = _UU03c3_ } _UU0394_ xIn)))))

  (** val asn_and_regs :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (RiscvPmpBase.coq_Reg -> Coq_asn.coq_Assertion) -> Coq_asn.coq_Assertion **)

  let asn_and_regs _ f =
    Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x1), (Coq_asn.Coq_sep
      ((f RiscvPmpBase.Coq_x2), (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x3),
      (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x4), (Coq_asn.Coq_sep
      ((f RiscvPmpBase.Coq_x5), (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x6),
      (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x7), (Coq_asn.Coq_sep
      ((f RiscvPmpBase.Coq_x8), (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x9),
      (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x10), (Coq_asn.Coq_sep
      ((f RiscvPmpBase.Coq_x11), (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x12),
      (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x13), (Coq_asn.Coq_sep
      ((f RiscvPmpBase.Coq_x14), (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x15),
      (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x16), (Coq_asn.Coq_sep
      ((f RiscvPmpBase.Coq_x17), (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x18),
      (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x19), (Coq_asn.Coq_sep
      ((f RiscvPmpBase.Coq_x20), (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x21),
      (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x22), (Coq_asn.Coq_sep
      ((f RiscvPmpBase.Coq_x23), (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x24),
      (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x25), (Coq_asn.Coq_sep
      ((f RiscvPmpBase.Coq_x26), (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x27),
      (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x28), (Coq_asn.Coq_sep
      ((f RiscvPmpBase.Coq_x29), (Coq_asn.Coq_sep ((f RiscvPmpBase.Coq_x30),
      (f RiscvPmpBase.Coq_x31))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val asn_regs_ptsto :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_asn.coq_Assertion **)

  let asn_regs_ptsto _UU03a3_ =
    asn_and_regs _UU03a3_ (fun r -> Coq_asn.Coq_exist
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_xlenbits, (Coq_asn.Coq_chunk (Coq_chunk_ptsreg
      (RiscvPmpBase.ty_xlenbits, r, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_xlenbits, O)))))))

  (** val term_pmp_entries :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term **)

  let term_pmp_entries _UU03a3_ =
    RiscvPmpBase.term_list _UU03a3_ (Coq_ty.Coq_prod
      (RiscvPmpBase.ty_pmpcfgidx, RiscvPmpBase.ty_pmpaddridx)) (Coq_cons
      ((RiscvPmpBase.Coq_term_binop (RiscvPmpBase.ty_pmpcfgidx,
      RiscvPmpBase.ty_pmpaddridx, (Coq_ty.Coq_prod
      (RiscvPmpBase.ty_pmpcfgidx, RiscvPmpBase.ty_pmpaddridx)),
      (Coq_bop.Coq_pair (RiscvPmpBase.ty_pmpcfgidx,
      RiscvPmpBase.ty_pmpaddridx)), (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_pmpcfgidx, (Obj.magic PMP0CFG))),
      (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_pmpaddridx,
      (Obj.magic PMPADDR0))))), (Coq_cons ((RiscvPmpBase.Coq_term_binop
      (RiscvPmpBase.ty_pmpcfgidx, RiscvPmpBase.ty_pmpaddridx,
      (Coq_ty.Coq_prod (RiscvPmpBase.ty_pmpcfgidx,
      RiscvPmpBase.ty_pmpaddridx)), (Coq_bop.Coq_pair
      (RiscvPmpBase.ty_pmpcfgidx, RiscvPmpBase.ty_pmpaddridx)),
      (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_pmpcfgidx,
      (Obj.magic PMP1CFG))), (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_pmpaddridx, (Obj.magic PMPADDR1))))), Coq_nil))))

  module Coq_rv_notations =
   struct
   end
 end
