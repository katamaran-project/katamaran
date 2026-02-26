open Ascii
open BinNums
open BinOps
open Bitvector
open CRelationClasses
open Classes
open Context
open Datatypes
open Environment
open Hoare
open Predicates
open Prelude
open Signature
open Specif
open String
open TypeDecl
open UnOps
open Variables
open Base
open Finite
open Interface
open Modalities

type __ = Obj.t
type coq_Pred = __
type 'a coq_CPureSpec = __
type 'a coq_CHeapSpec = __

let __ = let rec f _ = Obj.repr f in Obj.repr f

module MakeExecutor =
 functor (B:Base0.Base) ->
 functor (SIG:sig
  type _UU1d477_

  val _UU1d477__Ty : _UU1d477_ -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx

  val _UU1d477__inst :
    _UU1d477_ -> (Coq_ty.coq_Ty, Coq_ty.coq_Val, __) Coq_env.abstract

  val _UU1d477__eq_dec : _UU1d477_ coq_EqDec

  type _UU1d46f_

  val _UU1d46f__Ty : _UU1d46f_ -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx

  val _UU1d46f__is_dup : _UU1d46f_ coq_IsDuplicable

  val _UU1d46f__eq_dec : _UU1d46f_ coq_EqDec

  val _UU1d46f__precise : _UU1d46f_ -> _UU1d46f_ B.coq_Precise option

  type coq_PredicateDef = { lptsreg : (Coq_ty.coq_Ty ->
                                      B._UU1d479__UU1d46c__UU1d46e_ ->
                                      Coq_ty.coq_Val -> __);
                            luser : (_UU1d46f_ -> (Coq_ty.coq_Ty,
                                    Coq_ty.coq_Val) Coq_env.coq_Env -> __) }

  val lptsreg :
    bi -> coq_PredicateDef -> Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_
    -> Coq_ty.coq_Val -> __

  val luser :
    bi -> coq_PredicateDef -> _UU1d46f_ -> (Coq_ty.coq_Ty, Coq_ty.coq_Val)
    Coq_env.coq_Env -> __

  type coq_Formula =
  | Coq_formula_user of _UU1d477_
     * (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env
  | Coq_formula_bool of B.coq_Term
  | Coq_formula_prop of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                        Coq_ctx.coq_Ctx
     * B.coq_Sub
     * (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named
  | Coq_formula_relop of Coq_ty.coq_Ty * Coq_bop.coq_RelOp * B.coq_Term
     * B.coq_Term
  | Coq_formula_true
  | Coq_formula_false
  | Coq_formula_and of coq_Formula * coq_Formula
  | Coq_formula_or of coq_Formula * coq_Formula

  val coq_Formula_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (_UU1d477_ -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> 'a1) ->
    (B.coq_Term -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> B.coq_Sub -> (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val,
    __) abstract_named -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp ->
    B.coq_Term -> B.coq_Term -> 'a1) -> 'a1 -> 'a1 -> (coq_Formula -> 'a1 ->
    coq_Formula -> 'a1 -> 'a1) -> (coq_Formula -> 'a1 -> coq_Formula -> 'a1
    -> 'a1) -> coq_Formula -> 'a1

  val coq_Formula_rec :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (_UU1d477_ -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> 'a1) ->
    (B.coq_Term -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> B.coq_Sub -> (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val,
    __) abstract_named -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp ->
    B.coq_Term -> B.coq_Term -> 'a1) -> 'a1 -> 'a1 -> (coq_Formula -> 'a1 ->
    coq_Formula -> 'a1 -> 'a1) -> (coq_Formula -> 'a1 -> coq_Formula -> 'a1
    -> 'a1) -> coq_Formula -> 'a1

  val formula_relop_neg :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
    coq_Formula

  val subSU_formula : 'a1 B.coq_SubstUniv -> ('a1, coq_Formula) B.coq_SubstSU

  val sub_formula : coq_Formula B.coq_Subst

  val substlaws_formula : coq_Formula B.coq_SubstLaws

  val coq_OccursCheckFormula : coq_Formula B.coq_OccursCheck

  val coq_GenOccursCheckFormula :
    'a1 B.coq_SubstUniv -> 'a1 B.coq_SubstUnivMeet -> 'a1 B.coq_SubstUnivVar
    -> 'a1 B.coq_SubstUniv -> 'a1 B.coq_SubstUnivMeet -> 'a1 B.coq_SubstUniv
    -> 'a1 B.coq_SubstUnivMeet -> ('a1, coq_Formula) B.coq_GenOccursCheck

  type coq_PathCondition = coq_Formula Coq_ctx.coq_Ctx

  val formula_eqs_ctx :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_Term)
    Coq_env.coq_Env -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env ->
    coq_PathCondition

  val formula_eqs_nctx :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
    Coq_ty.coq_Ty, B.coq_Term) coq_NamedEnv -> ('a1, Coq_ty.coq_Ty,
    B.coq_Term) coq_NamedEnv -> coq_PathCondition

  type coq_EFormula =
  | Coq_eformula_user of _UU1d477_
     * (Coq_ty.coq_Ty, B.coq_ETerm) Coq_env.coq_Env
  | Coq_eformula_bool of B.coq_ETerm
  | Coq_eformula_prop of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                         Coq_ctx.coq_Ctx
     * ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, B.coq_ETerm)
       Coq_env.coq_Env
     * (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named
  | Coq_eformula_relop of Coq_ty.coq_Ty * Coq_bop.coq_RelOp * B.coq_ETerm
     * B.coq_ETerm
  | Coq_eformula_true
  | Coq_eformula_false
  | Coq_eformula_and of coq_EFormula * coq_EFormula
  | Coq_eformula_or of coq_EFormula * coq_EFormula

  val coq_EFormula_rect :
    (_UU1d477_ -> (Coq_ty.coq_Ty, B.coq_ETerm) Coq_env.coq_Env -> 'a1) ->
    (B.coq_ETerm -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding,
    B.coq_ETerm) Coq_env.coq_Env -> (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val,
    __) abstract_named -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp ->
    B.coq_ETerm -> B.coq_ETerm -> 'a1) -> 'a1 -> 'a1 -> (coq_EFormula -> 'a1
    -> coq_EFormula -> 'a1 -> 'a1) -> (coq_EFormula -> 'a1 -> coq_EFormula ->
    'a1 -> 'a1) -> coq_EFormula -> 'a1

  val coq_EFormula_rec :
    (_UU1d477_ -> (Coq_ty.coq_Ty, B.coq_ETerm) Coq_env.coq_Env -> 'a1) ->
    (B.coq_ETerm -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding,
    B.coq_ETerm) Coq_env.coq_Env -> (coq_LVar, Coq_ty.coq_Ty, Coq_ty.coq_Val,
    __) abstract_named -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp ->
    B.coq_ETerm -> B.coq_ETerm -> 'a1) -> 'a1 -> 'a1 -> (coq_EFormula -> 'a1
    -> coq_EFormula -> 'a1 -> 'a1) -> (coq_EFormula -> 'a1 -> coq_EFormula ->
    'a1 -> 'a1) -> coq_EFormula -> 'a1

  val erase_formula :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Formula -> coq_EFormula

  val erase_Formula : (coq_Formula, coq_EFormula) B.coq_Erase

  type 'v coq_GChunk =
  | Coq_chunk_user of _UU1d46f_ * (Coq_ty.coq_Ty, 'v) Coq_env.coq_Env
  | Coq_chunk_ptsreg of Coq_ty.coq_Ty * B._UU1d479__UU1d46c__UU1d46e_ * 'v
  | Coq_chunk_conj of 'v coq_GChunk * 'v coq_GChunk
  | Coq_chunk_wand of 'v coq_GChunk * 'v coq_GChunk

  val coq_GChunk_rect :
    (_UU1d46f_ -> (Coq_ty.coq_Ty, 'a1) Coq_env.coq_Env -> 'a2) ->
    (Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> 'a1 -> 'a2) -> ('a1
    coq_GChunk -> 'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> ('a1 coq_GChunk ->
    'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> 'a1 coq_GChunk -> 'a2

  val coq_GChunk_rec :
    (_UU1d46f_ -> (Coq_ty.coq_Ty, 'a1) Coq_env.coq_Env -> 'a2) ->
    (Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> 'a1 -> 'a2) -> ('a1
    coq_GChunk -> 'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> ('a1 coq_GChunk ->
    'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> 'a1 coq_GChunk -> 'a2

  type coq_SCChunk = Coq_ty.coq_Val coq_GChunk

  type coq_Chunk = B.coq_Term coq_GChunk

  val coq_NoConfusionPackage_GChunk : 'a1 coq_GChunk coq_NoConfusionPackage

  val chunk_isdup : 'a1 coq_GChunk coq_IsDuplicable

  val chunk_eqb :
    (Coq_ty.coq_Ty -> 'a1 -> 'a1 -> bool) -> 'a1 coq_GChunk -> 'a1 coq_GChunk
    -> bool

  val chunk_eqb_spec :
    (Coq_ty.coq_Ty -> 'a1 -> 'a1 -> bool) -> (Coq_ty.coq_Ty -> 'a1 -> 'a1 ->
    reflect) -> 'a1 coq_GChunk -> 'a1 coq_GChunk -> reflect

  val coq_SubstChunk : coq_Chunk B.coq_Subst

  val coq_SubstSUChunk : 'a1 B.coq_SubstUniv -> ('a1, coq_Chunk) B.coq_SubstSU

  val substlaws_chunk : coq_Chunk B.coq_SubstLaws

  val map_GChunk :
    (Coq_ty.coq_Ty -> 'a1 -> 'a2) -> 'a1 coq_GChunk -> 'a2 coq_GChunk

  val inst_chunk : (coq_Chunk, coq_SCChunk) B.coq_Inst

  val coq_OccursCheckChunk : coq_Chunk B.coq_OccursCheck

  val coq_GenOccursCheckChunk :
    (B.coq_WeakensTo, coq_Chunk) B.coq_GenOccursCheck

  type coq_SCHeap = coq_SCChunk list

  type coq_SHeap = coq_Chunk list

  val inst_heap : (coq_SHeap, coq_SCHeap) B.coq_Inst

  val peval_chunk :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Chunk -> coq_Chunk

  val try_consume_chunk_exact :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_SHeap -> coq_Chunk -> coq_SHeap option

  val match_chunk_user_precise_clause_1 :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    _UU1d46f_ -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env ->
    (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> _UU1d46f_ -> sumbool ->
    (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> coq_PathCondition option

  val match_chunk_user_precise :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    _UU1d46f_ -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env ->
    (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> coq_Chunk ->
    coq_PathCondition option

  val try_consume_chunk_user_precise :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    _UU1d46f_ -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env ->
    (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> coq_SHeap -> (coq_SHeap,
    coq_PathCondition) prod option

  val match_chunk_ptsreg_precise_clause_1 :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> Coq_ty.coq_Ty ->
    B._UU1d479__UU1d46c__UU1d46e_ -> sumbool -> B.coq_Term -> B.coq_Term
    option

  val match_chunk_ptsreg_precise :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> coq_Chunk -> B.coq_Term
    option

  val find_chunk_ptsreg_precise :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> coq_SHeap ->
    (B.coq_Term, coq_SHeap) prod option

  val try_consume_chunk_ptsreg_precise :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> coq_SHeap -> B.coq_Term
    -> (coq_SHeap, coq_PathCondition) prod option

  val try_consume_chunk_precise :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_SHeap -> coq_Chunk -> (coq_SHeap, coq_PathCondition) prod option

  val interpret_chunk :
    bi -> coq_PredicateDef -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Chunk -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> __

  val interpret_scchunk : bi -> coq_PredicateDef -> coq_SCChunk -> __

  val interpret_scheap : bi -> coq_PredicateDef -> coq_SCHeap -> __

  type coq_EChunk = B.coq_ETerm coq_GChunk

  val coq_Erase_Chunk : (coq_Chunk, coq_EChunk) B.coq_Erase

  type coq_World = { wctx : (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                            Coq_ctx.coq_Ctx;
                     wco : coq_PathCondition }

  val wctx :
    coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val wco : coq_World -> coq_PathCondition

  val wnil : coq_World

  val wlctx :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_World

  val wsnoc :
    coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_World

  val term_var_zero :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> B.coq_Term

  val wlet :
    coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    Coq_ty.coq_Val -> coq_World

  val wcat :
    coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_World

  val wformula : coq_World -> coq_Formula -> coq_World

  val wpathcondition : coq_World -> coq_PathCondition -> coq_World

  val wsubst :
    coq_World -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term -> coq_World

  val wmatch :
    coq_World -> Coq_ty.coq_Ty -> B.coq_Term -> coq_LVar B.coq_Pattern ->
    coq_LVar B.coq_PatternCase -> coq_World

  val wmatchvar_patternvars :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar
    -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_LVar B.coq_Pattern -> coq_LVar B.coq_PatternCase ->
    B.coq_Sub

  val wmatchvar :
    coq_World -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_LVar B.coq_Pattern -> coq_LVar
    B.coq_PatternCase -> coq_World

  type 'a coq_Valid = coq_World -> 'a

  type ('a, 'b) coq_Impl = 'a -> 'b

  type ('i, 'a) coq_Forall = 'i -> 'a

  type coq_Tri =
  | Coq_tri_id
  | Coq_tri_cons of coq_World * coq_LVar * Coq_ty.coq_Ty
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * B.coq_Term * coq_Tri

  val coq_Tri_rect :
    (coq_World -> 'a1) -> (coq_World -> coq_World -> coq_LVar ->
    Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> B.coq_Term -> coq_Tri -> 'a1 -> 'a1) -> coq_World ->
    coq_World -> coq_Tri -> 'a1

  val coq_Tri_rec :
    (coq_World -> 'a1) -> (coq_World -> coq_World -> coq_LVar ->
    Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> B.coq_Term -> coq_Tri -> 'a1 -> 'a1) -> coq_World ->
    coq_World -> coq_Tri -> 'a1

  val tri_comp :
    coq_World -> coq_World -> coq_World -> coq_Tri -> coq_Tri -> coq_Tri

  val sub_wmatch_patctx :
    coq_World -> Coq_ty.coq_Ty -> B.coq_Term -> coq_LVar B.coq_Pattern ->
    coq_LVar B.coq_PatternCase -> B.coq_Sub

  val sub_triangular : coq_World -> coq_World -> coq_Tri -> B.coq_Sub

  val sub_triangular_inv : coq_World -> coq_World -> coq_Tri -> B.coq_Sub

  type coq_Acc =
  | Coq_acc_refl
  | Coq_acc_sub of coq_World * B.coq_Sub

  val coq_Acc_rect :
    coq_World -> 'a1 -> (coq_World -> B.coq_Sub -> __ -> 'a1) -> coq_World ->
    coq_Acc -> 'a1

  val coq_Acc_rec :
    coq_World -> 'a1 -> (coq_World -> B.coq_Sub -> __ -> 'a1) -> coq_World ->
    coq_Acc -> 'a1

  val acc_trans :
    coq_World -> coq_World -> coq_World -> coq_Acc -> coq_Acc -> coq_Acc

  val sub_acc : coq_World -> coq_World -> coq_Acc -> B.coq_Sub

  type 'a coq_Box = coq_World -> coq_Acc -> 'a

  val acc_wnil_init : coq_World -> coq_Acc

  val acc_wlctx_valuation :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
    Coq_env.coq_Env -> coq_Acc

  val acc_snoc_right :
    coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Acc

  val acc_cat_right :
    coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Acc

  val acc_snoc_left :
    coq_World -> coq_World -> coq_Acc -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> B.coq_Term -> coq_Acc

  val acc_snoc_left' :
    coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> B.coq_Term
    -> coq_Acc

  val acc_cat_left :
    coq_World -> coq_World -> coq_Acc -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Sub -> coq_Acc

  val acc_formula_right : coq_World -> coq_Formula -> coq_Acc

  val acc_pathcondition_right : coq_World -> coq_PathCondition -> coq_Acc

  val acc_subst_right :
    coq_World -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term -> coq_Acc

  val acc_match_right :
    coq_World -> Coq_ty.coq_Ty -> B.coq_Term -> coq_LVar B.coq_Pattern ->
    coq_LVar B.coq_PatternCase -> coq_Acc

  val sub_matchvar_right :
    coq_World -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_LVar B.coq_Pattern -> coq_LVar
    B.coq_PatternCase -> B.coq_Sub

  val acc_matchvar_right :
    coq_World -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_LVar B.coq_Pattern -> coq_LVar
    B.coq_PatternCase -> coq_Acc

  val acc_triangular : coq_World -> coq_World -> coq_Tri -> coq_Acc

  val preorder_acc : (coq_World, coq_Acc) coq_PreOrder

  val coq_K :
    (('a1, 'a2) coq_Impl coq_Box, ('a1 coq_Box, 'a2 coq_Box) coq_Impl)
    coq_Impl coq_Valid

  val coq_T : ('a1 coq_Box, 'a1) coq_Impl coq_Valid

  val four : ('a1 coq_Box, 'a1 coq_Box coq_Box) coq_Impl coq_Valid

  val valid_box : 'a1 coq_Valid -> 'a1 coq_Box coq_Valid

  val fmap_box :
    ('a1, 'a2) coq_Impl coq_Valid -> ('a1 coq_Box, 'a2 coq_Box) coq_Impl
    coq_Valid

  val extend_box :
    ('a1 coq_Box, 'a2) coq_Impl coq_Valid -> ('a1 coq_Box, 'a2 coq_Box)
    coq_Impl coq_Valid

  val comp :
    (('a2, 'a3) coq_Impl, (('a1, 'a2) coq_Impl, ('a1, 'a3) coq_Impl)
    coq_Impl) coq_Impl coq_Valid

  module ModalNotations :
   sig
   end

  type 'a coq_Persistent = ('a, 'a coq_Box) coq_Impl coq_Valid

  val persist : 'a1 coq_Persistent -> ('a1, 'a1 coq_Box) coq_Impl coq_Valid

  val persistent_box : 'a1 coq_Box coq_Persistent

  val persistent_subst : 'a1 B.coq_Subst -> 'a1 coq_Persistent

  type 'a coq_Tm = 'a

  val bi_pred : coq_World -> bi

  type 't coq_InstPred =
  | MkInstPred

  val instpred_option : 'a1 coq_InstPred -> 'a1 B.coq_Option coq_InstPred

  val instpred_pair :
    'a1 coq_InstPred -> 'a2 coq_InstPred -> ('a1, 'a2) B.coq_Pair coq_InstPred

  val instpred_ctx_inst : 'a1 coq_InstPred -> 'a1 Coq_ctx.coq_Ctx coq_InstPred

  val instpred_inst_formula : coq_Formula coq_InstPred

  type coq_Solver =
    coq_World -> coq_PathCondition -> (coq_World, (coq_Tri,
    coq_PathCondition) prod) sigT option

  val solver_null : coq_Solver

  type coq_SolverUserOnly =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    _UU1d477_ -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env ->
    coq_PathCondition B.coq_Option

  val simplify_all :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_Formula -> coq_PathCondition -> coq_PathCondition option) ->
    coq_PathCondition -> coq_PathCondition -> coq_PathCondition option

  val solveruseronly_simplify_formula :
    coq_SolverUserOnly -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Formula -> coq_PathCondition -> coq_PathCondition
    option

  val solveruseronly_to_solver : coq_SolverUserOnly -> coq_Solver

  val solver_compose : coq_Solver -> coq_Solver -> coq_Solver

  module DList :
   sig
    type coq_DList =
      coq_PathCondition -> coq_PathCondition B.coq_Option
      (* singleton inductive, whose constructor was MkDList *)

    val raw :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DList -> coq_PathCondition -> coq_PathCondition B.coq_Option

    val instpred_dlist : coq_DList coq_InstPred

    val singleton :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_DList

    val run :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DList -> coq_PathCondition B.coq_Option

    val error :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DList

    val empty :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DList

    val cat :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DList -> coq_DList -> coq_DList
   end

  val solver : coq_Solver

  type coq_Message = { msg_function : string; msg_message : string;
                       msg_program_context : (coq_PVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx;
                       msg_localstore : B.coq_SStore; msg_heap : coq_SHeap;
                       msg_pathcondition : coq_PathCondition }

  val msg_function :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Message -> string

  val msg_message :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Message -> string

  val msg_program_context :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Message -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val msg_localstore :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Message -> B.coq_SStore

  val msg_heap :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Message -> coq_SHeap

  val msg_pathcondition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Message -> coq_PathCondition

  type coq_EMessage = { emsg_function : string; emsg_message : string;
                        emsg_program_context : (coq_PVar, Coq_ty.coq_Ty)
                                               Binding.coq_Binding
                                               Coq_ctx.coq_Ctx;
                        emsg_localstore : (coq_PVar, Coq_ty.coq_Ty,
                                          B.coq_ETerm) coq_NamedEnv;
                        emsg_heap : coq_EChunk list;
                        emsg_pathcondition : coq_EFormula list }

  val emsg_function : coq_EMessage -> string

  val emsg_message : coq_EMessage -> string

  val emsg_program_context :
    coq_EMessage -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val emsg_localstore :
    coq_EMessage -> (coq_PVar, Coq_ty.coq_Ty, B.coq_ETerm) coq_NamedEnv

  val emsg_heap : coq_EMessage -> coq_EChunk list

  val emsg_pathcondition : coq_EMessage -> coq_EFormula list

  val coq_EraseMessage : (coq_Message, coq_EMessage) B.coq_Erase

  val coq_SubstMessage : coq_Message B.coq_Subst

  val coq_SubstSUMessage :
    'a1 B.coq_SubstUniv -> ('a1, coq_Message) B.coq_SubstSU

  val coq_SubstLawsMessage : coq_Message B.coq_SubstLaws

  val coq_OccursCheckMessage : coq_Message B.coq_OccursCheck

  val coq_GenOccursCheckMessage :
    (B.coq_WeakensTo, coq_Message) B.coq_GenOccursCheck

  val coq_Error_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Message -> 'a1

  val coq_Error_rec :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Message -> 'a1

  val coq_Obligation_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    B.Coq_amsg.coq_AMessage -> coq_Formula -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> (__ -> 'a1) -> 'a1

  val coq_Obligation_rec :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    B.Coq_amsg.coq_AMessage -> coq_Formula -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> (__ -> 'a1) -> 'a1

  val coq_Debug_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 ->
    (__ -> 'a2) -> 'a2

  val coq_Debug_rec :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 ->
    (__ -> 'a2) -> 'a2

  module SymProp :
   sig
    type coq_SymProp =
    | Coq_angelic_binary of coq_SymProp * coq_SymProp
    | Coq_demonic_binary of coq_SymProp * coq_SymProp
    | Coq_error of B.Coq_amsg.coq_AMessage
    | Coq_block
    | Coq_assertk of coq_Formula * B.Coq_amsg.coq_AMessage * coq_SymProp
    | Coq_assumek of coq_Formula * coq_SymProp
    | Coq_angelicv of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_SymProp
    | Coq_demonicv of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_SymProp
    | Coq_assert_vareq of coq_LVar * Coq_ty.coq_Ty
       * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * B.coq_Term * B.Coq_amsg.coq_AMessage * coq_SymProp
    | Coq_assume_vareq of coq_LVar * Coq_ty.coq_Ty
       * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * B.coq_Term * coq_SymProp
    | Coq_pattern_match of Coq_ty.coq_Ty * B.coq_Term
       * coq_LVar B.coq_Pattern * (coq_LVar B.coq_PatternCase -> coq_SymProp)
    | Coq_pattern_match_var of coq_LVar * Coq_ty.coq_Ty
       * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * coq_LVar B.coq_Pattern * (coq_LVar B.coq_PatternCase -> coq_SymProp)
    | Coq_debug of B.Coq_amsg.coq_AMessage * coq_SymProp

    val coq_SymProp_rect :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> 'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
      'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> B.Coq_amsg.coq_AMessage -> 'a1)
      -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> coq_Formula -> B.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1)
      -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term ->
      B.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar ->
      Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> B.coq_Term -> coq_SymProp -> 'a1 -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> B.coq_Term -> coq_LVar B.coq_Pattern -> (coq_LVar
      B.coq_PatternCase -> coq_SymProp) -> (coq_LVar B.coq_PatternCase ->
      'a1) -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_LVar
      B.coq_Pattern -> (coq_LVar B.coq_PatternCase -> coq_SymProp) ->
      (coq_LVar B.coq_PatternCase -> 'a1) -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp -> 'a1

    val coq_SymProp_rec :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> 'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
      'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> B.Coq_amsg.coq_AMessage -> 'a1)
      -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> coq_Formula -> B.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1)
      -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term ->
      B.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar ->
      Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> B.coq_Term -> coq_SymProp -> 'a1 -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> B.coq_Term -> coq_LVar B.coq_Pattern -> (coq_LVar
      B.coq_PatternCase -> coq_SymProp) -> (coq_LVar B.coq_PatternCase ->
      'a1) -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_LVar
      B.coq_Pattern -> (coq_LVar B.coq_PatternCase -> coq_SymProp) ->
      (coq_LVar B.coq_PatternCase -> 'a1) -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp -> 'a1

    val trunc :
      nat -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> coq_SymProp

    val angelic_close0 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> coq_SymProp

    val demonic_close0 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> coq_SymProp

    val demonic_close :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> coq_SymProp

    val angelic_list' :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> ('a1 -> coq_SymProp) -> 'a1 B.coq_List -> coq_SymProp

    val angelic_list :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> ('a1 -> coq_SymProp) -> 'a1 B.coq_List ->
      coq_SymProp

    val demonic_list' :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> ('a1 -> coq_SymProp) -> 'a1 B.coq_List -> coq_SymProp

    val demonic_list :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      -> coq_SymProp) -> 'a1 B.coq_List -> coq_SymProp

    val angelic_finite :
      ('a1, 'a1) coq_RelDecision -> 'a1 coq_Finite -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> ('a1 -> coq_SymProp) -> coq_SymProp

    val demonic_finite :
      ('a1, 'a1) coq_RelDecision -> 'a1 coq_Finite -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1 ->
      coq_SymProp) -> coq_SymProp

    val angelic_pattern_match :
      Coq_ty.coq_Ty -> coq_LVar B.coq_Pattern -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term -> (coq_LVar
      B.coq_PatternCase -> coq_SymProp) -> coq_SymProp

    val angelic_pattern_match_var :
      Coq_ty.coq_Ty -> coq_LVar B.coq_Pattern -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> (coq_LVar
      B.coq_PatternCase -> coq_SymProp) -> coq_SymProp

    val demonic_pattern_match :
      Coq_ty.coq_Ty -> coq_LVar B.coq_Pattern -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term -> (coq_LVar
      B.coq_PatternCase -> coq_SymProp) -> coq_SymProp

    val demonic_pattern_match_var :
      Coq_ty.coq_Ty -> coq_LVar B.coq_Pattern -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> (coq_LVar
      B.coq_PatternCase -> coq_SymProp) -> coq_SymProp

    val assume_pathcondition_without_solver' :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_SymProp -> coq_SymProp

    val assert_pathcondition_without_solver' :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> coq_PathCondition -> coq_SymProp ->
      coq_SymProp

    val assume_pathcondition_without_solver :
      coq_World -> coq_PathCondition -> coq_SymProp -> coq_SymProp

    val assert_pathcondition_without_solver :
      coq_World -> B.Coq_amsg.coq_AMessage -> coq_PathCondition ->
      coq_SymProp -> coq_SymProp

    val assume_triangular :
      coq_World -> coq_World -> coq_Tri -> coq_SymProp -> coq_SymProp

    val assert_triangular :
      coq_World -> coq_World -> B.Coq_amsg.coq_AMessage -> coq_Tri ->
      (B.Coq_amsg.coq_AMessage -> coq_SymProp) -> coq_SymProp

    module Coq_notations :
     sig
     end

    module Statistics :
     sig
      val size :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> coq_N

      type coq_Count = { block : coq_N; error : coq_N; debug : coq_N }

      val block : coq_Count -> coq_N

      val error : coq_Count -> coq_N

      val debug : coq_Count -> coq_N

      val empty : coq_Count

      val inc_block : coq_Count -> coq_Count

      val inc_error : coq_Count -> coq_Count

      val inc_debug : coq_Count -> coq_Count

      val count_nodes :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> coq_Count -> coq_Count

      val count_to_stats : coq_Count -> coq_Stats
     end
   end

  module Postprocessing :
   sig
    type ('m1, 'm2) coq_AngelicBinaryFailMsg = { angelic_binary_failmsg_left : 
                                                 'm1;
                                                 angelic_binary_failmsg_right : 
                                                 'm2 }

    val angelic_binary_failmsg_left :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
      'a2) coq_AngelicBinaryFailMsg -> 'a1

    val angelic_binary_failmsg_right :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
      'a2) coq_AngelicBinaryFailMsg -> 'a2

    val coq_SubstAngelicBinaryFailMsg :
      'a1 B.coq_Subst -> 'a2 B.coq_Subst -> ('a1, 'a2)
      coq_AngelicBinaryFailMsg B.coq_Subst

    val coq_SubstSUAngelicBinaryFailMsg :
      ('a1, 'a2) B.coq_SubstSU -> ('a1, 'a3) B.coq_SubstSU -> ('a1, ('a2,
      'a3) coq_AngelicBinaryFailMsg) B.coq_SubstSU

    val coq_SubstLawsAngelicBinaryFailMsg :
      'a1 B.coq_Subst -> 'a1 B.coq_SubstLaws -> 'a2 B.coq_Subst -> 'a2
      B.coq_SubstLaws -> ('a1, 'a2) coq_AngelicBinaryFailMsg B.coq_SubstLaws

    val coq_OccursCheckAngelicBinaryFailMsg :
      'a1 B.coq_OccursCheck -> 'a2 B.coq_OccursCheck -> ('a1, 'a2)
      coq_AngelicBinaryFailMsg B.coq_OccursCheck

    val coq_GenOccursCheckAngelicBinaryFailMsg :
      (B.coq_WeakensTo, 'a1) B.coq_SubstSU -> 'a1 B.coq_Subst ->
      (B.coq_WeakensTo, 'a2) B.coq_SubstSU -> 'a2 B.coq_Subst ->
      (B.coq_WeakensTo, 'a1) B.coq_GenOccursCheck -> (B.coq_WeakensTo, 'a2)
      B.coq_GenOccursCheck -> (B.coq_WeakensTo, ('a1, 'a2)
      coq_AngelicBinaryFailMsg) B.coq_GenOccursCheck

    type ('mE1, 'mE2) coq_EAngelicBinaryFailMsg =
    | MkEAngelicBinaryFailMsg of 'mE1 * 'mE2

    val coq_EAngelicBinaryFailMsg_rect :
      ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_EAngelicBinaryFailMsg -> 'a3

    val coq_EAngelicBinaryFailMsg_rec :
      ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_EAngelicBinaryFailMsg -> 'a3

    val coq_EraseAngelicBinaryFailMsg :
      ('a1, 'a2) B.coq_Erase -> ('a3, 'a4) B.coq_Erase -> (('a1, 'a3)
      coq_AngelicBinaryFailMsg, ('a2, 'a4) coq_EAngelicBinaryFailMsg)
      B.coq_Erase

    val angelic_binary_prune :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp -> SymProp.coq_SymProp

    val demonic_binary_prune :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp -> SymProp.coq_SymProp

    val assertk_prune :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> B.Coq_amsg.coq_AMessage -> SymProp.coq_SymProp ->
      SymProp.coq_SymProp

    val assumek_prune :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> SymProp.coq_SymProp -> SymProp.coq_SymProp

    val angelicv_prune :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> SymProp.coq_SymProp ->
      SymProp.coq_SymProp

    val demonicv_prune :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> SymProp.coq_SymProp ->
      SymProp.coq_SymProp

    val assume_vareq_prune :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term -> SymProp.coq_SymProp
      -> SymProp.coq_SymProp

    val assert_vareq_prune :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term ->
      B.Coq_amsg.coq_AMessage -> SymProp.coq_SymProp -> SymProp.coq_SymProp

    val prune :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    module SolveEvars :
     sig
      val assert_msgs_formulas :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (B.Coq_amsg.coq_AMessage, coq_Formula) B.coq_Pair Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp

      type coq_ECtx =
      | Coq_ectx of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                    Coq_ctx.coq_Ctx
         * (B.Coq_amsg.coq_AMessage, coq_Formula) B.coq_Pair Coq_ctx.coq_Ctx

      val coq_ECtx_rect :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (B.Coq_amsg.coq_AMessage, coq_Formula) B.coq_Pair Coq_ctx.coq_Ctx ->
        'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
        -> coq_ECtx -> 'a1

      val coq_ECtx_rec :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (B.Coq_amsg.coq_AMessage, coq_Formula) B.coq_Pair Coq_ctx.coq_Ctx ->
        'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
        -> coq_ECtx -> 'a1

      val ectx_refl :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_ECtx

      val ectx_formula :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_ECtx -> B.Coq_amsg.coq_AMessage -> coq_Formula -> coq_ECtx

      val ectx_snoc :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_ECtx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_ECtx

      val ectx_subst :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_ECtx -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term -> coq_ECtx option

      val plug :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_ECtx -> SymProp.coq_SymProp -> SymProp.coq_SymProp

      val plug_msg :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_ECtx -> B.Coq_amsg.coq_AMessage -> B.Coq_amsg.coq_AMessage

      val push :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_ECtx -> SymProp.coq_SymProp -> SymProp.coq_SymProp
     end

    val solve_evars :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    module SolveUvars :
     sig
      val assume_pathcondition :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> SymProp.coq_SymProp -> SymProp.coq_SymProp

      type coq_UCtx =
      | Coq_uctx of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                    Coq_ctx.coq_Ctx
         * coq_PathCondition

      val coq_UCtx_rect :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx -> 'a1

      val coq_UCtx_rec :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx -> 'a1

      val uctx_refl :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_UCtx

      val uctx_formula :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_UCtx -> coq_Formula -> coq_UCtx

      val uctx_snoc :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_UCtx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_UCtx

      val uctx_subst :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_UCtx -> coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term -> coq_UCtx option

      val plug :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_UCtx -> SymProp.coq_SymProp -> SymProp.coq_SymProp

      val plug_error :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_UCtx -> B.Coq_amsg.coq_AMessage -> SymProp.coq_SymProp

      val push :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_UCtx -> SymProp.coq_SymProp -> SymProp.coq_SymProp
     end

    val solve_uvars :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    module Experimental :
     sig
      type coq_Ephemeral = (SolveEvars.coq_ECtx, SolveUvars.coq_UCtx) sum

      type coq_EProp =
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Ephemeral -> SymProp.coq_SymProp

      val angelic_binary :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_EProp -> coq_EProp -> coq_EProp

      val angelicv :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_EProp ->
        coq_EProp

      val demonic_binary :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_EProp -> coq_EProp -> coq_EProp

      val error :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        B.Coq_amsg.coq_AMessage -> coq_EProp
     end

    val weaken_symprop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> B.coq_WeakensTo -> SymProp.coq_SymProp

    val coq_SubstSU_SymProp :
      (B.coq_WeakensTo, SymProp.coq_SymProp) B.coq_SubstSU

    type coq_UQSymProp = (B.coq_WeakensTo, SymProp.coq_SymProp) B.coq_Weakened

    val from_uqSymProp :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp -> SymProp.coq_SymProp

    val uq_angelic_binary :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp -> coq_UQSymProp -> coq_UQSymProp

    val uq_demonic_binary :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp -> coq_UQSymProp -> coq_UQSymProp

    val uq_error :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> coq_UQSymProp

    val uq_block :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp

    val uq_assertk :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> B.Coq_amsg.coq_AMessage -> coq_UQSymProp -> coq_UQSymProp

    val uq_assumek :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_UQSymProp -> coq_UQSymProp

    val uq_angelicv :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_UQSymProp ->
      coq_UQSymProp

    val uq_demonicv :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_UQSymProp ->
      coq_UQSymProp

    val uq_assert_vareq :
      coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term ->
      B.Coq_amsg.coq_AMessage -> coq_UQSymProp -> coq_UQSymProp

    val uq_assume_vareq :
      coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term -> coq_UQSymProp ->
      coq_UQSymProp

    val uq_debug :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> coq_UQSymProp -> coq_UQSymProp

    val to_uqSymProp :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> coq_UQSymProp

    val unquantify :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    val weakenWorld :
      coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> B.coq_WeakensTo -> coq_World

    val weakenWorld_acc :
      coq_World -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> B.coq_WeakensTo -> coq_Acc
   end

  val postprocess :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    SymProp.coq_SymProp -> SymProp.coq_SymProp

  val postprocess2 :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    SymProp.coq_SymProp -> SymProp.coq_SymProp

  module Erasure :
   sig
    type coq_ESymProp =
    | Coq_eangelic_binary of coq_ESymProp * coq_ESymProp
    | Coq_edemonic_binary of coq_ESymProp * coq_ESymProp
    | Coq_eerror of B.Coq_amsg.coq_EAMessage
    | Coq_eblock
    | Coq_eassertk of coq_EFormula * coq_ESymProp
    | Coq_eassumek of coq_EFormula * coq_ESymProp
    | Coq_eangelicv of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_ESymProp
    | Coq_edemonicv of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_ESymProp
    | Coq_eassert_vareq of coq_LVar * Coq_ty.coq_Ty * nat * B.coq_ETerm
       * coq_ESymProp
    | Coq_eassume_vareq of coq_LVar * Coq_ty.coq_Ty * nat * B.coq_ETerm
       * coq_ESymProp
    | Coq_epattern_match of Coq_ty.coq_Ty * B.coq_ETerm
       * coq_LVar B.coq_Pattern * (coq_LVar B.coq_PatternCase -> coq_ESymProp)
    | Coq_epattern_match_var of coq_LVar * Coq_ty.coq_Ty * nat
       * coq_LVar B.coq_Pattern * (coq_LVar B.coq_PatternCase -> coq_ESymProp)
    | Coq_edebug of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                    Coq_ctx.coq_Ctx
       * B.Coq_amsg.coq_AMessage * coq_ESymProp

    val coq_ESymProp_rect :
      (coq_ESymProp -> 'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_ESymProp ->
      'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (B.Coq_amsg.coq_EAMessage -> 'a1)
      -> 'a1 -> (coq_EFormula -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_EFormula
      -> coq_ESymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> coq_ESymProp -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_ESymProp -> 'a1 -> 'a1) ->
      (coq_LVar -> Coq_ty.coq_Ty -> nat -> B.coq_ETerm -> coq_ESymProp -> 'a1
      -> 'a1) -> (coq_LVar -> Coq_ty.coq_Ty -> nat -> B.coq_ETerm ->
      coq_ESymProp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> B.coq_ETerm ->
      coq_LVar B.coq_Pattern -> (coq_LVar B.coq_PatternCase -> coq_ESymProp)
      -> (coq_LVar B.coq_PatternCase -> 'a1) -> 'a1) -> (coq_LVar ->
      Coq_ty.coq_Ty -> nat -> coq_LVar B.coq_Pattern -> (coq_LVar
      B.coq_PatternCase -> coq_ESymProp) -> (coq_LVar B.coq_PatternCase ->
      'a1) -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> B.Coq_amsg.coq_AMessage -> coq_ESymProp -> 'a1 ->
      'a1) -> coq_ESymProp -> 'a1

    val coq_ESymProp_rec :
      (coq_ESymProp -> 'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_ESymProp ->
      'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (B.Coq_amsg.coq_EAMessage -> 'a1)
      -> 'a1 -> (coq_EFormula -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_EFormula
      -> coq_ESymProp -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> coq_ESymProp -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_ESymProp -> 'a1 -> 'a1) ->
      (coq_LVar -> Coq_ty.coq_Ty -> nat -> B.coq_ETerm -> coq_ESymProp -> 'a1
      -> 'a1) -> (coq_LVar -> Coq_ty.coq_Ty -> nat -> B.coq_ETerm ->
      coq_ESymProp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> B.coq_ETerm ->
      coq_LVar B.coq_Pattern -> (coq_LVar B.coq_PatternCase -> coq_ESymProp)
      -> (coq_LVar B.coq_PatternCase -> 'a1) -> 'a1) -> (coq_LVar ->
      Coq_ty.coq_Ty -> nat -> coq_LVar B.coq_Pattern -> (coq_LVar
      B.coq_PatternCase -> coq_ESymProp) -> (coq_LVar B.coq_PatternCase ->
      'a1) -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> B.Coq_amsg.coq_AMessage -> coq_ESymProp -> 'a1 ->
      'a1) -> coq_ESymProp -> 'a1

    val erase_symprop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> coq_ESymProp

    val erase_SymProp : (SymProp.coq_SymProp, coq_ESymProp) B.coq_Erase

    val erase_valuation :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
      Coq_env.coq_Env -> (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list

    val erase_Valuation :
      (((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
      Coq_env.coq_Env, (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list) B.coq_Erase

    val inst_env' :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> (Coq_ty.coq_Ty ->
      B.coq_ETerm -> Coq_ty.coq_Val option) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx
      -> (Coq_ty.coq_Ty, B.coq_ETerm) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
      Coq_ty.coq_Val) Coq_env.coq_Env option

    val inst_namedenv' :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> (Coq_ty.coq_Ty ->
      B.coq_ETerm -> Coq_ty.coq_Val option) -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty,
      B.coq_ETerm) coq_NamedEnv -> ('a1, Coq_ty.coq_Ty, Coq_ty.coq_Val)
      coq_NamedEnv option

    val inst_eterm :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> Coq_ty.coq_Ty ->
      B.coq_ETerm -> Coq_ty.coq_Val option

    val inst_namedenv :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty,
      B.coq_ETerm) coq_NamedEnv -> ('a1, Coq_ty.coq_Ty, Coq_ty.coq_Val)
      coq_NamedEnv option

    val inst_env :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> Coq_ty.coq_Ty
      Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_ETerm) Coq_env.coq_Env ->
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) Coq_env.coq_Env option

    val inst_eformula :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> coq_EFormula -> __ option

    val list_remove : 'a1 list -> nat -> 'a1 list

    module Coq_notations :
     sig
     end
   end

  module Coq_notations :
   sig
   end

  val modality_assuming : coq_World -> coq_World -> coq_Acc -> modality

  val modality_forgetting : coq_World -> coq_World -> coq_Acc -> modality

  module Coq_logicalrelation :
   sig
    type ('aT, 'a) coq_Rel =
      'a -> ('aT, coq_Pred) coq_Impl coq_Valid
      (* singleton inductive, whose constructor was MkRel *)

    val coq_RInst : ('a1, 'a2) B.coq_Inst -> ('a1, 'a2) coq_Rel

    val coq_RInstPropIff : 'a1 coq_InstPred -> ('a1, __) coq_Rel

    val coq_RBox : ('a1, 'a2) coq_Rel -> ('a1 coq_Box, 'a2) coq_Rel

    val coq_RImpl :
      ('a1, 'a2) coq_Rel -> ('a3, 'a4) coq_Rel -> (('a1, 'a3) coq_Impl, 'a2
      -> 'a4) coq_Rel

    val coq_RForall :
      ('a1 -> ('a2, 'a3) coq_Rel) -> (('a1, 'a2) coq_Forall, 'a1 -> 'a3)
      coq_Rel

    val coq_RVal : Coq_ty.coq_Ty -> (B.coq_Term, Coq_ty.coq_Val) coq_Rel

    val coq_RNEnv :
      ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (('a1,
      Coq_ty.coq_Ty, B.coq_Term) coq_NamedEnv, ('a1, Coq_ty.coq_Ty,
      Coq_ty.coq_Val) coq_NamedEnv) coq_Rel

    val coq_REnv :
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ((Coq_ty.coq_Ty, B.coq_Term)
      Coq_env.coq_Env, (Coq_ty.coq_Ty, Coq_ty.coq_Val) Coq_env.coq_Env)
      coq_Rel

    val coq_RUnit : (B.coq_Unit, coq_unit) coq_Rel

    val coq_RPathCondition : (coq_PathCondition, __) coq_Rel

    val coq_RFormula : (coq_Formula, __) coq_Rel

    val coq_RChunk : (coq_Chunk, coq_SCChunk) coq_Rel

    val coq_RMsg : ('a2, 'a3) coq_Rel -> (('a1, 'a2) coq_Impl, 'a3) coq_Rel

    val coq_RList : ('a1, 'a2) coq_Rel -> ('a1 list, 'a2 list) coq_Rel

    val coq_RHeap : (coq_SHeap, coq_SCHeap) coq_Rel

    val coq_RConst : ('a1 B.coq_Const, 'a1) coq_Rel

    val coq_RProd :
      ('a1, 'a2) coq_Rel -> ('a3, 'a4) coq_Rel -> (('a1, 'a3) prod, ('a2,
      'a4) prod) coq_Rel

    val coq_RMatchResult :
      Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> ('a1 B.coq_SMatchResult, 'a1
      B.coq_MatchResult) coq_Rel

    val coq_RIn :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In, Coq_ty.coq_Val)
      coq_Rel

    module Coq_notations :
     sig
     end
   end

  module RSolve :
   sig
   end

  module AutorewriteUnifLogic :
   sig
   end

  module LogicalSoundness :
   sig
    val coq_RProp : (SymProp.coq_SymProp, __) Coq_logicalrelation.coq_Rel
   end

  module Coq_asn :
   sig
    type coq_Assertion =
    | Coq_formula of coq_Formula
    | Coq_chunk of coq_Chunk
    | Coq_chunk_angelic of coq_Chunk
    | Coq_pattern_match of Coq_ty.coq_Ty * B.coq_Term
       * coq_LVar B.coq_Pattern
       * (coq_LVar B.coq_PatternCase -> coq_Assertion)
    | Coq_sep of coq_Assertion * coq_Assertion
    | Coq_or of coq_Assertion * coq_Assertion
    | Coq_exist of coq_LVar * Coq_ty.coq_Ty * coq_Assertion
    | Coq_debug

    val coq_Assertion_rect :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
      B.coq_Term -> coq_LVar B.coq_Pattern -> (coq_LVar B.coq_PatternCase ->
      coq_Assertion) -> (coq_LVar B.coq_PatternCase -> 'a1) -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Assertion -> 'a1 -> coq_Assertion -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion ->
      'a1 -> coq_Assertion -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar -> Coq_ty.coq_Ty ->
      coq_Assertion -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1) -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion ->
      'a1

    val coq_Assertion_rec :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
      B.coq_Term -> coq_LVar B.coq_Pattern -> (coq_LVar B.coq_PatternCase ->
      coq_Assertion) -> (coq_LVar B.coq_PatternCase -> 'a1) -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Assertion -> 'a1 -> coq_Assertion -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion ->
      'a1 -> coq_Assertion -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar -> Coq_ty.coq_Ty ->
      coq_Assertion -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1) -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion ->
      'a1

    val match_bool :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> coq_Assertion -> coq_Assertion -> coq_Assertion

    val match_enum :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.enumi -> B.coq_Term -> (Coq_ty.enumt -> coq_Assertion) ->
      coq_Assertion

    val match_sum :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> coq_LVar ->
      coq_Assertion -> coq_LVar -> coq_Assertion -> coq_Assertion

    val match_list :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> B.coq_Term -> coq_Assertion -> coq_LVar -> coq_LVar ->
      coq_Assertion -> coq_Assertion

    val match_prod :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> coq_LVar -> coq_LVar ->
      coq_Assertion -> coq_Assertion

    val match_tuple :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term -> coq_LVar
      B.coq_TuplePat -> coq_Assertion -> coq_Assertion

    val match_record :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.recordi -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> B.coq_Term -> coq_LVar B.coq_RecordPat ->
      coq_Assertion -> coq_Assertion

    val match_union_alt :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.unioni -> B.coq_Term -> (Coq_ty.unionk -> (coq_LVar,
      coq_Assertion) B.coq_Alternative) -> coq_Assertion

    val exs :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Assertion -> coq_Assertion

    val sub_assertion : coq_Assertion B.coq_Subst

    val coq_OccursCheckAssertion : coq_Assertion B.coq_OccursCheck

    val is_pure :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Assertion -> bool

    val interpret :
      bi -> coq_PredicateDef -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Assertion -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> __

    module Coq_notations :
     sig
     end
   end

  type coq_SepContract = { sep_contract_logic_variables : (coq_LVar,
                                                          Coq_ty.coq_Ty)
                                                          Binding.coq_Binding
                                                          Coq_ctx.coq_Ctx;
                           sep_contract_localstore : B.coq_SStore;
                           sep_contract_precondition : Coq_asn.coq_Assertion;
                           sep_contract_result : coq_LVar;
                           sep_contract_postcondition : Coq_asn.coq_Assertion }

  val sep_contract_logic_variables :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx

  val sep_contract_localstore :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> B.coq_SStore

  val sep_contract_precondition :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> Coq_asn.coq_Assertion

  val sep_contract_result :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> coq_LVar

  val sep_contract_postcondition :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> Coq_asn.coq_Assertion

  type coq_Lemma = { lemma_logic_variables : (coq_LVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx;
                     lemma_patterns : B.coq_SStore;
                     lemma_precondition : Coq_asn.coq_Assertion;
                     lemma_postcondition : Coq_asn.coq_Assertion }

  val lemma_logic_variables :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Lemma -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val lemma_patterns :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Lemma -> B.coq_SStore

  val lemma_precondition :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Lemma -> Coq_asn.coq_Assertion

  val lemma_postcondition :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Lemma -> Coq_asn.coq_Assertion

  val lint_assertion :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_asn.coq_Assertion -> bool

  val lint_contract :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> bool

  val lint_lemma :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Lemma -> bool

  val sep_contract_pun_logvars :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  type coq_SepContractPun = { sep_contract_pun_logic_variables : (coq_LVar,
                                                                 Coq_ty.coq_Ty)
                                                                 Binding.coq_Binding
                                                                 Coq_ctx.coq_Ctx;
                              sep_contract_pun_precondition : Coq_asn.coq_Assertion;
                              sep_contract_pun_result : coq_LVar;
                              sep_contract_pun_postcondition : Coq_asn.coq_Assertion }

  val sep_contract_pun_logic_variables :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx

  val sep_contract_pun_precondition :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> Coq_asn.coq_Assertion

  val sep_contract_pun_result :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> coq_LVar

  val sep_contract_pun_postcondition :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> Coq_asn.coq_Assertion

  val sep_contract_pun_to_sep_contract :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> coq_SepContract

  val inst_contract_localstore :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> (coq_PVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv

  val interpret_contract_precondition :
    bi -> coq_PredicateDef -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_SepContract -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> __

  val interpret_contract_postcondition :
    bi -> coq_PredicateDef -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_SepContract -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
    Coq_ty.coq_Val -> __

  module GenericSolver :
   sig
    val simplify_bool :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> DList.coq_DList

    val simplify_bool_neg :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> DList.coq_DList

    val simplify_eqb :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_default_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_default_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> B.coq_Term ->
      Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_and_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_or_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_not_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_relop_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
      Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_pair_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term ->
      Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_cons_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_binop_bvapp_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      nat -> nat -> B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_binop_bvcons_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      nat -> B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_inl_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_unop_inr_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_unop_neg_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_signed_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      nat -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_unsigned_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      nat -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> B.coq_Term ->
      Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_tuple_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_Term)
      Coq_env.coq_Env -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_union_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.unioni -> Coq_ty.unionk -> B.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_record_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, B.coq_Term)
      coq_NamedEnv -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_default :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_minus :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_times :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_unop_default :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> B.coq_Term ->
      B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_plus :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_and :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_or :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_pair :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term ->
      B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_cons :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq_binop_append :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq_binop_bvapp' :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> nat
      -> nat -> B.coq_Term -> B.coq_Term -> nat -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq_binop_bvapp :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> nat
      -> nat -> B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_bvcons' :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> nat
      -> B.coq_Term -> B.coq_Term -> nat -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_bvcons :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> nat
      -> B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_relop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
      B.coq_Term -> DList.coq_DList

    val simplify_eq_binop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_unop_inl :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq_unop_inr :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq_unop_get_slice_int :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_unop_signed :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> nat
      -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_unop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> B.coq_Term ->
      B.coq_Term -> DList.coq_DList

    val formula_eqs_ctx :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_Term)
      Coq_env.coq_Env -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env ->
      DList.coq_DList

    val formula_eqs_nctx :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> ('a1,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
      Coq_ty.coq_Ty, B.coq_Term) coq_NamedEnv -> ('a1, Coq_ty.coq_Ty,
      B.coq_Term) coq_NamedEnv -> DList.coq_DList

    val simplify_eq_tuple :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_Term)
      Coq_env.coq_Env -> B.coq_Term -> DList.coq_DList

    val simplify_eq_record :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, B.coq_Term)
      coq_NamedEnv -> B.coq_Term -> DList.coq_DList

    val simplify_eq_union :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.unioni -> Coq_ty.unionk -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_relopb :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val peval_formula_le' :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> coq_Formula

    val peval_formula_le :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> B.coq_Term -> coq_Formula

    val peval_formula_lt :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> B.coq_Term -> coq_Formula

    val peval_formula_relop_neg :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
      coq_Formula

    val simplify_le :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_bvule :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_bvult :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_lt :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_relop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val smart_and :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> coq_Formula

    val coq_PathCondition_to_Formula :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_Formula

    val coq_PathCondition_to_DList :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> DList.coq_DList

    val simplify_formula :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> DList.coq_DList

    val simplify_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> DList.coq_DList

    val occurs_check_lt :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
      B.coq_Term -> B.coq_Term option

    val try_unify_bool :
      coq_World -> B.coq_Term -> (coq_World, coq_Tri) sigT option

    val try_unify_eq :
      coq_World -> Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> (coq_World,
      coq_Tri) sigT option

    val try_unify_formula :
      coq_World -> coq_Formula -> (coq_World, coq_Tri) sigT option

    val unify_formula :
      coq_World -> coq_Formula -> (coq_World, (coq_Tri, coq_PathCondition)
      prod) sigT

    val unify_pathcondition :
      coq_World -> coq_PathCondition -> (coq_World, (coq_Tri,
      coq_PathCondition) prod) sigT

    val formula_eqb_clause_3 :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> bool) -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d477_ -> (Coq_ty.coq_Ty,
      B.coq_Term) Coq_env.coq_Env -> _UU1d477_ -> sumbool -> (Coq_ty.coq_Ty,
      B.coq_Term) Coq_env.coq_Env -> bool

    val formula_eqb_clause_2 :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> bool) -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
      Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term -> Coq_ty.coq_Ty ->
      sumbool -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term -> bool

    val formula_eqb :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> bool

    val smart_or :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> coq_Formula

    val formula_simplifies :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> coq_Formula option

    val assumption_formula :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_Formula -> coq_PathCondition ->
      coq_PathCondition

    val assumption_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_PathCondition -> coq_PathCondition ->
      coq_PathCondition

    val solver_generic : coq_Solver
   end

  val combined_solver : coq_Solver

  module CPureSpec :
   sig
    module Coq_notations :
     sig
     end
   end

  module CHeapSpec :
   sig
    module Coq_notations :
     sig
     end
   end

  module CStatistics :
   sig
    type coq_PropShape =
    | Coq_psfork of coq_PropShape * coq_PropShape
    | Coq_psquant of coq_PropShape
    | Coq_pspruned
    | Coq_psfinish
    | Coq_psother

    val coq_PropShape_rect :
      (coq_PropShape -> 'a1 -> coq_PropShape -> 'a1 -> 'a1) -> (coq_PropShape
      -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_PropShape -> 'a1

    val coq_PropShape_rec :
      (coq_PropShape -> 'a1 -> coq_PropShape -> 'a1 -> 'a1) -> (coq_PropShape
      -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_PropShape -> 'a1

    val shape_to_stats : coq_PropShape -> coq_Stats

    type coq_ShallowStats = coq_Stats

    val stats : coq_ShallowStats -> coq_Stats

    val stats_true : coq_ShallowStats

    val stats_false : coq_ShallowStats

    val stats_finish : coq_ShallowStats

    val stats_true' : coq_ShallowStats

    val stats_false' : coq_ShallowStats

    val stats_eq : 'a1 -> 'a1 -> coq_ShallowStats

    val stats_zle : coq_Z -> coq_Z -> coq_ShallowStats

    val stats_and : coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats

    val stats_or : coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats

    val stats_impl : coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats

    val stats_forall :
      (__ -> __) -> ('a1 -> coq_ShallowStats) -> coq_ShallowStats

    val stats_exists :
      (__ -> __) -> ('a1 -> coq_ShallowStats) -> coq_ShallowStats
   end

  type coq_DebugAsn = { debug_asn_pathcondition : coq_PathCondition;
                        debug_asn_heap : coq_SHeap }

  val debug_asn_pathcondition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugAsn -> coq_PathCondition

  val debug_asn_heap :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugAsn -> coq_SHeap

  val coq_SubstDebugAsn : coq_DebugAsn B.coq_Subst

  val coq_SubstSUDebugAsn : (B.coq_WeakensTo, coq_DebugAsn) B.coq_SubstSU

  val coq_SubstLawsDebugAsn : coq_DebugAsn B.coq_SubstLaws

  val coq_OccursCheckDebugAsn : coq_DebugAsn B.coq_OccursCheck

  type coq_DebugConsumeChunk = { debug_consume_chunk_pathcondition : 
                                 coq_PathCondition;
                                 debug_consume_chunk_heap : coq_SHeap;
                                 debug_consume_chunk_chunk : coq_Chunk }

  val debug_consume_chunk_pathcondition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugConsumeChunk -> coq_PathCondition

  val debug_consume_chunk_heap :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugConsumeChunk -> coq_SHeap

  val debug_consume_chunk_chunk :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugConsumeChunk -> coq_Chunk

  type coq_EDebugConsumeChunk = { edebug_consume_chunk_pathcondition : 
                                  coq_EFormula list;
                                  edebug_consume_chunk_heap : coq_EChunk list;
                                  edebug_consume_chunk_chunk : coq_EChunk }

  val edebug_consume_chunk_pathcondition :
    coq_EDebugConsumeChunk -> coq_EFormula list

  val edebug_consume_chunk_heap : coq_EDebugConsumeChunk -> coq_EChunk list

  val edebug_consume_chunk_chunk : coq_EDebugConsumeChunk -> coq_EChunk

  val coq_Erase_DebugConsumeChunk :
    (coq_DebugConsumeChunk, coq_EDebugConsumeChunk) B.coq_Erase

  val coq_SubstDebugConsumeChunk : coq_DebugConsumeChunk B.coq_Subst

  val coq_SubstSUDebugConsumeChunk :
    'a1 B.coq_SubstUniv -> ('a1, coq_DebugConsumeChunk) B.coq_SubstSU

  val coq_SubstLawsDebugConsumeChunk : coq_DebugConsumeChunk B.coq_SubstLaws

  val coq_OccursCheckDebugConsumeChunk :
    coq_DebugConsumeChunk B.coq_OccursCheck

  type coq_DebugReadRegister = { debug_read_register_pathcondition : 
                                 coq_PathCondition;
                                 debug_read_register_heap : coq_SHeap;
                                 debug_read_register_type : Coq_ty.coq_Ty;
                                 debug_read_register_register : B._UU1d479__UU1d46c__UU1d46e_ }

  val debug_read_register_pathcondition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> coq_PathCondition

  val debug_read_register_heap :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> coq_SHeap

  val debug_read_register_type :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> Coq_ty.coq_Ty

  val debug_read_register_register :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> B._UU1d479__UU1d46c__UU1d46e_

  type coq_EDebugReadRegister = { edebug_read_register_pathcondition : 
                                  coq_EFormula list;
                                  edebug_read_register_heap : coq_EChunk list;
                                  edebug_read_register_type : Coq_ty.coq_Ty;
                                  edebug_read_register_register : B._UU1d479__UU1d46c__UU1d46e_ }

  val edebug_read_register_pathcondition :
    coq_EDebugReadRegister -> coq_EFormula list

  val edebug_read_register_heap : coq_EDebugReadRegister -> coq_EChunk list

  val edebug_read_register_type : coq_EDebugReadRegister -> Coq_ty.coq_Ty

  val edebug_read_register_register :
    coq_EDebugReadRegister -> B._UU1d479__UU1d46c__UU1d46e_

  val coq_EraseDebugReadRegister :
    (coq_DebugReadRegister, coq_EDebugReadRegister) B.coq_Erase

  val coq_SubstDebugReadRegister : coq_DebugReadRegister B.coq_Subst

  val coq_SubstSUDebugReadRegister :
    'a1 B.coq_SubstUniv -> ('a1, coq_DebugReadRegister) B.coq_SubstSU

  val coq_SubstLawsDebugReadRegister : coq_DebugReadRegister B.coq_SubstLaws

  val coq_OccursCheckDebugReadRegister :
    coq_DebugReadRegister B.coq_OccursCheck

  type coq_DebugWriteRegister = { debug_write_register_pathcondition : 
                                  coq_PathCondition;
                                  debug_write_register_heap : coq_SHeap;
                                  debug_write_register_type : Coq_ty.coq_Ty;
                                  debug_write_register_register : B._UU1d479__UU1d46c__UU1d46e_;
                                  debug_write_register_value : B.coq_Term }

  val debug_write_register_pathcondition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> coq_PathCondition

  val debug_write_register_heap :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> coq_SHeap

  val debug_write_register_type :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> Coq_ty.coq_Ty

  val debug_write_register_register :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> B._UU1d479__UU1d46c__UU1d46e_

  val debug_write_register_value :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> B.coq_Term

  type coq_EDebugWriteRegister = { edebug_write_register_pathcondition : 
                                   coq_EFormula list;
                                   edebug_write_register_heap : coq_EChunk
                                                                list;
                                   edebug_write_register_type : Coq_ty.coq_Ty;
                                   edebug_write_register_register : B._UU1d479__UU1d46c__UU1d46e_;
                                   edebug_write_register_value : B.coq_ETerm }

  val edebug_write_register_pathcondition :
    coq_EDebugWriteRegister -> coq_EFormula list

  val edebug_write_register_heap : coq_EDebugWriteRegister -> coq_EChunk list

  val edebug_write_register_type : coq_EDebugWriteRegister -> Coq_ty.coq_Ty

  val edebug_write_register_register :
    coq_EDebugWriteRegister -> B._UU1d479__UU1d46c__UU1d46e_

  val edebug_write_register_value : coq_EDebugWriteRegister -> B.coq_ETerm

  val coq_EraseDebugWriteRegister :
    (coq_DebugWriteRegister, coq_EDebugWriteRegister) B.coq_Erase

  val coq_SubstDebugWriteRegister : coq_DebugWriteRegister B.coq_Subst

  val coq_SubstSUDebugWriteRegister :
    'a1 B.coq_SubstUniv -> ('a1, coq_DebugWriteRegister) B.coq_SubstSU

  val coq_SubstLawsDebugWriteRegister : coq_DebugWriteRegister B.coq_SubstLaws

  val coq_OccursCheckDebugWriteRegister :
    coq_DebugWriteRegister B.coq_OccursCheck

  type coq_DebugString = { debug_string_pathcondition : coq_PathCondition;
                           debug_string_message : string }

  val debug_string_pathcondition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugString -> coq_PathCondition

  val debug_string_message :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugString -> string

  type coq_EDebugString = { edebug_string_pathcondition : coq_EFormula list;
                            edebug_string_message : string }

  val edebug_string_pathcondition : coq_EDebugString -> coq_EFormula list

  val edebug_string_message : coq_EDebugString -> string

  val coq_EraseDebugString : (coq_DebugString, coq_EDebugString) B.coq_Erase

  val coq_SubstDebugString : coq_DebugString B.coq_Subst

  val coq_SubstSUDebugString :
    (B.coq_WeakensTo, coq_DebugString) B.coq_SubstSU

  val coq_SubstLawsDebugString : coq_DebugString B.coq_SubstLaws

  val coq_OccursCheckDebugString : coq_DebugString B.coq_OccursCheck

  type coq_DebugAssertFormula = { debug_assert_formula_pathcondition : 
                                  coq_PathCondition;
                                  debug_assert_formula_heap : coq_SHeap;
                                  debug_assert_formula_formula : coq_Formula }

  val debug_assert_formula_pathcondition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugAssertFormula -> coq_PathCondition

  val debug_assert_formula_heap :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugAssertFormula -> coq_SHeap

  val debug_assert_formula_formula :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugAssertFormula -> coq_Formula

  val coq_SubstDebugAssertFormula : coq_DebugAssertFormula B.coq_Subst

  val coq_SubstSUDebugAssertFormula :
    (B.coq_WeakensTo, coq_DebugAssertFormula) B.coq_SubstSU

  val coq_SubstLawsDebugAssertFormula : coq_DebugAssertFormula B.coq_SubstLaws

  val coq_OccursCheckDebugAssertFormula :
    coq_DebugAssertFormula B.coq_OccursCheck

  type 'a coq_SPureSpec =
    (('a, SymProp.coq_SymProp) coq_Impl coq_Box, SymProp.coq_SymProp) coq_Impl

  module SPureSpec :
   sig
    val run :
      (B.coq_Unit coq_SPureSpec, SymProp.coq_SymProp) coq_Impl coq_Valid

    val pure : ('a1, 'a1 coq_SPureSpec) coq_Impl coq_Valid

    val bind :
      ('a1 coq_SPureSpec, (('a1, 'a2 coq_SPureSpec) coq_Impl coq_Box, 'a2
      coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    module Coq_notations :
     sig
     end

    val block : 'a1 coq_SPureSpec coq_Valid

    val error :
      (B.Coq_amsg.coq_AMessage, 'a1 coq_SPureSpec) coq_Impl coq_Valid

    val angelic :
      coq_LVar option -> (Coq_ty.coq_Ty, B.coq_Term coq_SPureSpec) coq_Forall
      coq_Valid

    val demonic :
      coq_LVar option -> (Coq_ty.coq_Ty, B.coq_Term coq_SPureSpec) coq_Forall
      coq_Valid

    val angelic_ctx :
      ('a1 -> coq_LVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) coq_NamedEnv
      coq_SPureSpec) coq_Forall coq_Valid

    val demonic_ctx :
      ('a1 -> coq_LVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) coq_NamedEnv
      coq_SPureSpec) coq_Forall coq_Valid

    val assert_pathcondition :
      (B.Coq_amsg.coq_AMessage, (coq_PathCondition, B.coq_Unit coq_SPureSpec)
      coq_Impl) coq_Impl coq_Valid

    val assume_pathcondition :
      (coq_PathCondition, B.coq_Unit coq_SPureSpec) coq_Impl coq_Valid

    val assert_formula :
      (B.Coq_amsg.coq_AMessage, (coq_Formula, B.coq_Unit coq_SPureSpec)
      coq_Impl) coq_Impl coq_Valid

    val assume_formula :
      (coq_Formula, B.coq_Unit coq_SPureSpec) coq_Impl coq_Valid

    val angelic_binary :
      ('a1 coq_SPureSpec, ('a1 coq_SPureSpec, 'a1 coq_SPureSpec) coq_Impl)
      coq_Impl coq_Valid

    val demonic_binary :
      ('a1 coq_SPureSpec, ('a1 coq_SPureSpec, 'a1 coq_SPureSpec) coq_Impl)
      coq_Impl coq_Valid

    val angelic_list' :
      ('a1, ('a1 list, 'a1 coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val angelic_list :
      (B.Coq_amsg.coq_AMessage, ('a1 list, 'a1 coq_SPureSpec) coq_Impl)
      coq_Impl coq_Valid

    val demonic_list' :
      ('a1, ('a1 list, 'a1 coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val demonic_list : ('a1 list, 'a1 coq_SPureSpec) coq_Impl coq_Valid

    val angelic_finite :
      ('a1, 'a1) coq_RelDecision -> 'a1 coq_Finite ->
      (B.Coq_amsg.coq_AMessage, 'a1 B.coq_Const coq_SPureSpec) coq_Impl
      coq_Valid

    val demonic_finite :
      ('a1, 'a1) coq_RelDecision -> 'a1 coq_Finite -> 'a1 B.coq_Const
      coq_SPureSpec coq_Valid

    val angelic_pattern_match' :
      ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern ->
      (B.Coq_amsg.coq_AMessage, (B.coq_Term, 'a1 B.coq_SMatchResult
      coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val angelic_pattern_match :
      ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern ->
      (B.Coq_amsg.coq_AMessage, (B.coq_Term, 'a1 B.coq_SMatchResult
      coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val demonic_pattern_match' :
      ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term,
      'a1 B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val demonic_pattern_match :
      ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term,
      'a1 B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match_regular :
      ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term,
      'a1 B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match_var :
      ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> coq_LVar -> 'a1 B.coq_Pattern ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In, 'a1
      B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match' :
      ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term,
      'a1 B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match :
      ('a1 -> coq_LVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term,
      'a1 B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val debug :
      (B.Coq_amsg.coq_AMessage, ('a1 coq_SPureSpec, 'a1 coq_SPureSpec)
      coq_Impl) coq_Impl coq_Valid

    val assert_eq_env :
      (Coq_ty.coq_Ty Coq_ctx.coq_Ctx, (B.Coq_amsg.coq_AMessage,
      ((Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env, ((Coq_ty.coq_Ty,
      B.coq_Term) Coq_env.coq_Env, B.coq_Unit coq_SPureSpec) coq_Impl)
      coq_Impl) coq_Impl) coq_Forall coq_Valid

    val assert_eq_nenv :
      (('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx,
      (B.Coq_amsg.coq_AMessage, (('a1, Coq_ty.coq_Ty, B.coq_Term)
      coq_NamedEnv, (('a1, Coq_ty.coq_Ty, B.coq_Term) coq_NamedEnv,
      B.coq_Unit coq_SPureSpec) coq_Impl) coq_Impl) coq_Impl) coq_Forall
      coq_Valid

    val assert_eq_chunk :
      (B.Coq_amsg.coq_AMessage, (coq_Chunk, (coq_Chunk, B.coq_Unit
      coq_SPureSpec coq_Box) coq_Impl) coq_Impl) coq_Impl coq_Valid

    val replay_aux :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> (B.coq_Sub, B.coq_Unit coq_SPureSpec) coq_Impl
      coq_Valid

    val replay : (SymProp.coq_SymProp, SymProp.coq_SymProp) coq_Impl coq_Valid

    val produce_chunk :
      (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
      coq_Valid

    val consume_chunk :
      (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
      coq_Valid

    val consume_chunk_angelic :
      (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
      coq_Valid

    val read_register :
      Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> (coq_SHeap,
      (B.coq_Term, coq_SHeap) B.coq_Pair coq_SPureSpec) coq_Impl coq_Valid

    val write_register :
      Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> (B.coq_Term,
      (coq_SHeap, (B.coq_Term, coq_SHeap) B.coq_Pair coq_SPureSpec) coq_Impl)
      coq_Impl coq_Valid
   end

  type 'a coq_SHeapSpec =
    (('a, (coq_SHeap, SymProp.coq_SymProp) coq_Impl) coq_Impl coq_Box,
    (coq_SHeap, SymProp.coq_SymProp) coq_Impl) coq_Impl

  module SHeapSpec :
   sig
    val run :
      (B.coq_Unit coq_SHeapSpec, SymProp.coq_SymProp) coq_Impl coq_Valid

    val lift_purespec :
      ('a1 coq_SPureSpec, 'a1 coq_SHeapSpec) coq_Impl coq_Valid

    val pure : ('a1, 'a1 coq_SHeapSpec) coq_Impl coq_Valid

    val bind :
      ('a1 coq_SHeapSpec, (('a1, 'a2 coq_SHeapSpec) coq_Impl coq_Box, 'a2
      coq_SHeapSpec) coq_Impl) coq_Impl coq_Valid

    module Coq_notations :
     sig
     end

    val error :
      ((coq_SHeap, B.Coq_amsg.coq_AMessage) coq_Impl, 'a1 coq_SHeapSpec)
      coq_Impl coq_Valid

    val angelic :
      coq_LVar option -> (Coq_ty.coq_Ty, B.coq_Term coq_SHeapSpec) coq_Forall
      coq_Valid

    val demonic :
      coq_LVar option -> (Coq_ty.coq_Ty, B.coq_Term coq_SHeapSpec) coq_Forall
      coq_Valid

    val angelic_ctx :
      ('a1 -> coq_LVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) coq_NamedEnv
      coq_SHeapSpec) coq_Forall coq_Valid

    val demonic_ctx :
      ('a1 -> coq_LVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) coq_NamedEnv
      coq_SHeapSpec) coq_Forall coq_Valid

    val angelic_binary :
      ('a1 coq_SHeapSpec, ('a1 coq_SHeapSpec, 'a1 coq_SHeapSpec) coq_Impl)
      coq_Impl coq_Valid

    val demonic_binary :
      ('a1 coq_SHeapSpec, ('a1 coq_SHeapSpec, 'a1 coq_SHeapSpec) coq_Impl)
      coq_Impl coq_Valid

    val debug :
      ((coq_SHeap, B.Coq_amsg.coq_AMessage) coq_Impl, ('a1 coq_SHeapSpec, 'a1
      coq_SHeapSpec) coq_Impl) coq_Impl coq_Valid

    val assert_formula :
      ((coq_SHeap, B.Coq_amsg.coq_AMessage) coq_Impl, (coq_Formula,
      B.coq_Unit coq_SHeapSpec) coq_Impl) coq_Impl coq_Valid

    val assume_formula :
      (coq_Formula, B.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val produce_chunk :
      (coq_Chunk, B.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val consume_chunk :
      (coq_Chunk, B.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val consume_chunk_angelic :
      (coq_Chunk, B.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val read_register :
      Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> B.coq_Term
      coq_SHeapSpec coq_Valid

    val write_register :
      Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> (B.coq_Term,
      B.coq_Term coq_SHeapSpec) coq_Impl coq_Valid

    val produce :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_asn.coq_Assertion -> (B.coq_Sub, B.coq_Unit coq_SHeapSpec) coq_Impl
      coq_Valid

    val consume :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_asn.coq_Assertion -> (B.coq_Sub, B.coq_Unit coq_SHeapSpec) coq_Impl
      coq_Valid

    val call_contract :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContract -> (B.coq_SStore, B.coq_Term
      coq_SHeapSpec) coq_Impl coq_Valid

    val call_lemma :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Lemma -> (B.coq_SStore, B.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid
   end

  val coq_RPureSpec :
    ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SPureSpec, 'a2
    coq_CPureSpec) Coq_logicalrelation.coq_Rel

  module PureSpec :
   sig
    val coq_RPureSpec :
      ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SPureSpec, 'a2
      coq_CPureSpec) Coq_logicalrelation.coq_Rel
   end

  val coq_RHeapSpec :
    ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SHeapSpec, 'a2
    coq_CHeapSpec) Coq_logicalrelation.coq_Rel

  module HeapSpec :
   sig
   end
 end) ->
 functor (PROG:sig
  type _UU1d46d_

  type _UU1d46d__UU1d47f_

  type _UU1d473_

  type coq_Stm =
  | Coq_stm_val of Coq_ty.coq_Val
  | Coq_stm_exp of B.coq_Exp
  | Coq_stm_let of coq_PVar * Coq_ty.coq_Ty * coq_Stm * coq_Stm
  | Coq_stm_block of (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
                     Coq_ctx.coq_Ctx
     * (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv * coq_Stm
  | Coq_stm_assign of coq_PVar
     * (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * 
     coq_Stm
  | Coq_stm_call of (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
                    Coq_ctx.coq_Ctx
     * _UU1d46d_ * (coq_PVar, Coq_ty.coq_Ty, B.coq_Exp) coq_NamedEnv
  | Coq_stm_call_frame of (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv * coq_Stm
  | Coq_stm_foreign of (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
                       Coq_ctx.coq_Ctx
     * _UU1d46d__UU1d47f_ * (coq_PVar, Coq_ty.coq_Ty, B.coq_Exp) coq_NamedEnv
  | Coq_stm_lemmak of (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
                      Coq_ctx.coq_Ctx
     * _UU1d473_ * (coq_PVar, Coq_ty.coq_Ty, B.coq_Exp) coq_NamedEnv * 
     coq_Stm
  | Coq_stm_seq of Coq_ty.coq_Ty * coq_Stm * coq_Stm
  | Coq_stm_assertk of B.coq_Exp * B.coq_Exp * coq_Stm
  | Coq_stm_fail of Coq_ty.coq_Val
  | Coq_stm_pattern_match of Coq_ty.coq_Ty * coq_Stm * coq_PVar B.coq_Pattern
     * (coq_PVar B.coq_PatternCase -> coq_Stm)
  | Coq_stm_read_register of B._UU1d479__UU1d46c__UU1d46e_
  | Coq_stm_write_register of B._UU1d479__UU1d46c__UU1d46e_ * B.coq_Exp
  | Coq_stm_bind of Coq_ty.coq_Ty * coq_Stm * (Coq_ty.coq_Val -> coq_Stm)
  | Coq_stm_debugk of coq_Stm

  val coq_Stm_rect :
    ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> B.coq_Exp -> 'a1)
    -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_PVar -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm
    -> 'a1 -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_PVar, Coq_ty.coq_Ty,
    Coq_ty.coq_Val) coq_NamedEnv -> coq_Stm -> 'a1 -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    coq_PVar -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_Stm -> 'a1 -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d46d_ ->
    (coq_PVar, Coq_ty.coq_Ty, B.coq_Exp) coq_NamedEnv -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv -> coq_Stm -> 'a1
    -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> _UU1d46d__UU1d47f_ -> (coq_PVar, Coq_ty.coq_Ty,
    B.coq_Exp) coq_NamedEnv -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d473_ ->
    (coq_PVar, Coq_ty.coq_Ty, B.coq_Exp) coq_NamedEnv -> coq_Stm -> 'a1 ->
    'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm -> 'a1 ->
    'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B.coq_Exp -> B.coq_Exp -> coq_Stm -> 'a1 -> 'a1) ->
    ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    coq_Stm -> 'a1 -> coq_PVar B.coq_Pattern -> (coq_PVar B.coq_PatternCase
    -> coq_Stm) -> (coq_PVar B.coq_PatternCase -> 'a1) -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    B._UU1d479__UU1d46c__UU1d46e_ -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    B._UU1d479__UU1d46c__UU1d46e_ -> B.coq_Exp -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> (Coq_ty.coq_Val -> coq_Stm) ->
    (Coq_ty.coq_Val -> 'a1) -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 ->
    'a1) -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1

  val coq_Stm_rec :
    ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> B.coq_Exp -> 'a1)
    -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_PVar -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm
    -> 'a1 -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_PVar, Coq_ty.coq_Ty,
    Coq_ty.coq_Val) coq_NamedEnv -> coq_Stm -> 'a1 -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    coq_PVar -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_Stm -> 'a1 -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d46d_ ->
    (coq_PVar, Coq_ty.coq_Ty, B.coq_Exp) coq_NamedEnv -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv -> coq_Stm -> 'a1
    -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> _UU1d46d__UU1d47f_ -> (coq_PVar, Coq_ty.coq_Ty,
    B.coq_Exp) coq_NamedEnv -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d473_ ->
    (coq_PVar, Coq_ty.coq_Ty, B.coq_Exp) coq_NamedEnv -> coq_Stm -> 'a1 ->
    'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm -> 'a1 ->
    'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B.coq_Exp -> B.coq_Exp -> coq_Stm -> 'a1 -> 'a1) ->
    ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    coq_Stm -> 'a1 -> coq_PVar B.coq_Pattern -> (coq_PVar B.coq_PatternCase
    -> coq_Stm) -> (coq_PVar B.coq_PatternCase -> 'a1) -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    B._UU1d479__UU1d46c__UU1d46e_ -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    B._UU1d479__UU1d46c__UU1d46e_ -> B.coq_Exp -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> (Coq_ty.coq_Val -> coq_Stm) ->
    (Coq_ty.coq_Val -> 'a1) -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 ->
    'a1) -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1

  val coq_NoConfusionHomPackage_Stm :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm coq_NoConfusionPackage

  type coq_Stm_sig = coq_Stm

  val coq_Stm_sig_pack :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx * Coq_ty.coq_Ty) * coq_Stm

  val coq_Stm_Signature :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_Stm, (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx * Coq_ty.coq_Ty, coq_Stm_sig) coq_Signature

  val stm_assert :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    B.coq_Exp -> B.coq_Exp -> coq_Stm

  val stm_lemma :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    _UU1d473_ -> (coq_PVar, Coq_ty.coq_Ty, B.coq_Exp) coq_NamedEnv -> coq_Stm

  val stm_if :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> coq_Stm -> coq_Stm -> coq_Stm

  val stm_match_prod :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> coq_PVar ->
    coq_PVar -> coq_Stm -> coq_Stm

  val stm_match_tuple :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm -> coq_PVar
    B.coq_TuplePat -> coq_Stm -> coq_Stm

  val stm_match_record :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.recordi -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm -> coq_PVar
    B.coq_RecordPat -> coq_Stm -> coq_Stm

  val stm_match_bvec_split :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> nat -> nat -> coq_Stm -> coq_PVar -> coq_PVar -> coq_Stm
    -> coq_Stm

  val stm_match_list :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> coq_Stm -> coq_PVar ->
    coq_PVar -> coq_Stm -> coq_Stm

  val stm_match_sum :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> coq_PVar ->
    coq_Stm -> coq_PVar -> coq_Stm -> coq_Stm

  val stm_match_enum :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.enumi -> coq_Stm -> (Coq_ty.enumt -> coq_Stm) ->
    coq_Stm

  val stm_match_bvec :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> nat -> coq_Stm -> (Coq_bv.bv -> coq_Stm) -> coq_Stm

  val stm_match_union_alt :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.unioni -> coq_Stm -> (Coq_ty.unionk -> (coq_PVar,
    coq_Stm) B.coq_Alternative) -> coq_Stm

  type coq_UnionAlt = (coq_PVar, coq_Stm) B.coq_Alternative

  type coq_UnionAlts = (Coq_ty.unionk, coq_UnionAlt) sigT list

  val findUnionAlt :
    Coq_ty.unioni -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.unionk -> coq_UnionAlts ->
    coq_UnionAlt option

  val stm_match_union_alt_list :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.unioni -> coq_Stm -> coq_UnionAlts -> coq_Stm

  val stm_bindfree :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> bool

  val exp_smart_var :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_PVar
    -> Coq_ty.coq_Ty coq_IsSome -> B.coq_Exp

  val stm_smart_assign :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_PVar
    -> Coq_ty.coq_Ty coq_IsSome -> coq_Stm -> coq_Stm

  type coq_RegStore

  val read_register :
    coq_RegStore -> Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ ->
    Coq_ty.coq_Val

  val write_register :
    coq_RegStore -> Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ ->
    Coq_ty.coq_Val -> coq_RegStore

  val coq_FunDef :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> _UU1d46d_ -> coq_Stm

  module Coq_callgraph :
   sig
    type coq_Node = { _UU0394_ : (coq_PVar, Coq_ty.coq_Ty)
                                 Binding.coq_Binding Coq_ctx.coq_Ctx;
                      _UU03c4_ : Coq_ty.coq_Ty; f : _UU1d46d_ }

    val _UU0394_ :
      coq_Node -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx

    val _UU03c4_ : coq_Node -> Coq_ty.coq_Ty

    val f : coq_Node -> _UU1d46d_

    type coq_CallGraph = coq_Node -> coq_Node list

    val coq_InvokedByStmList :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Stm -> coq_Node list
   end

  val generic_call_graph : Coq_callgraph.coq_CallGraph

  module AccessibleTactics :
   sig
   end

  val _UU1d46d__call_graph : Coq_callgraph.coq_CallGraph

  val _UU1d46d__accessible :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> _UU1d46d_ -> __ option
 end) ->
 functor (FL:FailLogic) ->
 functor (SPEC:sig
  type coq_SepContractEnv =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> PROG._UU1d46d_ -> SIG.coq_SepContract option

  type coq_SepContractEnvEx =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> PROG._UU1d46d__UU1d47f_ -> SIG.coq_SepContract

  type coq_LemmaEnv =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    PROG._UU1d473_ -> SIG.coq_Lemma

  type coq_SepContractFun = SIG.coq_SepContract

  type coq_SepContractFunX = SIG.coq_SepContract

  type coq_SepLemma = SIG.coq_Lemma

  val coq_CEnv : coq_SepContractEnv

  val coq_CEnvEx : coq_SepContractEnvEx

  val coq_LEnv : coq_LemmaEnv
 end) ->
 struct
  type coq_DebugCall = { debug_call_function_parameters : (coq_PVar,
                                                          Coq_ty.coq_Ty)
                                                          Binding.coq_Binding
                                                          Coq_ctx.coq_Ctx;
                         debug_call_function_result_type : Coq_ty.coq_Ty;
                         debug_call_function_name : PROG._UU1d46d_;
                         debug_call_function_contract : SIG.coq_SepContract
                                                        option;
                         debug_call_function_arguments : B.coq_SStore;
                         debug_call_pathcondition : SIG.coq_PathCondition;
                         debug_call_heap : SIG.coq_SHeap }

  (** val debug_call_function_parameters :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCall -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let debug_call_function_parameters _ d =
    d.debug_call_function_parameters

  (** val debug_call_function_result_type :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCall -> Coq_ty.coq_Ty **)

  let debug_call_function_result_type _ d =
    d.debug_call_function_result_type

  (** val debug_call_function_name :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCall -> PROG._UU1d46d_ **)

  let debug_call_function_name _ d =
    d.debug_call_function_name

  (** val debug_call_function_contract :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCall -> SIG.coq_SepContract option **)

  let debug_call_function_contract _ d =
    d.debug_call_function_contract

  (** val debug_call_function_arguments :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCall -> B.coq_SStore **)

  let debug_call_function_arguments _ d =
    d.debug_call_function_arguments

  (** val debug_call_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCall -> SIG.coq_PathCondition **)

  let debug_call_pathcondition _ d =
    d.debug_call_pathcondition

  (** val debug_call_heap :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCall -> SIG.coq_SHeap **)

  let debug_call_heap _ d =
    d.debug_call_heap

  type coq_EDebugCall = { edebug_call_function_parameters : (coq_PVar,
                                                            Coq_ty.coq_Ty)
                                                            Binding.coq_Binding
                                                            Coq_ctx.coq_Ctx;
                          edebug_call_function_result_type : Coq_ty.coq_Ty;
                          edebug_call_function_name : PROG._UU1d46d_;
                          edebug_call_function_contract : SIG.coq_SepContract
                                                          option;
                          edebug_call_function_arguments : (coq_PVar,
                                                           Coq_ty.coq_Ty,
                                                           B.coq_ETerm)
                                                           coq_NamedEnv;
                          edebug_call_pathcondition : SIG.coq_EFormula list;
                          edebug_call_heap : SIG.coq_EChunk list }

  (** val edebug_call_function_parameters :
      coq_EDebugCall -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let edebug_call_function_parameters e =
    e.edebug_call_function_parameters

  (** val edebug_call_function_result_type :
      coq_EDebugCall -> Coq_ty.coq_Ty **)

  let edebug_call_function_result_type e =
    e.edebug_call_function_result_type

  (** val edebug_call_function_name : coq_EDebugCall -> PROG._UU1d46d_ **)

  let edebug_call_function_name e =
    e.edebug_call_function_name

  (** val edebug_call_function_contract :
      coq_EDebugCall -> SIG.coq_SepContract option **)

  let edebug_call_function_contract e =
    e.edebug_call_function_contract

  (** val edebug_call_function_arguments :
      coq_EDebugCall -> (coq_PVar, Coq_ty.coq_Ty, B.coq_ETerm) coq_NamedEnv **)

  let edebug_call_function_arguments e =
    e.edebug_call_function_arguments

  (** val edebug_call_pathcondition :
      coq_EDebugCall -> SIG.coq_EFormula list **)

  let edebug_call_pathcondition e =
    e.edebug_call_pathcondition

  (** val edebug_call_heap : coq_EDebugCall -> SIG.coq_EChunk list **)

  let edebug_call_heap e =
    e.edebug_call_heap

  (** val coq_EraseDebugCall : (coq_DebugCall, coq_EDebugCall) B.coq_Erase **)

  let coq_EraseDebugCall _UU03a3_ pat =
    let { debug_call_function_parameters = debug_call_function_parameters0;
      debug_call_function_result_type = debug_call_function_result_type0;
      debug_call_function_name = f0; debug_call_function_contract = fc;
      debug_call_function_arguments = args; debug_call_pathcondition = pc;
      debug_call_heap = h } = pat
    in
    { edebug_call_function_parameters = debug_call_function_parameters0;
    edebug_call_function_result_type = debug_call_function_result_type0;
    edebug_call_function_name = f0; edebug_call_function_contract = fc;
    edebug_call_function_arguments =
    (B.erase (B.coq_EraseSStore debug_call_function_parameters0) _UU03a3_
      args);
    edebug_call_pathcondition =
    (B.erase (B.erase_Ctx SIG.erase_Formula) _UU03a3_ pc); edebug_call_heap =
    (B.erase (B.erase_List SIG.coq_Erase_Chunk) _UU03a3_ h) }

  type coq_DebugCallLemma = { debug_call_lemma_parameters : (coq_PVar,
                                                            Coq_ty.coq_Ty)
                                                            Binding.coq_Binding
                                                            Coq_ctx.coq_Ctx;
                              debug_call_lemma_name : PROG._UU1d473_;
                              debug_call_lemma_contract : SIG.coq_Lemma;
                              debug_call_lemma_arguments : B.coq_SStore;
                              debug_call_lemma_pathcondition : SIG.coq_PathCondition;
                              debug_call_lemma_heap : SIG.coq_SHeap }

  (** val debug_call_lemma_parameters :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCallLemma -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let debug_call_lemma_parameters _ d =
    d.debug_call_lemma_parameters

  (** val debug_call_lemma_name :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCallLemma -> PROG._UU1d473_ **)

  let debug_call_lemma_name _ d =
    d.debug_call_lemma_name

  (** val debug_call_lemma_contract :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCallLemma -> SIG.coq_Lemma **)

  let debug_call_lemma_contract _ d =
    d.debug_call_lemma_contract

  (** val debug_call_lemma_arguments :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCallLemma -> B.coq_SStore **)

  let debug_call_lemma_arguments _ d =
    d.debug_call_lemma_arguments

  (** val debug_call_lemma_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCallLemma -> SIG.coq_PathCondition **)

  let debug_call_lemma_pathcondition _ d =
    d.debug_call_lemma_pathcondition

  (** val debug_call_lemma_heap :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugCallLemma -> SIG.coq_SHeap **)

  let debug_call_lemma_heap _ d =
    d.debug_call_lemma_heap

  type coq_EDebugCallLemma = { edebug_call_lemma_parameters : (coq_PVar,
                                                              Coq_ty.coq_Ty)
                                                              Binding.coq_Binding
                                                              Coq_ctx.coq_Ctx;
                               edebug_call_lemma_name : PROG._UU1d473_;
                               edebug_call_lemma_contract : SIG.coq_Lemma;
                               edebug_call_lemma_arguments : (coq_PVar,
                                                             Coq_ty.coq_Ty,
                                                             B.coq_ETerm)
                                                             coq_NamedEnv;
                               edebug_call_lemma_pathcondition : SIG.coq_EFormula
                                                                 list;
                               edebug_call_lemma_heap : SIG.coq_EChunk list }

  (** val edebug_call_lemma_parameters :
      coq_EDebugCallLemma -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let edebug_call_lemma_parameters e =
    e.edebug_call_lemma_parameters

  (** val edebug_call_lemma_name : coq_EDebugCallLemma -> PROG._UU1d473_ **)

  let edebug_call_lemma_name e =
    e.edebug_call_lemma_name

  (** val edebug_call_lemma_contract :
      coq_EDebugCallLemma -> SIG.coq_Lemma **)

  let edebug_call_lemma_contract e =
    e.edebug_call_lemma_contract

  (** val edebug_call_lemma_arguments :
      coq_EDebugCallLemma -> (coq_PVar, Coq_ty.coq_Ty, B.coq_ETerm)
      coq_NamedEnv **)

  let edebug_call_lemma_arguments e =
    e.edebug_call_lemma_arguments

  (** val edebug_call_lemma_pathcondition :
      coq_EDebugCallLemma -> SIG.coq_EFormula list **)

  let edebug_call_lemma_pathcondition e =
    e.edebug_call_lemma_pathcondition

  (** val edebug_call_lemma_heap :
      coq_EDebugCallLemma -> SIG.coq_EChunk list **)

  let edebug_call_lemma_heap e =
    e.edebug_call_lemma_heap

  (** val coq_EraseDebugCallLemma :
      (coq_DebugCallLemma, coq_EDebugCallLemma) B.coq_Erase **)

  let coq_EraseDebugCallLemma _UU03a3_ pat =
    let { debug_call_lemma_parameters = debug_call_lemma_parameters0;
      debug_call_lemma_name = l; debug_call_lemma_contract = lc;
      debug_call_lemma_arguments = args; debug_call_lemma_pathcondition = pc;
      debug_call_lemma_heap = h } = pat
    in
    { edebug_call_lemma_parameters = debug_call_lemma_parameters0;
    edebug_call_lemma_name = l; edebug_call_lemma_contract = lc;
    edebug_call_lemma_arguments =
    (B.erase (B.coq_EraseSStore debug_call_lemma_parameters0) _UU03a3_ args);
    edebug_call_lemma_pathcondition =
    (B.erase (B.erase_Ctx SIG.erase_Formula) _UU03a3_ pc);
    edebug_call_lemma_heap =
    (B.erase (B.erase_List SIG.coq_Erase_Chunk) _UU03a3_ h) }

  (** val coq_SubstDebugCallLemma : coq_DebugCallLemma B.coq_Subst **)

  let coq_SubstDebugCallLemma _UU03a3_0 d _UU03a3_1 _UU03b6_01 =
    let { debug_call_lemma_parameters = debug_call_lemma_parameters0;
      debug_call_lemma_name = l; debug_call_lemma_contract = c;
      debug_call_lemma_arguments = ts; debug_call_lemma_pathcondition = pc;
      debug_call_lemma_heap = h } = d
    in
    { debug_call_lemma_parameters = debug_call_lemma_parameters0;
    debug_call_lemma_name = l; debug_call_lemma_contract = c;
    debug_call_lemma_arguments =
    (B.subst (B.subst_localstore debug_call_lemma_parameters0) _UU03a3_0 ts
      _UU03a3_1 _UU03b6_01);
    debug_call_lemma_pathcondition =
    (B.subst (B.subst_ctx SIG.sub_formula) _UU03a3_0 pc _UU03a3_1 _UU03b6_01);
    debug_call_lemma_heap =
    (B.subst (B.coq_SubstList SIG.coq_SubstChunk) _UU03a3_0 h _UU03a3_1
      _UU03b6_01) }

  (** val coq_SubstSUDebugCallLemma :
      'a1 B.coq_SubstUniv -> ('a1, coq_DebugCallLemma) B.coq_SubstSU **)

  let coq_SubstSUDebugCallLemma h _UU03a3_0 _UU03a3_1 d _UU03b6_01 =
    let { debug_call_lemma_parameters = debug_call_lemma_parameters0;
      debug_call_lemma_name = l; debug_call_lemma_contract = c;
      debug_call_lemma_arguments = ts; debug_call_lemma_pathcondition = pc;
      debug_call_lemma_heap = h0 } = d
    in
    { debug_call_lemma_parameters = debug_call_lemma_parameters0;
    debug_call_lemma_name = l; debug_call_lemma_contract = c;
    debug_call_lemma_arguments =
    (B.substSU
      (B.coq_SubstSU_env h debug_call_lemma_parameters0 (fun b ->
        B.coq_SubstSUTerm h b.Binding.coq_type))
      _UU03a3_0 _UU03a3_1 ts _UU03b6_01);
    debug_call_lemma_pathcondition =
    (B.substSU (B.substSU_ctx (SIG.subSU_formula h)) _UU03a3_0 _UU03a3_1 pc
      _UU03b6_01);
    debug_call_lemma_heap =
    (B.substSU (B.substSU_list (SIG.coq_SubstSUChunk h)) _UU03a3_0 _UU03a3_1
      h0 _UU03b6_01) }

  (** val coq_SubstLawsDebugCallLemma : coq_DebugCallLemma B.coq_SubstLaws **)

  let coq_SubstLawsDebugCallLemma =
    B.Build_SubstLaws

  (** val coq_OccursCheckDebugCallLemma :
      coq_DebugCallLemma B.coq_OccursCheck **)

  let coq_OccursCheckDebugCallLemma _UU03a3_ x xIn d =
    let { debug_call_lemma_parameters = debug_call_lemma_parameters0;
      debug_call_lemma_name = l; debug_call_lemma_contract = c;
      debug_call_lemma_arguments = ts; debug_call_lemma_pathcondition = pc;
      debug_call_lemma_heap = h } = d
    in
    Coq_option.bind
      (B.occurs_check
        (B.occurs_check_env (fun i -> B.occurs_check_term i.Binding.coq_type)
          debug_call_lemma_parameters0)
        _UU03a3_ x xIn ts)
      (fun ts' ->
      Coq_option.bind
        (B.occurs_check (B.occurscheck_ctx SIG.coq_OccursCheckFormula)
          _UU03a3_ x xIn pc)
        (fun pc' ->
        Coq_option.bind
          (B.occurs_check (B.occurs_check_list SIG.coq_OccursCheckChunk)
            _UU03a3_ x xIn h)
          (fun h' -> Some { debug_call_lemma_parameters =
          debug_call_lemma_parameters0; debug_call_lemma_name = l;
          debug_call_lemma_contract = c; debug_call_lemma_arguments = ts';
          debug_call_lemma_pathcondition = pc'; debug_call_lemma_heap = h' })))

  (** val coq_GenOccursCheckDebugCallLemma :
      (B.coq_WeakensTo, coq_DebugCallLemma) B.coq_GenOccursCheck **)

  let coq_GenOccursCheckDebugCallLemma _UU03a3_ d =
    let { debug_call_lemma_parameters = debug_call_lemma_parameters0;
      debug_call_lemma_name = l; debug_call_lemma_contract = c;
      debug_call_lemma_arguments = ts; debug_call_lemma_pathcondition = pc;
      debug_call_lemma_heap = h } = d
    in
    B.liftTernOp B.substUniv_weaken B.substUnivMeet_weaken B.substUniv_weaken
      B.substUnivMeet_weaken _UU03a3_
      (B.coq_SubstSU_env B.substUniv_weaken debug_call_lemma_parameters0
        (fun b -> B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type))
      (B.substSU_ctx (SIG.subSU_formula B.substUniv_weaken))
      (B.substSU_list (SIG.coq_SubstSUChunk B.substUniv_weaken))
      (coq_SubstSUDebugCallLemma B.substUniv_weaken) (fun _ ts' pc' h' ->
      { debug_call_lemma_parameters = debug_call_lemma_parameters0;
      debug_call_lemma_name = l; debug_call_lemma_contract = c;
      debug_call_lemma_arguments = ts'; debug_call_lemma_pathcondition = pc';
      debug_call_lemma_heap = h' })
      (B.gen_occurs_check B.substUniv_weaken
        (B.coq_SubstSU_env B.substUniv_weaken debug_call_lemma_parameters0
          (fun b -> B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type))
        (B.gen_occurs_check_env B.substUniv_weaken B.substUnivMeet_weaken
          B.substUniv_weaken B.substUnivMeet_weaken (fun b ->
          B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type) (fun i ->
          B.gen_occurs_check_term B.substUniv_weaken B.substUnivMeet_weaken
            B.substUnivVar_weaken B.substUniv_weaken B.substUnivMeet_weaken
            B.substUniv_weaken B.substUnivMeet_weaken i.Binding.coq_type)
          debug_call_lemma_parameters0)
        _UU03a3_ ts)
      (B.gen_occurs_check B.substUniv_weaken
        (B.substSU_ctx (SIG.subSU_formula B.substUniv_weaken))
        (B.gen_occurscheck_ctx (SIG.subSU_formula B.substUniv_weaken)
          B.substUniv_weaken B.substUnivMeet_weaken
          (SIG.coq_GenOccursCheckFormula B.substUniv_weaken
            B.substUnivMeet_weaken B.substUnivVar_weaken B.substUniv_weaken
            B.substUnivMeet_weaken B.substUniv_weaken B.substUnivMeet_weaken))
        _UU03a3_ pc)
      (B.gen_occurs_check B.substUniv_weaken
        (B.substSU_list (SIG.coq_SubstSUChunk B.substUniv_weaken))
        (B.gen_occurs_check_list B.substUniv_weaken B.substUnivMeet_weaken
          B.substUniv_weaken B.substUnivMeet_weaken
          (SIG.coq_SubstSUChunk B.substUniv_weaken)
          SIG.coq_GenOccursCheckChunk)
        _UU03a3_ h)

  (** val coq_SubstDebugCall : coq_DebugCall B.coq_Subst **)

  let coq_SubstDebugCall _UU03a3_0 d _UU03a3_1 _UU03b6_01 =
    let { debug_call_function_parameters = debug_call_function_parameters0;
      debug_call_function_result_type = debug_call_function_result_type0;
      debug_call_function_name = f0; debug_call_function_contract = c;
      debug_call_function_arguments = ts; debug_call_pathcondition = pc;
      debug_call_heap = h } = d
    in
    { debug_call_function_parameters = debug_call_function_parameters0;
    debug_call_function_result_type = debug_call_function_result_type0;
    debug_call_function_name = f0; debug_call_function_contract = c;
    debug_call_function_arguments =
    (B.subst (B.subst_localstore debug_call_function_parameters0) _UU03a3_0
      ts _UU03a3_1 _UU03b6_01);
    debug_call_pathcondition =
    (B.subst (B.subst_ctx SIG.sub_formula) _UU03a3_0 pc _UU03a3_1 _UU03b6_01);
    debug_call_heap =
    (B.subst (B.coq_SubstList SIG.coq_SubstChunk) _UU03a3_0 h _UU03a3_1
      _UU03b6_01) }

  (** val coq_SubstSUDebugCall :
      'a1 B.coq_SubstUniv -> ('a1, coq_DebugCall) B.coq_SubstSU **)

  let coq_SubstSUDebugCall h _UU03a3_0 _UU03a3_1 d _UU03b6_01 =
    let { debug_call_function_parameters = debug_call_function_parameters0;
      debug_call_function_result_type = debug_call_function_result_type0;
      debug_call_function_name = f0; debug_call_function_contract = c;
      debug_call_function_arguments = ts; debug_call_pathcondition = pc;
      debug_call_heap = h0 } = d
    in
    { debug_call_function_parameters = debug_call_function_parameters0;
    debug_call_function_result_type = debug_call_function_result_type0;
    debug_call_function_name = f0; debug_call_function_contract = c;
    debug_call_function_arguments =
    (B.substSU
      (B.coq_SubstSU_env h debug_call_function_parameters0 (fun b ->
        B.coq_SubstSUTerm h b.Binding.coq_type))
      _UU03a3_0 _UU03a3_1 ts _UU03b6_01);
    debug_call_pathcondition =
    (B.substSU (B.substSU_ctx (SIG.subSU_formula h)) _UU03a3_0 _UU03a3_1 pc
      _UU03b6_01);
    debug_call_heap =
    (B.substSU (B.substSU_list (SIG.coq_SubstSUChunk h)) _UU03a3_0 _UU03a3_1
      h0 _UU03b6_01) }

  (** val coq_SubstLawsDebugCall : coq_DebugCall B.coq_SubstLaws **)

  let coq_SubstLawsDebugCall =
    B.Build_SubstLaws

  (** val coq_OccursCheckDebugCall : coq_DebugCall B.coq_OccursCheck **)

  let coq_OccursCheckDebugCall _UU03a3_ x xIn d =
    let { debug_call_function_parameters = debug_call_function_parameters0;
      debug_call_function_result_type = debug_call_function_result_type0;
      debug_call_function_name = f0; debug_call_function_contract = c;
      debug_call_function_arguments = ts; debug_call_pathcondition = pc;
      debug_call_heap = h } = d
    in
    Coq_option.bind
      (B.occurs_check
        (B.occurs_check_env (fun i -> B.occurs_check_term i.Binding.coq_type)
          debug_call_function_parameters0)
        _UU03a3_ x xIn ts)
      (fun ts' ->
      Coq_option.bind
        (B.occurs_check (B.occurscheck_ctx SIG.coq_OccursCheckFormula)
          _UU03a3_ x xIn pc)
        (fun pc' ->
        Coq_option.bind
          (B.occurs_check (B.occurs_check_list SIG.coq_OccursCheckChunk)
            _UU03a3_ x xIn h)
          (fun h' -> Some { debug_call_function_parameters =
          debug_call_function_parameters0; debug_call_function_result_type =
          debug_call_function_result_type0; debug_call_function_name = f0;
          debug_call_function_contract = c; debug_call_function_arguments =
          ts'; debug_call_pathcondition = pc'; debug_call_heap = h' })))

  (** val coq_GenOccursCheckDebugCall :
      (B.coq_WeakensTo, coq_DebugCall) B.coq_GenOccursCheck **)

  let coq_GenOccursCheckDebugCall _UU03a3_ d =
    let { debug_call_function_parameters = debug_call_function_parameters0;
      debug_call_function_result_type = debug_call_function_result_type0;
      debug_call_function_name = f0; debug_call_function_contract = c;
      debug_call_function_arguments = ts; debug_call_pathcondition = pc;
      debug_call_heap = h } = d
    in
    B.liftTernOp B.substUniv_weaken B.substUnivMeet_weaken B.substUniv_weaken
      B.substUnivMeet_weaken _UU03a3_
      (B.coq_SubstSU_env B.substUniv_weaken debug_call_function_parameters0
        (fun b -> B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type))
      (B.substSU_ctx (SIG.subSU_formula B.substUniv_weaken))
      (B.substSU_list (SIG.coq_SubstSUChunk B.substUniv_weaken))
      (coq_SubstSUDebugCall B.substUniv_weaken) (fun _ ts' pc' h' ->
      { debug_call_function_parameters = debug_call_function_parameters0;
      debug_call_function_result_type = debug_call_function_result_type0;
      debug_call_function_name = f0; debug_call_function_contract = c;
      debug_call_function_arguments = ts'; debug_call_pathcondition = pc';
      debug_call_heap = h' })
      (B.gen_occurs_check B.substUniv_weaken
        (B.coq_SubstSU_env B.substUniv_weaken debug_call_function_parameters0
          (fun b -> B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type))
        (B.gen_occurs_check_env B.substUniv_weaken B.substUnivMeet_weaken
          B.substUniv_weaken B.substUnivMeet_weaken (fun b ->
          B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type) (fun i ->
          B.gen_occurs_check_term B.substUniv_weaken B.substUnivMeet_weaken
            B.substUnivVar_weaken B.substUniv_weaken B.substUnivMeet_weaken
            B.substUniv_weaken B.substUnivMeet_weaken i.Binding.coq_type)
          debug_call_function_parameters0)
        _UU03a3_ ts)
      (B.gen_occurs_check B.substUniv_weaken
        (B.substSU_ctx (SIG.subSU_formula B.substUniv_weaken))
        (B.gen_occurscheck_ctx (SIG.subSU_formula B.substUniv_weaken)
          B.substUniv_weaken B.substUnivMeet_weaken
          (SIG.coq_GenOccursCheckFormula B.substUniv_weaken
            B.substUnivMeet_weaken B.substUnivVar_weaken B.substUniv_weaken
            B.substUnivMeet_weaken B.substUniv_weaken B.substUnivMeet_weaken))
        _UU03a3_ pc)
      (B.gen_occurs_check B.substUniv_weaken
        (B.substSU_list (SIG.coq_SubstSUChunk B.substUniv_weaken))
        (B.gen_occurs_check_list B.substUniv_weaken B.substUnivMeet_weaken
          B.substUniv_weaken B.substUnivMeet_weaken
          (SIG.coq_SubstSUChunk B.substUniv_weaken)
          SIG.coq_GenOccursCheckChunk)
        _UU03a3_ h)

  type coq_DebugStm = { debug_stm_program_context : (coq_PVar, Coq_ty.coq_Ty)
                                                    Binding.coq_Binding
                                                    Coq_ctx.coq_Ctx;
                        debug_stm_statement_type : Coq_ty.coq_Ty;
                        debug_stm_statement : PROG.coq_Stm;
                        debug_stm_pathcondition : SIG.coq_PathCondition;
                        debug_stm_localstore : B.coq_SStore;
                        debug_stm_heap : SIG.coq_SHeap }

  (** val debug_stm_program_context :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugStm -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let debug_stm_program_context _ d =
    d.debug_stm_program_context

  (** val debug_stm_statement_type :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugStm -> Coq_ty.coq_Ty **)

  let debug_stm_statement_type _ d =
    d.debug_stm_statement_type

  (** val debug_stm_statement :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugStm -> PROG.coq_Stm **)

  let debug_stm_statement _ d =
    d.debug_stm_statement

  (** val debug_stm_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugStm -> SIG.coq_PathCondition **)

  let debug_stm_pathcondition _ d =
    d.debug_stm_pathcondition

  (** val debug_stm_localstore :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugStm -> B.coq_SStore **)

  let debug_stm_localstore _ d =
    d.debug_stm_localstore

  (** val debug_stm_heap :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_DebugStm -> SIG.coq_SHeap **)

  let debug_stm_heap _ d =
    d.debug_stm_heap

  type coq_EDebugStm = { edebug_stm_program_context : (coq_PVar,
                                                      Coq_ty.coq_Ty)
                                                      Binding.coq_Binding
                                                      Coq_ctx.coq_Ctx;
                         edebug_stm_statement_type : Coq_ty.coq_Ty;
                         edebug_stm_statement : PROG.coq_Stm;
                         edebug_stm_pathcondition : SIG.coq_EFormula list;
                         edebug_stm_localstore : (coq_PVar, Coq_ty.coq_Ty,
                                                 B.coq_ETerm) coq_NamedEnv;
                         edebug_stm_heap : SIG.coq_EChunk list }

  (** val edebug_stm_program_context :
      coq_EDebugStm -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let edebug_stm_program_context e =
    e.edebug_stm_program_context

  (** val edebug_stm_statement_type : coq_EDebugStm -> Coq_ty.coq_Ty **)

  let edebug_stm_statement_type e =
    e.edebug_stm_statement_type

  (** val edebug_stm_statement : coq_EDebugStm -> PROG.coq_Stm **)

  let edebug_stm_statement e =
    e.edebug_stm_statement

  (** val edebug_stm_pathcondition :
      coq_EDebugStm -> SIG.coq_EFormula list **)

  let edebug_stm_pathcondition e =
    e.edebug_stm_pathcondition

  (** val edebug_stm_localstore :
      coq_EDebugStm -> (coq_PVar, Coq_ty.coq_Ty, B.coq_ETerm) coq_NamedEnv **)

  let edebug_stm_localstore e =
    e.edebug_stm_localstore

  (** val edebug_stm_heap : coq_EDebugStm -> SIG.coq_EChunk list **)

  let edebug_stm_heap e =
    e.edebug_stm_heap

  (** val coq_EraseDebugStm : (coq_DebugStm, coq_EDebugStm) B.coq_Erase **)

  let coq_EraseDebugStm _UU03a3_ pat =
    let { debug_stm_program_context = debug_stm_program_context0;
      debug_stm_statement_type = debug_stm_statement_type0;
      debug_stm_statement = s; debug_stm_pathcondition = pc;
      debug_stm_localstore = _UU0394_0; debug_stm_heap = h } = pat
    in
    { edebug_stm_program_context = debug_stm_program_context0;
    edebug_stm_statement_type = debug_stm_statement_type0;
    edebug_stm_statement = s; edebug_stm_pathcondition =
    (B.erase (B.erase_Ctx SIG.erase_Formula) _UU03a3_ pc);
    edebug_stm_localstore =
    (B.erase (B.coq_EraseSStore debug_stm_program_context0) _UU03a3_
      _UU0394_0);
    edebug_stm_heap =
    (B.erase (B.erase_List SIG.coq_Erase_Chunk) _UU03a3_ h) }

  (** val coq_SubstDebugStm : coq_DebugStm B.coq_Subst **)

  let coq_SubstDebugStm _UU03a3_0 d _UU03a3_1 _UU03b6_01 =
    let { debug_stm_program_context = debug_stm_program_context0;
      debug_stm_statement_type = debug_stm_statement_type0;
      debug_stm_statement = s; debug_stm_pathcondition = pc;
      debug_stm_localstore = _UU03b4_; debug_stm_heap = h } = d
    in
    { debug_stm_program_context = debug_stm_program_context0;
    debug_stm_statement_type = debug_stm_statement_type0;
    debug_stm_statement = s; debug_stm_pathcondition =
    (B.subst (B.subst_ctx SIG.sub_formula) _UU03a3_0 pc _UU03a3_1 _UU03b6_01);
    debug_stm_localstore =
    (B.subst (B.subst_localstore debug_stm_program_context0) _UU03a3_0
      _UU03b4_ _UU03a3_1 _UU03b6_01);
    debug_stm_heap =
    (B.subst (B.coq_SubstList SIG.coq_SubstChunk) _UU03a3_0 h _UU03a3_1
      _UU03b6_01) }

  (** val coq_SubstSUDebugStm :
      'a1 B.coq_SubstUniv -> ('a1, coq_DebugStm) B.coq_SubstSU **)

  let coq_SubstSUDebugStm h _UU03a3_0 _UU03a3_1 d _UU03b6_01 =
    let { debug_stm_program_context = debug_stm_program_context0;
      debug_stm_statement_type = debug_stm_statement_type0;
      debug_stm_statement = s; debug_stm_pathcondition = pc;
      debug_stm_localstore = _UU03b4_; debug_stm_heap = h0 } = d
    in
    { debug_stm_program_context = debug_stm_program_context0;
    debug_stm_statement_type = debug_stm_statement_type0;
    debug_stm_statement = s; debug_stm_pathcondition =
    (B.substSU (B.substSU_ctx (SIG.subSU_formula h)) _UU03a3_0 _UU03a3_1 pc
      _UU03b6_01);
    debug_stm_localstore =
    (B.substSU
      (B.coq_SubstSU_env h debug_stm_program_context0 (fun b ->
        B.coq_SubstSUTerm h b.Binding.coq_type))
      _UU03a3_0 _UU03a3_1 _UU03b4_ _UU03b6_01);
    debug_stm_heap =
    (B.substSU (B.substSU_list (SIG.coq_SubstSUChunk h)) _UU03a3_0 _UU03a3_1
      h0 _UU03b6_01) }

  (** val coq_SubstLawsDebugStm : coq_DebugStm B.coq_SubstLaws **)

  let coq_SubstLawsDebugStm =
    B.Build_SubstLaws

  (** val coq_OccursCheckDebugStm : coq_DebugStm B.coq_OccursCheck **)

  let coq_OccursCheckDebugStm _UU03a3_ x xIn d =
    let { debug_stm_program_context = debug_stm_program_context0;
      debug_stm_statement_type = debug_stm_statement_type0;
      debug_stm_statement = s; debug_stm_pathcondition = pc;
      debug_stm_localstore = _UU03b4_; debug_stm_heap = h } = d
    in
    Coq_option.bind
      (B.occurs_check (B.occurscheck_ctx SIG.coq_OccursCheckFormula) _UU03a3_
        x xIn pc)
      (fun pc' ->
      Coq_option.bind
        (B.occurs_check
          (B.occurs_check_env (fun i ->
            B.occurs_check_term i.Binding.coq_type)
            debug_stm_program_context0)
          _UU03a3_ x xIn _UU03b4_)
        (fun _UU03b4_' ->
        Coq_option.bind
          (B.occurs_check (B.occurs_check_list SIG.coq_OccursCheckChunk)
            _UU03a3_ x xIn h)
          (fun h' -> Some { debug_stm_program_context =
          debug_stm_program_context0; debug_stm_statement_type =
          debug_stm_statement_type0; debug_stm_statement = s;
          debug_stm_pathcondition = pc'; debug_stm_localstore = _UU03b4_';
          debug_stm_heap = h' })))

  (** val coq_GenOccursCheckDebugStm :
      (B.coq_WeakensTo, coq_DebugStm) B.coq_GenOccursCheck **)

  let coq_GenOccursCheckDebugStm _UU03a3_ d =
    let { debug_stm_program_context = debug_stm_program_context0;
      debug_stm_statement_type = debug_stm_statement_type0;
      debug_stm_statement = s; debug_stm_pathcondition = pc;
      debug_stm_localstore = _UU03b4_; debug_stm_heap = h } = d
    in
    B.liftTernOp B.substUniv_weaken B.substUnivMeet_weaken B.substUniv_weaken
      B.substUnivMeet_weaken _UU03a3_
      (B.substSU_ctx (SIG.subSU_formula B.substUniv_weaken))
      (B.coq_SubstSU_env B.substUniv_weaken debug_stm_program_context0
        (fun b -> B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type))
      (B.substSU_list (SIG.coq_SubstSUChunk B.substUniv_weaken))
      (coq_SubstSUDebugStm B.substUniv_weaken) (fun _ pc' _UU03b4_' h' ->
      { debug_stm_program_context = debug_stm_program_context0;
      debug_stm_statement_type = debug_stm_statement_type0;
      debug_stm_statement = s; debug_stm_pathcondition = pc';
      debug_stm_localstore = _UU03b4_'; debug_stm_heap = h' })
      (B.gen_occurs_check B.substUniv_weaken
        (B.substSU_ctx (SIG.subSU_formula B.substUniv_weaken))
        (B.gen_occurscheck_ctx (SIG.subSU_formula B.substUniv_weaken)
          B.substUniv_weaken B.substUnivMeet_weaken
          (SIG.coq_GenOccursCheckFormula B.substUniv_weaken
            B.substUnivMeet_weaken B.substUnivVar_weaken B.substUniv_weaken
            B.substUnivMeet_weaken B.substUniv_weaken B.substUnivMeet_weaken))
        _UU03a3_ pc)
      (B.gen_occurs_check B.substUniv_weaken
        (B.coq_SubstSU_env B.substUniv_weaken debug_stm_program_context0
          (fun b -> B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type))
        (B.gen_occurs_check_env B.substUniv_weaken B.substUnivMeet_weaken
          B.substUniv_weaken B.substUnivMeet_weaken (fun b ->
          B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type) (fun i ->
          B.gen_occurs_check_term B.substUniv_weaken B.substUnivMeet_weaken
            B.substUnivVar_weaken B.substUniv_weaken B.substUnivMeet_weaken
            B.substUniv_weaken B.substUnivMeet_weaken i.Binding.coq_type)
          debug_stm_program_context0)
        _UU03a3_ _UU03b4_)
      (B.gen_occurs_check B.substUniv_weaken
        (B.substSU_list (SIG.coq_SubstSUChunk B.substUniv_weaken))
        (B.gen_occurs_check_list B.substUniv_weaken B.substUnivMeet_weaken
          B.substUniv_weaken B.substUnivMeet_weaken
          (SIG.coq_SubstSUChunk B.substUniv_weaken)
          SIG.coq_GenOccursCheckChunk)
        _UU03a3_ h)

  type coq_ErrorNoFuel = { error_no_fuel_call_parameter_types : (coq_PVar,
                                                                Coq_ty.coq_Ty)
                                                                Binding.coq_Binding
                                                                Coq_ctx.coq_Ctx;
                           error_no_fuel_call_return_type : Coq_ty.coq_Ty;
                           error_no_fuel_call_function : PROG._UU1d46d_;
                           error_no_fuel_call_arguments : B.coq_SStore;
                           error_no_fuel_pathcondition : SIG.coq_PathCondition;
                           error_no_fuel_heap : SIG.coq_SHeap }

  (** val error_no_fuel_call_parameter_types :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_ErrorNoFuel -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let error_no_fuel_call_parameter_types _ e =
    e.error_no_fuel_call_parameter_types

  (** val error_no_fuel_call_return_type :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_ErrorNoFuel -> Coq_ty.coq_Ty **)

  let error_no_fuel_call_return_type _ e =
    e.error_no_fuel_call_return_type

  (** val error_no_fuel_call_function :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_ErrorNoFuel -> PROG._UU1d46d_ **)

  let error_no_fuel_call_function _ e =
    e.error_no_fuel_call_function

  (** val error_no_fuel_call_arguments :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_ErrorNoFuel -> B.coq_SStore **)

  let error_no_fuel_call_arguments _ e =
    e.error_no_fuel_call_arguments

  (** val error_no_fuel_pathcondition :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_ErrorNoFuel -> SIG.coq_PathCondition **)

  let error_no_fuel_pathcondition _ e =
    e.error_no_fuel_pathcondition

  (** val error_no_fuel_heap :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_ErrorNoFuel -> SIG.coq_SHeap **)

  let error_no_fuel_heap _ e =
    e.error_no_fuel_heap

  type coq_EErrorNoFuel = { eerror_no_fuel_call_parameter_types : (coq_PVar,
                                                                  Coq_ty.coq_Ty)
                                                                  Binding.coq_Binding
                                                                  Coq_ctx.coq_Ctx;
                            eerror_no_fuel_call_return_type : Coq_ty.coq_Ty;
                            eerror_no_fuel_call_function : PROG._UU1d46d_;
                            eerror_no_fuel_call_arguments : (coq_PVar,
                                                            Coq_ty.coq_Ty,
                                                            B.coq_ETerm)
                                                            coq_NamedEnv;
                            eerror_no_fuel_pathcondition : SIG.coq_EFormula
                                                           list;
                            eerror_no_fuel_heap : SIG.coq_EChunk list }

  (** val eerror_no_fuel_call_parameter_types :
      coq_EErrorNoFuel -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let eerror_no_fuel_call_parameter_types e =
    e.eerror_no_fuel_call_parameter_types

  (** val eerror_no_fuel_call_return_type :
      coq_EErrorNoFuel -> Coq_ty.coq_Ty **)

  let eerror_no_fuel_call_return_type e =
    e.eerror_no_fuel_call_return_type

  (** val eerror_no_fuel_call_function :
      coq_EErrorNoFuel -> PROG._UU1d46d_ **)

  let eerror_no_fuel_call_function e =
    e.eerror_no_fuel_call_function

  (** val eerror_no_fuel_call_arguments :
      coq_EErrorNoFuel -> (coq_PVar, Coq_ty.coq_Ty, B.coq_ETerm) coq_NamedEnv **)

  let eerror_no_fuel_call_arguments e =
    e.eerror_no_fuel_call_arguments

  (** val eerror_no_fuel_pathcondition :
      coq_EErrorNoFuel -> SIG.coq_EFormula list **)

  let eerror_no_fuel_pathcondition e =
    e.eerror_no_fuel_pathcondition

  (** val eerror_no_fuel_heap : coq_EErrorNoFuel -> SIG.coq_EChunk list **)

  let eerror_no_fuel_heap e =
    e.eerror_no_fuel_heap

  (** val coq_EraseErrorNoFuel :
      (coq_ErrorNoFuel, coq_EErrorNoFuel) B.coq_Erase **)

  let coq_EraseErrorNoFuel _UU03a3_ pat =
    let { error_no_fuel_call_parameter_types =
      error_no_fuel_call_parameter_types0; error_no_fuel_call_return_type =
      error_no_fuel_call_return_type0; error_no_fuel_call_function = f0;
      error_no_fuel_call_arguments = _UU0394_0; error_no_fuel_pathcondition =
      pc; error_no_fuel_heap = h } = pat
    in
    { eerror_no_fuel_call_parameter_types =
    error_no_fuel_call_parameter_types0; eerror_no_fuel_call_return_type =
    error_no_fuel_call_return_type0; eerror_no_fuel_call_function = f0;
    eerror_no_fuel_call_arguments =
    (B.erase (B.coq_EraseSStore error_no_fuel_call_parameter_types0) _UU03a3_
      _UU0394_0);
    eerror_no_fuel_pathcondition =
    (B.erase (B.erase_Ctx SIG.erase_Formula) _UU03a3_ pc);
    eerror_no_fuel_heap =
    (B.erase (B.erase_List SIG.coq_Erase_Chunk) _UU03a3_ h) }

  (** val coq_SubstErrorNoFuel : coq_ErrorNoFuel B.coq_Subst **)

  let coq_SubstErrorNoFuel _UU03a3_0 e _UU03a3_1 _UU03b6_01 =
    let { error_no_fuel_call_parameter_types =
      error_no_fuel_call_parameter_types0; error_no_fuel_call_return_type =
      error_no_fuel_call_return_type0; error_no_fuel_call_function = f0;
      error_no_fuel_call_arguments = args; error_no_fuel_pathcondition = pc;
      error_no_fuel_heap = h } = e
    in
    { error_no_fuel_call_parameter_types =
    error_no_fuel_call_parameter_types0; error_no_fuel_call_return_type =
    error_no_fuel_call_return_type0; error_no_fuel_call_function = f0;
    error_no_fuel_call_arguments =
    (B.subst (B.subst_localstore error_no_fuel_call_parameter_types0)
      _UU03a3_0 args _UU03a3_1 _UU03b6_01);
    error_no_fuel_pathcondition =
    (B.subst (B.subst_ctx SIG.sub_formula) _UU03a3_0 pc _UU03a3_1 _UU03b6_01);
    error_no_fuel_heap =
    (B.subst (B.coq_SubstList SIG.coq_SubstChunk) _UU03a3_0 h _UU03a3_1
      _UU03b6_01) }

  (** val coq_SubstSUErrorNoFuel :
      'a1 B.coq_SubstUniv -> ('a1, coq_ErrorNoFuel) B.coq_SubstSU **)

  let coq_SubstSUErrorNoFuel h _UU03a3_0 _UU03a3_1 e _UU03b6_01 =
    let { error_no_fuel_call_parameter_types =
      error_no_fuel_call_parameter_types0; error_no_fuel_call_return_type =
      error_no_fuel_call_return_type0; error_no_fuel_call_function = f0;
      error_no_fuel_call_arguments = args; error_no_fuel_pathcondition = pc;
      error_no_fuel_heap = h0 } = e
    in
    { error_no_fuel_call_parameter_types =
    error_no_fuel_call_parameter_types0; error_no_fuel_call_return_type =
    error_no_fuel_call_return_type0; error_no_fuel_call_function = f0;
    error_no_fuel_call_arguments =
    (B.substSU
      (B.coq_SubstSU_env h error_no_fuel_call_parameter_types0 (fun b ->
        B.coq_SubstSUTerm h b.Binding.coq_type))
      _UU03a3_0 _UU03a3_1 args _UU03b6_01);
    error_no_fuel_pathcondition =
    (B.substSU (B.substSU_ctx (SIG.subSU_formula h)) _UU03a3_0 _UU03a3_1 pc
      _UU03b6_01);
    error_no_fuel_heap =
    (B.substSU (B.substSU_list (SIG.coq_SubstSUChunk h)) _UU03a3_0 _UU03a3_1
      h0 _UU03b6_01) }

  (** val coq_SubstLawsErrorNoFuel : coq_ErrorNoFuel B.coq_SubstLaws **)

  let coq_SubstLawsErrorNoFuel =
    B.Build_SubstLaws

  (** val coq_OccursCheckErrorNoFuel : coq_ErrorNoFuel B.coq_OccursCheck **)

  let coq_OccursCheckErrorNoFuel _UU03a3_ x xIn d =
    let { error_no_fuel_call_parameter_types =
      error_no_fuel_call_parameter_types0; error_no_fuel_call_return_type =
      error_no_fuel_call_return_type0; error_no_fuel_call_function = f0;
      error_no_fuel_call_arguments = args; error_no_fuel_pathcondition = pc;
      error_no_fuel_heap = h } = d
    in
    Coq_option.bind
      (B.occurs_check
        (B.occurs_check_env (fun i -> B.occurs_check_term i.Binding.coq_type)
          error_no_fuel_call_parameter_types0)
        _UU03a3_ x xIn args)
      (fun args' ->
      Coq_option.bind
        (B.occurs_check (B.occurscheck_ctx SIG.coq_OccursCheckFormula)
          _UU03a3_ x xIn pc)
        (fun pc' ->
        Coq_option.bind
          (B.occurs_check (B.occurs_check_list SIG.coq_OccursCheckChunk)
            _UU03a3_ x xIn h)
          (fun h' -> Some { error_no_fuel_call_parameter_types =
          error_no_fuel_call_parameter_types0;
          error_no_fuel_call_return_type = error_no_fuel_call_return_type0;
          error_no_fuel_call_function = f0; error_no_fuel_call_arguments =
          args'; error_no_fuel_pathcondition = pc'; error_no_fuel_heap = h' })))

  (** val coq_GenOccursCheckErrorNoFuel :
      (B.coq_WeakensTo, coq_ErrorNoFuel) B.coq_GenOccursCheck **)

  let coq_GenOccursCheckErrorNoFuel _UU03a3_ d =
    let { error_no_fuel_call_parameter_types =
      error_no_fuel_call_parameter_types0; error_no_fuel_call_return_type =
      error_no_fuel_call_return_type0; error_no_fuel_call_function = f0;
      error_no_fuel_call_arguments = args; error_no_fuel_pathcondition = pc;
      error_no_fuel_heap = h } = d
    in
    B.liftTernOp B.substUniv_weaken B.substUnivMeet_weaken B.substUniv_weaken
      B.substUnivMeet_weaken _UU03a3_
      (B.coq_SubstSU_env B.substUniv_weaken
        error_no_fuel_call_parameter_types0 (fun b ->
        B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type))
      (B.substSU_ctx (SIG.subSU_formula B.substUniv_weaken))
      (B.substSU_list (SIG.coq_SubstSUChunk B.substUniv_weaken))
      (coq_SubstSUErrorNoFuel B.substUniv_weaken) (fun _ args' pc' h' ->
      { error_no_fuel_call_parameter_types =
      error_no_fuel_call_parameter_types0; error_no_fuel_call_return_type =
      error_no_fuel_call_return_type0; error_no_fuel_call_function = f0;
      error_no_fuel_call_arguments = args'; error_no_fuel_pathcondition =
      pc'; error_no_fuel_heap = h' })
      (B.gen_occurs_check B.substUniv_weaken
        (B.coq_SubstSU_env B.substUniv_weaken
          error_no_fuel_call_parameter_types0 (fun b ->
          B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type))
        (B.gen_occurs_check_env B.substUniv_weaken B.substUnivMeet_weaken
          B.substUniv_weaken B.substUnivMeet_weaken (fun b ->
          B.coq_SubstSUTerm B.substUniv_weaken b.Binding.coq_type) (fun i ->
          B.gen_occurs_check_term B.substUniv_weaken B.substUnivMeet_weaken
            B.substUnivVar_weaken B.substUniv_weaken B.substUnivMeet_weaken
            B.substUniv_weaken B.substUnivMeet_weaken i.Binding.coq_type)
          error_no_fuel_call_parameter_types0)
        _UU03a3_ args)
      (B.gen_occurs_check B.substUniv_weaken
        (B.substSU_ctx (SIG.subSU_formula B.substUniv_weaken))
        (B.gen_occurscheck_ctx (SIG.subSU_formula B.substUniv_weaken)
          B.substUniv_weaken B.substUnivMeet_weaken
          (SIG.coq_GenOccursCheckFormula B.substUniv_weaken
            B.substUnivMeet_weaken B.substUnivVar_weaken B.substUniv_weaken
            B.substUnivMeet_weaken B.substUniv_weaken B.substUnivMeet_weaken))
        _UU03a3_ pc)
      (B.gen_occurs_check B.substUniv_weaken
        (B.substSU_list (SIG.coq_SubstSUChunk B.substUniv_weaken))
        (B.gen_occurs_check_list B.substUniv_weaken B.substUnivMeet_weaken
          B.substUniv_weaken B.substUnivMeet_weaken
          (SIG.coq_SubstSUChunk B.substUniv_weaken)
          SIG.coq_GenOccursCheckChunk)
        _UU03a3_ h)

  (** val coq_VerificationCondition_rect :
      SIG.SymProp.coq_SymProp -> (__ -> 'a1) -> 'a1 **)

  let coq_VerificationCondition_rect _ f0 =
    f0 __

  (** val coq_VerificationCondition_rec :
      SIG.SymProp.coq_SymProp -> (__ -> 'a1) -> 'a1 **)

  let coq_VerificationCondition_rec _ f0 =
    f0 __

  (** val coq_VerificationConditionWithErasure_rect :
      SIG.Erasure.coq_ESymProp -> (__ -> 'a1) -> 'a1 **)

  let coq_VerificationConditionWithErasure_rect _ f0 =
    f0 __

  (** val coq_VerificationConditionWithErasure_rec :
      SIG.Erasure.coq_ESymProp -> (__ -> 'a1) -> 'a1 **)

  let coq_VerificationConditionWithErasure_rec _ f0 =
    f0 __

  type coq_Config = { config_debug_function : ((coq_PVar, Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_Ctx ->
                                              Coq_ty.coq_Ty -> PROG._UU1d46d_
                                              -> bool);
                      config_debug_lemma : ((coq_PVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding
                                           Coq_ctx.coq_Ctx -> PROG._UU1d473_
                                           -> bool) }

  (** val config_debug_function :
      coq_Config -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> PROG._UU1d46d_ -> bool **)

  let config_debug_function c =
    c.config_debug_function

  (** val config_debug_lemma :
      coq_Config -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> PROG._UU1d473_ -> bool **)

  let config_debug_lemma c =
    c.config_debug_lemma

  (** val default_config : coq_Config **)

  let default_config =
    { config_debug_function = (fun _ _ _ -> Coq_false); config_debug_lemma =
      (fun _ _ -> Coq_false) }

  type 'a coq_SStoreSpec =
    (('a, (B.coq_SStore, (SIG.coq_SHeap, SIG.SymProp.coq_SymProp)
    SIG.coq_Impl) SIG.coq_Impl) SIG.coq_Impl SIG.coq_Box, (B.coq_SStore,
    (SIG.coq_SHeap, SIG.SymProp.coq_SymProp) SIG.coq_Impl) SIG.coq_Impl)
    SIG.coq_Impl

  type coq_ExecCall =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> PROG._UU1d46d_ -> (B.coq_SStore, B.coq_Term
    SIG.coq_SHeapSpec) SIG.coq_Impl SIG.coq_Valid

  type coq_ExecCallForeign =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> PROG._UU1d46d__UU1d47f_ -> (B.coq_SStore, B.coq_Term
    SIG.coq_SHeapSpec) SIG.coq_Impl SIG.coq_Valid

  type coq_ExecLemma =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    PROG._UU1d473_ -> (B.coq_SStore, B.coq_Unit SIG.coq_SHeapSpec)
    SIG.coq_Impl SIG.coq_Valid

  type coq_ExecFail =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> B.coq_Term coq_SStoreSpec SIG.coq_Valid

  type coq_Exec =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> PROG.coq_Stm -> B.coq_Term coq_SStoreSpec SIG.coq_Valid

  module SStoreSpec =
   struct
    (** val evalStoreSpec :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
        coq_SStoreSpec, (B.coq_SStore, 'a1 SIG.coq_SHeapSpec) SIG.coq_Impl)
        SIG.coq_Impl SIG.coq_Valid **)

    let evalStoreSpec _ _ _ m _UU03b4_ _UU03a6_ =
      m (fun w1 _UU03b8_1 a1 _ -> _UU03a6_ w1 _UU03b8_1 a1) _UU03b4_

    (** val lift_purespec :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
        SIG.coq_SPureSpec, 'a1 coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid **)

    let lift_purespec _UU0393_ w0 m pOST _UU03b4_0 h0 =
      m (fun w1 _UU03c9_01 a1 ->
        pOST w1 _UU03c9_01 a1
          (SIG.persist (SIG.persistent_subst (B.subst_localstore _UU0393_))
            w0 _UU03b4_0 w1 _UU03c9_01)
          (SIG.persist
            (SIG.persistent_subst (B.coq_SubstList SIG.coq_SubstChunk)) w0 h0
            w1 _UU03c9_01))

    (** val lift_heapspec :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
        SIG.coq_SHeapSpec, 'a1 coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid **)

    let lift_heapspec _UU0393_ w0 m _UU03a6_ _UU03b4_0 =
      m (fun w1 _UU03b8_1 a1 ->
        _UU03a6_ w1 _UU03b8_1 a1
          (SIG.persist (SIG.persistent_subst (B.subst_localstore _UU0393_))
            w0 _UU03b4_0 w1 _UU03b8_1))

    (** val pure :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ('a1, 'a1 coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid **)

    let pure _ w a k =
      SIG.coq_T w k a

    (** val bind :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
        coq_SStoreSpec, (('a1, 'a2 coq_SStoreSpec) SIG.coq_Impl SIG.coq_Box,
        'a2 coq_SStoreSpec) SIG.coq_Impl) SIG.coq_Impl SIG.coq_Valid **)

    let bind _ _ _ w0 ma f0 k =
      ma (fun w1 _UU03c9_01 a1 ->
        f0 w1 _UU03c9_01 a1 (SIG.four w0 k w1 _UU03c9_01))

    (** val error :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ((B.coq_SStore, (SIG.coq_SHeap, B.Coq_amsg.coq_AMessage)
        SIG.coq_Impl) SIG.coq_Impl, 'a1 coq_SStoreSpec) SIG.coq_Impl
        SIG.coq_Valid **)

    let error _ _ _ msg _ _UU03b4_ h =
      SIG.SymProp.Coq_error (msg _UU03b4_ h)

    (** val block :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
        coq_SStoreSpec SIG.coq_Valid **)

    let block _ _ _ _ _ _ =
      SIG.SymProp.Coq_block

    (** val angelic_binary :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
        coq_SStoreSpec, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
        SIG.coq_Impl) SIG.coq_Impl SIG.coq_Valid **)

    let angelic_binary _ _ _ m1 m2 pOST _UU03b4_1 h1 =
      SIG.SymProp.Coq_angelic_binary ((m1 pOST _UU03b4_1 h1),
        (m2 pOST _UU03b4_1 h1))

    (** val demonic_binary :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
        coq_SStoreSpec, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
        SIG.coq_Impl) SIG.coq_Impl SIG.coq_Valid **)

    let demonic_binary _ _ _ m1 m2 pOST _UU03b4_1 h1 =
      SIG.SymProp.Coq_demonic_binary ((m1 pOST _UU03b4_1 h1),
        (m2 pOST _UU03b4_1 h1))

    (** val angelic :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_LVar option -> (Coq_ty.coq_Ty, B.coq_Term coq_SStoreSpec)
        SIG.coq_Forall SIG.coq_Valid **)

    let angelic _UU0393_ x w _UU03c3_ =
      lift_purespec _UU0393_ w (SIG.SPureSpec.angelic x w _UU03c3_)

    (** val demonic :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_LVar option -> (Coq_ty.coq_Ty, B.coq_Term coq_SStoreSpec)
        SIG.coq_Forall SIG.coq_Valid **)

    let demonic _UU0393_ x w _UU03c3_ =
      lift_purespec _UU0393_ w (SIG.SPureSpec.demonic x w _UU03c3_)

    (** val debug :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ((B.coq_SStore, (SIG.coq_SHeap, B.Coq_amsg.coq_AMessage)
        SIG.coq_Impl) SIG.coq_Impl, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
        SIG.coq_Impl) SIG.coq_Impl SIG.coq_Valid **)

    let debug _ _ _ d m pOST _UU03b4_ h =
      SIG.SymProp.Coq_debug ((d _UU03b4_ h), (m pOST _UU03b4_ h))

    (** val angelic_ctx :
        ('a1 -> coq_LVar) -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) coq_NamedEnv
        coq_SStoreSpec) SIG.coq_Forall SIG.coq_Valid **)

    let angelic_ctx n _UU0393_ w _UU0394_0 =
      lift_purespec _UU0393_ w (SIG.SPureSpec.angelic_ctx n w _UU0394_0)

    (** val demonic_ctx :
        ('a1 -> coq_LVar) -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) coq_NamedEnv
        coq_SStoreSpec) SIG.coq_Forall SIG.coq_Valid **)

    let demonic_ctx n _UU0393_ w _UU0394_0 =
      lift_purespec _UU0393_ w (SIG.SPureSpec.demonic_ctx n w _UU0394_0)

    module Coq_notations =
     struct
     end

    (** val demonic_pattern_match :
        ('a1 -> coq_LVar) -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term,
        'a1 B.coq_SMatchResult coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid **)

    let demonic_pattern_match n _UU0393_ _UU03c3_ pat w0 t _UU03a6_ _UU03b4_ h =
      SIG.SPureSpec.demonic_pattern_match n _UU03c3_ pat w0 t
        (fun w1 _UU03b8_1 mr ->
        _UU03a6_ w1 _UU03b8_1 mr
          (SIG.persist (SIG.persistent_subst (B.subst_localstore _UU0393_))
            w0 _UU03b4_ w1 _UU03b8_1)
          (SIG.persist
            (SIG.persistent_subst (B.coq_SubstList SIG.coq_SubstChunk)) w0 h
            w1 _UU03b8_1))

    (** val pushpop :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PVar -> Coq_ty.coq_Ty -> (B.coq_Term, ('a1 coq_SStoreSpec, 'a1
        coq_SStoreSpec) SIG.coq_Impl) SIG.coq_Impl SIG.coq_Valid **)

    let pushpop _UU0393_1 _UU0393_2 x _UU03c3_ _ t m pOST _UU03b4_ h =
      m (fun w1 _UU03c9_01 a1 _UU03b4_1 ->
        pOST w1 _UU03c9_01 a1
          (Coq_env.tail _UU0393_2 { Binding.name = x; Binding.coq_type =
            _UU03c3_ } _UU03b4_1))
        (Coq_env.Coq_snoc (_UU0393_1, _UU03b4_, { Binding.name = x;
        Binding.coq_type = _UU03c3_ }, t)) h

    (** val pushspops :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (B.coq_SStore, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec) SIG.coq_Impl)
        SIG.coq_Impl SIG.coq_Valid **)

    let pushspops _UU0393_1 _UU0393_2 _UU0394_0 _ _UU03b4__UU0394_ m pOST _UU03b4_ h =
      m (fun w1 _UU03c9_01 a1 _UU03b4_1 ->
        pOST w1 _UU03c9_01 a1 (Coq_env.drop _UU0393_2 _UU0394_0 _UU03b4_1))
        (Coq_env.cat _UU0393_1 _UU0394_0 _UU03b4_ _UU03b4__UU0394_) h

    (** val get_local :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        B.coq_SStore coq_SStoreSpec SIG.coq_Valid **)

    let get_local _ w0 pOST _UU03b4_ =
      SIG.coq_T w0 pOST _UU03b4_ _UU03b4_

    (** val put_local :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (B.coq_SStore, B.coq_Unit coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid **)

    let put_local _ _ w0 _UU03b4_ pOST _ =
      SIG.coq_T w0 pOST Coq_tt _UU03b4_

    (** val eval_exp :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> B.coq_Exp -> B.coq_Term coq_SStoreSpec SIG.coq_Valid **)

    let eval_exp _UU0393_ _UU03c3_ e w pOST _UU03b4_ =
      SIG.coq_T w pOST
        (B.peval (SIG.wctx w) _UU03c3_
          (B.seval_exp _UU0393_ (SIG.wctx w) _UU03b4_ _UU03c3_ e))
        _UU03b4_

    (** val eval_exps :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_PVar, Coq_ty.coq_Ty, B.coq_Exp) coq_NamedEnv -> B.coq_SStore
        coq_SStoreSpec SIG.coq_Valid **)

    let eval_exps _UU0393_ _UU03c3_s es w pOST _UU03b4_ =
      SIG.coq_T w pOST
        (B.seval_exps _UU0393_ (SIG.wctx w) _UU03b4_ _UU03c3_s es) _UU03b4_

    (** val assign :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PVar -> Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_In -> (B.coq_Term, B.coq_Unit
        coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid **)

    let assign _UU0393_ x _UU03c3_ xIn w0 t pOST _UU03b4_ =
      SIG.coq_T w0 pOST Coq_tt
        (Coq_env.update _UU0393_ _UU03b4_ { Binding.name = x;
          Binding.coq_type = _UU03c3_ } xIn t)

    (** val exec_aux :
        coq_ExecCallForeign -> coq_ExecLemma -> coq_ExecCall -> coq_ExecFail
        -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> PROG.coq_Stm -> B.coq_Term coq_SStoreSpec
        SIG.coq_Valid **)

    let rec exec_aux exec_call_foreign exec_lemma exec_call exec_fail _UU0393_ _UU03c4_0 s w0 =
      match s with
      | PROG.Coq_stm_val v -> pure _UU0393_ w0 (B.Coq_term_val (_UU03c4_0, v))
      | PROG.Coq_stm_exp e -> eval_exp _UU0393_ _UU03c4_0 e w0
      | PROG.Coq_stm_let (x, _UU03c3_, s___UU03c3_, s___UU03c4_) ->
        bind _UU0393_ _UU0393_ _UU0393_ w0
          (exec_aux exec_call_foreign exec_lemma exec_call exec_fail _UU0393_
            _UU03c3_ s___UU03c3_ w0)
          (fun w1 _ t ->
          pushpop _UU0393_ _UU0393_ x _UU03c3_ w1 t
            (exec_aux exec_call_foreign exec_lemma exec_call exec_fail
              (Coq_ctx.Coq_snoc (_UU0393_, { Binding.name = x;
              Binding.coq_type = _UU03c3_ })) _UU03c4_0 s___UU03c4_ w1))
      | PROG.Coq_stm_block (_UU0394_0, _UU03b4_, s0) ->
        pushspops _UU0393_ _UU0393_ _UU0394_0 w0
          (B.lift
            (B.lift_env (fun _UU03c4_1 ->
              B.lift_term _UU03c4_1.Binding.coq_type) _UU0394_0)
            (SIG.wctx w0) _UU03b4_)
          (exec_aux exec_call_foreign exec_lemma exec_call exec_fail
            (Coq_ctx.cat _UU0393_ _UU0394_0) _UU03c4_0 s0 w0)
      | PROG.Coq_stm_assign (x, xIn_UU0393_, s0) ->
        bind _UU0393_ _UU0393_ _UU0393_ w0
          (exec_aux exec_call_foreign exec_lemma exec_call exec_fail _UU0393_
            _UU03c4_0 s0 w0)
          (fun w1 _ t ->
          bind _UU0393_ _UU0393_ _UU0393_ w1
            (assign _UU0393_ x _UU03c4_0 xIn_UU0393_ w1 t)
            (fun w2 _UU03c9_12 _ ->
            pure _UU0393_ w2
              (SIG.persist (SIG.persistent_subst (B.coq_SubstTerm _UU03c4_0))
                w1 t w2 _UU03c9_12)))
      | PROG.Coq_stm_call (_UU0394_0, f0, es) ->
        bind _UU0393_ _UU0393_ _UU0393_ w0
          (eval_exps _UU0393_ _UU0394_0 es w0) (fun w1 _ args ->
          lift_heapspec _UU0393_ w1 (exec_call _UU0394_0 _UU03c4_0 f0 w1 args))
      | PROG.Coq_stm_call_frame (_UU0394_0, _UU03b4_, s0) ->
        bind _UU0393_ _UU0393_ _UU0393_ w0 (get_local _UU0393_ w0)
          (fun w1 _ _UU03b4_1 ->
          bind _UU0393_ _UU0394_0 _UU0393_ w1
            (put_local _UU0393_ _UU0394_0 w1
              (B.lift
                (B.lift_env (fun _UU03c4_1 ->
                  B.lift_term _UU03c4_1.Binding.coq_type) _UU0394_0)
                (SIG.wctx w1) _UU03b4_))
            (fun w2 _UU03c9_12 _ ->
            bind _UU0394_0 _UU0394_0 _UU0393_ w2
              (exec_aux exec_call_foreign exec_lemma exec_call exec_fail
                _UU0394_0 _UU03c4_0 s0 w2)
              (fun w3 _UU03c9_23 t ->
              bind _UU0394_0 _UU0393_ _UU0393_ w3
                (put_local _UU0394_0 _UU0393_ w3
                  (SIG.persist
                    (SIG.persistent_subst (B.subst_localstore _UU0393_)) w1
                    _UU03b4_1 w3
                    (SIG.acc_trans w1 w2 w3 _UU03c9_12 _UU03c9_23)))
                (fun w4 _UU03c9_34 _ ->
                pure _UU0393_ w4
                  (SIG.persist
                    (SIG.persistent_subst (B.coq_SubstTerm _UU03c4_0)) w3 t
                    w4 _UU03c9_34)))))
      | PROG.Coq_stm_foreign (_UU0394_0, f0, es) ->
        bind _UU0393_ _UU0393_ _UU0393_ w0
          (eval_exps _UU0393_ _UU0394_0 es w0) (fun w1 _ args ->
          lift_heapspec _UU0393_ w1
            (exec_call_foreign _UU0394_0 _UU03c4_0 f0 w1 args))
      | PROG.Coq_stm_lemmak (_UU0394_0, l, es, k) ->
        bind _UU0393_ _UU0393_ _UU0393_ w0
          (eval_exps _UU0393_ _UU0394_0 es w0) (fun w1 _ args ->
          bind _UU0393_ _UU0393_ _UU0393_ w1
            (lift_heapspec _UU0393_ w1 (exec_lemma _UU0394_0 l w1 args))
            (fun w2 _ _ ->
            exec_aux exec_call_foreign exec_lemma exec_call exec_fail
              _UU0393_ _UU03c4_0 k w2))
      | PROG.Coq_stm_seq (_UU03c3_, s1, s2) ->
        bind _UU0393_ _UU0393_ _UU0393_ w0
          (exec_aux exec_call_foreign exec_lemma exec_call exec_fail _UU0393_
            _UU03c3_ s1 w0)
          (fun w1 _ _ ->
          exec_aux exec_call_foreign exec_lemma exec_call exec_fail _UU0393_
            _UU03c4_0 s2 w1)
      | PROG.Coq_stm_assertk (e, _, k) ->
        bind _UU0393_ _UU0393_ _UU0393_ w0
          (eval_exp _UU0393_ Coq_ty.Coq_bool e w0) (fun w1 _ t ->
          bind _UU0393_ _UU0393_ _UU0393_ w1
            (lift_heapspec _UU0393_ w1
              (SIG.SHeapSpec.assert_formula w1 (fun _ ->
                B.Coq_amsg.empty (SIG.wctx w1))
                (match FL.fail_rule_pre with
                 | Coq_true -> SIG.Coq_formula_true
                 | Coq_false ->
                   SIG.Coq_formula_relop (Coq_ty.Coq_bool, (Coq_bop.Coq_neq
                     Coq_ty.Coq_bool), t, (B.Coq_term_val (Coq_ty.Coq_bool,
                     (Obj.magic Coq_false)))))))
            (fun w2 _UU03c9_12 _ ->
            bind _UU0393_ _UU0393_ _UU0393_ w2
              (lift_heapspec _UU0393_ w2
                (SIG.SHeapSpec.assume_formula w2 (SIG.Coq_formula_bool
                  (SIG.persist
                    (SIG.persistent_subst (B.coq_SubstTerm Coq_ty.Coq_bool))
                    w1 t w2 _UU03c9_12))))
              (fun w3 _ _ ->
              exec_aux exec_call_foreign exec_lemma exec_call exec_fail
                _UU0393_ _UU03c4_0 k w3)))
      | PROG.Coq_stm_fail s0 -> exec_fail _UU0393_ _UU03c4_0 s0 w0
      | PROG.Coq_stm_pattern_match (_UU03c3_, s0, pat, rhs) ->
        bind _UU0393_ _UU0393_ _UU0393_ w0
          (exec_aux exec_call_foreign exec_lemma exec_call exec_fail _UU0393_
            _UU03c3_ s0 w0)
          (fun w1 _ v ->
          bind _UU0393_ _UU0393_ _UU0393_ w1
            (demonic_pattern_match B.varkit.coq_PVartoLVar _UU0393_ _UU03c3_
              pat w1 v)
            (fun w2 _ pat0 ->
            let Coq_existT (pc, vs) = pat0 in
            pushspops _UU0393_ _UU0393_
              (B.coq_PatternCaseCtx _UU03c3_ pat pc) w2 vs
              (exec_aux exec_call_foreign exec_lemma exec_call exec_fail
                (Coq_ctx.cat _UU0393_ (B.coq_PatternCaseCtx _UU03c3_ pat pc))
                _UU03c4_0 (rhs pc) w2)))
      | PROG.Coq_stm_read_register reg ->
        lift_heapspec _UU0393_ w0
          (SIG.SHeapSpec.read_register _UU03c4_0 reg w0)
      | PROG.Coq_stm_write_register (reg, e) ->
        bind _UU0393_ _UU0393_ _UU0393_ w0 (eval_exp _UU0393_ _UU03c4_0 e w0)
          (fun w1 _ tnew ->
          lift_heapspec _UU0393_ w1
            (SIG.SHeapSpec.write_register _UU03c4_0 reg w1 tnew))
      | PROG.Coq_stm_bind (_, _, _) ->
        error _UU0393_ _UU0393_ w0 (fun _UU03b4_ h -> B.Coq_amsg.Coq_mk
          ((Obj.magic SIG.coq_SubstMessage),
          (Obj.magic SIG.coq_SubstSUMessage B.substUniv_weaken),
          (Obj.magic SIG.coq_SubstLawsMessage),
          (Obj.magic SIG.coq_OccursCheckMessage),
          (Obj.magic SIG.coq_EraseMessage),
          (Obj.magic { SIG.msg_function = (String ((Ascii (Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))); SIG.msg_message =
            (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            EmptyString))))))))))))))))))))))))))))))))))))))))))));
            SIG.msg_program_context = _UU0393_; SIG.msg_localstore =
            _UU03b4_; SIG.msg_heap = h; SIG.msg_pathcondition =
            (SIG.wco w0) })))
      | PROG.Coq_stm_debugk k ->
        debug _UU0393_ _UU0393_ w0 (fun _UU03b4_0 h0 -> B.Coq_amsg.Coq_mk
          ((Obj.magic coq_SubstDebugStm),
          (Obj.magic coq_SubstSUDebugStm B.substUniv_weaken),
          (Obj.magic coq_SubstLawsDebugStm),
          (Obj.magic coq_OccursCheckDebugStm), (Obj.magic coq_EraseDebugStm),
          (Obj.magic { debug_stm_program_context = _UU0393_;
            debug_stm_statement_type = _UU03c4_0; debug_stm_statement = k;
            debug_stm_pathcondition = (SIG.wco w0); debug_stm_localstore =
            _UU03b4_0; debug_stm_heap = h0 })))
          (exec_aux exec_call_foreign exec_lemma exec_call exec_fail _UU0393_
            _UU03c4_0 k w0)
   end

  (** val exec_contract :
      coq_Exec -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> SIG.coq_SepContract -> PROG.coq_Stm
      -> B.coq_Unit SIG.coq_SHeapSpec SIG.coq_Valid **)

  let exec_contract exec _UU0394_0 _UU03c4_0 c s w =
    let { SIG.sep_contract_logic_variables = lvars;
      SIG.sep_contract_localstore = pats; SIG.sep_contract_precondition =
      req; SIG.sep_contract_result = result; SIG.sep_contract_postcondition =
      ens } = c
    in
    SIG.SHeapSpec.bind w (SIG.SHeapSpec.demonic_ctx id w lvars)
      (fun w1 _ lenv ->
      SIG.SHeapSpec.bind w1 (SIG.SHeapSpec.produce lvars req w1 lenv)
        (fun w2 _UU03b8_2 _ ->
        let lenv2 =
          SIG.persist
            (SIG.persistent_subst
              (B.coq_SubstEnv (fun b -> B.coq_SubstTerm b.Binding.coq_type)
                lvars))
            w1 lenv w2 _UU03b8_2
        in
        SIG.SHeapSpec.bind w2
          (SStoreSpec.evalStoreSpec _UU0394_0 _UU0394_0 w2
            (exec _UU0394_0 _UU03c4_0 s w2)
            (B.subst (B.subst_localstore _UU0394_0) lvars pats (SIG.wctx w2)
              lenv2))
          (fun w3 _UU03b8_3 res ->
          let lenv3 =
            SIG.persist
              (SIG.persistent_subst
                (B.coq_SubstEnv (fun b -> B.coq_SubstTerm b.Binding.coq_type)
                  lvars))
              w2 lenv2 w3 _UU03b8_3
          in
          SIG.SHeapSpec.consume (Coq_ctx.Coq_snoc (lvars, { Binding.name =
            result; Binding.coq_type = _UU03c4_0 })) ens w3
            (B.sub_snoc lvars (SIG.wctx w3) lenv3 { Binding.name = result;
              Binding.coq_type = _UU03c4_0 } res))))

  (** val exec_call_error_no_fuel : coq_ExecCall **)

  let exec_call_error_no_fuel _UU0394_0 _UU03c4_0 f0 w args _ h =
    SIG.SymProp.Coq_error (B.Coq_amsg.Coq_mk
      ((Obj.magic coq_SubstErrorNoFuel),
      (Obj.magic coq_SubstSUErrorNoFuel B.substUniv_weaken),
      (Obj.magic coq_SubstLawsErrorNoFuel),
      (Obj.magic coq_OccursCheckErrorNoFuel),
      (Obj.magic coq_EraseErrorNoFuel),
      (Obj.magic { error_no_fuel_call_parameter_types = _UU0394_0;
        error_no_fuel_call_return_type = _UU03c4_0;
        error_no_fuel_call_function = f0; error_no_fuel_call_arguments =
        args; error_no_fuel_pathcondition = (SIG.wco w); error_no_fuel_heap =
        h })))

  (** val sexec_call_foreign : coq_ExecCallForeign **)

  let sexec_call_foreign _UU0394_0 _UU03c4_0 f0 w args =
    SIG.SHeapSpec.call_contract _UU0394_0 _UU03c4_0
      (SPEC.coq_CEnvEx _UU0394_0 _UU03c4_0 f0) w args

  (** val debug_lemma :
      coq_Config -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> PROG._UU1d473_ -> (B.coq_SStore, B.coq_Unit
      SIG.coq_SHeapSpec) SIG.coq_Impl SIG.coq_Valid **)

  let debug_lemma cfg _UU0394_0 l w0 args0 =
    match cfg.config_debug_lemma _UU0394_0 l with
    | Coq_true ->
      SIG.SHeapSpec.debug w0 (fun h0 -> B.Coq_amsg.Coq_mk
        ((Obj.magic coq_SubstDebugCallLemma),
        (Obj.magic coq_SubstSUDebugCallLemma B.substUniv_weaken),
        (Obj.magic coq_SubstLawsDebugCallLemma),
        (Obj.magic coq_OccursCheckDebugCallLemma),
        (Obj.magic coq_EraseDebugCallLemma),
        (Obj.magic { debug_call_lemma_parameters = _UU0394_0;
          debug_call_lemma_name = l; debug_call_lemma_contract =
          (SPEC.coq_LEnv _UU0394_0 l); debug_call_lemma_arguments = args0;
          debug_call_lemma_pathcondition = (SIG.wco w0);
          debug_call_lemma_heap = h0 })))
        (SIG.SHeapSpec.pure w0 Coq_tt)
    | Coq_false -> SIG.SHeapSpec.pure w0 Coq_tt

  (** val sexec_lemma : coq_Config -> coq_ExecLemma **)

  let sexec_lemma cfg _UU0394_0 l w args =
    SIG.SHeapSpec.bind w (debug_lemma cfg _UU0394_0 l w args)
      (fun w1 _UU03b8_ _ ->
      SIG.SHeapSpec.call_lemma _UU0394_0 (SPEC.coq_LEnv _UU0394_0 l) w1
        (SIG.persist (SIG.persistent_subst (B.subst_localstore _UU0394_0)) w
          args w1 _UU03b8_))

  (** val debug_call :
      coq_Config -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> PROG._UU1d46d_ -> (B.coq_SStore,
      B.coq_Unit SIG.coq_SHeapSpec) SIG.coq_Impl SIG.coq_Valid **)

  let debug_call cfg _UU0394_0 _UU03c4_0 f0 w0 args0 =
    match cfg.config_debug_function _UU0394_0 _UU03c4_0 f0 with
    | Coq_true ->
      SIG.SHeapSpec.debug w0 (fun h0 -> B.Coq_amsg.Coq_mk
        ((Obj.magic coq_SubstDebugCall),
        (Obj.magic coq_SubstSUDebugCall B.substUniv_weaken),
        (Obj.magic coq_SubstLawsDebugCall),
        (Obj.magic coq_OccursCheckDebugCall), (Obj.magic coq_EraseDebugCall),
        (Obj.magic { debug_call_function_parameters = _UU0394_0;
          debug_call_function_result_type = _UU03c4_0;
          debug_call_function_name = f0; debug_call_function_contract =
          (SPEC.coq_CEnv _UU0394_0 _UU03c4_0 f0);
          debug_call_function_arguments = args0; debug_call_pathcondition =
          (SIG.wco w0); debug_call_heap = h0 })))
        (SIG.SHeapSpec.pure w0 Coq_tt)
    | Coq_false -> SIG.SHeapSpec.pure w0 Coq_tt

  (** val sexec_fail : coq_ExecFail **)

  let sexec_fail _UU0393_ _ _ w0 =
    match FL.fail_rule_pre with
    | Coq_true -> SStoreSpec.block _UU0393_ _UU0393_ w0
    | Coq_false ->
      SStoreSpec.error _UU0393_ _UU0393_ w0 (fun _UU03b4_ h ->
        B.Coq_amsg.Coq_mk ((Obj.magic SIG.coq_SubstMessage),
        (Obj.magic SIG.coq_SubstSUMessage B.substUniv_weaken),
        (Obj.magic SIG.coq_SubstLawsMessage),
        (Obj.magic SIG.coq_OccursCheckMessage),
        (Obj.magic SIG.coq_EraseMessage),
        (Obj.magic { SIG.msg_function = (String ((Ascii (Coq_true, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
          (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
          Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
          (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
          Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
          (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
          EmptyString)))))))))))))))))))); SIG.msg_message = (String ((Ascii
          (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
          (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
          Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
          (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
          Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
          (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
          Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
          (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
          (Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
          Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
          (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false)), EmptyString))))))))))))))))))))))))))))))));
          SIG.msg_program_context = _UU0393_; SIG.msg_localstore = _UU03b4_;
          SIG.msg_heap = h; SIG.msg_pathcondition = (SIG.wco w0) })))

  (** val sexec_call : coq_Config -> nat -> coq_ExecCall **)

  let rec sexec_call cfg inline_fuel _UU0394_0 _UU03c4_0 f0 w0 args0 =
    SIG.SHeapSpec.bind w0 (debug_call cfg _UU0394_0 _UU03c4_0 f0 w0 args0)
      (fun w1 _UU03b8_1 _ ->
      match SPEC.coq_CEnv _UU0394_0 _UU03c4_0 f0 with
      | Some c ->
        SIG.SHeapSpec.call_contract _UU0394_0 _UU03c4_0 c w1
          (SIG.persist (SIG.persistent_subst (B.subst_localstore _UU0394_0))
            w0 args0 w1 _UU03b8_1)
      | None ->
        (match inline_fuel with
         | O ->
           exec_call_error_no_fuel _UU0394_0 _UU03c4_0 f0 w1
             (SIG.persist
               (SIG.persistent_subst (B.subst_localstore _UU0394_0)) w0 args0
               w1 _UU03b8_1)
         | S n ->
           SStoreSpec.evalStoreSpec _UU0394_0 _UU0394_0 w1
             (SStoreSpec.exec_aux sexec_call_foreign (sexec_lemma cfg)
               (sexec_call cfg n) sexec_fail _UU0394_0 _UU03c4_0
               (PROG.coq_FunDef _UU0394_0 _UU03c4_0 f0) w1)
             (SIG.persist
               (SIG.persistent_subst (B.subst_localstore _UU0394_0)) w0 args0
               w1 _UU03b8_1)))

  (** val sexec : coq_Config -> nat -> coq_Exec **)

  let sexec cfg inline_fuel =
    SStoreSpec.exec_aux sexec_call_foreign (sexec_lemma cfg)
      (sexec_call cfg inline_fuel) sexec_fail

  (** val vcgen :
      coq_Config -> nat -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> SIG.coq_SepContract -> PROG.coq_Stm
      -> SIG.SymProp.coq_SymProp SIG.coq_Valid **)

  let vcgen cfg inline_fuel _UU0394_0 _UU03c4_0 c s w =
    SIG.SHeapSpec.run w
      (exec_contract (sexec cfg inline_fuel) _UU0394_0 _UU03c4_0 c s w)

  module Symbolic =
   struct
    (** val verification_failed_with_error :
        B.Coq_amsg.coq_EAMessage -> bool **)

    let verification_failed_with_error _ =
      Coq_false

    (** val ok' :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SIG.SymProp.coq_SymProp -> bool **)

    let rec ok' _UU03a3_ = function
    | SIG.SymProp.Coq_error msg ->
      verification_failed_with_error (B.Coq_amsg.erase_amessage _UU03a3_ msg)
    | SIG.SymProp.Coq_block -> Coq_true
    | SIG.SymProp.Coq_debug (_, p0) -> ok' _UU03a3_ p0
    | _ -> Coq_false

    (** val ok :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        SIG.SymProp.coq_SymProp -> bool **)

    let ok _UU03a3_ p =
      ok' _UU03a3_ (SIG.Postprocessing.prune _UU03a3_ p)

    (** val coq_VcGenErasureFuel :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> nat -> SIG.coq_SepContract -> PROG.coq_Stm ->
        SIG.Erasure.coq_ESymProp **)

    let coq_VcGenErasureFuel _UU0394_0 _UU03c4_0 fuel c body =
      SIG.Erasure.erase_symprop (SIG.wctx SIG.wnil)
        (SIG.postprocess (SIG.wctx SIG.wnil)
          (SIG.SPureSpec.replay SIG.wnil
            (SIG.postprocess (SIG.wctx SIG.wnil)
              (vcgen default_config fuel _UU0394_0 _UU03c4_0 c body SIG.wnil))))

    (** val coq_VcGenErasure :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> SIG.coq_SepContract -> PROG.coq_Stm ->
        SIG.Erasure.coq_ESymProp **)

    let coq_VcGenErasure _UU0394_0 _UU03c4_0 c body =
      coq_VcGenErasureFuel _UU0394_0 _UU03c4_0 (S O) c body

    module Statistics =
     struct
      (** val extend_postcond_with_debug :
          (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          Coq_ty.coq_Ty -> SIG.coq_SepContract -> SIG.coq_SepContract **)

      let extend_postcond_with_debug _ _ c =
        let { SIG.sep_contract_logic_variables = lvars;
          SIG.sep_contract_localstore = store;
          SIG.sep_contract_precondition = pre; SIG.sep_contract_result = res;
          SIG.sep_contract_postcondition = post } = c
        in
        { SIG.sep_contract_logic_variables = lvars;
        SIG.sep_contract_localstore = store; SIG.sep_contract_precondition =
        pre; SIG.sep_contract_result = res; SIG.sep_contract_postcondition =
        (SIG.Coq_asn.Coq_sep (post, SIG.Coq_asn.Coq_debug)) }

      (** val calc :
          (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
          Coq_ty.coq_Ty -> PROG._UU1d46d_ -> coq_Stats option **)

      let calc _UU0394_0 _UU03c4_0 f0 =
        match SPEC.coq_CEnv _UU0394_0 _UU03c4_0 f0 with
        | Some contract ->
          let contract' =
            extend_postcond_with_debug _UU0394_0 _UU03c4_0 contract
          in
          let body = PROG.coq_FunDef _UU0394_0 _UU03c4_0 f0 in
          let vc =
            vcgen default_config (S O) _UU0394_0 _UU03c4_0 contract' body
              SIG.wnil
          in
          Some
          (SIG.SymProp.Statistics.count_to_stats
            (SIG.SymProp.Statistics.count_nodes (SIG.wctx SIG.wnil) vc
              SIG.SymProp.Statistics.empty))
        | None -> None
     end
   end
 end
