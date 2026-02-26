open Ascii
open Base1
open BinOps
open Context
open Datatypes
open Environment
open Machine
open Sig
open Spec
open String
open TypeDecl
open Variables

val exec_instruction_prologue :
  coq_AST -> RiscvPmpSignature.Coq_asn.coq_Assertion

val exec_instruction_epilogue :
  coq_AST -> RiscvPmpSignature.Coq_asn.coq_Assertion

val sexec_instruction :
  coq_AST -> (RiscvPmpBase.coq_Term, RiscvPmpBase.coq_Term
  RiscvPmpSignature.coq_SHeapSpec) RiscvPmpSignature.coq_Impl
  RiscvPmpSignature.coq_Valid

val sexec_block_addr :
  coq_AST list -> (RiscvPmpBase.coq_Term, (RiscvPmpBase.coq_Term,
  RiscvPmpBase.coq_Term RiscvPmpSignature.coq_SHeapSpec)
  RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
  RiscvPmpSignature.coq_Valid

val sexec_triple_addr :
  (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
  RiscvPmpSignature.Coq_asn.coq_Assertion -> coq_AST list ->
  RiscvPmpSignature.Coq_asn.coq_Assertion -> RiscvPmpBase.coq_Unit
  RiscvPmpSignature.coq_SHeapSpec RiscvPmpSignature.coq_Valid

val sblock_verification_condition :
  (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
  RiscvPmpSignature.Coq_asn.coq_Assertion -> coq_AST list ->
  RiscvPmpSignature.Coq_asn.coq_Assertion ->
  RiscvPmpSignature.SymProp.coq_SymProp RiscvPmpSignature.coq_Valid
