open Ascii
open Base1
open BinOps
open Bitvector
open Context
open Datatypes
open Environment
open PartialVerifier
open Sig
open String
open TypeDecl
open Variables

module Examples :
 sig
  val minimal_pre :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val minimal_post :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val extend_to_minimal_pre :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val extend_to_minimal_post :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val coq_VC_triple :
    (string, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion -> coq_AST list ->
    RiscvPmpSignature.Coq_asn.coq_Assertion ->
    RiscvPmpSignature.SymProp.coq_SymProp

  type coq_BlockVerifierContract = { precondition : RiscvPmpSignature.Coq_asn.coq_Assertion;
                                     instrs : coq_AST list;
                                     postcondition : RiscvPmpSignature.Coq_asn.coq_Assertion }

  val exec_VC :
    (string, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_BlockVerifierContract -> RiscvPmpSignature.SymProp.coq_SymProp
 end
