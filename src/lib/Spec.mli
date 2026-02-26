open Ascii
open Base1
open BinInt
open BinNat
open BinNums
open BinOps
open Bitvector
open Context
open Contracts
open Datatypes
open Environment
open IrisInstance
open Machine
open Nat
open Prelude
open Sig
open String
open SymbolicExecutor
open TypeDecl
open UnOps
open Variables

type __ = Obj.t

module RiscvPmpBlockVerifFailLogic :
 sig
  val fail_rule_pre : bool
 end

module RiscvPmpBlockVerifSpec :
 sig
  type coq_SepContractEnv =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun ->
    RiscvPmpSignature.coq_SepContract option

  type coq_SepContractEnvEx =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_FunX ->
    RiscvPmpSignature.coq_SepContract

  type coq_LemmaEnv =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpProgram.coq_Lem -> RiscvPmpSignature.coq_Lemma

  type coq_SepContractFun = RiscvPmpSignature.coq_SepContract

  type coq_SepContractFunX = RiscvPmpSignature.coq_SepContract

  type coq_SepLemma = RiscvPmpSignature.coq_Lemma

  val term_eqb :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term

  val z_term :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Z ->
    RiscvPmpBase.coq_Term

  val sep_contract_logvars :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val create_localstore :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_SStore

  val asn_exists :
    (string, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (string,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val asn_with_reg :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> (RiscvPmpBase.coq_Reg ->
    RiscvPmpSignature.Coq_asn.coq_Assertion) ->
    RiscvPmpSignature.Coq_asn.coq_Assertion ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val asn_reg_ptsto :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val sep_contract_rX : RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_wX : RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_fetch_instr : RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_checked_mem_read :
    nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_checked_mem_write :
    nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_pmpCheck : nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_pmp_mem_read :
    nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_pmp_mem_write :
    nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_mem_read : nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_mem_write_value :
    nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_tick_pc : RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_within_phys_mem : RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_execute_EBREAK : RiscvPmpSpecification.coq_SepContractFun

  val coq_CEnv : RiscvPmpSpecification.coq_SepContractEnv

  val sep_contract_read_ram : nat -> RiscvPmpSpecification.coq_SepContractFunX

  val sep_contract_write_ram :
    nat -> RiscvPmpSpecification.coq_SepContractFunX

  val sep_contract_within_mmio :
    nat -> RiscvPmpSpecification.coq_SepContractFunX

  val sep_contract_mmio_write :
    nat -> RiscvPmpSpecification.coq_SepContractFunX

  val sep_contract_decode : RiscvPmpSpecification.coq_SepContractFunX

  val coq_CEnvEx : RiscvPmpSpecification.coq_SepContractEnvEx

  val lemma_open_gprs : RiscvPmpSpecification.coq_SepLemma

  val lemma_close_gprs : RiscvPmpSpecification.coq_SepLemma

  val lemma_open_ptsto_instr : RiscvPmpSpecification.coq_SepLemma

  val lemma_close_ptsto_instr : RiscvPmpSpecification.coq_SepLemma

  val lemma_extract_pmp_ptsto : nat -> RiscvPmpSpecification.coq_SepLemma

  val lemma_return_pmp_ptsto : nat -> RiscvPmpSpecification.coq_SepLemma

  val map_wordwidth : coq_WordWidth -> nat

  val lemma_close_mmio_write :
    Coq_bv.bv -> coq_WordWidth -> RiscvPmpSpecification.coq_SepLemma

  val coq_LEnv : RiscvPmpSpecification.coq_LemmaEnv
 end

module RiscvPmpBlockVerifExecutor :
 sig
  type coq_DebugCall = { debug_call_function_parameters : (coq_PVar,
                                                          Coq_ty.coq_Ty)
                                                          Binding.coq_Binding
                                                          Coq_ctx.coq_Ctx;
                         debug_call_function_result_type : Coq_ty.coq_Ty;
                         debug_call_function_name : RiscvPmpProgram.coq_Fun;
                         debug_call_function_contract : RiscvPmpSignature.coq_SepContract
                                                        option;
                         debug_call_function_arguments : RiscvPmpBase.coq_SStore;
                         debug_call_pathcondition : RiscvPmpSignature.coq_PathCondition;
                         debug_call_heap : RiscvPmpSignature.coq_SHeap }

  val debug_call_function_parameters :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val debug_call_function_result_type :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> Coq_ty.coq_Ty

  val debug_call_function_name :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpProgram.coq_Fun

  val debug_call_function_contract :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpSignature.coq_SepContract option

  val debug_call_function_arguments :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpBase.coq_SStore

  val debug_call_pathcondition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpSignature.coq_PathCondition

  val debug_call_heap :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpSignature.coq_SHeap

  type coq_EDebugCall = { edebug_call_function_parameters : (coq_PVar,
                                                            Coq_ty.coq_Ty)
                                                            Binding.coq_Binding
                                                            Coq_ctx.coq_Ctx;
                          edebug_call_function_result_type : Coq_ty.coq_Ty;
                          edebug_call_function_name : RiscvPmpProgram.coq_Fun;
                          edebug_call_function_contract : RiscvPmpSignature.coq_SepContract
                                                          option;
                          edebug_call_function_arguments : (coq_PVar,
                                                           Coq_ty.coq_Ty,
                                                           RiscvPmpBase.coq_ETerm)
                                                           coq_NamedEnv;
                          edebug_call_pathcondition : RiscvPmpSignature.coq_EFormula
                                                      list;
                          edebug_call_heap : RiscvPmpSignature.coq_EChunk list }

  val edebug_call_function_parameters :
    coq_EDebugCall -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val edebug_call_function_result_type : coq_EDebugCall -> Coq_ty.coq_Ty

  val edebug_call_function_name : coq_EDebugCall -> RiscvPmpProgram.coq_Fun

  val edebug_call_function_contract :
    coq_EDebugCall -> RiscvPmpSignature.coq_SepContract option

  val edebug_call_function_arguments :
    coq_EDebugCall -> (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
    coq_NamedEnv

  val edebug_call_pathcondition :
    coq_EDebugCall -> RiscvPmpSignature.coq_EFormula list

  val edebug_call_heap : coq_EDebugCall -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseDebugCall :
    (coq_DebugCall, coq_EDebugCall) RiscvPmpBase.coq_Erase

  type coq_DebugCallLemma = { debug_call_lemma_parameters : (coq_PVar,
                                                            Coq_ty.coq_Ty)
                                                            Binding.coq_Binding
                                                            Coq_ctx.coq_Ctx;
                              debug_call_lemma_name : RiscvPmpProgram.coq_Lem;
                              debug_call_lemma_contract : RiscvPmpSignature.coq_Lemma;
                              debug_call_lemma_arguments : RiscvPmpBase.coq_SStore;
                              debug_call_lemma_pathcondition : RiscvPmpSignature.coq_PathCondition;
                              debug_call_lemma_heap : RiscvPmpSignature.coq_SHeap }

  val debug_call_lemma_parameters :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val debug_call_lemma_name :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpProgram.coq_Lem

  val debug_call_lemma_contract :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpSignature.coq_Lemma

  val debug_call_lemma_arguments :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpBase.coq_SStore

  val debug_call_lemma_pathcondition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpSignature.coq_PathCondition

  val debug_call_lemma_heap :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpSignature.coq_SHeap

  type coq_EDebugCallLemma = { edebug_call_lemma_parameters : (coq_PVar,
                                                              Coq_ty.coq_Ty)
                                                              Binding.coq_Binding
                                                              Coq_ctx.coq_Ctx;
                               edebug_call_lemma_name : RiscvPmpProgram.coq_Lem;
                               edebug_call_lemma_contract : RiscvPmpSignature.coq_Lemma;
                               edebug_call_lemma_arguments : (coq_PVar,
                                                             Coq_ty.coq_Ty,
                                                             RiscvPmpBase.coq_ETerm)
                                                             coq_NamedEnv;
                               edebug_call_lemma_pathcondition : RiscvPmpSignature.coq_EFormula
                                                                 list;
                               edebug_call_lemma_heap : RiscvPmpSignature.coq_EChunk
                                                        list }

  val edebug_call_lemma_parameters :
    coq_EDebugCallLemma -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val edebug_call_lemma_name : coq_EDebugCallLemma -> RiscvPmpProgram.coq_Lem

  val edebug_call_lemma_contract :
    coq_EDebugCallLemma -> RiscvPmpSignature.coq_Lemma

  val edebug_call_lemma_arguments :
    coq_EDebugCallLemma -> (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
    coq_NamedEnv

  val edebug_call_lemma_pathcondition :
    coq_EDebugCallLemma -> RiscvPmpSignature.coq_EFormula list

  val edebug_call_lemma_heap :
    coq_EDebugCallLemma -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseDebugCallLemma :
    (coq_DebugCallLemma, coq_EDebugCallLemma) RiscvPmpBase.coq_Erase

  val coq_SubstDebugCallLemma : coq_DebugCallLemma RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugCallLemma :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugCallLemma)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugCallLemma :
    coq_DebugCallLemma RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugCallLemma :
    coq_DebugCallLemma RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckDebugCallLemma :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugCallLemma)
    RiscvPmpBase.coq_GenOccursCheck

  val coq_SubstDebugCall : coq_DebugCall RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugCall :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugCall)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugCall : coq_DebugCall RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugCall : coq_DebugCall RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckDebugCall :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugCall)
    RiscvPmpBase.coq_GenOccursCheck

  type coq_DebugStm = { debug_stm_program_context : (coq_PVar, Coq_ty.coq_Ty)
                                                    Binding.coq_Binding
                                                    Coq_ctx.coq_Ctx;
                        debug_stm_statement_type : Coq_ty.coq_Ty;
                        debug_stm_statement : RiscvPmpProgram.coq_Stm;
                        debug_stm_pathcondition : RiscvPmpSignature.coq_PathCondition;
                        debug_stm_localstore : RiscvPmpBase.coq_SStore;
                        debug_stm_heap : RiscvPmpSignature.coq_SHeap }

  val debug_stm_program_context :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugStm -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val debug_stm_statement_type :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugStm -> Coq_ty.coq_Ty

  val debug_stm_statement :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugStm -> RiscvPmpProgram.coq_Stm

  val debug_stm_pathcondition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugStm -> RiscvPmpSignature.coq_PathCondition

  val debug_stm_localstore :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugStm -> RiscvPmpBase.coq_SStore

  val debug_stm_heap :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugStm -> RiscvPmpSignature.coq_SHeap

  type coq_EDebugStm = { edebug_stm_program_context : (coq_PVar,
                                                      Coq_ty.coq_Ty)
                                                      Binding.coq_Binding
                                                      Coq_ctx.coq_Ctx;
                         edebug_stm_statement_type : Coq_ty.coq_Ty;
                         edebug_stm_statement : RiscvPmpProgram.coq_Stm;
                         edebug_stm_pathcondition : RiscvPmpSignature.coq_EFormula
                                                    list;
                         edebug_stm_localstore : (coq_PVar, Coq_ty.coq_Ty,
                                                 RiscvPmpBase.coq_ETerm)
                                                 coq_NamedEnv;
                         edebug_stm_heap : RiscvPmpSignature.coq_EChunk list }

  val edebug_stm_program_context :
    coq_EDebugStm -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val edebug_stm_statement_type : coq_EDebugStm -> Coq_ty.coq_Ty

  val edebug_stm_statement : coq_EDebugStm -> RiscvPmpProgram.coq_Stm

  val edebug_stm_pathcondition :
    coq_EDebugStm -> RiscvPmpSignature.coq_EFormula list

  val edebug_stm_localstore :
    coq_EDebugStm -> (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
    coq_NamedEnv

  val edebug_stm_heap : coq_EDebugStm -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseDebugStm : (coq_DebugStm, coq_EDebugStm) RiscvPmpBase.coq_Erase

  val coq_SubstDebugStm : coq_DebugStm RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugStm :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugStm)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugStm : coq_DebugStm RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugStm : coq_DebugStm RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckDebugStm :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugStm) RiscvPmpBase.coq_GenOccursCheck

  type coq_ErrorNoFuel = { error_no_fuel_call_parameter_types : (coq_PVar,
                                                                Coq_ty.coq_Ty)
                                                                Binding.coq_Binding
                                                                Coq_ctx.coq_Ctx;
                           error_no_fuel_call_return_type : Coq_ty.coq_Ty;
                           error_no_fuel_call_function : RiscvPmpProgram.coq_Fun;
                           error_no_fuel_call_arguments : RiscvPmpBase.coq_SStore;
                           error_no_fuel_pathcondition : RiscvPmpSignature.coq_PathCondition;
                           error_no_fuel_heap : RiscvPmpSignature.coq_SHeap }

  val error_no_fuel_call_parameter_types :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val error_no_fuel_call_return_type :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> Coq_ty.coq_Ty

  val error_no_fuel_call_function :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpProgram.coq_Fun

  val error_no_fuel_call_arguments :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpBase.coq_SStore

  val error_no_fuel_pathcondition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpSignature.coq_PathCondition

  val error_no_fuel_heap :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpSignature.coq_SHeap

  type coq_EErrorNoFuel = { eerror_no_fuel_call_parameter_types : (coq_PVar,
                                                                  Coq_ty.coq_Ty)
                                                                  Binding.coq_Binding
                                                                  Coq_ctx.coq_Ctx;
                            eerror_no_fuel_call_return_type : Coq_ty.coq_Ty;
                            eerror_no_fuel_call_function : RiscvPmpProgram.coq_Fun;
                            eerror_no_fuel_call_arguments : (coq_PVar,
                                                            Coq_ty.coq_Ty,
                                                            RiscvPmpBase.coq_ETerm)
                                                            coq_NamedEnv;
                            eerror_no_fuel_pathcondition : RiscvPmpSignature.coq_EFormula
                                                           list;
                            eerror_no_fuel_heap : RiscvPmpSignature.coq_EChunk
                                                  list }

  val eerror_no_fuel_call_parameter_types :
    coq_EErrorNoFuel -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val eerror_no_fuel_call_return_type : coq_EErrorNoFuel -> Coq_ty.coq_Ty

  val eerror_no_fuel_call_function :
    coq_EErrorNoFuel -> RiscvPmpProgram.coq_Fun

  val eerror_no_fuel_call_arguments :
    coq_EErrorNoFuel -> (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
    coq_NamedEnv

  val eerror_no_fuel_pathcondition :
    coq_EErrorNoFuel -> RiscvPmpSignature.coq_EFormula list

  val eerror_no_fuel_heap :
    coq_EErrorNoFuel -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseErrorNoFuel :
    (coq_ErrorNoFuel, coq_EErrorNoFuel) RiscvPmpBase.coq_Erase

  val coq_SubstErrorNoFuel : coq_ErrorNoFuel RiscvPmpBase.coq_Subst

  val coq_SubstSUErrorNoFuel :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_ErrorNoFuel)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsErrorNoFuel : coq_ErrorNoFuel RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckErrorNoFuel :
    coq_ErrorNoFuel RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckErrorNoFuel :
    (RiscvPmpBase.coq_WeakensTo, coq_ErrorNoFuel)
    RiscvPmpBase.coq_GenOccursCheck

  val coq_VerificationCondition_rect :
    RiscvPmpSignature.SymProp.coq_SymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationCondition_rec :
    RiscvPmpSignature.SymProp.coq_SymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationConditionWithErasure_rect :
    RiscvPmpSignature.Erasure.coq_ESymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationConditionWithErasure_rec :
    RiscvPmpSignature.Erasure.coq_ESymProp -> (__ -> 'a1) -> 'a1

  type coq_Config = { config_debug_function : ((coq_PVar, Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_Ctx ->
                                              Coq_ty.coq_Ty ->
                                              RiscvPmpProgram.coq_Fun -> bool);
                      config_debug_lemma : ((coq_PVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding
                                           Coq_ctx.coq_Ctx ->
                                           RiscvPmpProgram.coq_Lem -> bool) }

  val config_debug_function :
    coq_Config -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun -> bool

  val config_debug_lemma :
    coq_Config -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> RiscvPmpProgram.coq_Lem -> bool

  val default_config : coq_Config

  type 'a coq_SStoreSpec =
    (('a, (RiscvPmpBase.coq_SStore, (RiscvPmpSignature.coq_SHeap,
    RiscvPmpSignature.SymProp.coq_SymProp) RiscvPmpSignature.coq_Impl)
    RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
    RiscvPmpSignature.coq_Box, (RiscvPmpBase.coq_SStore,
    (RiscvPmpSignature.coq_SHeap, RiscvPmpSignature.SymProp.coq_SymProp)
    RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl)
    RiscvPmpSignature.coq_Impl

  type coq_ExecCall =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Term RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  type coq_ExecCallForeign =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_FunX -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Term RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  type coq_ExecLemma =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpProgram.coq_Lem -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Unit RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  type coq_ExecFail =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> RiscvPmpBase.coq_Term coq_SStoreSpec
    RiscvPmpSignature.coq_Valid

  type coq_Exec =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Stm -> RiscvPmpBase.coq_Term
    coq_SStoreSpec RiscvPmpSignature.coq_Valid

  module SStoreSpec :
   sig
    val evalStoreSpec :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, (RiscvPmpBase.coq_SStore, 'a1
      RiscvPmpSignature.coq_SHeapSpec) RiscvPmpSignature.coq_Impl)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val lift_purespec :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      RiscvPmpSignature.coq_SPureSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val lift_heapspec :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      RiscvPmpSignature.coq_SHeapSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val pure :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
      'a1 coq_SStoreSpec) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val bind :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, (('a1, 'a2 coq_SStoreSpec) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Box, 'a2 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val error :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((RiscvPmpBase.coq_SStore, (RiscvPmpSignature.coq_SHeap,
      RiscvPmpBase.Coq_amsg.coq_AMessage) RiscvPmpSignature.coq_Impl)
      RiscvPmpSignature.coq_Impl, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val block :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
      coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val angelic_binary :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val demonic_binary :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val angelic :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_LVar option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term
      coq_SStoreSpec) RiscvPmpSignature.coq_Forall RiscvPmpSignature.coq_Valid

    val demonic :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_LVar option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term
      coq_SStoreSpec) RiscvPmpSignature.coq_Forall RiscvPmpSignature.coq_Valid

    val debug :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((RiscvPmpBase.coq_SStore, (RiscvPmpSignature.coq_SHeap,
      RiscvPmpBase.Coq_amsg.coq_AMessage) RiscvPmpSignature.coq_Impl)
      RiscvPmpSignature.coq_Impl, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val angelic_ctx :
      ('a1 -> coq_LVar) -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
      coq_NamedEnv coq_SStoreSpec) RiscvPmpSignature.coq_Forall
      RiscvPmpSignature.coq_Valid

    val demonic_ctx :
      ('a1 -> coq_LVar) -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term)
      coq_NamedEnv coq_SStoreSpec) RiscvPmpSignature.coq_Forall
      RiscvPmpSignature.coq_Valid

    module Coq_notations :
     sig
     end

    val demonic_pattern_match :
      ('a1 -> coq_LVar) -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
      (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
      coq_SStoreSpec) RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val pushpop :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PVar -> Coq_ty.coq_Ty -> (RiscvPmpBase.coq_Term, ('a1
      coq_SStoreSpec, 'a1 coq_SStoreSpec) RiscvPmpSignature.coq_Impl)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val pushspops :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (RiscvPmpBase.coq_SStore, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val get_local :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_SStore coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val put_local :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (RiscvPmpBase.coq_SStore, RiscvPmpBase.coq_Unit coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val eval_exp :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Exp -> RiscvPmpBase.coq_Term
      coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val eval_exps :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) coq_NamedEnv ->
      RiscvPmpBase.coq_SStore coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val assign :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PVar -> Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> (RiscvPmpBase.coq_Term,
      RiscvPmpBase.coq_Unit coq_SStoreSpec) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val exec_aux :
      coq_ExecCallForeign -> coq_ExecLemma -> coq_ExecCall -> coq_ExecFail ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Stm -> RiscvPmpBase.coq_Term
      coq_SStoreSpec RiscvPmpSignature.coq_Valid
   end

  val exec_contract :
    coq_Exec -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
    RiscvPmpProgram.coq_Stm -> RiscvPmpBase.coq_Unit
    RiscvPmpSignature.coq_SHeapSpec RiscvPmpSignature.coq_Valid

  val exec_call_error_no_fuel : coq_ExecCall

  val sexec_call_foreign : coq_ExecCallForeign

  val debug_lemma :
    coq_Config -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> RiscvPmpProgram.coq_Lem -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Unit RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  val sexec_lemma : coq_Config -> coq_ExecLemma

  val debug_call :
    coq_Config -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun ->
    (RiscvPmpBase.coq_SStore, RiscvPmpBase.coq_Unit
    RiscvPmpSignature.coq_SHeapSpec) RiscvPmpSignature.coq_Impl
    RiscvPmpSignature.coq_Valid

  val sexec_fail : coq_ExecFail

  val sexec_call : coq_Config -> nat -> coq_ExecCall

  val sexec : coq_Config -> nat -> coq_Exec

  val vcgen :
    coq_Config -> nat -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
    RiscvPmpProgram.coq_Stm -> RiscvPmpSignature.SymProp.coq_SymProp
    RiscvPmpSignature.coq_Valid

  module Symbolic :
   sig
    val verification_failed_with_error :
      RiscvPmpBase.Coq_amsg.coq_EAMessage -> bool

    val ok' :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.SymProp.coq_SymProp -> bool

    val ok :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.SymProp.coq_SymProp -> bool

    val coq_VcGenErasureFuel :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> nat -> RiscvPmpSignature.coq_SepContract ->
      RiscvPmpProgram.coq_Stm -> RiscvPmpSignature.Erasure.coq_ESymProp

    val coq_VcGenErasure :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
      RiscvPmpProgram.coq_Stm -> RiscvPmpSignature.Erasure.coq_ESymProp

    module Statistics :
     sig
      val extend_postcond_with_debug :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
        RiscvPmpSignature.coq_SepContract

      val calc :
        (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun -> coq_Stats option
     end
   end
 end
