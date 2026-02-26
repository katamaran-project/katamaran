open Ascii
open Base1
open BinInt
open BinNat
open BinNums
open BinOps
open Bitvector
open Classes
open Context
open Datatypes
open Environment
open List
open Nat
open Prelude
open Signature
open Specif
open String
open TypeDecl
open UnOps
open Variables

type __ = Obj.t

module RiscvPmpProgram :
 sig
  val width_constraint : nat -> bool

  type coq_Fun =
  | Coq_rX
  | Coq_wX
  | Coq_bool_to_bits
  | Coq_shift_right_arith32
  | Coq_extend_value of nat
  | Coq_get_arch_pc
  | Coq_get_next_pc
  | Coq_set_next_pc
  | Coq_tick_pc
  | Coq_to_bits of nat
  | Coq_within_phys_mem
  | Coq_mem_read of nat
  | Coq_checked_mem_read of nat
  | Coq_checked_mem_write of nat
  | Coq_pmp_mem_read of nat
  | Coq_pmp_mem_write of nat
  | Coq_pmpLocked
  | Coq_pmpWriteCfgReg
  | Coq_pmpWriteCfg
  | Coq_pmpWriteAddr
  | Coq_pmpCheck of nat
  | Coq_pmpCheckPerms
  | Coq_pmpCheckRWX
  | Coq_pmpMatchEntry
  | Coq_pmpAddrRange
  | Coq_pmpMatchAddr
  | Coq_process_load of nat
  | Coq_mem_write_value of nat
  | Coq_main
  | Coq_init_model
  | Coq_loop
  | Coq_step
  | Coq_fetch
  | Coq_init_sys
  | Coq_init_pmp
  | Coq_exceptionType_to_bits
  | Coq_interruptType_to_bits
  | Minterrupts_to_bits
  | Minterrupts_from_bits
  | Coq_privLevel_to_bits
  | Coq_handle_mem_exception
  | Coq_exception_handler
  | Coq_exception_delegatee
  | Coq_trap_handler
  | Coq_prepare_trap_vector
  | Coq_tvec_addr
  | Coq_handle_illegal
  | Coq_check_CSR
  | Coq_is_CSR_defined
  | Coq_csrAccess
  | Coq_csrPriv
  | Coq_check_CSR_access
  | Coq_readCSR
  | Coq_writeCSR
  | Coq_dispatchInterrupt
  | Coq_handle_interrupt
  | Coq_and_Minterrupts
  | Coq_processPending
  | Coq_getPendingSet
  | Coq_findPendingInterrupt
  | Coq_execute
  | Coq_execute_RTYPE
  | Coq_execute_ITYPE
  | Coq_execute_SHIFTIOP
  | Coq_execute_UTYPE
  | Coq_execute_BTYPE
  | Coq_execute_RISCV_JAL
  | Coq_execute_RISCV_JALR
  | Coq_execute_LOAD
  | Coq_execute_STORE
  | Coq_execute_ECALL
  | Coq_execute_EBREAK
  | Coq_execute_MRET
  | Coq_execute_CSR
  | Coq_execute_MUL

  val coq_Fun_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> (nat -> 'a1) -> 'a1 -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) ->
    (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_Fun -> 'a1

  val coq_Fun_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> (nat -> 'a1) -> 'a1 -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) ->
    (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_Fun -> 'a1

  type coq_FunX =
  | Coq_read_ram of nat
  | Coq_write_ram of nat
  | Coq_mmio_read of nat
  | Coq_mmio_write of nat
  | Coq_within_mmio of nat
  | Coq_decode
  | Coq_externalWorldUpdates

  val coq_FunX_rect :
    (nat -> 'a1) -> (nat -> 'a1) -> (nat -> 'a1) -> (nat -> __ -> 'a1) ->
    (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_FunX -> 'a1

  val coq_FunX_rec :
    (nat -> 'a1) -> (nat -> 'a1) -> (nat -> 'a1) -> (nat -> __ -> 'a1) ->
    (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_FunX -> 'a1

  type coq_Lem =
  | Coq_open_gprs
  | Coq_close_gprs
  | Coq_open_pmp_entries
  | Coq_close_pmp_entries
  | Coq_extract_pmp_ptsto of nat
  | Coq_return_pmp_ptsto of nat
  | Coq_open_ptsto_instr
  | Coq_close_ptsto_instr
  | Coq_close_mmio_write of Coq_bv.bv * coq_WordWidth

  val coq_Lem_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (nat -> 'a1) -> (nat -> 'a1) -> 'a1 -> 'a1 ->
    (Coq_bv.bv -> coq_WordWidth -> 'a1) -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lem -> 'a1

  val coq_Lem_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (nat -> 'a1) -> (nat -> 'a1) -> 'a1 -> 'a1 ->
    (Coq_bv.bv -> coq_WordWidth -> 'a1) -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lem -> 'a1

  type _UU1d46d_ = coq_Fun

  type _UU1d46d__UU1d47f_ = coq_FunX

  type _UU1d473_ = coq_Lem

  type coq_Stm =
  | Coq_stm_val of Coq_ty.coq_Val
  | Coq_stm_exp of RiscvPmpBase.coq_Exp
  | Coq_stm_let of coq_PVar * Coq_ty.coq_Ty * coq_Stm * coq_Stm
  | Coq_stm_block of (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
                     Coq_ctx.coq_Ctx
     * (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv * coq_Stm
  | Coq_stm_assign of coq_PVar
     * (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * 
     coq_Stm
  | Coq_stm_call of (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
                    Coq_ctx.coq_Ctx
     * coq_Fun * (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) coq_NamedEnv
  | Coq_stm_call_frame of (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv * coq_Stm
  | Coq_stm_foreign of (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
                       Coq_ctx.coq_Ctx
     * coq_FunX * (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) coq_NamedEnv
  | Coq_stm_lemmak of (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
                      Coq_ctx.coq_Ctx
     * coq_Lem * (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) coq_NamedEnv
     * coq_Stm
  | Coq_stm_seq of Coq_ty.coq_Ty * coq_Stm * coq_Stm
  | Coq_stm_assertk of RiscvPmpBase.coq_Exp * RiscvPmpBase.coq_Exp * coq_Stm
  | Coq_stm_fail of Coq_ty.coq_Val
  | Coq_stm_pattern_match of Coq_ty.coq_Ty * coq_Stm
     * coq_PVar RiscvPmpBase.coq_Pattern
     * (coq_PVar RiscvPmpBase.coq_PatternCase -> coq_Stm)
  | Coq_stm_read_register of RiscvPmpBase.coq_Reg
  | Coq_stm_write_register of RiscvPmpBase.coq_Reg * RiscvPmpBase.coq_Exp
  | Coq_stm_bind of Coq_ty.coq_Ty * coq_Stm * (Coq_ty.coq_Val -> coq_Stm)
  | Coq_stm_debugk of coq_Stm

  val coq_Stm_rect :
    ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Exp -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_PVar ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm -> 'a1 -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv -> coq_Stm -> 'a1
    -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> coq_PVar -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_Stm -> 'a1 -> 'a1) ->
    ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Fun -> (coq_PVar, Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Exp) coq_NamedEnv -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_PVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv -> coq_Stm -> 'a1 -> 'a1) ->
    ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_FunX -> (coq_PVar, Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Exp) coq_NamedEnv -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lem ->
    (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) coq_NamedEnv -> coq_Stm
    -> 'a1 -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 ->
    coq_Stm -> 'a1 -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Exp ->
    RiscvPmpBase.coq_Exp -> coq_Stm -> 'a1 -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Val -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 ->
    coq_PVar RiscvPmpBase.coq_Pattern -> (coq_PVar
    RiscvPmpBase.coq_PatternCase -> coq_Stm) -> (coq_PVar
    RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Reg -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Reg -> RiscvPmpBase.coq_Exp -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> (Coq_ty.coq_Val -> coq_Stm) ->
    (Coq_ty.coq_Val -> 'a1) -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 ->
    'a1) -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1

  val coq_Stm_rec :
    ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Exp -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_PVar ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm -> 'a1 -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv -> coq_Stm -> 'a1
    -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> coq_PVar -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_Stm -> 'a1 -> 'a1) ->
    ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Fun -> (coq_PVar, Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Exp) coq_NamedEnv -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_PVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv -> coq_Stm -> 'a1 -> 'a1) ->
    ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_FunX -> (coq_PVar, Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Exp) coq_NamedEnv -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lem ->
    (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) coq_NamedEnv -> coq_Stm
    -> 'a1 -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 ->
    coq_Stm -> 'a1 -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Exp ->
    RiscvPmpBase.coq_Exp -> coq_Stm -> 'a1 -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Val -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 ->
    coq_PVar RiscvPmpBase.coq_Pattern -> (coq_PVar
    RiscvPmpBase.coq_PatternCase -> coq_Stm) -> (coq_PVar
    RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((coq_PVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Reg -> 'a1) -> ((coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Reg -> RiscvPmpBase.coq_Exp -> 'a1) -> ((coq_PVar,
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
    RiscvPmpBase.coq_Exp -> RiscvPmpBase.coq_Exp -> coq_Stm

  val stm_lemma :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lem
    -> (coq_PVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) coq_NamedEnv -> coq_Stm

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
    RiscvPmpBase.coq_TuplePat -> coq_Stm -> coq_Stm

  val stm_match_record :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.recordi -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm -> coq_PVar
    RiscvPmpBase.coq_RecordPat -> coq_Stm -> coq_Stm

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
    coq_Stm) RiscvPmpBase.coq_Alternative) -> coq_Stm

  type coq_UnionAlt = (coq_PVar, coq_Stm) RiscvPmpBase.coq_Alternative

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
    -> Coq_ty.coq_Ty coq_IsSome -> RiscvPmpBase.coq_Exp

  val stm_smart_assign :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_PVar
    -> Coq_ty.coq_Ty coq_IsSome -> coq_Stm -> coq_Stm

  module Riscv_UU03bc_SailNotations :
   sig
   end

  val zero_reg :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm

  val stm_mstatus_from_bits :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm
    -> coq_Stm

  val stm_mstatus_to_bits :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm
    -> coq_Stm

  val fun_Minterrupts_to_bits : coq_Stm

  val exp_testbit :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    RiscvPmpBase.coq_Exp -> coq_N -> RiscvPmpBase.coq_Exp

  val stm_pmpcfg_ent_from_bits :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm
    -> coq_Stm

  val fun_Minterrupts_from_bits : coq_Stm

  val stm_pmpcfg_ent_to_bits :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm
    -> coq_Stm

  val fun_rX : coq_Stm

  val fun_wX : coq_Stm

  val fun_bool_to_bits : coq_Stm

  val fun_shift_right_arith32 : coq_Stm

  val fun_extend_value : nat -> coq_Stm

  val fun_get_arch_pc : coq_Stm

  val fun_get_next_pc : coq_Stm

  val fun_set_next_pc : coq_Stm

  val fun_tick_pc : coq_Stm

  val fun_to_bits : nat -> coq_Stm

  val fun_abs : coq_Stm

  val fun_within_phys_mem : coq_Stm

  val fun_mem_read : nat -> coq_Stm

  val fun_checked_mem_read : nat -> coq_Stm

  val fun_checked_mem_write : nat -> coq_Stm

  val fun_pmp_mem_read : nat -> coq_Stm

  val fun_pmp_mem_write : nat -> coq_Stm

  val fun_pmpLocked : coq_Stm

  val fun_pmpWriteCfgReg : coq_Stm

  val fun_pmpWriteCfg : coq_Stm

  val fun_pmpWriteAddr : coq_Stm

  val fun_pmpCheck : nat -> coq_Stm

  val fun_pmpCheckPerms : coq_Stm

  val fun_pmpCheckRWX : coq_Stm

  val fun_pmpMatchEntry : coq_Stm

  val fun_pmpAddrRange : coq_Stm

  val fun_pmpMatchAddr : coq_Stm

  val fun_process_load : nat -> coq_Stm

  val fun_mem_write_value : nat -> coq_Stm

  val fun_main : coq_Stm

  val fun_init_model : coq_Stm

  val fun_loop : coq_Stm

  val fun_fetch : coq_Stm

  val fun_step : coq_Stm

  val fun_init_sys : coq_Stm

  val fun_init_pmp : coq_Stm

  val fun_exceptionType_to_bits : coq_Stm

  val fun_interruptType_to_bits : coq_Stm

  val fun_handle_mem_exception : coq_Stm

  val fun_exception_handler : coq_Stm

  val fun_exception_delegatee : coq_Stm

  val fun_trap_handler : coq_Stm

  val fun_prepare_trap_vector : coq_Stm

  val fun_tvec_addr : coq_Stm

  val fun_handle_illegal : coq_Stm

  val fun_check_CSR : coq_Stm

  val fun_is_CSR_defined : coq_Stm

  val fun_csrAccess : coq_Stm

  val fun_csrPriv : coq_Stm

  val fun_check_CSR_access : coq_Stm

  val fun_privLevel_to_bits : coq_Stm

  val fun_readCSR : coq_Stm

  val fun_writeCSR : coq_Stm

  val fun_and_Minterrupts : coq_Stm

  val coq_Minterrupts_zero : coq_Minterrupts

  val fun_processPending : coq_Stm

  val fun_findPendingInterrupt : coq_Stm

  val fun_getPendingSet : coq_Stm

  val fun_dispatchInterrupt : coq_Stm

  val fun_handle_interrupt : coq_Stm

  val fun_execute : coq_Stm

  val fun_execute_MUL : coq_Stm

  val fun_execute_RTYPE : coq_Stm

  val fun_execute_ITYPE : coq_Stm

  val fun_execute_SHIFTIOP : coq_Stm

  val fun_execute_UTYPE : coq_Stm

  val fun_execute_RISCV_JAL : coq_Stm

  val fun_execute_RISCV_JALR : coq_Stm

  val fun_execute_BTYPE : coq_Stm

  val fun_execute_LOAD : coq_Stm

  val fun_execute_STORE : coq_Stm

  val fun_execute_ECALL : coq_Stm

  val fun_execute_EBREAK : coq_Stm

  val fun_execute_MRET : coq_Stm

  val fun_execute_CSR : coq_Stm

  type coq_RegStore = Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> Coq_ty.coq_Val

  val write_register :
    coq_RegStore -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> Coq_ty.coq_Val
    -> coq_RegStore

  val read_register :
    coq_RegStore -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> Coq_ty.coq_Val

  val coq_FunDef :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Fun -> coq_Stm

  module Coq_callgraph :
   sig
    type coq_Node = { _UU0394_ : (coq_PVar, Coq_ty.coq_Ty)
                                 Binding.coq_Binding Coq_ctx.coq_Ctx;
                      _UU03c4_ : Coq_ty.coq_Ty; f : coq_Fun }

    val _UU0394_ :
      coq_Node -> (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx

    val _UU03c4_ : coq_Node -> Coq_ty.coq_Ty

    val f : coq_Node -> coq_Fun

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

  module WithAccessibleTactics :
   sig
   end

  val _UU1d46d__accessible :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> _UU1d46d_ -> __ option
 end
