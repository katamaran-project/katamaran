open Ascii
open Basics
open BinInt
open BinNat
open BinNums
open BinOps
open BinPos
open Bitvector
open Classes
open Context
open Datatypes
open Environment
open EqDec
open EqDecInstances
open EqdepFacts
open InitialRing
open ListDef
open Nat
open PartialEvaluation
open Prelude
open Ring_polynom
open Ring_theory
open Signature
open Specif
open String
open TypeDecl
open UnOps
open Variables
open Vector
open Base
open Decidable
open Finite
open List0
open Numbers
open Ssrbool

type __ = Obj.t

val xlen : nat

val byte : nat

val bytes_per_word : nat

val bytes_per_instr : nat

val word : nat

val xlenbytes : nat

val xlenbits : nat

val bv_instrsize : nat -> Coq_bv.bv

type coq_Xlenbits = Coq_bv.bv

type coq_Addr = Coq_bv.bv

type coq_Word = Coq_bv.bv

type coq_Byte = Coq_bv.bv

val minAddr : coq_N

val lenAddr : coq_N

val maxAddr : coq_N

val mmioStartAddr : coq_N

val mmioLenAddr : coq_N

val mmioAddrs : coq_Addr list

val withinMMIODec : coq_Addr -> nat -> coq_Decision

type coq_Minterrupts = { coq_MEI : bool; coq_UEI : bool; coq_MTI : bool;
                         coq_UTI : bool; coq_MSI : bool; coq_USI : bool }

type coq_State = __

type coq_Privilege =
| User
| Machine

type coq_InterruptType =
| I_U_Software
| I_M_Software
| I_U_Timer
| I_M_Timer
| I_U_External
| I_M_External

type coq_CSRIdx =
| MStatus
| Mie
| MTvec
| MScratch
| MEpc
| MCause
| MPMP0CFG
| Mip
| MPMPADDR0
| MPMPADDR1

type coq_PmpCfgIdx =
| PMP0CFG
| PMP1CFG

type coq_PmpCfgPerm =
| PmpO
| PmpR
| PmpW
| PmpX
| PmpRW
| PmpRX
| PmpWX
| PmpRWX

type coq_PmpAddrIdx =
| PMPADDR0
| PMPADDR1

type coq_PmpAddrMatchType =
| OFF
| TOR

type coq_PmpMatch =
| PMP_Success
| PMP_Continue
| PMP_Fail

type coq_PmpAddrMatch =
| PMP_NoMatch
| PMP_PartialMatch
| PMP_Match

type coq_ROP =
| RISCV_ADD
| RISCV_SLT
| RISCV_SLTU
| RISCV_AND
| RISCV_OR
| RISCV_XOR
| RISCV_SLL
| RISCV_SRL
| RISCV_SUB
| RISCV_SRA

type coq_IOP =
| RISCV_ADDI
| RISCV_SLTI
| RISCV_SLTIU
| RISCV_ANDI
| RISCV_ORI
| RISCV_XORI

type coq_SOP =
| RISCV_SLLI
| RISCV_SRLI
| RISCV_SRAI

type coq_UOP =
| RISCV_LUI
| RISCV_AUIPC

type coq_BOP =
| RISCV_BEQ
| RISCV_BNE
| RISCV_BLT
| RISCV_BGE
| RISCV_BLTU
| RISCV_BGEU

type coq_CSROP =
| CSRRW
| CSRRS
| CSRRC

type coq_MOP =
| RISCV_MUL
| RISCV_MULH
| RISCV_MULHSU
| RISCV_MULHU

type coq_Retired =
| RETIRE_SUCCESS
| RETIRE_FAIL

type coq_WordWidth =
| BYTE
| HALF
| WORD

type coq_Enums =
| Coq_privilege
| Coq_interruptType
| Coq_csridx
| Coq_pmpcfgidx
| Coq_pmpcfgperm
| Coq_pmpaddridx
| Coq_pmpaddrmatchtype
| Coq_pmpmatch
| Coq_pmpaddrmatch
| Coq_rop
| Coq_iop
| Coq_sop
| Coq_uop
| Coq_bop
| Coq_csrop
| Coq_retired
| Coq_wordwidth
| Coq_mop

type coq_RegIdx = Coq_bv.bv

type coq_AST =
| RTYPE of coq_RegIdx * coq_RegIdx * coq_RegIdx * coq_ROP
| ITYPE of Coq_bv.bv * coq_RegIdx * coq_RegIdx * coq_IOP
| SHIFTIOP of Coq_bv.bv * coq_RegIdx * coq_RegIdx * coq_SOP
| UTYPE of Coq_bv.bv * coq_RegIdx * coq_UOP
| BTYPE of Coq_bv.bv * coq_RegIdx * coq_RegIdx * coq_BOP
| RISCV_JAL of Coq_bv.bv * coq_RegIdx
| RISCV_JALR of Coq_bv.bv * coq_RegIdx * coq_RegIdx
| LOAD of Coq_bv.bv * coq_RegIdx * coq_RegIdx * bool * coq_WordWidth
| STORE of Coq_bv.bv * coq_RegIdx * coq_RegIdx * coq_WordWidth
| ECALL
| EBREAK
| MRET
| CSR of coq_CSRIdx * coq_RegIdx * coq_RegIdx * bool * coq_CSROP
| MUL of coq_RegIdx * coq_RegIdx * coq_RegIdx * bool * bool * bool

type coq_AccessType =
| Read
| Write
| ReadWrite
| Execute

type coq_ExceptionType =
| E_Fetch_Access_Fault
| E_Load_Access_Fault
| E_SAMO_Access_Fault
| E_U_EnvCall
| E_M_EnvCall
| E_Illegal_Instr

type coq_FetchResult =
| F_Base of coq_Word
| F_Error of coq_ExceptionType * coq_Xlenbits

type coq_CtlResult =
| CTL_TRAP of coq_ExceptionType
| CTL_MRET

type coq_InterruptSet =
| Ints_Pending of coq_Minterrupts
| Ints_Delegated of coq_Minterrupts
| Ints_Empty

type coq_MemoryOpResult =
| MemValue of Coq_bv.bv
| MemException of coq_ExceptionType

type coq_ASTConstructor =
| KRTYPE
| KITYPE
| KSHIFTIOP
| KUTYPE
| KBTYPE
| KRISCV_JAL
| KRISCV_JALR
| KLOAD
| KSTORE
| KECALL
| KEBREAK
| KMRET
| KCSR
| KMUL

type coq_AccessTypeConstructor =
| KRead
| KWrite
| KReadWrite
| KExecute

type coq_ExceptionTypeConstructor =
| KE_Fetch_Access_Fault
| KE_Load_Access_Fault
| KE_SAMO_Access_Fault
| KE_U_EnvCall
| KE_M_EnvCall
| KE_Illegal_Instr

type coq_MemoryOpResultConstructor =
| KMemValue
| KMemException

type coq_FetchResultConstructor =
| KF_Base
| KF_Error

type coq_CtlResultConstructor =
| KCTL_TRAP
| KCTL_MRET

type coq_InterruptSetConstructor =
| KInts_Pending
| KInts_Delegated
| KInts_Empty

type coq_Unions =
| Coq_ast
| Coq_access_type
| Coq_exception_type
| Coq_memory_op_result of nat
| Coq_fetch_result
| Coq_ctl_result
| Coq_interrupt_set

type coq_Pmpcfg_ent = { coq_L : bool; coq_A : coq_PmpAddrMatchType;
                        coq_X : bool; coq_W : bool; coq_R : bool }

type coq_Mstatus = { coq_MPP : coq_Privilege; coq_MPIE : bool; coq_MIE : bool }

type coq_Records =
| Coq_rpmpcfg_ent
| Coq_rmstatus
| Coq_rminterrupts

val coq_Enums_eqdec : coq_Enums -> coq_Enums -> coq_Enums dec_eq

val coq_Enums_EqDec : coq_Enums coq_EqDec

val coq_Privilege_eqdec :
  coq_Privilege -> coq_Privilege -> coq_Privilege dec_eq

val coq_Privilege_EqDec : coq_Privilege coq_EqDec

val coq_CSRIdx_eqdec : coq_CSRIdx -> coq_CSRIdx -> coq_CSRIdx dec_eq

val coq_CSRIdx_EqDec : coq_CSRIdx coq_EqDec

val coq_PmpCfgIdx_eqdec :
  coq_PmpCfgIdx -> coq_PmpCfgIdx -> coq_PmpCfgIdx dec_eq

val coq_PmpCfgIdx_EqDec : coq_PmpCfgIdx coq_EqDec

val coq_PmpCfgPerm_eqdec :
  coq_PmpCfgPerm -> coq_PmpCfgPerm -> coq_PmpCfgPerm dec_eq

val coq_PmpCfgPerm_EqDec : coq_PmpCfgPerm coq_EqDec

val coq_PmpAddrIdx_eqdec :
  coq_PmpAddrIdx -> coq_PmpAddrIdx -> coq_PmpAddrIdx dec_eq

val coq_PmpAddrIdx_EqDec : coq_PmpAddrIdx coq_EqDec

val coq_PmpAddrMatchType_eqdec :
  coq_PmpAddrMatchType -> coq_PmpAddrMatchType -> coq_PmpAddrMatchType dec_eq

val coq_PmpAddrMatchType_EqDec : coq_PmpAddrMatchType coq_EqDec

val coq_PmpMatch_eqdec : coq_PmpMatch -> coq_PmpMatch -> coq_PmpMatch dec_eq

val coq_PmpMatch_EqDec : coq_PmpMatch coq_EqDec

val coq_PmpAddrMatch_eqdec :
  coq_PmpAddrMatch -> coq_PmpAddrMatch -> coq_PmpAddrMatch dec_eq

val coq_PmpAddrMatch_EqDec : coq_PmpAddrMatch coq_EqDec

val coq_ROP_eqdec : coq_ROP -> coq_ROP -> coq_ROP dec_eq

val coq_ROP_EqDec : coq_ROP coq_EqDec

val coq_IOP_eqdec : coq_IOP -> coq_IOP -> coq_IOP dec_eq

val coq_IOP_EqDec : coq_IOP coq_EqDec

val coq_SOP_eqdec : coq_SOP -> coq_SOP -> coq_SOP dec_eq

val coq_SOP_EqDec : coq_SOP coq_EqDec

val coq_UOP_eqdec : coq_UOP -> coq_UOP -> coq_UOP dec_eq

val coq_UOP_EqDec : coq_UOP coq_EqDec

val coq_BOP_eqdec : coq_BOP -> coq_BOP -> coq_BOP dec_eq

val coq_BOP_EqDec : coq_BOP coq_EqDec

val coq_CSROP_eqdec : coq_CSROP -> coq_CSROP -> coq_CSROP dec_eq

val coq_CSROP_EqDec : coq_CSROP coq_EqDec

val coq_MOP_eqdec : coq_MOP -> coq_MOP -> coq_MOP dec_eq

val coq_MOP_EqDec : coq_MOP coq_EqDec

val coq_Retired_eqdec : coq_Retired -> coq_Retired -> coq_Retired dec_eq

val coq_Retired_EqDec : coq_Retired coq_EqDec

val coq_WordWidth_eqdec :
  coq_WordWidth -> coq_WordWidth -> coq_WordWidth dec_eq

val coq_WordWidth_EqDec : coq_WordWidth coq_EqDec

val coq_Unions_eqdec : coq_Unions -> coq_Unions -> coq_Unions dec_eq

val coq_Unions_EqDec : coq_Unions coq_EqDec

val coq_AST_eqdec : coq_AST -> coq_AST -> coq_AST dec_eq

val coq_AST_EqDec : coq_AST coq_EqDec

val coq_ASTConstructor_eqdec :
  coq_ASTConstructor -> coq_ASTConstructor -> coq_ASTConstructor dec_eq

val coq_ASTConstructor_EqDec : coq_ASTConstructor coq_EqDec

val coq_AccessType_eqdec :
  coq_AccessType -> coq_AccessType -> coq_AccessType dec_eq

val coq_AccessType_EqDec : coq_AccessType coq_EqDec

val coq_AccessTypeConstructor_eqdec :
  coq_AccessTypeConstructor -> coq_AccessTypeConstructor ->
  coq_AccessTypeConstructor dec_eq

val coq_AccessTypeConstructor_EqDec : coq_AccessTypeConstructor coq_EqDec

val coq_ExceptionType_eqdec :
  coq_ExceptionType -> coq_ExceptionType -> coq_ExceptionType dec_eq

val coq_ExceptionType_EqDec : coq_ExceptionType coq_EqDec

val coq_ExceptionTypeConstructor_eqdec :
  coq_ExceptionTypeConstructor -> coq_ExceptionTypeConstructor ->
  coq_ExceptionTypeConstructor dec_eq

val coq_ExceptionTypeConstructor_EqDec :
  coq_ExceptionTypeConstructor coq_EqDec

val coq_FetchResult_eqdec :
  coq_FetchResult -> coq_FetchResult -> coq_FetchResult dec_eq

val coq_FetchResult_EqDec : coq_FetchResult coq_EqDec

val coq_FetchResultConstructor_eqdec :
  coq_FetchResultConstructor -> coq_FetchResultConstructor ->
  coq_FetchResultConstructor dec_eq

val coq_FetchResultConstructor_EqDec : coq_FetchResultConstructor coq_EqDec

val coq_InterruptType_eqdec :
  coq_InterruptType -> coq_InterruptType -> coq_InterruptType dec_eq

val coq_InterruptType_EqDec : coq_InterruptType coq_EqDec

val coq_CtlResult_eqdec :
  coq_CtlResult -> coq_CtlResult -> coq_CtlResult dec_eq

val coq_CtlResult_EqDec : coq_CtlResult coq_EqDec

val coq_CtlResultConstructor_eqdec :
  coq_CtlResultConstructor -> coq_CtlResultConstructor ->
  coq_CtlResultConstructor dec_eq

val coq_CtlResultConstructor_EqDec : coq_CtlResultConstructor coq_EqDec

val coq_InterruptSetConstructor_eqdec :
  coq_InterruptSetConstructor -> coq_InterruptSetConstructor ->
  coq_InterruptSetConstructor dec_eq

val coq_InterruptSetConstructor_EqDec : coq_InterruptSetConstructor coq_EqDec

val coq_MemoryOpResult_eqdec :
  nat -> coq_MemoryOpResult -> coq_MemoryOpResult -> coq_MemoryOpResult dec_eq

val coq_MemoryOpResult_EqDec : nat -> coq_MemoryOpResult coq_EqDec

val coq_MemoryOpResultConstructor_eqdec :
  coq_MemoryOpResultConstructor -> coq_MemoryOpResultConstructor ->
  coq_MemoryOpResultConstructor dec_eq

val coq_MemoryOpResultConstructor_EqDec :
  coq_MemoryOpResultConstructor coq_EqDec

val coq_Records_eqdec : coq_Records -> coq_Records -> coq_Records dec_eq

val coq_Records_EqDec : coq_Records coq_EqDec

val coq_Pmpcfg_ent_eqdec :
  coq_Pmpcfg_ent -> coq_Pmpcfg_ent -> coq_Pmpcfg_ent dec_eq

val coq_Pmpcfg_ent_EqDec : coq_Pmpcfg_ent coq_EqDec

val coq_Mstatus_eqdec : coq_Mstatus -> coq_Mstatus -> coq_Mstatus dec_eq

val coq_Mstatus_EqDec : coq_Mstatus coq_EqDec

val coq_Minterrupts_eqdec :
  coq_Minterrupts -> coq_Minterrupts -> coq_Minterrupts dec_eq

val coq_Minterrupts_EqDec : coq_Minterrupts coq_EqDec

val coq_InterruptSet_eqdec :
  coq_InterruptSet -> coq_InterruptSet -> coq_InterruptSet dec_eq

val coq_InterruptSet_EqDec : coq_InterruptSet coq_EqDec

val coq_Privilege_finite : coq_Privilege coq_Finite

val coq_CSRIdx_finite : coq_CSRIdx coq_Finite

val coq_InterruptType_finite : coq_InterruptType coq_Finite

val coq_PmpCfgIdx_finite : coq_PmpCfgIdx coq_Finite

val coq_PmpCfgPerm_finite : coq_PmpCfgPerm coq_Finite

val coq_PmpAddrIdx_finite : coq_PmpAddrIdx coq_Finite

val coq_PmpAddrMatchType_finite : coq_PmpAddrMatchType coq_Finite

val coq_PmpMatch_finite : coq_PmpMatch coq_Finite

val coq_PmpAddrMatch_finite : coq_PmpAddrMatch coq_Finite

val coq_ROP_finite : coq_ROP coq_Finite

val coq_IOP_finite : coq_IOP coq_Finite

val coq_SOP_finite : coq_SOP coq_Finite

val coq_UOP_finite : coq_UOP coq_Finite

val coq_BOP_finite : coq_BOP coq_Finite

val coq_CSROP_finite : coq_CSROP coq_Finite

val coq_MOP_finite : coq_MOP coq_Finite

val coq_Retired_finite : coq_Retired coq_Finite

val coq_WordWidth_finite : coq_WordWidth coq_Finite

val coq_ASTConstructor_finite : coq_ASTConstructor coq_Finite

val coq_AccessTypeConstructor_finite : coq_AccessTypeConstructor coq_Finite

val coq_ExceptionTypeConstructor_finite :
  coq_ExceptionTypeConstructor coq_Finite

val coq_FetchResultConstructor_finite : coq_FetchResultConstructor coq_Finite

val coq_CtlResultConstructor_finite : coq_CtlResultConstructor coq_Finite

val coq_InterruptSetConstructor_finite :
  coq_InterruptSetConstructor coq_Finite

val coq_MemoryOpResultConstructor_finite :
  coq_MemoryOpResultConstructor coq_Finite

module RiscvPmpBase :
 sig
  val typedeclkit : Coq_ty.coq_TypeDeclKit

  val ty_xlenbits : Coq_ty.coq_Ty

  val ty_word : Coq_ty.coq_Ty

  val ty_byte : Coq_ty.coq_Ty

  val ty_bytes : nat -> Coq_ty.coq_Ty

  val ty_regno : Coq_ty.coq_Ty

  val ty_privilege : Coq_ty.coq_Ty

  val ty_interruptType : Coq_ty.coq_Ty

  val ty_priv_level : Coq_ty.coq_Ty

  val ty_csridx : Coq_ty.coq_Ty

  val ty_pmpcfgidx : Coq_ty.coq_Ty

  val ty_pmpcfgperm : Coq_ty.coq_Ty

  val ty_pmpaddridx : Coq_ty.coq_Ty

  val ty_pmpaddrmatchtype : Coq_ty.coq_Ty

  val ty_pmpmatch : Coq_ty.coq_Ty

  val ty_pmpaddrmatch : Coq_ty.coq_Ty

  val ty_pmp_addr_range : Coq_ty.coq_Ty

  val ty_rop : Coq_ty.coq_Ty

  val ty_iop : Coq_ty.coq_Ty

  val ty_sop : Coq_ty.coq_Ty

  val ty_uop : Coq_ty.coq_Ty

  val ty_bop : Coq_ty.coq_Ty

  val ty_csrop : Coq_ty.coq_Ty

  val ty_mop : Coq_ty.coq_Ty

  val ty_retired : Coq_ty.coq_Ty

  val ty_word_width : Coq_ty.coq_Ty

  val ty_mcause : Coq_ty.coq_Ty

  val ty_exc_code : Coq_ty.coq_Ty

  val ty_ast : Coq_ty.coq_Ty

  val ty_access_type : Coq_ty.coq_Ty

  val ty_exception_type : Coq_ty.coq_Ty

  val ty_memory_op_result : nat -> Coq_ty.coq_Ty

  val ty_fetch_result : Coq_ty.coq_Ty

  val ty_ctl_result : Coq_ty.coq_Ty

  val ty_interrupt_set : Coq_ty.coq_Ty

  val ty_pmpcfg_ent : Coq_ty.coq_Ty

  val ty_mstatus : Coq_ty.coq_Ty

  val ty_Minterrupts : Coq_ty.coq_Ty

  val ty_pmpentry : Coq_ty.coq_Ty

  val ty_pmpentries : Coq_ty.coq_Ty

  type enum_denote = __

  type union_denote = __

  type record_denote = __

  val typedenotekit : Coq_ty.coq_TypeDenoteKit

  type union_constructor = __

  val union_constructor_type :
    coq_Unions -> union_constructor -> Coq_ty.coq_Ty

  val eqdec_enum_denote : coq_Enums -> enum_denote coq_EqDec

  val finite_enum_denote : coq_Enums -> enum_denote coq_Finite

  val eqdec_union_denote : coq_Unions -> union_denote coq_EqDec

  val eqdec_union_constructor : coq_Unions -> union_constructor coq_EqDec

  val finite_union_constructor : coq_Unions -> union_constructor coq_Finite

  val eqdec_record_denote : coq_Records -> record_denote coq_EqDec

  val union_unfold :
    Coq_ty.unioni -> Coq_ty.uniont -> (union_constructor, Coq_ty.coq_Val) sigT

  val union_fold :
    Coq_ty.unioni -> (union_constructor, Coq_ty.coq_Val) sigT -> Coq_ty.uniont

  val record_field_type :
    Coq_ty.recordi -> (string, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val record_fold :
    Coq_ty.recordi -> (string, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv ->
    Coq_ty.recordt

  val record_unfold :
    Coq_ty.recordi -> Coq_ty.recordt -> (string, Coq_ty.coq_Ty,
    Coq_ty.coq_Val) coq_NamedEnv

  val typedefkit : Coq_ty.coq_TypeDefKit

  val varkit : coq_VarKit

  type coq_Reg =
  | Coq_pc
  | Coq_nextpc
  | Coq_mstatus
  | Coq_mie
  | Coq_mip
  | Coq_mtvec
  | Coq_mcause
  | Coq_mepc
  | Coq_mscratch
  | Coq_cur_privilege
  | Coq_x1
  | Coq_x2
  | Coq_x3
  | Coq_x4
  | Coq_x5
  | Coq_x6
  | Coq_x7
  | Coq_x8
  | Coq_x9
  | Coq_x10
  | Coq_x11
  | Coq_x12
  | Coq_x13
  | Coq_x14
  | Coq_x15
  | Coq_x16
  | Coq_x17
  | Coq_x18
  | Coq_x19
  | Coq_x20
  | Coq_x21
  | Coq_x22
  | Coq_x23
  | Coq_x24
  | Coq_x25
  | Coq_x26
  | Coq_x27
  | Coq_x28
  | Coq_x29
  | Coq_x30
  | Coq_x31
  | Coq_pmp0cfg
  | Coq_pmp1cfg
  | Coq_pmpaddr0
  | Coq_pmpaddr1

  val coq_Reg_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> Coq_ty.coq_Ty -> coq_Reg -> 'a1

  val coq_Reg_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> Coq_ty.coq_Ty -> coq_Reg -> 'a1

  val reg_convert : coq_RegIdx -> coq_Reg option

  type coq_Reg_sig = coq_Reg

  val coq_Reg_sig_pack : Coq_ty.coq_Ty -> coq_Reg -> Coq_ty.coq_Ty * coq_Reg

  val coq_Reg_Signature :
    Coq_ty.coq_Ty -> (coq_Reg, Coq_ty.coq_Ty, coq_Reg_sig) coq_Signature

  val coq_NoConfusionPackage_Reg :
    (Coq_ty.coq_Ty * coq_Reg) coq_NoConfusionPackage

  type _UU1d479__UU1d46c__UU1d46e_ = coq_Reg

  val _UU1d479__UU1d46c__UU1d46e__eq_dec :
    (Coq_ty.coq_Ty, coq_Reg) sigT coq_EqDec

  val _UU1d479__UU1d46c__UU1d46e__finite :
    (Coq_ty.coq_Ty, coq_Reg) sigT coq_Finite

  val val_inhabited : Coq_ty.coq_Ty -> Coq_ty.coq_Val coq_Inhabited

  type coq_RAM = coq_Addr -> coq_Byte

  type coq_EventTy =
  | IOWrite
  | IORead

  val coq_EventTy_rect : 'a1 -> 'a1 -> coq_EventTy -> 'a1

  val coq_EventTy_rec : 'a1 -> 'a1 -> coq_EventTy -> 'a1

  type coq_Event = { event_type : coq_EventTy; event_addr : coq_Addr;
                     event_nbbytes : nat; event_contents : Coq_bv.bv }

  val event_type : coq_Event -> coq_EventTy

  val event_addr : coq_Event -> coq_Addr

  val event_nbbytes : coq_Event -> nat

  val event_contents : coq_Event -> Coq_bv.bv

  type coq_Trace = coq_Event list

  type coq_MemoryType = { memory_ram : coq_RAM; memory_trace : coq_Trace;
                          memory_state : coq_State }

  val memory_ram : coq_MemoryType -> coq_RAM

  val memory_trace : coq_MemoryType -> coq_Trace

  val memory_state : coq_MemoryType -> coq_State

  type coq_Memory = coq_MemoryType

  val memory_update_ram : coq_Memory -> coq_RAM -> coq_MemoryType

  val memory_update_trace : coq_Memory -> coq_Trace -> coq_MemoryType

  val memory_append_trace : coq_Memory -> coq_Event -> coq_MemoryType

  val memory_update_state : coq_Memory -> coq_State -> coq_MemoryType

  val fun_read_ram : coq_Memory -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val

  val write_byte : coq_RAM -> Coq_ty.coq_Val -> coq_Byte -> coq_RAM

  val fun_write_ram :
    coq_Memory -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> coq_Memory

  val fun_within_mmio : nat -> Coq_ty.coq_Val -> bool

  val fun_externalWorldUpdates :
    coq_Memory -> (coq_Minterrupts, coq_Memory) prod

  type coq_Exp =
  | Coq_exp_var of coq_PVar * Coq_ty.coq_Ty
     * (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_exp_val of Coq_ty.coq_Ty * Coq_ty.coq_Val
  | Coq_exp_binop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Exp * coq_Exp
  | Coq_exp_unop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Exp
  | Coq_exp_list of Coq_ty.coq_Ty * coq_Exp list
  | Coq_exp_bvec of nat * coq_Exp t
  | Coq_exp_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * (Coq_ty.coq_Ty, coq_Exp) Coq_env.coq_Env
  | Coq_exp_union of Coq_ty.unioni * Coq_ty.unionk * coq_Exp
  | Coq_exp_record of Coq_ty.recordi
     * (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Exp) coq_NamedEnv

  val coq_Exp_rect :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_PVar -> Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Exp -> 'a1 -> coq_Exp -> 'a1 ->
    'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Exp ->
    'a1 -> 'a1) -> (Coq_ty.coq_Ty -> coq_Exp list -> __ -> 'a1) -> (nat ->
    coq_Exp t -> __ -> 'a1) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty, coq_Exp) Coq_env.coq_Env -> __ -> 'a1) -> (Coq_ty.unioni
    -> Coq_ty.unionk -> coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.recordi ->
    (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Exp) coq_NamedEnv -> __ -> 'a1) ->
    Coq_ty.coq_Ty -> coq_Exp -> 'a1

  val coq_Exp_rec :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_PVar -> Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Exp -> 'a1 -> coq_Exp -> 'a1 ->
    'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Exp ->
    'a1 -> 'a1) -> (Coq_ty.coq_Ty -> coq_Exp list -> __ -> 'a1) -> (nat ->
    coq_Exp t -> __ -> 'a1) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty, coq_Exp) Coq_env.coq_Env -> __ -> 'a1) -> (Coq_ty.unioni
    -> Coq_ty.unionk -> coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.recordi ->
    (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Exp) coq_NamedEnv -> __ -> 'a1) ->
    Coq_ty.coq_Ty -> coq_Exp -> 'a1

  val eval :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Exp -> (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val)
    coq_NamedEnv -> Coq_ty.coq_Val

  val evals :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_PVar, Coq_ty.coq_Ty, coq_Exp) coq_NamedEnv -> (coq_PVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv -> (coq_PVar, Coq_ty.coq_Ty,
    Coq_ty.coq_Val) coq_NamedEnv

  val exp_truncate :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> coq_Exp -> coq_Exp

  val exp_vector_subrange :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> coq_Exp -> coq_Exp

  val exp_update_vector_subrange :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> coq_Exp -> coq_Exp -> coq_Exp

  type coq_Term =
  | Coq_term_var of coq_LVar * Coq_ty.coq_Ty
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_term_val of Coq_ty.coq_Ty * Coq_ty.coq_Val
  | Coq_term_binop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_term_unop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term
  | Coq_term_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env
  | Coq_term_union of Coq_ty.unioni * Coq_ty.unionk * coq_Term
  | Coq_term_record of Coq_ty.recordi
     * (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) coq_NamedEnv

  val coq_NoConfusionPackage_Term :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty * coq_Term) coq_NoConfusionPackage

  type coq_Term_sig = coq_Term

  val coq_Term_sig_pack :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> Coq_ty.coq_Ty * coq_Term

  val coq_Term_Signature :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Ty, coq_Term_sig) coq_Signature

  val term_enum :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.enumi -> Coq_ty.enumt -> coq_Term

  val term_list :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term list -> coq_Term

  val term_bvec :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term t -> coq_Term

  val term_relop_neg :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> coq_Term

  val term_truncate :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> coq_Term -> coq_Term

  val term_vector_subrange :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> coq_Term -> coq_Term

  val term_update_vector_subrange :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> coq_Term -> coq_Term -> coq_Term

  val coq_Term_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1 -> 'a1
    -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty, coq_Term,
    'a1) Coq_env.coq_All -> 'a1) -> (Coq_ty.unioni -> Coq_ty.unionk ->
    coq_Term -> 'a1 -> 'a1) -> (Coq_ty.recordi -> (Coq_ty.recordf,
    Coq_ty.coq_Ty, coq_Term) coq_NamedEnv -> ((Coq_ty.recordf, Coq_ty.coq_Ty)
    Binding.coq_Binding, coq_Term, 'a1) Coq_env.coq_All -> 'a1) ->
    Coq_ty.coq_Ty -> coq_Term -> 'a1

  val coq_Term_rec :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1 -> 'a1
    -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty, coq_Term,
    'a1) Coq_env.coq_All -> 'a1) -> (Coq_ty.unioni -> Coq_ty.unionk ->
    coq_Term -> 'a1 -> 'a1) -> (Coq_ty.recordi -> (Coq_ty.recordf,
    Coq_ty.coq_Ty, coq_Term) coq_NamedEnv -> ((Coq_ty.recordf, Coq_ty.coq_Ty)
    Binding.coq_Binding, coq_Term, 'a1) Coq_env.coq_All -> 'a1) ->
    Coq_ty.coq_Ty -> coq_Term -> 'a1

  val coq_Term_int_case :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1) -> (coq_Term -> coq_Term -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1) -> (coq_Term -> 'a1) -> (nat -> coq_Term ->
    'a1) -> (nat -> coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_int_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1
    -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (coq_Term ->
    coq_Term -> 'a1 -> 'a1 -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 ->
    'a1) -> (coq_Term -> 'a1 -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_bool_case :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp ->
    coq_Term -> coq_Term -> 'a1) -> (coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_bool_ind :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1
    -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty
    -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> 'a1) -> (coq_Term -> 'a1
    -> 'a1) -> coq_Term -> 'a1

  val coq_Term_list_case :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1) -> (coq_Term -> coq_Term -> 'a1) ->
    (coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_prod_case :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_sum_case :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    (coq_Term -> 'a1) -> (coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_bvec_case :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat -> coq_Term ->
    'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1) -> (nat -> nat -> __ ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat -> nat -> __ ->
    coq_Term -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term -> 'a1) -> (nat
    -> nat -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> 'a1) -> nat ->
    coq_Term -> 'a1

  val coq_Term_bvec_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 ->
    'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 ->
    'a1 -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1)
    -> (nat -> nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat ->
    nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> 'a1 -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term ->
    coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term -> 'a1 -> 'a1) -> (nat
    -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1 ->
    'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1 -> 'a1) -> (nat -> coq_Term
    -> 'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat ->
    nat -> __ -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat -> coq_Term -> 'a1 ->
    'a1) -> (nat -> nat -> coq_Term -> 'a1 -> 'a1) -> nat -> coq_Term -> 'a1

  val coq_Term_tuple_case :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    ((Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env -> 'a1) -> coq_Term -> 'a1

  val coq_Term_union_case :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.unioni -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    (Coq_ty.unionk -> coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_record_case :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.recordi -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    ((Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) coq_NamedEnv -> 'a1) ->
    coq_Term -> 'a1

  type coq_ListView =
  | Coq_term_list_var of coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_term_list_val of Coq_ty.coq_Val
  | Coq_term_list_cons of coq_Term * coq_Term * coq_ListView
  | Coq_term_list_append of coq_Term * coq_Term * coq_ListView * coq_ListView
  | Coq_term_list_rev of coq_Term * coq_ListView

  val coq_ListView_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    (coq_Term -> coq_Term -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term ->
    coq_Term -> coq_ListView -> 'a1 -> coq_ListView -> 'a1 -> 'a1) ->
    (coq_Term -> coq_ListView -> 'a1 -> 'a1) -> coq_Term -> coq_ListView ->
    'a1

  val coq_ListView_rec :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    (coq_Term -> coq_Term -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term ->
    coq_Term -> coq_ListView -> 'a1 -> coq_ListView -> 'a1 -> 'a1) ->
    (coq_Term -> coq_ListView -> 'a1 -> 'a1) -> coq_Term -> coq_ListView ->
    'a1

  type coq_View = __

  val view_var :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_LVar
    -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_View

  val view_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> coq_View

  val view_binop :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> coq_View -> coq_View -> coq_View

  val view_unop :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    coq_View -> coq_View

  val view :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_View

  val coq_Term_eqb_clause_3 :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    sumbool -> coq_Term -> coq_Term -> bool

  val coq_Term_eqb_clause_4 :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> sumbool -> coq_Term -> bool

  val coq_Term_eqb_clause_6 :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.unioni ->
    Coq_ty.unionk -> coq_Term -> Coq_ty.unionk -> sumbool -> coq_Term -> bool

  val coq_Term_eqb :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool

  val coq_Term_eqb_spec :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term -> reflect

  type 'a coq_List = 'a list

  type 'a coq_Const = 'a

  type coq_Sub =
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, coq_Term) Coq_env.coq_Env

  type 't coq_Subst =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub
    -> 't

  val subst :
    'a1 coq_Subst -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Sub -> 'a1

  val sub_term :
    Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Term -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub -> coq_Term

  val coq_SubstTerm : Coq_ty.coq_Ty -> coq_Term coq_Subst

  val coq_SubstList : 'a1 coq_Subst -> 'a1 coq_List coq_Subst

  val coq_SubstConst : 'a1 coq_Const coq_Subst

  val coq_SubstEnv :
    ('a1 -> 'a2 coq_Subst) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2)
    Coq_env.coq_Env coq_Subst

  val sub_id :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub

  val sub_snoc :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub
    -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Term -> coq_Sub

  val sub_shift :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Sub

  val sub_wk1 :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Sub

  val sub_cat_left :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub

  val sub_cat_right :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub

  val sub_up1 :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub
    -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Sub

  val sub_up :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub
    -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Sub

  val sub_single :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term -> coq_Sub

  type 't coq_SubstLaws =
  | Build_SubstLaws

  val coq_SubstLawsTerm : Coq_ty.coq_Ty -> coq_Term coq_SubstLaws

  val coq_SubstLawsList :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_List coq_SubstLaws

  val coq_SubstLawsConst : 'a1 coq_Const coq_SubstLaws

  val coq_SubstLawsEnv :
    ('a1 -> 'a2 coq_Subst) -> ('a1 -> 'a2 coq_SubstLaws) -> 'a1
    Coq_ctx.coq_Ctx -> ('a1, 'a2) Coq_env.coq_Env coq_SubstLaws

  val subst_ctx : 'a1 coq_Subst -> 'a1 Coq_ctx.coq_Ctx coq_Subst

  val substlaws_ctx :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 Coq_ctx.coq_Ctx coq_SubstLaws

  module SubNotations :
   sig
   end

  type ('a, 'b) coq_Pair = ('a, 'b) prod

  val coq_SubstPair :
    'a1 coq_Subst -> 'a2 coq_Subst -> ('a1, 'a2) coq_Pair coq_Subst

  val coq_SubstLawsPair :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a2 coq_Subst -> 'a2 coq_SubstLaws
    -> ('a1, 'a2) coq_Pair coq_SubstLaws

  type 'a coq_Option = 'a option

  val coq_SubstOption : 'a1 coq_Subst -> 'a1 coq_Option coq_Subst

  val coq_SubstLawsOption :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_Option coq_SubstLaws

  type coq_Unit = coq_unit

  val coq_SubstUnit : coq_Unit coq_Subst

  val coq_SubstLawsUnit : coq_Unit coq_SubstLaws

  type coq_SStore = (coq_PVar, Coq_ty.coq_Ty, coq_Term) coq_NamedEnv

  val subst_localstore :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_SStore coq_Subst

  val substlaws_localstore :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_SStore coq_SubstLaws

  module TermNotations :
   sig
   end

  type coq_ETerm =
  | Coq_eterm_var of coq_LVar * Coq_ty.coq_Ty * nat
  | Coq_eterm_val of Coq_ty.coq_Ty * Coq_ty.coq_Val
  | Coq_eterm_binop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_ETerm * coq_ETerm
  | Coq_eterm_unop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_ETerm
  | Coq_eterm_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * (Coq_ty.coq_Ty, coq_ETerm) Coq_env.coq_Env
  | Coq_eterm_union of Coq_ty.unioni * Coq_ty.unionk * coq_ETerm
  | Coq_eterm_record of Coq_ty.recordi
     * (Coq_ty.recordf, Coq_ty.coq_Ty, coq_ETerm) coq_NamedEnv

  val erase_term :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_ETerm

  val erase_SStore :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_SStore -> (coq_PVar, Coq_ty.coq_Ty, coq_ETerm) coq_NamedEnv

  type 'n coq_TuplePat =
  | Coq_tuplepat_nil
  | Coq_tuplepat_snoc of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_TuplePat * Coq_ty.coq_Ty * 'n

  val coq_TuplePat_rect :
    'a2 -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2 ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat ->
    'a2

  val coq_TuplePat_rec :
    'a2 -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2 ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat ->
    'a2

  type 'n coq_RecordPat =
  | Coq_recordpat_nil
  | Coq_recordpat_snoc of (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_RecordPat * Coq_ty.recordf * Coq_ty.coq_Ty * 'n

  val coq_RecordPat_rect :
    'a2 -> ((Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2 -> Coq_ty.recordf ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> (Coq_ty.recordf, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2

  val coq_RecordPat_rec :
    'a2 -> ((Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2 -> Coq_ty.recordf ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> (Coq_ty.recordf, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2

  val tuple_pattern_match_env :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> (Coq_ty.coq_Ty, 'a2)
    Coq_env.coq_Env -> ('a1, Coq_ty.coq_Ty, 'a2) coq_NamedEnv

  val tuple_pattern_match_env_reverse :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> ('a1, Coq_ty.coq_Ty, 'a2)
    coq_NamedEnv -> (Coq_ty.coq_Ty, 'a2) Coq_env.coq_Env

  val tuple_pattern_match_val :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> Coq_ty.coq_Val -> ('a1,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv

  val record_pattern_match_env :
    (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
    coq_RecordPat -> (Coq_ty.recordf, Coq_ty.coq_Ty, 'a2) coq_NamedEnv ->
    ('a1, Coq_ty.coq_Ty, 'a2) coq_NamedEnv

  val record_pattern_match_env_reverse :
    (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
    coq_RecordPat -> ('a1, Coq_ty.coq_Ty, 'a2) coq_NamedEnv ->
    (Coq_ty.recordf, Coq_ty.coq_Ty, 'a2) coq_NamedEnv

  val record_pattern_match_val :
    Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> Coq_ty.coq_Val -> ('a1,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv

  type 'n coq_Pattern =
  | Coq_pat_var of 'n * Coq_ty.coq_Ty
  | Coq_pat_bool
  | Coq_pat_list of Coq_ty.coq_Ty * 'n * 'n
  | Coq_pat_pair of 'n * 'n * Coq_ty.coq_Ty * Coq_ty.coq_Ty
  | Coq_pat_sum of Coq_ty.coq_Ty * Coq_ty.coq_Ty * 'n * 'n
  | Coq_pat_unit
  | Coq_pat_enum of Coq_ty.enumi
  | Coq_pat_bvec_split of nat * nat * 'n * 'n
  | Coq_pat_bvec_exhaustive of nat
  | Coq_pat_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_TuplePat
  | Coq_pat_record of Coq_ty.recordi
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_RecordPat
  | Coq_pat_union of Coq_ty.unioni * (Coq_ty.unionk -> 'n coq_Pattern)

  val coq_Pattern_rect :
    ('a1 -> Coq_ty.coq_Ty -> 'a2) -> 'a2 -> (Coq_ty.coq_Ty -> 'a1 -> 'a1 ->
    'a2) -> ('a1 -> 'a1 -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a2) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a1 -> 'a1 -> 'a2) -> 'a2 ->
    (Coq_ty.enumi -> 'a2) -> (nat -> nat -> 'a1 -> 'a1 -> 'a2) -> (nat ->
    'a2) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2) ->
    (Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2) -> (Coq_ty.unioni ->
    (Coq_ty.unionk -> 'a1 coq_Pattern) -> (Coq_ty.unionk -> 'a2) -> 'a2) ->
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a2

  val coq_Pattern_rec :
    ('a1 -> Coq_ty.coq_Ty -> 'a2) -> 'a2 -> (Coq_ty.coq_Ty -> 'a1 -> 'a1 ->
    'a2) -> ('a1 -> 'a1 -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a2) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a1 -> 'a1 -> 'a2) -> 'a2 ->
    (Coq_ty.enumi -> 'a2) -> (nat -> nat -> 'a1 -> 'a1 -> 'a2) -> (nat ->
    'a2) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2) ->
    (Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2) -> (Coq_ty.unioni ->
    (Coq_ty.unionk -> 'a1 coq_Pattern) -> (Coq_ty.unionk -> 'a2) -> 'a2) ->
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a2

  type 'n coq_PatternCase = __

  val coq_EqDec_PatternCase :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase coq_EqDec

  val coq_Finite_PatternCase :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase coq_Finite

  val coq_PatternCaseCtx :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  type 'n coq_MatchResult =
    ('n coq_PatternCase, ('n, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv)
    sigT

  val pattern_match_val :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> Coq_ty.coq_Val -> 'a1 coq_MatchResult

  val pattern_match_val_reverse :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv -> Coq_ty.coq_Val

  val pattern_match_val_reverse' :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_MatchResult -> Coq_ty.coq_Val

  type ('n, 'r) coq_PatternCaseCurried = __

  val of_pattern_case_curried :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    -> 'a1 coq_Pattern -> ('a1, 'a2) coq_PatternCaseCurried -> 'a1
    coq_PatternCase -> 'a2

  type ('n, 'r) coq_Alternative = { alt_pat : 'n coq_Pattern;
                                    alt_rhs : ('n, 'r) coq_PatternCaseCurried }

  val alt_pat :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    -> ('a1, 'a2) coq_Alternative -> 'a1 coq_Pattern

  val alt_rhs :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    -> ('a1, 'a2) coq_Alternative -> ('a1, 'a2) coq_PatternCaseCurried

  val freshen_ctx :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val unfreshen_namedenv :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty, 'a2) coq_NamedEnv -> ('a1,
    Coq_ty.coq_Ty, 'a2) coq_NamedEnv

  val freshen_namedenv :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty, 'a2) coq_NamedEnv -> (coq_LVar,
    Coq_ty.coq_Ty, 'a2) coq_NamedEnv

  val freshen_tuplepat :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> coq_LVar
    coq_TuplePat

  val freshen_recordpat :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> coq_LVar coq_RecordPat

  val freshen_pattern :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> coq_LVar
    coq_Pattern

  val unfreshen_patterncase :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> coq_LVar
    coq_PatternCase -> 'a1 coq_PatternCase

  val freshen_patterncase :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
    coq_PatternCase -> coq_LVar coq_PatternCase

  val unfreshen_patterncaseenv' :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> coq_LVar
    coq_PatternCase -> (coq_LVar, Coq_ty.coq_Ty, 'a2) coq_NamedEnv -> ('a1,
    Coq_ty.coq_Ty, 'a2) coq_NamedEnv

  val freshen_patterncaseenv :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
    coq_PatternCase -> ('a1, Coq_ty.coq_Ty, 'a2) coq_NamedEnv -> (coq_LVar,
    Coq_ty.coq_Ty, 'a2) coq_NamedEnv

  val unfreshen_patterncaseenv :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> coq_LVar
    coq_PatternCase -> (coq_LVar, Coq_ty.coq_Ty, 'a2) coq_NamedEnv -> ('a1,
    Coq_ty.coq_Ty, 'a2) coq_NamedEnv

  val freshen_matchresult :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
    coq_MatchResult -> coq_LVar coq_MatchResult

  val unfreshen_matchresult :
    ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> coq_LVar
    coq_MatchResult -> 'a1 coq_MatchResult

  type 't coq_OccursCheck =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 't -> 't option

  val occurs_check :
    'a1 coq_OccursCheck -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 ->
    'a1 option

  val coq_OccursCheck_Const : 'a1 coq_Const coq_OccursCheck

  val occurs_check_env :
    ('a1 -> 'a2 coq_OccursCheck) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2)
    Coq_env.coq_Env coq_OccursCheck

  val occurs_check_term : Coq_ty.coq_Ty -> coq_Term coq_OccursCheck

  val occurs_check_list : 'a1 coq_OccursCheck -> 'a1 coq_List coq_OccursCheck

  val occurs_check_sub :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub
    coq_OccursCheck

  val occurs_check_pair :
    'a1 coq_OccursCheck -> 'a2 coq_OccursCheck -> ('a1, 'a2) coq_Pair
    coq_OccursCheck

  val occurs_check_option :
    'a1 coq_OccursCheck -> 'a1 coq_Option coq_OccursCheck

  val occurs_check_unit : coq_Unit coq_OccursCheck

  val occurscheck_ctx :
    'a1 coq_OccursCheck -> 'a1 Coq_ctx.coq_Ctx coq_OccursCheck

  module Experimental :
   sig
    type 't coq_OccursCheckView =
    | Succ of 't
    | Fail of 't

    val coq_OccursCheckView_rect :
      'a1 coq_Subst -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ('a1 ->
      'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 coq_OccursCheckView -> 'a2

    val coq_OccursCheckView_rec :
      'a1 coq_Subst -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ('a1 ->
      'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 coq_OccursCheckView -> 'a2

    type 't coq_OccursCheck =
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 't -> 't
      coq_OccursCheckView

    val occurs_check_view :
      'a1 coq_Subst -> 'a1 coq_OccursCheck -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1 -> 'a1 coq_OccursCheckView

    val coq_OccursCheckEnv :
      ('a1 -> 'a2 coq_Subst) -> ('a1 -> 'a2 coq_OccursCheck) -> 'a1
      Coq_ctx.coq_Ctx -> ('a1, 'a2) Coq_env.coq_Env coq_OccursCheck
   end

  type 'sb coq_SubstUniv = { initSU : ((coq_LVar, Coq_ty.coq_Ty)
                                      Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                      'sb);
                             transSU : ((coq_LVar, Coq_ty.coq_Ty)
                                       Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                       (coq_LVar, Coq_ty.coq_Ty)
                                       Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                       (coq_LVar, Coq_ty.coq_Ty)
                                       Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                       'sb -> 'sb -> 'sb);
                             interpSU : ((coq_LVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding Coq_ctx.coq_Ctx
                                        -> (coq_LVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding Coq_ctx.coq_Ctx
                                        -> 'sb -> coq_Sub) }

  val initSU :
    'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1

  val transSU :
    'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> 'a1 -> 'a1

  val interpSU :
    'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> coq_Sub

  type ('sb, 't) coq_SubstSU =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't ->
    'sb -> 't

  val substSU :
    ('a1, 'a2) coq_SubstSU -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> 'a1 -> 'a2

  val substSU_term :
    'a1 coq_SubstUniv -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term -> 'a1 -> coq_Term

  val coq_SubstSUTerm :
    'a1 coq_SubstUniv -> Coq_ty.coq_Ty -> ('a1, coq_Term) coq_SubstSU

  val substSU_option :
    ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 coq_Option) coq_SubstSU

  type 'sb coq_MeetResult = { _UU03a3_12 : (coq_LVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding Coq_ctx.coq_Ctx;
                              meetLeft : 'sb; meetRight : 'sb; meetUp : 
                              'sb }

  val _UU03a3_12 :
    'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx

  val meetLeft :
    'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1

  val meetRight :
    'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1

  val meetUp :
    'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1

  type 'sb coq_SubstUnivMeet =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'sb ->
    'sb -> 'sb coq_MeetResult

  val meetSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a1 -> 'a1 coq_MeetResult

  val coq_SubstSU_env :
    'a1 coq_SubstUniv -> 'a2 Coq_ctx.coq_Ctx -> ('a2 -> ('a1, 'a3)
    coq_SubstSU) -> ('a1, ('a2, 'a3) Coq_env.coq_Env) coq_SubstSU

  val coq_SubstSU_sub :
    'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, coq_Sub) coq_SubstSU

  val substSU_pair :
    ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU -> ('a1, ('a2, 'a3)
    coq_Pair) coq_SubstSU

  val substSU_list : ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 coq_List) coq_SubstSU

  val substSU_Const : ('a1, 'a2 coq_Const) coq_SubstSU

  type 'sb coq_SubstUnivVar =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'sb

  val suVar :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1

  type 'sb coq_SubstUnivVarUp =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> 'sb -> 'sb

  val upSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUnivVarUp -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1
    -> 'a1

  type 'sb coq_SubstUnivVarDown = { wkVarSU : ((coq_LVar, Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_Ctx -> (coq_LVar,
                                              Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_Ctx -> (coq_LVar,
                                              Coq_ty.coq_Ty)
                                              Binding.coq_Binding ->
                                              (coq_LVar, Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_In -> 'sb ->
                                              (coq_LVar, Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_In);
                                    downSU : ((coq_LVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx -> (coq_LVar,
                                             Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx -> (coq_LVar,
                                             Coq_ty.coq_Ty)
                                             Binding.coq_Binding ->
                                             (coq_LVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_In -> 'sb -> 'sb) }

  val wkVarSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUnivVarDown -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In

  val downSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUnivVarDown -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> 'a1

  type ('sb, 't) coq_BoxSb =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'sb -> 't
    (* singleton inductive, whose constructor was MkBoxSb *)

  val unboxSb :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
    'a2) coq_BoxSb -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> 'a2

  val boxSb :
    ('a1, 'a2) coq_SubstSU -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_BoxSb

  val substSU_BoxSb :
    ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> ('a1, ('a1, 'a2)
    coq_BoxSb) coq_SubstSU

  type ('sb, 't) coq_Weakened = { _UU03a3_supp : (coq_LVar, Coq_ty.coq_Ty)
                                                 Binding.coq_Binding
                                                 Coq_ctx.coq_Ctx;
                                  embedSupport : 'sb;
                                  wkVal : ('sb, 't) coq_BoxSb }

  val _UU03a3_supp :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Weakened ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val embedSupport :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Weakened -> 'a1

  val wkVal :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Weakened -> ('a1,
    'a2) coq_BoxSb

  val unWeaken :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
    coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2) coq_Weakened -> 'a2

  val liftBoxUnOp :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 ->
    'a2) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    ('a3, 'a1) coq_BoxSb -> ('a3, 'a2) coq_BoxSb

  val liftBoxBinOp :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 ->
    'a2 -> 'a3) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a4, 'a1) coq_BoxSb -> ('a4, 'a2) coq_BoxSb -> ('a4,
    'a3) coq_BoxSb

  val weakenInit :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU ->
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_Weakened

  type ('sb, 't) coq_GenOccursCheck =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't ->
    ('sb, 't) coq_Weakened

  val gen_occurs_check :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2)
    coq_GenOccursCheck -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_Weakened

  val coq_GenOccursCheck_Const :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2 coq_Const) coq_GenOccursCheck

  val liftUnOp :
    'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 ->
    'a3) -> ('a1, 'a2) coq_Weakened -> ('a1, 'a3) coq_Weakened

  val liftBinOp :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ('a1, 'a4) coq_SubstSU -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2) coq_Weakened -> ('a1,
    'a3) coq_Weakened -> ('a1, 'a4) coq_Weakened

  val liftTernOp :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ('a1, 'a4) coq_SubstSU -> ('a1, 'a5) coq_SubstSU -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 -> 'a3 -> 'a4
    -> 'a5) -> ('a1, 'a2) coq_Weakened -> ('a1, 'a3) coq_Weakened -> ('a1,
    'a4) coq_Weakened -> ('a1, 'a5) coq_Weakened

  val gen_occurs_check_env :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a2 -> ('a1, 'a3) coq_SubstSU) -> ('a2 -> ('a1,
    'a3) coq_GenOccursCheck) -> 'a2 Coq_ctx.coq_Ctx -> ('a1, ('a2, 'a3)
    Coq_env.coq_Env) coq_GenOccursCheck

  val gen_occurs_check_term :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> Coq_ty.coq_Ty -> ('a1, coq_Term) coq_GenOccursCheck

  val gen_occurs_check_list :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2)
    coq_GenOccursCheck -> ('a1, 'a2 coq_List) coq_GenOccursCheck

  val gen_occurs_check_pair :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a3) coq_GenOccursCheck -> ('a1,
    ('a2, 'a3) coq_Pair) coq_GenOccursCheck

  val gen_occurs_check_option :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a2
    coq_Option) coq_GenOccursCheck

  val substSU_ctx :
    ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 Coq_ctx.coq_Ctx) coq_SubstSU

  val gen_occurscheck_ctx :
    ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet ->
    ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a2 Coq_ctx.coq_Ctx)
    coq_GenOccursCheck

  val gen_occurs_check_unit :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, coq_Unit) coq_GenOccursCheck

  type coq_WeakensTo =
  | WkNil
  | WkSkipVar of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
  | WkKeepVar of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo

  val coq_WeakensTo_rect :
    'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 ->
    'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 ->
    'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> 'a1

  val coq_WeakensTo_rec :
    'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 ->
    'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 ->
    'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> 'a1

  val wkRefl :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo

  val wk1 :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo

  val interpWk :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_Sub

  val transWk :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo

  type transWk_graph =
  | Coq_transWk_graph_equation_1
  | Coq_transWk_graph_equation_2 of (coq_LVar, Coq_ty.coq_Ty)
                                    Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
     * coq_WeakensTo * transWk_graph
  | Coq_transWk_graph_equation_3 of (coq_LVar, Coq_ty.coq_Ty)
                                    Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * transWk_graph
  | Coq_transWk_graph_equation_4 of (coq_LVar, Coq_ty.coq_Ty)
                                    Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * transWk_graph

  val transWk_graph_rect :
    'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakensTo -> transWk_graph -> 'a1 -> 'a1) -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    transWk_graph -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> transWk_graph -> 'a1
    -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo -> transWk_graph -> 'a1

  val transWk_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakensTo -> transWk_graph

  val transWk_elim :
    'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakensTo -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> 'a1 -> 'a1) ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> 'a1 -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    'a1

  val coq_FunctionalElimination_transWk :
    __ -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakensTo -> __ -> __) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> __ -> __) ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> __ -> __) -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    __

  val coq_FunctionalInduction_transWk :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo) coq_FunctionalInduction

  val wkNilInit :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo

  val wkKeepCtx :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo

  type coq_WeakenZeroView =
  | VarUnused of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo
  | VarUsed of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo

  val coq_WeakenZeroView_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakenZeroView -> 'a1

  val coq_WeakenZeroView_rec :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakenZeroView -> 'a1

  val weakenZeroView :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakenZeroView

  type weakenZeroView_graph =
  | Coq_weakenZeroView_graph_equation_1 of (coq_LVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
  | Coq_weakenZeroView_graph_equation_2 of (coq_LVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo

  val weakenZeroView_graph_rect :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1) ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakenZeroView -> weakenZeroView_graph -> 'a1

  val weakenZeroView_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    weakenZeroView_graph

  val weakenZeroView_elim :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1) ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_weakenZeroView :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __) ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    __) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __

  val coq_FunctionalInduction_weakenZeroView :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakenZeroView) coq_FunctionalInduction

  type coq_WeakenNilView =
  | WkNilViewNil

  val coq_WeakenNilView_rect :
    'a1 -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView -> 'a1

  val coq_WeakenNilView_rec :
    'a1 -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView -> 'a1

  val weakenNilView :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView

  type weakenNilView_graph =
  | Coq_weakenNilView_graph_equation_1

  val weakenNilView_graph_rect :
    'a1 -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView -> weakenNilView_graph -> 'a1

  val weakenNilView_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> weakenNilView_graph

  val weakenNilView_elim :
    'a1 -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_weakenNilView :
    __ -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> __

  val coq_FunctionalInduction_weakenNilView :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView) coq_FunctionalInduction

  val wkRemove :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo

  val wkSingleton :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo

  val wkVarZeroIn :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In

  type wkVarZeroIn_graph =
  | Coq_wkVarZeroIn_graph_equation_1 of (coq_LVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
     * wkVarZeroIn_graph
  | Coq_wkVarZeroIn_graph_equation_2 of (coq_LVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo

  val wkVarZeroIn_graph_rect :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> wkVarZeroIn_graph
    -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> wkVarZeroIn_graph -> 'a1

  val wkVarZeroIn_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    wkVarZeroIn_graph

  val wkVarZeroIn_elim :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_wkVarZeroIn :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __ -> __) ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    __) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __

  val coq_FunctionalInduction_wkVarZeroIn :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In)
    coq_FunctionalInduction

  val weakenIn :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In

  val weakenRemovePres :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    coq_WeakensTo

  type coq_WeakenRemoveView =
  | MkWeakenRemoveView of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo

  val coq_WeakenRemoveView_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    coq_WeakensTo -> coq_WeakenRemoveView -> 'a1

  val coq_WeakenRemoveView_rec :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    coq_WeakensTo -> coq_WeakenRemoveView -> 'a1

  val weakenRemoveView :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakenRemoveView

  type coq_WeakenVarView =
  | WeakenVarUnused of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                       Coq_ctx.coq_Ctx
     * coq_WeakensTo
  | WeakenVarUsed of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                     Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo

  val coq_WeakenVarView_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    coq_WeakensTo -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakenVarView -> 'a1

  val coq_WeakenVarView_rec :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    coq_WeakensTo -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakenVarView -> 'a1

  val weakenVarView_obligations_obligation_1 :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakenVarView

  val weakenVarView_obligations_obligation_2 :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    coq_WeakenVarView) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    coq_WeakenVarView

  val weakenVarView_obligations_obligation_3 :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    coq_WeakenVarView) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    coq_WeakenVarView

  val weakenVarView :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    coq_WeakenVarView

  type weakenVarView_graph =
  | Coq_weakenVarView_graph_equation_1 of (coq_LVar, Coq_ty.coq_Ty)
                                          Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_weakenVarView_graph_equation_2 of (coq_LVar, Coq_ty.coq_Ty)
                                          Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo
     * ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
       Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
       weakenVarView_graph)
  | Coq_weakenVarView_graph_equation_3 of (coq_LVar, Coq_ty.coq_Ty)
                                          Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo
     * ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
       Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
       weakenVarView_graph)

  val weakenVarView_graph_rect :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> weakenVarView_graph) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    coq_WeakensTo -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    weakenVarView_graph) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    coq_WeakenVarView -> weakenVarView_graph -> 'a1

  val weakenVarView_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    weakenVarView_graph

  val weakenVarView_elim :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    coq_WeakensTo -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_weakenVarView :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> __) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    coq_WeakensTo -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    __) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> __

  val coq_FunctionalInduction_weakenVarView :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    coq_WeakenVarView) coq_FunctionalInduction

  val substUniv_weaken : coq_WeakensTo coq_SubstUniv

  val extendMeetSkipSkip :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo
    coq_MeetResult -> coq_WeakensTo coq_MeetResult

  val extendMeetSkipKeep :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo
    coq_MeetResult -> coq_WeakensTo coq_MeetResult

  val extendMeetKeepSkip :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo
    coq_MeetResult -> coq_WeakensTo coq_MeetResult

  val extendMeetKeepKeep :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo
    coq_MeetResult -> coq_WeakensTo coq_MeetResult

  val meetWk :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo coq_MeetResult

  type meetWk_graph =
  | Coq_meetWk_graph_equation_1
  | Coq_meetWk_graph_equation_2 of (coq_LVar, Coq_ty.coq_Ty)
                                   Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
     * coq_WeakensTo * meetWk_graph
  | Coq_meetWk_graph_equation_3 of (coq_LVar, Coq_ty.coq_Ty)
                                   Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * meetWk_graph
  | Coq_meetWk_graph_equation_4 of (coq_LVar, Coq_ty.coq_Ty)
                                   Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * meetWk_graph
  | Coq_meetWk_graph_equation_5 of (coq_LVar, Coq_ty.coq_Ty)
                                   Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * meetWk_graph

  val meetWk_graph_rect :
    'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakensTo -> meetWk_graph -> 'a1 -> 'a1) -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    meetWk_graph -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> meetWk_graph -> 'a1
    -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> meetWk_graph -> 'a1 -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    coq_WeakensTo coq_MeetResult -> meetWk_graph -> 'a1

  val meetWk_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakensTo -> meetWk_graph

  val meetWk_elim :
    'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakensTo -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> 'a1 -> 'a1) ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> 'a1 -> 'a1) ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_meetWk :
    __ -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakensTo -> __ -> __) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> __ -> __) ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> __ -> __) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> __ -> __) ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakensTo -> __

  val coq_FunctionalInduction_meetWk :
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo coq_MeetResult)
    coq_FunctionalInduction

  val substUnivMeet_weaken : coq_WeakensTo coq_SubstUnivMeet

  val wkVar :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo

  val coq_FunctionalInduction_transWk_assoc : __ coq_FunctionalInduction

  val substUnivVar_weaken : coq_WeakensTo coq_SubstUnivVar

  val substUnivVarUp_weaken : coq_WeakensTo coq_SubstUnivVarUp

  val substUnivVarDown_weaken : coq_WeakensTo coq_SubstUnivVarDown

  val restrictEnv :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, 'a1)
    Coq_env.coq_Env -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, 'a1)
    Coq_env.coq_Env

  val elimWeakenedVarZero :
    (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a1) -> (coq_WeakensTo,
    'a1) coq_Weakened -> (coq_WeakensTo, 'a1) coq_Weakened

  val elimWeakenedVar :
    (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a2) coq_SubstSU ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ((coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> 'a2) ->
    (coq_WeakensTo, 'a1) coq_Weakened -> (coq_WeakensTo, 'a2) coq_Weakened

  val old_occurs_check :
    (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a1)
    coq_GenOccursCheck -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 ->
    'a1 option

  type ('t, 'a) coq_Inst =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
    Coq_env.coq_Env -> 'a

  val inst :
    ('a1, 'a2) coq_Inst -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding,
    Coq_ty.coq_Val) Coq_env.coq_Env -> 'a2

  type ('t, 'a) coq_Lift =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a -> 't

  val lift :
    ('a1, 'a2) coq_Lift -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> 'a1

  val inst_list : ('a1, 'a2) coq_Inst -> ('a1 coq_List, 'a2 list) coq_Inst

  val lift_list : ('a1, 'a2) coq_Lift -> ('a1 coq_List, 'a2 list) coq_Lift

  val inst_const : ('a1 coq_Const, 'a1) coq_Inst

  val lift_const : ('a1 coq_Const, 'a1) coq_Lift

  val inst_env :
    ('a1 -> ('a2, 'a3) coq_Inst) -> 'a1 Coq_ctx.coq_Ctx -> (('a1, 'a2)
    Coq_env.coq_Env, ('a1, 'a3) Coq_env.coq_Env) coq_Inst

  val lift_env :
    ('a1 -> ('a2, 'a3) coq_Lift) -> 'a1 Coq_ctx.coq_Ctx -> (('a1, 'a2)
    Coq_env.coq_Env, ('a1, 'a3) Coq_env.coq_Env) coq_Lift

  val inst_term : Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Val) coq_Inst

  val lift_term : Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Val) coq_Lift

  val inst_sub :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_Sub, ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
    Coq_env.coq_Env) coq_Inst

  val inst_unit : (coq_Unit, coq_unit) coq_Inst

  val lift_unit : (coq_Unit, coq_unit) coq_Lift

  val inst_pair :
    ('a1, 'a3) coq_Inst -> ('a2, 'a4) coq_Inst -> (('a1, 'a2) coq_Pair, ('a3,
    'a4) prod) coq_Inst

  val lift_pair :
    ('a1, 'a3) coq_Lift -> ('a2, 'a4) coq_Lift -> (('a1, 'a2) coq_Pair, ('a3,
    'a4) prod) coq_Lift

  val inst_option :
    ('a1, 'a2) coq_Inst -> ('a1 coq_Option, 'a2 option) coq_Inst

  val lift_option :
    ('a1, 'a2) coq_Lift -> ('a1 coq_Option, 'a2 option) coq_Lift

  val inst_store :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_SStore, (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv)
    coq_Inst

  val term_get_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> Coq_ty.coq_Val option

  val term_get_pair :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Term -> (coq_Term, coq_Term) prod
    option

  val term_get_sum :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Term -> (coq_Term, coq_Term) sum
    option

  val term_get_list :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> ((coq_Term, coq_Term) prod, coq_unit) sum
    option

  val term_get_union :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.unioni -> coq_Term -> (Coq_ty.unionk, coq_Term) sigT option

  val term_get_record :
    Coq_ty.recordi -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Term -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term)
    coq_NamedEnv option

  val term_get_tuple :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term -> (Coq_ty.coq_Ty,
    coq_Term) Coq_env.coq_Env option

  module Entailment :
   sig
    module Coq_tactics :
     sig
     end
   end

  type ('t, 'tE) coq_Erase =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't -> 'tE

  val erase :
    ('a1, 'a2) coq_Erase -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> 'a2

  val erase_Unit : (coq_Unit, coq_unit) coq_Erase

  val erase_Const : ('a1 coq_Const, 'a1) coq_Erase

  val erase_Ctx :
    ('a1, 'a2) coq_Erase -> ('a1 Coq_ctx.coq_Ctx, 'a2 list) coq_Erase

  val erase_List : ('a1, 'a2) coq_Erase -> ('a1 list, 'a2 list) coq_Erase

  val erase_Term : Coq_ty.coq_Ty -> (coq_Term, coq_ETerm) coq_Erase

  val coq_EraseSStore :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_SStore, (coq_PVar, Coq_ty.coq_Ty, coq_ETerm) coq_NamedEnv) coq_Erase

  module Coq_amsg :
   sig
    type 'm coq_CloseMessage =
    | Coq_there of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding * 'm

    val coq_CloseMessage_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1 -> 'a2) -> 'a1
      coq_CloseMessage -> 'a2

    val coq_CloseMessage_rec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1 -> 'a2) -> 'a1
      coq_CloseMessage -> 'a2

    val subst_closemessage : 'a1 coq_Subst -> 'a1 coq_CloseMessage coq_Subst

    val substSU_closemessage :
      (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a1
      coq_CloseMessage) coq_SubstSU

    val substlaws_closemessage :
      'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_CloseMessage coq_SubstLaws

    val occurscheck_closemessage :
      'a1 coq_OccursCheck -> 'a1 coq_CloseMessage coq_OccursCheck

    val erase_closemessage :
      ('a1, 'a2) coq_Erase -> ('a1 coq_CloseMessage, 'a2) coq_Erase

    type coq_AMessage =
    | Coq_mk of __ coq_Subst * (coq_WeakensTo, __) coq_SubstSU
       * __ coq_SubstLaws * __ coq_OccursCheck * (__, __) coq_Erase * 
       __

    val coq_AMessage_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (__ ->
      __ coq_Subst -> (coq_WeakensTo, __) coq_SubstSU -> __ -> __
      coq_SubstLaws -> __ coq_OccursCheck -> __ -> (__, __) coq_Erase -> __
      -> 'a1) -> coq_AMessage -> 'a1

    val coq_AMessage_rec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (__ ->
      __ coq_Subst -> (coq_WeakensTo, __) coq_SubstSU -> __ -> __
      coq_SubstLaws -> __ coq_OccursCheck -> __ -> (__, __) coq_Erase -> __
      -> 'a1) -> coq_AMessage -> 'a1

    val empty :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_AMessage

    val closeAux :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_WeakensTo, 'a1) coq_SubstSU -> 'a1 coq_Subst -> 'a1 coq_SubstLaws
      -> 'a1 coq_OccursCheck -> ('a1, 'a2) coq_Erase -> 'a1 -> coq_AMessage

    val close :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_AMessage -> coq_AMessage

    val subst_amessage : coq_AMessage coq_Subst

    val substSU_amessage : (coq_WeakensTo, coq_AMessage) coq_SubstSU

    val substlaws_amessage : coq_AMessage coq_SubstLaws

    val occurscheck_amessage :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_AMessage ->
      coq_AMessage option

    type coq_EAMessage =
      __
      (* singleton inductive, whose constructor was MkEAMessage *)

    val coq_EAMessage_rect : (__ -> __ -> 'a1) -> coq_EAMessage -> 'a1

    val coq_EAMessage_rec : (__ -> __ -> 'a1) -> coq_EAMessage -> 'a1

    val erase_amessage : (coq_AMessage, coq_EAMessage) coq_Erase

    val boxMsg :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_AMessage -> coq_AMessage

    val genoccurscheck_amessage :
      (coq_WeakensTo, coq_AMessage) coq_GenOccursCheck
   end

  type coq_TermRing = { tmr_zero : Coq_ty.coq_Val; tmr_one : Coq_ty.coq_Val;
                        tmr_plus : Coq_bop.coq_BinOp;
                        tmr_times : Coq_bop.coq_BinOp;
                        tmr_minus : Coq_bop.coq_BinOp;
                        tmr_negate : Coq_uop.coq_UnOp;
                        tmr_of_Z : (coq_Z -> Coq_ty.coq_Val) }

  val tmr_zero :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_ty.coq_Val

  val tmr_one :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_ty.coq_Val

  val tmr_plus :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp

  val tmr_times :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp

  val tmr_minus :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp

  val tmr_negate :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_uop.coq_UnOp

  val tmr_of_Z :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> coq_Z -> Coq_ty.coq_Val

  val coq_TermRing_int :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_TermRing

  val coq_TermRing_bv :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_TermRing

  val evalPExprTm :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> coq_Term list -> coq_Z coq_PExpr ->
    coq_Term

  type coq_RQuote =
    coq_Term list -> positive -> (coq_Z coq_PExpr, coq_Term list) prod

  val coq_Term_Quote_def :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_RQuote

  val coq_Term_Quote_unop :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_Z coq_PExpr -> coq_Z coq_PExpr) -> coq_RQuote ->
    coq_RQuote

  val coq_Term_Quote_bin :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> (coq_Z coq_PExpr -> coq_Z coq_PExpr ->
    coq_Z coq_PExpr) -> coq_RQuote -> coq_RQuote -> coq_RQuote

  type coq_CanonTerm = __

  val peval_append :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term -> coq_Term

  val peval_and_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term
    -> Coq_ty.coq_Val -> coq_Term

  val peval_or_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term
    -> Coq_ty.coq_Val -> coq_Term

  val peval_and :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term
    -> coq_Term -> coq_Term

  val peval_or :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term
    -> coq_Term -> coq_Term

  val peval_plus :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term
    -> coq_Term -> coq_Term

  type peval_plus_graph =
  | Coq_peval_plus_graph_equation_1 of coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_2 of coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_3 of coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * 
     positive
  | Coq_peval_plus_graph_equation_4 of coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * 
     positive
  | Coq_peval_plus_graph_equation_5 of coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_plus_graph_equation_6 of coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_7 of coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_8 of positive * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_9 of positive * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_10 of Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_plus_graph_equation_11 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_12 of positive * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_13 of positive * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_14 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term
  | Coq_peval_plus_graph_equation_15 of positive * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_16 of positive * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_17 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_18 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_19 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * positive
  | Coq_peval_plus_graph_equation_20 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * positive
  | Coq_peval_plus_graph_equation_21 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_22 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_23 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_24 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term
  | Coq_peval_plus_graph_equation_25 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * positive
  | Coq_peval_plus_graph_equation_26 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * positive
  | Coq_peval_plus_graph_equation_27 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_28 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term

  val peval_plus_graph_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> positive -> 'a1) ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> positive -> 'a1) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (positive -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (positive -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (positive -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> coq_LVar
    -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
    -> coq_Term -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive ->
    'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> coq_Term -> coq_Term -> coq_Term -> peval_plus_graph
    -> 'a1

  val peval_plus_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term
    -> coq_Term -> peval_plus_graph

  val peval_plus_elim :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> positive -> 'a1) ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> positive -> 'a1) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (positive -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (positive -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (positive -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> coq_LVar
    -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
    -> coq_Term -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive ->
    'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> coq_Term -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_plus :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> positive -> __) ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> positive -> __) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (positive -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> (positive -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
    (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (positive -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
    -> coq_Term -> coq_Term -> positive -> __) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive ->
    __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
    -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> positive ->
    __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> positive -> __)
    -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_plus :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_Term -> coq_Term -> coq_Term) coq_FunctionalInduction

  val peval_bvadd :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> coq_Term

  type peval_bvadd_graph =
  | Coq_peval_bvadd_graph_equation_1 of nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_2 of nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_3 of nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * 
     positive
  | Coq_peval_bvadd_graph_equation_4 of nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvadd_graph_equation_5 of nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_6 of nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_7 of nat * positive * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_8 of nat * Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_bvadd_graph_equation_9 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_10 of nat * positive * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_11 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_12 of nat * positive * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_13 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_14 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_15 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * positive
  | Coq_peval_bvadd_graph_equation_16 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_17 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_18 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_19 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_20 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * positive
  | Coq_peval_bvadd_graph_equation_21 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_22 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term

  val peval_bvadd_graph_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __ -> 'a1) -> (nat -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> positive
    -> __ -> 'a1) -> (nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> __ ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (nat -> positive -> __ -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> positive -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> __ ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> positive
    -> __ -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __ -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> positive -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> __ -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> coq_Term -> coq_Term ->
    coq_Term -> peval_bvadd_graph -> 'a1

  val peval_bvadd_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> peval_bvadd_graph

  val peval_bvadd_elim :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __ -> 'a1) -> (nat -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> positive
    -> __ -> 'a1) -> (nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> __ ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (nat -> positive -> __ -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> positive -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> __ ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> positive
    -> __ -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __ -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> positive -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> __ -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> coq_Term -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvadd :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> (nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __ -> __) -> (nat -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> positive
    -> __ -> __) -> (nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> __ ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> __) -> (nat -> positive -> __ -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> __) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> positive ->
    __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> __) -> (nat -> positive -> __ -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> __ -> __) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive -> __ -> __) ->
    (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __ -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> __ -> __) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> nat -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_bvadd :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term -> coq_Term) coq_FunctionalInduction

  val peval_bvand_val_default :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvand_bvapp_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvand_bvcons_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> coq_Term

  val peval_bvand_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  type peval_bvand_val_graph =
  | Coq_peval_bvand_val_graph_equation_1 of nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_2 of nat * Coq_ty.coq_Val
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_3 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_4 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_5 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_6 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_7 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_8 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_9 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_10 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_11 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_12 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_14 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Val

  val peval_bvand_val_graph_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term -> peval_bvand_val_graph -> 'a1

  val peval_bvand_val_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> peval_bvand_val_graph

  val peval_bvand_val_elim :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> 'a1

  val coq_FunctionalElimination_peval_bvand_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> nat -> __ -> coq_Term
    -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> __) -> nat -> coq_Term
    -> Coq_ty.coq_Val -> __

  val coq_FunctionalInduction_peval_bvand_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) coq_FunctionalInduction

  val peval_bvand :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> coq_Term

  type peval_bvand_graph =
  | Coq_peval_bvand_graph_equation_1 of nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * 
     coq_Term
  | Coq_peval_bvand_graph_equation_2 of nat * Coq_ty.coq_Val * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvand_graph_equation_3 of nat * Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_bvand_graph_equation_4 of nat * Coq_ty.coq_Val * nat * 
     coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_5 of nat * Coq_ty.coq_Val * nat * 
     coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_6 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_7 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_8 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_9 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_10 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_11 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_12 of nat * nat * Coq_ty.coq_Val
     * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_13 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_14 of nat * Coq_ty.coq_Val * nat * 
     nat * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_15 of nat * Coq_ty.coq_Val * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvand_graph_equation_16 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_17 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_18 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_19 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_20 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_21 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_22 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_23 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_24 of nat * nat * coq_Term * coq_Term
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvand_graph_equation_25 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_graph_equation_26 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvand_graph_equation_27 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvand_graph_equation_28 of nat * coq_Term * coq_Term * 
     coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvand_graph_equation_29 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_graph_equation_30 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvand_graph_equation_31 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvand_graph_equation_32 of nat * nat * nat * coq_Term
     * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_33 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * coq_Term

  val peval_bvand_graph_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
    nat -> __ -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat
    -> coq_Term -> coq_Term -> coq_Term -> peval_bvand_graph -> 'a1

  val peval_bvand_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> peval_bvand_graph

  val peval_bvand_elim :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
    nat -> __ -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat
    -> coq_Term -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvand :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> nat
    -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> nat ->
    coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __)
    -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term
    -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> __) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> __) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat
    -> nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term
    -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
    nat -> __ -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> __) -> nat
    -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_bvand :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term -> coq_Term) coq_FunctionalInduction

  val peval_bvor_val_default :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvor_bvapp_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvor_bvcons_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> coq_Term

  val peval_bvor_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  type peval_bvor_val_graph =
  | Coq_peval_bvor_val_graph_equation_1 of nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_2 of nat * Coq_ty.coq_Val
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_3 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_4 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_5 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_6 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_7 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_8 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_9 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_10 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_11 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_12 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_14 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Val

  val peval_bvor_val_graph_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term -> peval_bvor_val_graph -> 'a1

  val peval_bvor_val_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> peval_bvor_val_graph

  val peval_bvor_val_elim :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> 'a1

  val coq_FunctionalElimination_peval_bvor_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> nat -> __ -> coq_Term
    -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> __) -> nat -> coq_Term
    -> Coq_ty.coq_Val -> __

  val coq_FunctionalInduction_peval_bvor_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) coq_FunctionalInduction

  val peval_bvor :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> coq_Term

  type peval_bvor_graph =
  | Coq_peval_bvor_graph_equation_1 of nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * 
     coq_Term
  | Coq_peval_bvor_graph_equation_2 of nat * Coq_ty.coq_Val * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvor_graph_equation_3 of nat * Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_bvor_graph_equation_4 of nat * Coq_ty.coq_Val * nat * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_5 of nat * Coq_ty.coq_Val * nat * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_6 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_7 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_8 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_9 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_10 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_11 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_12 of nat * nat * Coq_ty.coq_Val * 
     coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_13 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_14 of nat * Coq_ty.coq_Val * nat * 
     nat * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_15 of nat * Coq_ty.coq_Val * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvor_graph_equation_16 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_17 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_18 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_19 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_20 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_21 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_22 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_23 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_24 of nat * nat * coq_Term * coq_Term
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvor_graph_equation_25 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_graph_equation_26 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvor_graph_equation_27 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvor_graph_equation_28 of nat * coq_Term * coq_Term * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvor_graph_equation_29 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_graph_equation_30 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvor_graph_equation_31 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvor_graph_equation_32 of nat * nat * nat * coq_Term * 
     coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_33 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * coq_Term

  val peval_bvor_graph_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
    nat -> __ -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat
    -> coq_Term -> coq_Term -> coq_Term -> peval_bvor_graph -> 'a1

  val peval_bvor_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> peval_bvor_graph

  val peval_bvor_elim :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
    nat -> __ -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat
    -> coq_Term -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvor :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> nat
    -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> nat ->
    coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __)
    -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term
    -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> __) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> __) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat
    -> nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term
    -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
    nat -> __ -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> __) -> nat
    -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_bvor :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term -> coq_Term) coq_FunctionalInduction

  val peval_bvapp_val_r :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvapp :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> coq_Term -> coq_Term -> coq_Term

  type peval_bvapp_graph =
  | Coq_peval_bvapp_graph_equation_1 of nat * nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_2 of nat * nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_3 of nat * nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_4 of nat * nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_5 of nat * nat * Coq_ty.coq_Val * 
     coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_6 of nat * nat * Coq_ty.coq_Val
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_7 of nat * nat * Coq_ty.coq_Val
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_8 of nat * nat * Coq_ty.coq_Val
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_9 of nat * nat * nat * coq_Term * 
     coq_Term * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_10 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_11 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_12 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_14 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_15 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_16 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_17 of nat * nat * coq_Term * coq_Term
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_18 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_19 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_20 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_21 of nat * nat * coq_Term * coq_Term
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_22 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_23 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_24 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_25 of nat * nat * coq_Term * coq_Term
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_26 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_27 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_28 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_29 of nat * nat * coq_Term * coq_Term
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_30 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_31 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_32 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_33 of nat * nat * coq_Term * coq_Term
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_34 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_35 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_36 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_37 of nat * nat * coq_Term * coq_Term
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_38 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_39 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_40 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_41 of nat * nat * nat * coq_Term
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_42 of nat * nat * coq_Term * coq_Term
     * coq_LVar * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_43 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_44 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_45 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_46 of nat * nat * nat * nat * coq_Term
     * coq_Term * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_47 of nat * nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_48 of nat * nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_49 of nat * nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_50 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_51 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_52 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_53 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term

  val peval_bvapp_graph_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
    -> (nat -> nat -> Coq_ty.coq_Val -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term ->
    coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
    nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> nat -> __ -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> nat -> coq_Term ->
    coq_Term -> coq_Term -> peval_bvapp_graph -> 'a1

  val peval_bvapp_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> coq_Term -> coq_Term -> peval_bvapp_graph

  val peval_bvapp_elim :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
    -> (nat -> nat -> Coq_ty.coq_Val -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term ->
    coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
    nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> nat -> __ -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> nat -> coq_Term ->
    coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvapp :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_LVar ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat
    -> nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) ->
    (nat -> nat -> Coq_ty.coq_Val -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) -> (nat -> nat -> Coq_ty.coq_Val
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat -> nat -> coq_Term ->
    coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
    nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_Term -> __) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> __) -> (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> __) -> (nat -> nat -> nat -> nat -> __ -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (nat -> nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> __) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    Coq_ty.coq_Val -> __) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (nat -> nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> __) -> nat -> nat -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_bvapp :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    nat -> coq_Term -> coq_Term -> coq_Term) coq_FunctionalInduction

  val peval_bvdrop_bvapp :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term -> coq_Term

  val peval_bvdrop_bvcons :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat ->
    coq_Term -> coq_Term -> coq_Term

  val peval_bvdrop_bvdrop :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term

  val peval_bvdrop_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> Coq_ty.coq_Val -> coq_Term

  val peval_bvdrop_default :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> coq_Term -> coq_Term

  val peval_bvdrop_eq :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> coq_Term -> coq_Term

  val peval_bvdrop :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> coq_Term -> coq_Term

  val peval_bvtake_bvapp :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term -> coq_Term

  val peval_bvtake_bvcons :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat ->
    coq_Term -> coq_Term -> coq_Term

  val peval_bvtake_bvtake :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term

  val peval_bvtake_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> Coq_ty.coq_Val -> coq_Term

  val peval_bvtake_default :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> coq_Term -> coq_Term

  val peval_bvtake_eq :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> coq_Term -> coq_Term

  val peval_bvtake :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> coq_Term -> coq_Term

  val peval_update_vector_subrange :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> coq_Term -> coq_Term -> coq_Term

  val peval_binop' :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> coq_Term

  val peval_binop :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> coq_Term

  val peval_not :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term
    -> coq_Term

  type peval_not_graph =
  | Coq_peval_not_graph_equation_1 of coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_not_graph_equation_2 of Coq_ty.coq_Val
  | Coq_peval_not_graph_equation_3 of coq_Term * coq_Term * peval_not_graph
     * peval_not_graph
  | Coq_peval_not_graph_equation_4 of coq_Term * coq_Term * peval_not_graph
     * peval_not_graph
  | Coq_peval_not_graph_equation_5 of Coq_ty.coq_Ty * Coq_bop.coq_RelOp
     * coq_Term * coq_Term
  | Coq_peval_not_graph_equation_6 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term

  val peval_not_graph_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term ->
    peval_not_graph -> 'a1 -> peval_not_graph -> 'a1 -> 'a1) -> (coq_Term ->
    coq_Term -> peval_not_graph -> 'a1 -> peval_not_graph -> 'a1 -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> coq_Term ->
    coq_Term -> peval_not_graph -> 'a1

  val peval_not_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term
    -> peval_not_graph

  val peval_not_elim :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1
    -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty
    -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_not :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> __) -> (Coq_ty.coq_Val -> __) -> (coq_Term -> coq_Term -> __ -> __ ->
    __) -> (coq_Term -> coq_Term -> __ -> __ -> __) -> (Coq_ty.coq_Ty ->
    Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> __) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> coq_Term -> __

  val coq_FunctionalInduction_peval_not :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_Term -> coq_Term) coq_FunctionalInduction

  val peval_unsigned_bvapp :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> coq_Term -> coq_Term -> coq_Term

  val peval_unsigned :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term

  type peval_unsigned_graph =
  | Coq_peval_unsigned_graph_equation_1 of nat * coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_unsigned_graph_equation_2 of nat * Coq_ty.coq_Val
  | Coq_peval_unsigned_graph_equation_3 of nat * nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_4 of nat * nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_5 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_6 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_7 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_8 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_9 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_10 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_11 of nat * nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_12 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term
  | Coq_peval_unsigned_graph_equation_14 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term

  val peval_unsigned_graph_rect :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> nat -> coq_Term -> coq_Term -> peval_unsigned_graph
    -> 'a1

  val peval_unsigned_graph_correct :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> peval_unsigned_graph

  val peval_unsigned_elim :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> nat -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_unsigned :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> __) -> (nat -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term -> __) -> (nat ->
    coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> __) ->
    (nat -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term ->
    __) -> (nat -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term -> __) -> (nat ->
    coq_Term -> coq_Term -> __) -> (nat -> nat -> nat -> __ -> coq_Term ->
    coq_Term -> __) -> (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> __) -> nat -> coq_Term -> __

  val coq_FunctionalInduction_peval_unsigned :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term) coq_FunctionalInduction

  val peval_vector_subrange :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> nat -> coq_Term -> coq_Term

  val peval_unop' :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term

  val peval_zext :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    nat -> coq_Term -> coq_Term

  val peval_unop :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term

  val evalPolTm :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> coq_Term list -> coq_Z coq_Pol ->
    coq_Term

  val coq_CanonTerm_to_Term :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_CanonTerm -> coq_Term

  val peval_union :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.unioni -> Coq_ty.unionk -> coq_Term -> coq_Term

  val peval_record' :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) coq_NamedEnv ->
    (Coq_ty.recordf, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv option

  val peval_record :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) coq_NamedEnv
    -> coq_Term

  val coq_CanonTerm_def :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_CanonTerm

  val peval2_val :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> coq_CanonTerm

  val peval2_binop :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_CanonTerm -> coq_CanonTerm -> coq_CanonTerm

  val peval2_unop :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_CanonTerm ->
    coq_CanonTerm

  val peval2 :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_CanonTerm

  val peval :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term

  val pevals :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Term)
    Coq_env.coq_Env -> (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env

  type 'n coq_SMatchResult =
    ('n coq_PatternCase, ('n, Coq_ty.coq_Ty, coq_Term) coq_NamedEnv) sigT

  val pattern_match_term_reverse :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
    Coq_ty.coq_Ty, coq_Term) coq_NamedEnv -> coq_Term

  val seval_exp :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_SStore -> Coq_ty.coq_Ty -> coq_Exp -> coq_Term

  val seval_exps :
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_SStore -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    ('a1, Coq_ty.coq_Ty, coq_Exp) coq_NamedEnv -> ('a1, Coq_ty.coq_Ty,
    coq_Term) coq_NamedEnv

  type 'p coq_Precise = { prec_input : Coq_ty.coq_Ty Coq_ctx.coq_Ctx;
                          prec_output : Coq_ty.coq_Ty Coq_ctx.coq_Ctx }

  val prec_input :
    ('a1 -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx) -> 'a1 -> 'a1 coq_Precise ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx

  val prec_output :
    ('a1 -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx) -> 'a1 -> 'a1 coq_Precise ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx
 end
