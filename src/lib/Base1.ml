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
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val xlen : nat **)

let xlen =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))

(** val byte : nat **)

let byte =
  S (S (S (S (S (S (S (S O)))))))

(** val bytes_per_word : nat **)

let bytes_per_word =
  S (S (S (S O)))

(** val bytes_per_instr : nat **)

let bytes_per_instr =
  S (S (S (S O)))

(** val word : nat **)

let word =
  mul bytes_per_word byte

(** val xlenbytes : nat **)

let xlenbytes =
  S (S (S (S O)))

(** val xlenbits : nat **)

let xlenbits =
  mul xlenbytes byte

(** val bv_instrsize : nat -> Coq_bv.bv **)

let bv_instrsize n =
  Coq_bv.of_nat n bytes_per_instr

type coq_Xlenbits = Coq_bv.bv

type coq_Addr = Coq_bv.bv

type coq_Word = Coq_bv.bv

type coq_Byte = Coq_bv.bv

(** val minAddr : coq_N **)

let minAddr =
  N0

(** val lenAddr : coq_N **)

let lenAddr =
  BinNat.N.pow (Npos (Coq_xO Coq_xH)) (Npos (Coq_xO (Coq_xI (Coq_xO Coq_xH))))

(** val maxAddr : coq_N **)

let maxAddr =
  BinNat.N.add minAddr lenAddr

(** val mmioStartAddr : coq_N **)

let mmioStartAddr =
  maxAddr

(** val mmioLenAddr : coq_N **)

let mmioLenAddr =
  BinNat.N.add maxAddr lenAddr

(** val mmioAddrs : coq_Addr list **)

let mmioAddrs =
  Coq_bv.seqBv xlenbits (Coq_bv.of_N xlenbits mmioStartAddr) mmioLenAddr

(** val withinMMIODec : coq_Addr -> nat -> coq_Decision **)

let rec withinMMIODec a = function
| O -> coq_False_dec
| S n ->
  (match n with
   | O ->
     decide_rel
       (elem_of_list_dec
         (coq_EqDecision_from_EqDec (Coq_bv.eqdec_bv xlenbits)))
       a mmioAddrs
   | S _ ->
     and_dec
       (decide_rel
         (elem_of_list_dec
           (coq_EqDecision_from_EqDec (Coq_bv.eqdec_bv xlenbits)))
         a mmioAddrs)
       (withinMMIODec
         (Coq_bv.add (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S
           O)))))))))))))))))))))))))))))))) (Npos Coq_xH) a)
         n))

type coq_Minterrupts = { coq_MEI : bool; coq_UEI : bool; coq_MTI : bool;
                         coq_UTI : bool; coq_MSI : bool; coq_USI : bool }

type coq_MMIOEnv = { state_tra_read : (__ -> coq_Addr -> nat -> (__,
                                      Coq_bv.bv) prod);
                     state_tra_write : (__ -> coq_Addr -> nat -> Coq_bv.bv ->
                                       __);
                     state_tra_world_updates : (__ -> (coq_Minterrupts, __)
                                               prod);
                     state_init : __ }

type coq_State = __

(** val mmioenv : coq_MMIOEnv **)

let mmioenv =
  failwith "AXIOM TO BE REALIZED (Katamaran.RiscvPmp.Base.mmioenv)"

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

(** val coq_Enums_eqdec : coq_Enums -> coq_Enums -> coq_Enums dec_eq **)

let coq_Enums_eqdec x y =
  match x with
  | Coq_privilege -> (match y with
                      | Coq_privilege -> Coq_left
                      | _ -> Coq_right)
  | Coq_interruptType ->
    (match y with
     | Coq_interruptType -> Coq_left
     | _ -> Coq_right)
  | Coq_csridx -> (match y with
                   | Coq_csridx -> Coq_left
                   | _ -> Coq_right)
  | Coq_pmpcfgidx -> (match y with
                      | Coq_pmpcfgidx -> Coq_left
                      | _ -> Coq_right)
  | Coq_pmpcfgperm ->
    (match y with
     | Coq_pmpcfgperm -> Coq_left
     | _ -> Coq_right)
  | Coq_pmpaddridx ->
    (match y with
     | Coq_pmpaddridx -> Coq_left
     | _ -> Coq_right)
  | Coq_pmpaddrmatchtype ->
    (match y with
     | Coq_pmpaddrmatchtype -> Coq_left
     | _ -> Coq_right)
  | Coq_pmpmatch -> (match y with
                     | Coq_pmpmatch -> Coq_left
                     | _ -> Coq_right)
  | Coq_pmpaddrmatch ->
    (match y with
     | Coq_pmpaddrmatch -> Coq_left
     | _ -> Coq_right)
  | Coq_rop -> (match y with
                | Coq_rop -> Coq_left
                | _ -> Coq_right)
  | Coq_iop -> (match y with
                | Coq_iop -> Coq_left
                | _ -> Coq_right)
  | Coq_sop -> (match y with
                | Coq_sop -> Coq_left
                | _ -> Coq_right)
  | Coq_uop -> (match y with
                | Coq_uop -> Coq_left
                | _ -> Coq_right)
  | Coq_bop -> (match y with
                | Coq_bop -> Coq_left
                | _ -> Coq_right)
  | Coq_csrop -> (match y with
                  | Coq_csrop -> Coq_left
                  | _ -> Coq_right)
  | Coq_retired -> (match y with
                    | Coq_retired -> Coq_left
                    | _ -> Coq_right)
  | Coq_wordwidth -> (match y with
                      | Coq_wordwidth -> Coq_left
                      | _ -> Coq_right)
  | Coq_mop -> (match y with
                | Coq_mop -> Coq_left
                | _ -> Coq_right)

(** val coq_Enums_EqDec : coq_Enums coq_EqDec **)

let coq_Enums_EqDec =
  coq_Enums_eqdec

(** val coq_Privilege_eqdec :
    coq_Privilege -> coq_Privilege -> coq_Privilege dec_eq **)

let coq_Privilege_eqdec x y =
  match x with
  | User -> (match y with
             | User -> Coq_left
             | Machine -> Coq_right)
  | Machine -> (match y with
                | User -> Coq_right
                | Machine -> Coq_left)

(** val coq_Privilege_EqDec : coq_Privilege coq_EqDec **)

let coq_Privilege_EqDec =
  coq_Privilege_eqdec

(** val coq_CSRIdx_eqdec : coq_CSRIdx -> coq_CSRIdx -> coq_CSRIdx dec_eq **)

let coq_CSRIdx_eqdec x y =
  match x with
  | MStatus -> (match y with
                | MStatus -> Coq_left
                | _ -> Coq_right)
  | Mie -> (match y with
            | Mie -> Coq_left
            | _ -> Coq_right)
  | MTvec -> (match y with
              | MTvec -> Coq_left
              | _ -> Coq_right)
  | MScratch -> (match y with
                 | MScratch -> Coq_left
                 | _ -> Coq_right)
  | MEpc -> (match y with
             | MEpc -> Coq_left
             | _ -> Coq_right)
  | MCause -> (match y with
               | MCause -> Coq_left
               | _ -> Coq_right)
  | MPMP0CFG -> (match y with
                 | MPMP0CFG -> Coq_left
                 | _ -> Coq_right)
  | Mip -> (match y with
            | Mip -> Coq_left
            | _ -> Coq_right)
  | MPMPADDR0 -> (match y with
                  | MPMPADDR0 -> Coq_left
                  | _ -> Coq_right)
  | MPMPADDR1 -> (match y with
                  | MPMPADDR1 -> Coq_left
                  | _ -> Coq_right)

(** val coq_CSRIdx_EqDec : coq_CSRIdx coq_EqDec **)

let coq_CSRIdx_EqDec =
  coq_CSRIdx_eqdec

(** val coq_PmpCfgIdx_eqdec :
    coq_PmpCfgIdx -> coq_PmpCfgIdx -> coq_PmpCfgIdx dec_eq **)

let coq_PmpCfgIdx_eqdec x y =
  match x with
  | PMP0CFG -> (match y with
                | PMP0CFG -> Coq_left
                | PMP1CFG -> Coq_right)
  | PMP1CFG -> (match y with
                | PMP0CFG -> Coq_right
                | PMP1CFG -> Coq_left)

(** val coq_PmpCfgIdx_EqDec : coq_PmpCfgIdx coq_EqDec **)

let coq_PmpCfgIdx_EqDec =
  coq_PmpCfgIdx_eqdec

(** val coq_PmpCfgPerm_eqdec :
    coq_PmpCfgPerm -> coq_PmpCfgPerm -> coq_PmpCfgPerm dec_eq **)

let coq_PmpCfgPerm_eqdec x y =
  match x with
  | PmpO -> (match y with
             | PmpO -> Coq_left
             | _ -> Coq_right)
  | PmpR -> (match y with
             | PmpR -> Coq_left
             | _ -> Coq_right)
  | PmpW -> (match y with
             | PmpW -> Coq_left
             | _ -> Coq_right)
  | PmpX -> (match y with
             | PmpX -> Coq_left
             | _ -> Coq_right)
  | PmpRW -> (match y with
              | PmpRW -> Coq_left
              | _ -> Coq_right)
  | PmpRX -> (match y with
              | PmpRX -> Coq_left
              | _ -> Coq_right)
  | PmpWX -> (match y with
              | PmpWX -> Coq_left
              | _ -> Coq_right)
  | PmpRWX -> (match y with
               | PmpRWX -> Coq_left
               | _ -> Coq_right)

(** val coq_PmpCfgPerm_EqDec : coq_PmpCfgPerm coq_EqDec **)

let coq_PmpCfgPerm_EqDec =
  coq_PmpCfgPerm_eqdec

(** val coq_PmpAddrIdx_eqdec :
    coq_PmpAddrIdx -> coq_PmpAddrIdx -> coq_PmpAddrIdx dec_eq **)

let coq_PmpAddrIdx_eqdec x y =
  match x with
  | PMPADDR0 -> (match y with
                 | PMPADDR0 -> Coq_left
                 | PMPADDR1 -> Coq_right)
  | PMPADDR1 -> (match y with
                 | PMPADDR0 -> Coq_right
                 | PMPADDR1 -> Coq_left)

(** val coq_PmpAddrIdx_EqDec : coq_PmpAddrIdx coq_EqDec **)

let coq_PmpAddrIdx_EqDec =
  coq_PmpAddrIdx_eqdec

(** val coq_PmpAddrMatchType_eqdec :
    coq_PmpAddrMatchType -> coq_PmpAddrMatchType -> coq_PmpAddrMatchType
    dec_eq **)

let coq_PmpAddrMatchType_eqdec x y =
  match x with
  | OFF -> (match y with
            | OFF -> Coq_left
            | TOR -> Coq_right)
  | TOR -> (match y with
            | OFF -> Coq_right
            | TOR -> Coq_left)

(** val coq_PmpAddrMatchType_EqDec : coq_PmpAddrMatchType coq_EqDec **)

let coq_PmpAddrMatchType_EqDec =
  coq_PmpAddrMatchType_eqdec

(** val coq_PmpMatch_eqdec :
    coq_PmpMatch -> coq_PmpMatch -> coq_PmpMatch dec_eq **)

let coq_PmpMatch_eqdec x y =
  match x with
  | PMP_Success -> (match y with
                    | PMP_Success -> Coq_left
                    | _ -> Coq_right)
  | PMP_Continue -> (match y with
                     | PMP_Continue -> Coq_left
                     | _ -> Coq_right)
  | PMP_Fail -> (match y with
                 | PMP_Fail -> Coq_left
                 | _ -> Coq_right)

(** val coq_PmpMatch_EqDec : coq_PmpMatch coq_EqDec **)

let coq_PmpMatch_EqDec =
  coq_PmpMatch_eqdec

(** val coq_PmpAddrMatch_eqdec :
    coq_PmpAddrMatch -> coq_PmpAddrMatch -> coq_PmpAddrMatch dec_eq **)

let coq_PmpAddrMatch_eqdec x y =
  match x with
  | PMP_NoMatch -> (match y with
                    | PMP_NoMatch -> Coq_left
                    | _ -> Coq_right)
  | PMP_PartialMatch ->
    (match y with
     | PMP_PartialMatch -> Coq_left
     | _ -> Coq_right)
  | PMP_Match -> (match y with
                  | PMP_Match -> Coq_left
                  | _ -> Coq_right)

(** val coq_PmpAddrMatch_EqDec : coq_PmpAddrMatch coq_EqDec **)

let coq_PmpAddrMatch_EqDec =
  coq_PmpAddrMatch_eqdec

(** val coq_ROP_eqdec : coq_ROP -> coq_ROP -> coq_ROP dec_eq **)

let coq_ROP_eqdec x y =
  match x with
  | RISCV_ADD -> (match y with
                  | RISCV_ADD -> Coq_left
                  | _ -> Coq_right)
  | RISCV_SLT -> (match y with
                  | RISCV_SLT -> Coq_left
                  | _ -> Coq_right)
  | RISCV_SLTU -> (match y with
                   | RISCV_SLTU -> Coq_left
                   | _ -> Coq_right)
  | RISCV_AND -> (match y with
                  | RISCV_AND -> Coq_left
                  | _ -> Coq_right)
  | RISCV_OR -> (match y with
                 | RISCV_OR -> Coq_left
                 | _ -> Coq_right)
  | RISCV_XOR -> (match y with
                  | RISCV_XOR -> Coq_left
                  | _ -> Coq_right)
  | RISCV_SLL -> (match y with
                  | RISCV_SLL -> Coq_left
                  | _ -> Coq_right)
  | RISCV_SRL -> (match y with
                  | RISCV_SRL -> Coq_left
                  | _ -> Coq_right)
  | RISCV_SUB -> (match y with
                  | RISCV_SUB -> Coq_left
                  | _ -> Coq_right)
  | RISCV_SRA -> (match y with
                  | RISCV_SRA -> Coq_left
                  | _ -> Coq_right)

(** val coq_ROP_EqDec : coq_ROP coq_EqDec **)

let coq_ROP_EqDec =
  coq_ROP_eqdec

(** val coq_IOP_eqdec : coq_IOP -> coq_IOP -> coq_IOP dec_eq **)

let coq_IOP_eqdec x y =
  match x with
  | RISCV_ADDI -> (match y with
                   | RISCV_ADDI -> Coq_left
                   | _ -> Coq_right)
  | RISCV_SLTI -> (match y with
                   | RISCV_SLTI -> Coq_left
                   | _ -> Coq_right)
  | RISCV_SLTIU -> (match y with
                    | RISCV_SLTIU -> Coq_left
                    | _ -> Coq_right)
  | RISCV_ANDI -> (match y with
                   | RISCV_ANDI -> Coq_left
                   | _ -> Coq_right)
  | RISCV_ORI -> (match y with
                  | RISCV_ORI -> Coq_left
                  | _ -> Coq_right)
  | RISCV_XORI -> (match y with
                   | RISCV_XORI -> Coq_left
                   | _ -> Coq_right)

(** val coq_IOP_EqDec : coq_IOP coq_EqDec **)

let coq_IOP_EqDec =
  coq_IOP_eqdec

(** val coq_SOP_eqdec : coq_SOP -> coq_SOP -> coq_SOP dec_eq **)

let coq_SOP_eqdec x y =
  match x with
  | RISCV_SLLI -> (match y with
                   | RISCV_SLLI -> Coq_left
                   | _ -> Coq_right)
  | RISCV_SRLI -> (match y with
                   | RISCV_SRLI -> Coq_left
                   | _ -> Coq_right)
  | RISCV_SRAI -> (match y with
                   | RISCV_SRAI -> Coq_left
                   | _ -> Coq_right)

(** val coq_SOP_EqDec : coq_SOP coq_EqDec **)

let coq_SOP_EqDec =
  coq_SOP_eqdec

(** val coq_UOP_eqdec : coq_UOP -> coq_UOP -> coq_UOP dec_eq **)

let coq_UOP_eqdec x y =
  match x with
  | RISCV_LUI ->
    (match y with
     | RISCV_LUI -> Coq_left
     | RISCV_AUIPC -> Coq_right)
  | RISCV_AUIPC ->
    (match y with
     | RISCV_LUI -> Coq_right
     | RISCV_AUIPC -> Coq_left)

(** val coq_UOP_EqDec : coq_UOP coq_EqDec **)

let coq_UOP_EqDec =
  coq_UOP_eqdec

(** val coq_BOP_eqdec : coq_BOP -> coq_BOP -> coq_BOP dec_eq **)

let coq_BOP_eqdec x y =
  match x with
  | RISCV_BEQ -> (match y with
                  | RISCV_BEQ -> Coq_left
                  | _ -> Coq_right)
  | RISCV_BNE -> (match y with
                  | RISCV_BNE -> Coq_left
                  | _ -> Coq_right)
  | RISCV_BLT -> (match y with
                  | RISCV_BLT -> Coq_left
                  | _ -> Coq_right)
  | RISCV_BGE -> (match y with
                  | RISCV_BGE -> Coq_left
                  | _ -> Coq_right)
  | RISCV_BLTU -> (match y with
                   | RISCV_BLTU -> Coq_left
                   | _ -> Coq_right)
  | RISCV_BGEU -> (match y with
                   | RISCV_BGEU -> Coq_left
                   | _ -> Coq_right)

(** val coq_BOP_EqDec : coq_BOP coq_EqDec **)

let coq_BOP_EqDec =
  coq_BOP_eqdec

(** val coq_CSROP_eqdec : coq_CSROP -> coq_CSROP -> coq_CSROP dec_eq **)

let coq_CSROP_eqdec x y =
  match x with
  | CSRRW -> (match y with
              | CSRRW -> Coq_left
              | _ -> Coq_right)
  | CSRRS -> (match y with
              | CSRRS -> Coq_left
              | _ -> Coq_right)
  | CSRRC -> (match y with
              | CSRRC -> Coq_left
              | _ -> Coq_right)

(** val coq_CSROP_EqDec : coq_CSROP coq_EqDec **)

let coq_CSROP_EqDec =
  coq_CSROP_eqdec

(** val coq_MOP_eqdec : coq_MOP -> coq_MOP -> coq_MOP dec_eq **)

let coq_MOP_eqdec x y =
  match x with
  | RISCV_MUL -> (match y with
                  | RISCV_MUL -> Coq_left
                  | _ -> Coq_right)
  | RISCV_MULH -> (match y with
                   | RISCV_MULH -> Coq_left
                   | _ -> Coq_right)
  | RISCV_MULHSU -> (match y with
                     | RISCV_MULHSU -> Coq_left
                     | _ -> Coq_right)
  | RISCV_MULHU -> (match y with
                    | RISCV_MULHU -> Coq_left
                    | _ -> Coq_right)

(** val coq_MOP_EqDec : coq_MOP coq_EqDec **)

let coq_MOP_EqDec =
  coq_MOP_eqdec

(** val coq_Retired_eqdec :
    coq_Retired -> coq_Retired -> coq_Retired dec_eq **)

let coq_Retired_eqdec x y =
  match x with
  | RETIRE_SUCCESS ->
    (match y with
     | RETIRE_SUCCESS -> Coq_left
     | RETIRE_FAIL -> Coq_right)
  | RETIRE_FAIL ->
    (match y with
     | RETIRE_SUCCESS -> Coq_right
     | RETIRE_FAIL -> Coq_left)

(** val coq_Retired_EqDec : coq_Retired coq_EqDec **)

let coq_Retired_EqDec =
  coq_Retired_eqdec

(** val coq_WordWidth_eqdec :
    coq_WordWidth -> coq_WordWidth -> coq_WordWidth dec_eq **)

let coq_WordWidth_eqdec x y =
  match x with
  | BYTE -> (match y with
             | BYTE -> Coq_left
             | _ -> Coq_right)
  | HALF -> (match y with
             | HALF -> Coq_left
             | _ -> Coq_right)
  | WORD -> (match y with
             | WORD -> Coq_left
             | _ -> Coq_right)

(** val coq_WordWidth_EqDec : coq_WordWidth coq_EqDec **)

let coq_WordWidth_EqDec =
  coq_WordWidth_eqdec

(** val coq_Unions_eqdec : coq_Unions -> coq_Unions -> coq_Unions dec_eq **)

let coq_Unions_eqdec x y =
  match x with
  | Coq_ast -> (match y with
                | Coq_ast -> Coq_left
                | _ -> Coq_right)
  | Coq_access_type ->
    (match y with
     | Coq_access_type -> Coq_left
     | _ -> Coq_right)
  | Coq_exception_type ->
    (match y with
     | Coq_exception_type -> Coq_left
     | _ -> Coq_right)
  | Coq_memory_op_result bytes ->
    (match y with
     | Coq_memory_op_result bytes0 ->
       eq_dec_point bytes (coq_EqDec_EqDecPoint nat_EqDec bytes) bytes0
     | _ -> Coq_right)
  | Coq_fetch_result ->
    (match y with
     | Coq_fetch_result -> Coq_left
     | _ -> Coq_right)
  | Coq_ctl_result ->
    (match y with
     | Coq_ctl_result -> Coq_left
     | _ -> Coq_right)
  | Coq_interrupt_set ->
    (match y with
     | Coq_interrupt_set -> Coq_left
     | _ -> Coq_right)

(** val coq_Unions_EqDec : coq_Unions coq_EqDec **)

let coq_Unions_EqDec =
  coq_Unions_eqdec

(** val coq_AST_eqdec : coq_AST -> coq_AST -> coq_AST dec_eq **)

let coq_AST_eqdec x y =
  match x with
  | RTYPE (rs2, rs1, rd, op) ->
    (match y with
     | RTYPE (rs3, rs4, rd0, op0) ->
       (match eq_dec_point rs2
                (coq_EqDec_EqDecPoint (Coq_bv.eqdec_bv (S (S (S (S (S O))))))
                  rs2)
                rs3 with
        | Coq_left ->
          (match eq_dec_point rs1
                   (coq_EqDec_EqDecPoint
                     (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rs1)
                   rs4 with
           | Coq_left ->
             (match eq_dec_point rd
                      (coq_EqDec_EqDecPoint
                        (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rd)
                      rd0 with
              | Coq_left ->
                eq_dec_point op (coq_EqDec_EqDecPoint coq_ROP_EqDec op) op0
              | Coq_right -> Coq_right)
           | Coq_right -> Coq_right)
        | Coq_right -> Coq_right)
     | _ -> Coq_right)
  | ITYPE (imm, rs1, rd, op) ->
    (match y with
     | ITYPE (imm0, rs2, rd0, op0) ->
       (match eq_dec_point imm
                (coq_EqDec_EqDecPoint
                  (Coq_bv.eqdec_bv (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))
                  imm)
                imm0 with
        | Coq_left ->
          (match eq_dec_point rs1
                   (coq_EqDec_EqDecPoint
                     (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rs1)
                   rs2 with
           | Coq_left ->
             (match eq_dec_point rd
                      (coq_EqDec_EqDecPoint
                        (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rd)
                      rd0 with
              | Coq_left ->
                eq_dec_point op (coq_EqDec_EqDecPoint coq_IOP_EqDec op) op0
              | Coq_right -> Coq_right)
           | Coq_right -> Coq_right)
        | Coq_right -> Coq_right)
     | _ -> Coq_right)
  | SHIFTIOP (shamt, rs1, rd, op) ->
    (match y with
     | SHIFTIOP (shamt0, rs2, rd0, op0) ->
       (match eq_dec_point shamt
                (coq_EqDec_EqDecPoint
                  (Coq_bv.eqdec_bv (S (S (S (S (S (S O))))))) shamt)
                shamt0 with
        | Coq_left ->
          (match eq_dec_point rs1
                   (coq_EqDec_EqDecPoint
                     (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rs1)
                   rs2 with
           | Coq_left ->
             (match eq_dec_point rd
                      (coq_EqDec_EqDecPoint
                        (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rd)
                      rd0 with
              | Coq_left ->
                eq_dec_point op (coq_EqDec_EqDecPoint coq_SOP_EqDec op) op0
              | Coq_right -> Coq_right)
           | Coq_right -> Coq_right)
        | Coq_right -> Coq_right)
     | _ -> Coq_right)
  | UTYPE (imm, rd, op) ->
    (match y with
     | UTYPE (imm0, rd0, op0) ->
       (match eq_dec_point imm
                (coq_EqDec_EqDecPoint
                  (Coq_bv.eqdec_bv (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S O)))))))))))))))))))))
                  imm)
                imm0 with
        | Coq_left ->
          (match eq_dec_point rd
                   (coq_EqDec_EqDecPoint
                     (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rd)
                   rd0 with
           | Coq_left ->
             eq_dec_point op (coq_EqDec_EqDecPoint coq_UOP_EqDec op) op0
           | Coq_right -> Coq_right)
        | Coq_right -> Coq_right)
     | _ -> Coq_right)
  | BTYPE (imm, rs2, rs1, op) ->
    (match y with
     | BTYPE (imm0, rs3, rs4, op0) ->
       (match eq_dec_point imm
                (coq_EqDec_EqDecPoint
                  (Coq_bv.eqdec_bv (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O))))))))))))))
                  imm)
                imm0 with
        | Coq_left ->
          (match eq_dec_point rs2
                   (coq_EqDec_EqDecPoint
                     (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rs2)
                   rs3 with
           | Coq_left ->
             (match eq_dec_point rs1
                      (coq_EqDec_EqDecPoint
                        (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rs1)
                      rs4 with
              | Coq_left ->
                eq_dec_point op (coq_EqDec_EqDecPoint coq_BOP_EqDec op) op0
              | Coq_right -> Coq_right)
           | Coq_right -> Coq_right)
        | Coq_right -> Coq_right)
     | _ -> Coq_right)
  | RISCV_JAL (imm, rd) ->
    (match y with
     | RISCV_JAL (imm0, rd0) ->
       (match eq_dec_point imm
                (coq_EqDec_EqDecPoint
                  (Coq_bv.eqdec_bv (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S O))))))))))))))))))))))
                  imm)
                imm0 with
        | Coq_left ->
          eq_dec_point rd
            (coq_EqDec_EqDecPoint (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rd)
            rd0
        | Coq_right -> Coq_right)
     | _ -> Coq_right)
  | RISCV_JALR (imm, rs1, rd) ->
    (match y with
     | RISCV_JALR (imm0, rs2, rd0) ->
       (match eq_dec_point imm
                (coq_EqDec_EqDecPoint
                  (Coq_bv.eqdec_bv (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))
                  imm)
                imm0 with
        | Coq_left ->
          (match eq_dec_point rs1
                   (coq_EqDec_EqDecPoint
                     (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rs1)
                   rs2 with
           | Coq_left ->
             eq_dec_point rd
               (coq_EqDec_EqDecPoint (Coq_bv.eqdec_bv (S (S (S (S (S O))))))
                 rd)
               rd0
           | Coq_right -> Coq_right)
        | Coq_right -> Coq_right)
     | _ -> Coq_right)
  | LOAD (imm, rs1, rd, is_unsigned, width) ->
    (match y with
     | LOAD (imm0, rs2, rd0, is_unsigned0, width0) ->
       (match eq_dec_point imm
                (coq_EqDec_EqDecPoint
                  (Coq_bv.eqdec_bv (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))
                  imm)
                imm0 with
        | Coq_left ->
          (match eq_dec_point rs1
                   (coq_EqDec_EqDecPoint
                     (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rs1)
                   rs2 with
           | Coq_left ->
             (match eq_dec_point rd
                      (coq_EqDec_EqDecPoint
                        (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rd)
                      rd0 with
              | Coq_left ->
                (match eq_dec_point is_unsigned
                         (coq_EqDec_EqDecPoint bool_EqDec is_unsigned)
                         is_unsigned0 with
                 | Coq_left ->
                   eq_dec_point width
                     (coq_EqDec_EqDecPoint coq_WordWidth_EqDec width) width0
                 | Coq_right -> Coq_right)
              | Coq_right -> Coq_right)
           | Coq_right -> Coq_right)
        | Coq_right -> Coq_right)
     | _ -> Coq_right)
  | STORE (imm, rs2, rs1, width) ->
    (match y with
     | STORE (imm0, rs3, rs4, width0) ->
       (match eq_dec_point imm
                (coq_EqDec_EqDecPoint
                  (Coq_bv.eqdec_bv (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))
                  imm)
                imm0 with
        | Coq_left ->
          (match eq_dec_point rs2
                   (coq_EqDec_EqDecPoint
                     (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rs2)
                   rs3 with
           | Coq_left ->
             (match eq_dec_point rs1
                      (coq_EqDec_EqDecPoint
                        (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rs1)
                      rs4 with
              | Coq_left ->
                eq_dec_point width
                  (coq_EqDec_EqDecPoint coq_WordWidth_EqDec width) width0
              | Coq_right -> Coq_right)
           | Coq_right -> Coq_right)
        | Coq_right -> Coq_right)
     | _ -> Coq_right)
  | ECALL -> (match y with
              | ECALL -> Coq_left
              | _ -> Coq_right)
  | EBREAK -> (match y with
               | EBREAK -> Coq_left
               | _ -> Coq_right)
  | MRET -> (match y with
             | MRET -> Coq_left
             | _ -> Coq_right)
  | CSR (csr, rs1, rd, is_imm, csrop) ->
    (match y with
     | CSR (csr0, rs2, rd0, is_imm0, csrop0) ->
       (match eq_dec_point csr (coq_EqDec_EqDecPoint coq_CSRIdx_EqDec csr)
                csr0 with
        | Coq_left ->
          (match eq_dec_point rs1
                   (coq_EqDec_EqDecPoint
                     (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rs1)
                   rs2 with
           | Coq_left ->
             (match eq_dec_point rd
                      (coq_EqDec_EqDecPoint
                        (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rd)
                      rd0 with
              | Coq_left ->
                (match eq_dec_point is_imm
                         (coq_EqDec_EqDecPoint bool_EqDec is_imm) is_imm0 with
                 | Coq_left ->
                   eq_dec_point csrop
                     (coq_EqDec_EqDecPoint coq_CSROP_EqDec csrop) csrop0
                 | Coq_right -> Coq_right)
              | Coq_right -> Coq_right)
           | Coq_right -> Coq_right)
        | Coq_right -> Coq_right)
     | _ -> Coq_right)
  | MUL (rs2, rs1, rd, high, signed1, signed2) ->
    (match y with
     | MUL (rs3, rs4, rd0, high0, signed3, signed4) ->
       (match eq_dec_point rs2
                (coq_EqDec_EqDecPoint (Coq_bv.eqdec_bv (S (S (S (S (S O))))))
                  rs2)
                rs3 with
        | Coq_left ->
          (match eq_dec_point rs1
                   (coq_EqDec_EqDecPoint
                     (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rs1)
                   rs4 with
           | Coq_left ->
             (match eq_dec_point rd
                      (coq_EqDec_EqDecPoint
                        (Coq_bv.eqdec_bv (S (S (S (S (S O)))))) rd)
                      rd0 with
              | Coq_left ->
                (match eq_dec_point high
                         (coq_EqDec_EqDecPoint bool_EqDec high) high0 with
                 | Coq_left ->
                   (match eq_dec_point signed1
                            (coq_EqDec_EqDecPoint bool_EqDec signed1) signed3 with
                    | Coq_left ->
                      eq_dec_point signed2
                        (coq_EqDec_EqDecPoint bool_EqDec signed2) signed4
                    | Coq_right -> Coq_right)
                 | Coq_right -> Coq_right)
              | Coq_right -> Coq_right)
           | Coq_right -> Coq_right)
        | Coq_right -> Coq_right)
     | _ -> Coq_right)

(** val coq_AST_EqDec : coq_AST coq_EqDec **)

let coq_AST_EqDec =
  coq_AST_eqdec

(** val coq_ASTConstructor_eqdec :
    coq_ASTConstructor -> coq_ASTConstructor -> coq_ASTConstructor dec_eq **)

let coq_ASTConstructor_eqdec x y =
  match x with
  | KRTYPE -> (match y with
               | KRTYPE -> Coq_left
               | _ -> Coq_right)
  | KITYPE -> (match y with
               | KITYPE -> Coq_left
               | _ -> Coq_right)
  | KSHIFTIOP -> (match y with
                  | KSHIFTIOP -> Coq_left
                  | _ -> Coq_right)
  | KUTYPE -> (match y with
               | KUTYPE -> Coq_left
               | _ -> Coq_right)
  | KBTYPE -> (match y with
               | KBTYPE -> Coq_left
               | _ -> Coq_right)
  | KRISCV_JAL -> (match y with
                   | KRISCV_JAL -> Coq_left
                   | _ -> Coq_right)
  | KRISCV_JALR -> (match y with
                    | KRISCV_JALR -> Coq_left
                    | _ -> Coq_right)
  | KLOAD -> (match y with
              | KLOAD -> Coq_left
              | _ -> Coq_right)
  | KSTORE -> (match y with
               | KSTORE -> Coq_left
               | _ -> Coq_right)
  | KECALL -> (match y with
               | KECALL -> Coq_left
               | _ -> Coq_right)
  | KEBREAK -> (match y with
                | KEBREAK -> Coq_left
                | _ -> Coq_right)
  | KMRET -> (match y with
              | KMRET -> Coq_left
              | _ -> Coq_right)
  | KCSR -> (match y with
             | KCSR -> Coq_left
             | _ -> Coq_right)
  | KMUL -> (match y with
             | KMUL -> Coq_left
             | _ -> Coq_right)

(** val coq_ASTConstructor_EqDec : coq_ASTConstructor coq_EqDec **)

let coq_ASTConstructor_EqDec =
  coq_ASTConstructor_eqdec

(** val coq_AccessType_eqdec :
    coq_AccessType -> coq_AccessType -> coq_AccessType dec_eq **)

let coq_AccessType_eqdec x y =
  match x with
  | Read -> (match y with
             | Read -> Coq_left
             | _ -> Coq_right)
  | Write -> (match y with
              | Write -> Coq_left
              | _ -> Coq_right)
  | ReadWrite -> (match y with
                  | ReadWrite -> Coq_left
                  | _ -> Coq_right)
  | Execute -> (match y with
                | Execute -> Coq_left
                | _ -> Coq_right)

(** val coq_AccessType_EqDec : coq_AccessType coq_EqDec **)

let coq_AccessType_EqDec =
  coq_AccessType_eqdec

(** val coq_AccessTypeConstructor_eqdec :
    coq_AccessTypeConstructor -> coq_AccessTypeConstructor ->
    coq_AccessTypeConstructor dec_eq **)

let coq_AccessTypeConstructor_eqdec x y =
  match x with
  | KRead -> (match y with
              | KRead -> Coq_left
              | _ -> Coq_right)
  | KWrite -> (match y with
               | KWrite -> Coq_left
               | _ -> Coq_right)
  | KReadWrite -> (match y with
                   | KReadWrite -> Coq_left
                   | _ -> Coq_right)
  | KExecute -> (match y with
                 | KExecute -> Coq_left
                 | _ -> Coq_right)

(** val coq_AccessTypeConstructor_EqDec :
    coq_AccessTypeConstructor coq_EqDec **)

let coq_AccessTypeConstructor_EqDec =
  coq_AccessTypeConstructor_eqdec

(** val coq_ExceptionType_eqdec :
    coq_ExceptionType -> coq_ExceptionType -> coq_ExceptionType dec_eq **)

let coq_ExceptionType_eqdec x y =
  match x with
  | E_Fetch_Access_Fault ->
    (match y with
     | E_Fetch_Access_Fault -> Coq_left
     | _ -> Coq_right)
  | E_Load_Access_Fault ->
    (match y with
     | E_Load_Access_Fault -> Coq_left
     | _ -> Coq_right)
  | E_SAMO_Access_Fault ->
    (match y with
     | E_SAMO_Access_Fault -> Coq_left
     | _ -> Coq_right)
  | E_U_EnvCall -> (match y with
                    | E_U_EnvCall -> Coq_left
                    | _ -> Coq_right)
  | E_M_EnvCall -> (match y with
                    | E_M_EnvCall -> Coq_left
                    | _ -> Coq_right)
  | E_Illegal_Instr ->
    (match y with
     | E_Illegal_Instr -> Coq_left
     | _ -> Coq_right)

(** val coq_ExceptionType_EqDec : coq_ExceptionType coq_EqDec **)

let coq_ExceptionType_EqDec =
  coq_ExceptionType_eqdec

(** val coq_ExceptionTypeConstructor_eqdec :
    coq_ExceptionTypeConstructor -> coq_ExceptionTypeConstructor ->
    coq_ExceptionTypeConstructor dec_eq **)

let coq_ExceptionTypeConstructor_eqdec x y =
  match x with
  | KE_Fetch_Access_Fault ->
    (match y with
     | KE_Fetch_Access_Fault -> Coq_left
     | _ -> Coq_right)
  | KE_Load_Access_Fault ->
    (match y with
     | KE_Load_Access_Fault -> Coq_left
     | _ -> Coq_right)
  | KE_SAMO_Access_Fault ->
    (match y with
     | KE_SAMO_Access_Fault -> Coq_left
     | _ -> Coq_right)
  | KE_U_EnvCall -> (match y with
                     | KE_U_EnvCall -> Coq_left
                     | _ -> Coq_right)
  | KE_M_EnvCall -> (match y with
                     | KE_M_EnvCall -> Coq_left
                     | _ -> Coq_right)
  | KE_Illegal_Instr ->
    (match y with
     | KE_Illegal_Instr -> Coq_left
     | _ -> Coq_right)

(** val coq_ExceptionTypeConstructor_EqDec :
    coq_ExceptionTypeConstructor coq_EqDec **)

let coq_ExceptionTypeConstructor_EqDec =
  coq_ExceptionTypeConstructor_eqdec

(** val coq_FetchResult_eqdec :
    coq_FetchResult -> coq_FetchResult -> coq_FetchResult dec_eq **)

let coq_FetchResult_eqdec x y =
  match x with
  | F_Base v ->
    (match y with
     | F_Base v0 ->
       eq_dec_point v (coq_EqDec_EqDecPoint (Coq_bv.eqdec_bv word) v) v0
     | F_Error (_, _) -> Coq_right)
  | F_Error (e, v) ->
    (match y with
     | F_Base _ -> Coq_right
     | F_Error (e0, v0) ->
       (match eq_dec_point e (coq_EqDec_EqDecPoint coq_ExceptionType_EqDec e)
                e0 with
        | Coq_left ->
          eq_dec_point v (coq_EqDec_EqDecPoint (Coq_bv.eqdec_bv xlenbits) v)
            v0
        | Coq_right -> Coq_right))

(** val coq_FetchResult_EqDec : coq_FetchResult coq_EqDec **)

let coq_FetchResult_EqDec =
  coq_FetchResult_eqdec

(** val coq_FetchResultConstructor_eqdec :
    coq_FetchResultConstructor -> coq_FetchResultConstructor ->
    coq_FetchResultConstructor dec_eq **)

let coq_FetchResultConstructor_eqdec x y =
  match x with
  | KF_Base -> (match y with
                | KF_Base -> Coq_left
                | KF_Error -> Coq_right)
  | KF_Error -> (match y with
                 | KF_Base -> Coq_right
                 | KF_Error -> Coq_left)

(** val coq_FetchResultConstructor_EqDec :
    coq_FetchResultConstructor coq_EqDec **)

let coq_FetchResultConstructor_EqDec =
  coq_FetchResultConstructor_eqdec

(** val coq_InterruptType_eqdec :
    coq_InterruptType -> coq_InterruptType -> coq_InterruptType dec_eq **)

let coq_InterruptType_eqdec x y =
  match x with
  | I_U_Software -> (match y with
                     | I_U_Software -> Coq_left
                     | _ -> Coq_right)
  | I_M_Software -> (match y with
                     | I_M_Software -> Coq_left
                     | _ -> Coq_right)
  | I_U_Timer -> (match y with
                  | I_U_Timer -> Coq_left
                  | _ -> Coq_right)
  | I_M_Timer -> (match y with
                  | I_M_Timer -> Coq_left
                  | _ -> Coq_right)
  | I_U_External -> (match y with
                     | I_U_External -> Coq_left
                     | _ -> Coq_right)
  | I_M_External -> (match y with
                     | I_M_External -> Coq_left
                     | _ -> Coq_right)

(** val coq_InterruptType_EqDec : coq_InterruptType coq_EqDec **)

let coq_InterruptType_EqDec =
  coq_InterruptType_eqdec

(** val coq_CtlResult_eqdec :
    coq_CtlResult -> coq_CtlResult -> coq_CtlResult dec_eq **)

let coq_CtlResult_eqdec x y =
  match x with
  | CTL_TRAP e ->
    (match y with
     | CTL_TRAP e0 ->
       eq_dec_point e (coq_EqDec_EqDecPoint coq_ExceptionType_EqDec e) e0
     | CTL_MRET -> Coq_right)
  | CTL_MRET -> (match y with
                 | CTL_TRAP _ -> Coq_right
                 | CTL_MRET -> Coq_left)

(** val coq_CtlResult_EqDec : coq_CtlResult coq_EqDec **)

let coq_CtlResult_EqDec =
  coq_CtlResult_eqdec

(** val coq_CtlResultConstructor_eqdec :
    coq_CtlResultConstructor -> coq_CtlResultConstructor ->
    coq_CtlResultConstructor dec_eq **)

let coq_CtlResultConstructor_eqdec x y =
  match x with
  | KCTL_TRAP -> (match y with
                  | KCTL_TRAP -> Coq_left
                  | KCTL_MRET -> Coq_right)
  | KCTL_MRET -> (match y with
                  | KCTL_TRAP -> Coq_right
                  | KCTL_MRET -> Coq_left)

(** val coq_CtlResultConstructor_EqDec :
    coq_CtlResultConstructor coq_EqDec **)

let coq_CtlResultConstructor_EqDec =
  coq_CtlResultConstructor_eqdec

(** val coq_InterruptSetConstructor_eqdec :
    coq_InterruptSetConstructor -> coq_InterruptSetConstructor ->
    coq_InterruptSetConstructor dec_eq **)

let coq_InterruptSetConstructor_eqdec x y =
  match x with
  | KInts_Pending -> (match y with
                      | KInts_Pending -> Coq_left
                      | _ -> Coq_right)
  | KInts_Delegated ->
    (match y with
     | KInts_Delegated -> Coq_left
     | _ -> Coq_right)
  | KInts_Empty -> (match y with
                    | KInts_Empty -> Coq_left
                    | _ -> Coq_right)

(** val coq_InterruptSetConstructor_EqDec :
    coq_InterruptSetConstructor coq_EqDec **)

let coq_InterruptSetConstructor_EqDec =
  coq_InterruptSetConstructor_eqdec

(** val coq_MemoryOpResult_eqdec :
    nat -> coq_MemoryOpResult -> coq_MemoryOpResult -> coq_MemoryOpResult
    dec_eq **)

let coq_MemoryOpResult_eqdec bytes x y =
  match x with
  | MemValue bs ->
    (match y with
     | MemValue bs0 ->
       eq_dec_point bs
         (coq_EqDec_EqDecPoint
           (Coq_bv.eqdec_bv (mul bytes (S (S (S (S (S (S (S (S O)))))))))) bs)
         bs0
     | MemException _ -> Coq_right)
  | MemException e ->
    (match y with
     | MemValue _ -> Coq_right
     | MemException e0 ->
       eq_dec_point e (coq_EqDec_EqDecPoint coq_ExceptionType_EqDec e) e0)

(** val coq_MemoryOpResult_EqDec : nat -> coq_MemoryOpResult coq_EqDec **)

let coq_MemoryOpResult_EqDec =
  coq_MemoryOpResult_eqdec

(** val coq_MemoryOpResultConstructor_eqdec :
    coq_MemoryOpResultConstructor -> coq_MemoryOpResultConstructor ->
    coq_MemoryOpResultConstructor dec_eq **)

let coq_MemoryOpResultConstructor_eqdec x y =
  match x with
  | KMemValue ->
    (match y with
     | KMemValue -> Coq_left
     | KMemException -> Coq_right)
  | KMemException ->
    (match y with
     | KMemValue -> Coq_right
     | KMemException -> Coq_left)

(** val coq_MemoryOpResultConstructor_EqDec :
    coq_MemoryOpResultConstructor coq_EqDec **)

let coq_MemoryOpResultConstructor_EqDec =
  coq_MemoryOpResultConstructor_eqdec

(** val coq_Records_eqdec :
    coq_Records -> coq_Records -> coq_Records dec_eq **)

let coq_Records_eqdec x y =
  match x with
  | Coq_rpmpcfg_ent ->
    (match y with
     | Coq_rpmpcfg_ent -> Coq_left
     | _ -> Coq_right)
  | Coq_rmstatus -> (match y with
                     | Coq_rmstatus -> Coq_left
                     | _ -> Coq_right)
  | Coq_rminterrupts ->
    (match y with
     | Coq_rminterrupts -> Coq_left
     | _ -> Coq_right)

(** val coq_Records_EqDec : coq_Records coq_EqDec **)

let coq_Records_EqDec =
  coq_Records_eqdec

(** val coq_Pmpcfg_ent_eqdec :
    coq_Pmpcfg_ent -> coq_Pmpcfg_ent -> coq_Pmpcfg_ent dec_eq **)

let coq_Pmpcfg_ent_eqdec x y =
  let { coq_L = l; coq_A = a; coq_X = x0; coq_W = w; coq_R = r } = x in
  let { coq_L = l0; coq_A = a0; coq_X = x1; coq_W = w0; coq_R = r0 } = y in
  (match eq_dec_point l (coq_EqDec_EqDecPoint bool_EqDec l) l0 with
   | Coq_left ->
     (match eq_dec_point a
              (coq_EqDec_EqDecPoint coq_PmpAddrMatchType_EqDec a) a0 with
      | Coq_left ->
        (match eq_dec_point x0 (coq_EqDec_EqDecPoint bool_EqDec x0) x1 with
         | Coq_left ->
           (match eq_dec_point w (coq_EqDec_EqDecPoint bool_EqDec w) w0 with
            | Coq_left ->
              eq_dec_point r (coq_EqDec_EqDecPoint bool_EqDec r) r0
            | Coq_right -> Coq_right)
         | Coq_right -> Coq_right)
      | Coq_right -> Coq_right)
   | Coq_right -> Coq_right)

(** val coq_Pmpcfg_ent_EqDec : coq_Pmpcfg_ent coq_EqDec **)

let coq_Pmpcfg_ent_EqDec =
  coq_Pmpcfg_ent_eqdec

(** val coq_Mstatus_eqdec :
    coq_Mstatus -> coq_Mstatus -> coq_Mstatus dec_eq **)

let coq_Mstatus_eqdec x y =
  let { coq_MPP = mPP; coq_MPIE = mPIE; coq_MIE = mIE } = x in
  let { coq_MPP = mPP0; coq_MPIE = mPIE0; coq_MIE = mIE0 } = y in
  (match eq_dec_point mPP (coq_EqDec_EqDecPoint coq_Privilege_EqDec mPP) mPP0 with
   | Coq_left ->
     (match eq_dec_point mPIE (coq_EqDec_EqDecPoint bool_EqDec mPIE) mPIE0 with
      | Coq_left ->
        eq_dec_point mIE (coq_EqDec_EqDecPoint bool_EqDec mIE) mIE0
      | Coq_right -> Coq_right)
   | Coq_right -> Coq_right)

(** val coq_Mstatus_EqDec : coq_Mstatus coq_EqDec **)

let coq_Mstatus_EqDec =
  coq_Mstatus_eqdec

(** val coq_Minterrupts_eqdec :
    coq_Minterrupts -> coq_Minterrupts -> coq_Minterrupts dec_eq **)

let coq_Minterrupts_eqdec x y =
  let { coq_MEI = mEI; coq_UEI = uEI; coq_MTI = mTI; coq_UTI = uTI; coq_MSI =
    mSI; coq_USI = uSI } = x
  in
  let { coq_MEI = mEI0; coq_UEI = uEI0; coq_MTI = mTI0; coq_UTI = uTI0;
    coq_MSI = mSI0; coq_USI = uSI0 } = y
  in
  (match eq_dec_point mEI (coq_EqDec_EqDecPoint bool_EqDec mEI) mEI0 with
   | Coq_left ->
     (match eq_dec_point uEI (coq_EqDec_EqDecPoint bool_EqDec uEI) uEI0 with
      | Coq_left ->
        (match eq_dec_point mTI (coq_EqDec_EqDecPoint bool_EqDec mTI) mTI0 with
         | Coq_left ->
           (match eq_dec_point uTI (coq_EqDec_EqDecPoint bool_EqDec uTI) uTI0 with
            | Coq_left ->
              (match eq_dec_point mSI (coq_EqDec_EqDecPoint bool_EqDec mSI)
                       mSI0 with
               | Coq_left ->
                 eq_dec_point uSI (coq_EqDec_EqDecPoint bool_EqDec uSI) uSI0
               | Coq_right -> Coq_right)
            | Coq_right -> Coq_right)
         | Coq_right -> Coq_right)
      | Coq_right -> Coq_right)
   | Coq_right -> Coq_right)

(** val coq_Minterrupts_EqDec : coq_Minterrupts coq_EqDec **)

let coq_Minterrupts_EqDec =
  coq_Minterrupts_eqdec

(** val coq_InterruptSet_eqdec :
    coq_InterruptSet -> coq_InterruptSet -> coq_InterruptSet dec_eq **)

let coq_InterruptSet_eqdec x y =
  match x with
  | Ints_Pending v ->
    (match y with
     | Ints_Pending v0 ->
       eq_dec_point v (coq_EqDec_EqDecPoint coq_Minterrupts_EqDec v) v0
     | _ -> Coq_right)
  | Ints_Delegated v ->
    (match y with
     | Ints_Delegated v0 ->
       eq_dec_point v (coq_EqDec_EqDecPoint coq_Minterrupts_EqDec v) v0
     | _ -> Coq_right)
  | Ints_Empty -> (match y with
                   | Ints_Empty -> Coq_left
                   | _ -> Coq_right)

(** val coq_InterruptSet_EqDec : coq_InterruptSet coq_EqDec **)

let coq_InterruptSet_EqDec =
  coq_InterruptSet_eqdec

(** val coq_Privilege_finite : coq_Privilege coq_Finite **)

let coq_Privilege_finite =
  Datatypes.Coq_cons (User, (Datatypes.Coq_cons (Machine, Datatypes.Coq_nil)))

(** val coq_CSRIdx_finite : coq_CSRIdx coq_Finite **)

let coq_CSRIdx_finite =
  Datatypes.Coq_cons (MStatus, (Datatypes.Coq_cons (Mie, (Datatypes.Coq_cons
    (MTvec, (Datatypes.Coq_cons (MScratch, (Datatypes.Coq_cons (MEpc,
    (Datatypes.Coq_cons (MCause, (Datatypes.Coq_cons (MPMP0CFG,
    (Datatypes.Coq_cons (MPMPADDR0, (Datatypes.Coq_cons (MPMPADDR1,
    (Datatypes.Coq_cons (Mip, Datatypes.Coq_nil)))))))))))))))))))

(** val coq_InterruptType_finite : coq_InterruptType coq_Finite **)

let coq_InterruptType_finite =
  Datatypes.Coq_cons (I_U_Software, (Datatypes.Coq_cons (I_M_Software,
    (Datatypes.Coq_cons (I_U_Timer, (Datatypes.Coq_cons (I_M_Timer,
    (Datatypes.Coq_cons (I_U_External, (Datatypes.Coq_cons (I_M_External,
    Datatypes.Coq_nil)))))))))))

(** val coq_PmpCfgIdx_finite : coq_PmpCfgIdx coq_Finite **)

let coq_PmpCfgIdx_finite =
  Datatypes.Coq_cons (PMP0CFG, (Datatypes.Coq_cons (PMP1CFG,
    Datatypes.Coq_nil)))

(** val coq_PmpCfgPerm_finite : coq_PmpCfgPerm coq_Finite **)

let coq_PmpCfgPerm_finite =
  Datatypes.Coq_cons (PmpO, (Datatypes.Coq_cons (PmpR, (Datatypes.Coq_cons
    (PmpW, (Datatypes.Coq_cons (PmpX, (Datatypes.Coq_cons (PmpRW,
    (Datatypes.Coq_cons (PmpRX, (Datatypes.Coq_cons (PmpWX,
    (Datatypes.Coq_cons (PmpRWX, Datatypes.Coq_nil)))))))))))))))

(** val coq_PmpAddrIdx_finite : coq_PmpAddrIdx coq_Finite **)

let coq_PmpAddrIdx_finite =
  Datatypes.Coq_cons (PMPADDR0, (Datatypes.Coq_cons (PMPADDR1,
    Datatypes.Coq_nil)))

(** val coq_PmpAddrMatchType_finite : coq_PmpAddrMatchType coq_Finite **)

let coq_PmpAddrMatchType_finite =
  Datatypes.Coq_cons (OFF, (Datatypes.Coq_cons (TOR, Datatypes.Coq_nil)))

(** val coq_PmpMatch_finite : coq_PmpMatch coq_Finite **)

let coq_PmpMatch_finite =
  Datatypes.Coq_cons (PMP_Success, (Datatypes.Coq_cons (PMP_Continue,
    (Datatypes.Coq_cons (PMP_Fail, Datatypes.Coq_nil)))))

(** val coq_PmpAddrMatch_finite : coq_PmpAddrMatch coq_Finite **)

let coq_PmpAddrMatch_finite =
  Datatypes.Coq_cons (PMP_NoMatch, (Datatypes.Coq_cons (PMP_PartialMatch,
    (Datatypes.Coq_cons (PMP_Match, Datatypes.Coq_nil)))))

(** val coq_ROP_finite : coq_ROP coq_Finite **)

let coq_ROP_finite =
  Datatypes.Coq_cons (RISCV_ADD, (Datatypes.Coq_cons (RISCV_SUB,
    (Datatypes.Coq_cons (RISCV_SLT, (Datatypes.Coq_cons (RISCV_SLTU,
    (Datatypes.Coq_cons (RISCV_SLL, (Datatypes.Coq_cons (RISCV_SRL,
    (Datatypes.Coq_cons (RISCV_SRA, (Datatypes.Coq_cons (RISCV_AND,
    (Datatypes.Coq_cons (RISCV_OR, (Datatypes.Coq_cons (RISCV_XOR,
    Datatypes.Coq_nil)))))))))))))))))))

(** val coq_IOP_finite : coq_IOP coq_Finite **)

let coq_IOP_finite =
  Datatypes.Coq_cons (RISCV_ADDI, (Datatypes.Coq_cons (RISCV_SLTI,
    (Datatypes.Coq_cons (RISCV_SLTIU, (Datatypes.Coq_cons (RISCV_ANDI,
    (Datatypes.Coq_cons (RISCV_ORI, (Datatypes.Coq_cons (RISCV_XORI,
    Datatypes.Coq_nil)))))))))))

(** val coq_SOP_finite : coq_SOP coq_Finite **)

let coq_SOP_finite =
  Datatypes.Coq_cons (RISCV_SLLI, (Datatypes.Coq_cons (RISCV_SRLI,
    (Datatypes.Coq_cons (RISCV_SRAI, Datatypes.Coq_nil)))))

(** val coq_UOP_finite : coq_UOP coq_Finite **)

let coq_UOP_finite =
  Datatypes.Coq_cons (RISCV_LUI, (Datatypes.Coq_cons (RISCV_AUIPC,
    Datatypes.Coq_nil)))

(** val coq_BOP_finite : coq_BOP coq_Finite **)

let coq_BOP_finite =
  Datatypes.Coq_cons (RISCV_BEQ, (Datatypes.Coq_cons (RISCV_BNE,
    (Datatypes.Coq_cons (RISCV_BLT, (Datatypes.Coq_cons (RISCV_BGE,
    (Datatypes.Coq_cons (RISCV_BLTU, (Datatypes.Coq_cons (RISCV_BGEU,
    Datatypes.Coq_nil)))))))))))

(** val coq_CSROP_finite : coq_CSROP coq_Finite **)

let coq_CSROP_finite =
  Datatypes.Coq_cons (CSRRW, (Datatypes.Coq_cons (CSRRS, (Datatypes.Coq_cons
    (CSRRC, Datatypes.Coq_nil)))))

(** val coq_MOP_finite : coq_MOP coq_Finite **)

let coq_MOP_finite =
  Datatypes.Coq_cons (RISCV_MUL, (Datatypes.Coq_cons (RISCV_MULH,
    (Datatypes.Coq_cons (RISCV_MULHU, (Datatypes.Coq_cons (RISCV_MULHSU,
    Datatypes.Coq_nil)))))))

(** val coq_Retired_finite : coq_Retired coq_Finite **)

let coq_Retired_finite =
  Datatypes.Coq_cons (RETIRE_SUCCESS, (Datatypes.Coq_cons (RETIRE_FAIL,
    Datatypes.Coq_nil)))

(** val coq_WordWidth_finite : coq_WordWidth coq_Finite **)

let coq_WordWidth_finite =
  Datatypes.Coq_cons (BYTE, (Datatypes.Coq_cons (HALF, (Datatypes.Coq_cons
    (WORD, Datatypes.Coq_nil)))))

(** val coq_ASTConstructor_finite : coq_ASTConstructor coq_Finite **)

let coq_ASTConstructor_finite =
  Datatypes.Coq_cons (KRTYPE, (Datatypes.Coq_cons (KITYPE,
    (Datatypes.Coq_cons (KSHIFTIOP, (Datatypes.Coq_cons (KUTYPE,
    (Datatypes.Coq_cons (KBTYPE, (Datatypes.Coq_cons (KRISCV_JAL,
    (Datatypes.Coq_cons (KRISCV_JALR, (Datatypes.Coq_cons (KLOAD,
    (Datatypes.Coq_cons (KSTORE, (Datatypes.Coq_cons (KECALL,
    (Datatypes.Coq_cons (KEBREAK, (Datatypes.Coq_cons (KMRET,
    (Datatypes.Coq_cons (KCSR, (Datatypes.Coq_cons (KMUL,
    Datatypes.Coq_nil)))))))))))))))))))))))))))

(** val coq_AccessTypeConstructor_finite :
    coq_AccessTypeConstructor coq_Finite **)

let coq_AccessTypeConstructor_finite =
  Datatypes.Coq_cons (KRead, (Datatypes.Coq_cons (KWrite, (Datatypes.Coq_cons
    (KReadWrite, (Datatypes.Coq_cons (KExecute, Datatypes.Coq_nil)))))))

(** val coq_ExceptionTypeConstructor_finite :
    coq_ExceptionTypeConstructor coq_Finite **)

let coq_ExceptionTypeConstructor_finite =
  Datatypes.Coq_cons (KE_Fetch_Access_Fault, (Datatypes.Coq_cons
    (KE_Load_Access_Fault, (Datatypes.Coq_cons (KE_SAMO_Access_Fault,
    (Datatypes.Coq_cons (KE_U_EnvCall, (Datatypes.Coq_cons (KE_M_EnvCall,
    (Datatypes.Coq_cons (KE_Illegal_Instr, Datatypes.Coq_nil)))))))))))

(** val coq_FetchResultConstructor_finite :
    coq_FetchResultConstructor coq_Finite **)

let coq_FetchResultConstructor_finite =
  Datatypes.Coq_cons (KF_Base, (Datatypes.Coq_cons (KF_Error,
    Datatypes.Coq_nil)))

(** val coq_CtlResultConstructor_finite :
    coq_CtlResultConstructor coq_Finite **)

let coq_CtlResultConstructor_finite =
  Datatypes.Coq_cons (KCTL_TRAP, (Datatypes.Coq_cons (KCTL_MRET,
    Datatypes.Coq_nil)))

(** val coq_InterruptSetConstructor_finite :
    coq_InterruptSetConstructor coq_Finite **)

let coq_InterruptSetConstructor_finite =
  Datatypes.Coq_cons (KInts_Pending, (Datatypes.Coq_cons (KInts_Delegated,
    (Datatypes.Coq_cons (KInts_Empty, Datatypes.Coq_nil)))))

(** val coq_MemoryOpResultConstructor_finite :
    coq_MemoryOpResultConstructor coq_Finite **)

let coq_MemoryOpResultConstructor_finite =
  Datatypes.Coq_cons (KMemValue, (Datatypes.Coq_cons (KMemException,
    Datatypes.Coq_nil)))

module RiscvPmpBase =
 struct
  (** val typedeclkit : Coq_ty.coq_TypeDeclKit **)

  let typedeclkit =
    Coq_ty.Build_TypeDeclKit

  (** val ty_xlenbits : Coq_ty.coq_Ty **)

  let ty_xlenbits =
    Coq_ty.Coq_bvec xlenbits

  (** val ty_word : Coq_ty.coq_Ty **)

  let ty_word =
    Coq_ty.Coq_bvec word

  (** val ty_byte : Coq_ty.coq_Ty **)

  let ty_byte =
    Coq_ty.Coq_bvec byte

  (** val ty_bytes : nat -> Coq_ty.coq_Ty **)

  let ty_bytes bytes =
    Coq_ty.Coq_bvec (mul bytes byte)

  (** val ty_regno : Coq_ty.coq_Ty **)

  let ty_regno =
    Coq_ty.Coq_bvec (S (S (S (S (S O)))))

  (** val ty_privilege : Coq_ty.coq_Ty **)

  let ty_privilege =
    Coq_ty.Coq_enum (Obj.magic Coq_privilege)

  (** val ty_interruptType : Coq_ty.coq_Ty **)

  let ty_interruptType =
    Coq_ty.Coq_enum (Obj.magic Coq_interruptType)

  (** val ty_priv_level : Coq_ty.coq_Ty **)

  let ty_priv_level =
    Coq_ty.Coq_bvec (S (S O))

  (** val ty_csridx : Coq_ty.coq_Ty **)

  let ty_csridx =
    Coq_ty.Coq_enum (Obj.magic Coq_csridx)

  (** val ty_pmpcfgidx : Coq_ty.coq_Ty **)

  let ty_pmpcfgidx =
    Coq_ty.Coq_enum (Obj.magic Coq_pmpcfgidx)

  (** val ty_pmpcfgperm : Coq_ty.coq_Ty **)

  let ty_pmpcfgperm =
    Coq_ty.Coq_enum (Obj.magic Coq_pmpcfgperm)

  (** val ty_pmpaddridx : Coq_ty.coq_Ty **)

  let ty_pmpaddridx =
    Coq_ty.Coq_enum (Obj.magic Coq_pmpaddridx)

  (** val ty_pmpaddrmatchtype : Coq_ty.coq_Ty **)

  let ty_pmpaddrmatchtype =
    Coq_ty.Coq_enum (Obj.magic Coq_pmpaddrmatchtype)

  (** val ty_pmpmatch : Coq_ty.coq_Ty **)

  let ty_pmpmatch =
    Coq_ty.Coq_enum (Obj.magic Coq_pmpmatch)

  (** val ty_pmpaddrmatch : Coq_ty.coq_Ty **)

  let ty_pmpaddrmatch =
    Coq_ty.Coq_enum (Obj.magic Coq_pmpaddrmatch)

  (** val ty_pmp_addr_range : Coq_ty.coq_Ty **)

  let ty_pmp_addr_range =
    Coq_ty.option typedeclkit (Coq_ty.Coq_prod (ty_xlenbits, ty_xlenbits))

  (** val ty_rop : Coq_ty.coq_Ty **)

  let ty_rop =
    Coq_ty.Coq_enum (Obj.magic Coq_rop)

  (** val ty_iop : Coq_ty.coq_Ty **)

  let ty_iop =
    Coq_ty.Coq_enum (Obj.magic Coq_iop)

  (** val ty_sop : Coq_ty.coq_Ty **)

  let ty_sop =
    Coq_ty.Coq_enum (Obj.magic Coq_sop)

  (** val ty_uop : Coq_ty.coq_Ty **)

  let ty_uop =
    Coq_ty.Coq_enum (Obj.magic Coq_uop)

  (** val ty_bop : Coq_ty.coq_Ty **)

  let ty_bop =
    Coq_ty.Coq_enum (Obj.magic Coq_bop)

  (** val ty_csrop : Coq_ty.coq_Ty **)

  let ty_csrop =
    Coq_ty.Coq_enum (Obj.magic Coq_csrop)

  (** val ty_mop : Coq_ty.coq_Ty **)

  let ty_mop =
    Coq_ty.Coq_enum (Obj.magic Coq_mop)

  (** val ty_retired : Coq_ty.coq_Ty **)

  let ty_retired =
    Coq_ty.Coq_enum (Obj.magic Coq_retired)

  (** val ty_word_width : Coq_ty.coq_Ty **)

  let ty_word_width =
    Coq_ty.Coq_enum (Obj.magic Coq_wordwidth)

  (** val ty_mcause : Coq_ty.coq_Ty **)

  let ty_mcause =
    ty_xlenbits

  (** val ty_exc_code : Coq_ty.coq_Ty **)

  let ty_exc_code =
    Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S O))))))))

  (** val ty_ast : Coq_ty.coq_Ty **)

  let ty_ast =
    Coq_ty.Coq_union (Obj.magic Coq_ast)

  (** val ty_access_type : Coq_ty.coq_Ty **)

  let ty_access_type =
    Coq_ty.Coq_union (Obj.magic Coq_access_type)

  (** val ty_exception_type : Coq_ty.coq_Ty **)

  let ty_exception_type =
    Coq_ty.Coq_union (Obj.magic Coq_exception_type)

  (** val ty_memory_op_result : nat -> Coq_ty.coq_Ty **)

  let ty_memory_op_result bytes =
    Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result bytes))

  (** val ty_fetch_result : Coq_ty.coq_Ty **)

  let ty_fetch_result =
    Coq_ty.Coq_union (Obj.magic Coq_fetch_result)

  (** val ty_ctl_result : Coq_ty.coq_Ty **)

  let ty_ctl_result =
    Coq_ty.Coq_union (Obj.magic Coq_ctl_result)

  (** val ty_interrupt_set : Coq_ty.coq_Ty **)

  let ty_interrupt_set =
    Coq_ty.Coq_union (Obj.magic Coq_interrupt_set)

  (** val ty_pmpcfg_ent : Coq_ty.coq_Ty **)

  let ty_pmpcfg_ent =
    Coq_ty.Coq_record (Obj.magic Coq_rpmpcfg_ent)

  (** val ty_mstatus : Coq_ty.coq_Ty **)

  let ty_mstatus =
    Coq_ty.Coq_record (Obj.magic Coq_rmstatus)

  (** val ty_Minterrupts : Coq_ty.coq_Ty **)

  let ty_Minterrupts =
    Coq_ty.Coq_record (Obj.magic Coq_rminterrupts)

  (** val ty_pmpentry : Coq_ty.coq_Ty **)

  let ty_pmpentry =
    Coq_ty.Coq_prod (ty_pmpcfg_ent, ty_xlenbits)

  (** val ty_pmpentries : Coq_ty.coq_Ty **)

  let ty_pmpentries =
    Coq_ty.Coq_list (Coq_ty.Coq_prod (ty_pmpcfg_ent, ty_xlenbits))

  type enum_denote = __

  type union_denote = __

  type record_denote = __

  (** val typedenotekit : Coq_ty.coq_TypeDenoteKit **)

  let typedenotekit =
    Coq_ty.Build_TypeDenoteKit

  type union_constructor = __

  (** val union_constructor_type :
      coq_Unions -> union_constructor -> Coq_ty.coq_Ty **)

  let union_constructor_type u k =
    match u with
    | Coq_ast ->
      (match Obj.magic k with
       | KRTYPE ->
         Coq_ty.Coq_tuple (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
           ty_regno)), ty_regno)), ty_regno)), ty_rop))
       | KITYPE ->
         Coq_ty.Coq_tuple (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
           (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))), ty_regno)), ty_regno)), ty_iop))
       | KSHIFTIOP ->
         Coq_ty.Coq_tuple (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
           (Coq_ty.Coq_bvec (S (S (S (S (S (S O))))))))), ty_regno)),
           ty_regno)), ty_sop))
       | KUTYPE ->
         Coq_ty.Coq_tuple (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_bvec (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))), ty_regno)), ty_uop))
       | KBTYPE ->
         Coq_ty.Coq_tuple (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
           (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S
           O)))))))))))))))), ty_regno)), ty_regno)), ty_bop))
       | KRISCV_JAL ->
         Coq_ty.Coq_tuple (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           (Coq_ctx.Coq_nil, (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))),
           ty_regno))
       | KRISCV_JALR ->
         Coq_ty.Coq_tuple (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, (Coq_ty.Coq_bvec (S (S (S (S
           (S (S (S (S (S (S (S (S O))))))))))))))), ty_regno)), ty_regno))
       | KLOAD ->
         Coq_ty.Coq_tuple (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           (Coq_ctx.Coq_nil, (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S
           (S (S O))))))))))))))), ty_regno)), ty_regno)), Coq_ty.Coq_bool)),
           ty_word_width))
       | KSTORE ->
         Coq_ty.Coq_tuple (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
           (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))), ty_regno)), ty_regno)), ty_word_width))
       | KCSR ->
         Coq_ty.Coq_tuple (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           (Coq_ctx.Coq_nil, ty_csridx)), ty_regno)), ty_regno)),
           Coq_ty.Coq_bool)), ty_csrop))
       | KMUL ->
         Coq_ty.Coq_tuple (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
           ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, ty_regno)), ty_regno)),
           ty_regno)), Coq_ty.Coq_bool)), Coq_ty.Coq_bool)), Coq_ty.Coq_bool))
       | _ -> Coq_ty.Coq_unit)
    | Coq_memory_op_result bytes ->
      (match Obj.magic k with
       | KMemValue ->
         Coq_ty.Coq_bvec (mul bytes (S (S (S (S (S (S (S (S O)))))))))
       | KMemException -> ty_exception_type)
    | Coq_fetch_result ->
      (match Obj.magic k with
       | KF_Base -> ty_word
       | KF_Error -> Coq_ty.Coq_prod (ty_exception_type, ty_word))
    | Coq_ctl_result ->
      (match Obj.magic k with
       | KCTL_TRAP -> ty_exception_type
       | KCTL_MRET -> Coq_ty.Coq_unit)
    | Coq_interrupt_set ->
      (match Obj.magic k with
       | KInts_Empty -> Coq_ty.Coq_unit
       | _ -> ty_Minterrupts)
    | _ -> Coq_ty.Coq_unit

  (** val eqdec_enum_denote : coq_Enums -> enum_denote coq_EqDec **)

  let eqdec_enum_denote = function
  | Coq_privilege -> Obj.magic coq_Privilege_EqDec
  | Coq_interruptType -> Obj.magic coq_InterruptType_EqDec
  | Coq_csridx -> Obj.magic coq_CSRIdx_EqDec
  | Coq_pmpcfgidx -> Obj.magic coq_PmpCfgIdx_EqDec
  | Coq_pmpcfgperm -> Obj.magic coq_PmpCfgPerm_EqDec
  | Coq_pmpaddridx -> Obj.magic coq_PmpAddrIdx_EqDec
  | Coq_pmpaddrmatchtype -> Obj.magic coq_PmpAddrMatchType_EqDec
  | Coq_pmpmatch -> Obj.magic coq_PmpMatch_EqDec
  | Coq_pmpaddrmatch -> Obj.magic coq_PmpAddrMatch_EqDec
  | Coq_rop -> Obj.magic coq_ROP_EqDec
  | Coq_iop -> Obj.magic coq_IOP_EqDec
  | Coq_sop -> Obj.magic coq_SOP_EqDec
  | Coq_uop -> Obj.magic coq_UOP_EqDec
  | Coq_bop -> Obj.magic coq_BOP_EqDec
  | Coq_csrop -> Obj.magic coq_CSROP_EqDec
  | Coq_retired -> Obj.magic coq_Retired_EqDec
  | Coq_wordwidth -> Obj.magic coq_WordWidth_EqDec
  | Coq_mop -> Obj.magic coq_MOP_EqDec

  (** val finite_enum_denote : coq_Enums -> enum_denote coq_Finite **)

  let finite_enum_denote = function
  | Coq_privilege -> Obj.magic coq_Privilege_finite
  | Coq_interruptType -> Obj.magic coq_InterruptType_finite
  | Coq_csridx -> Obj.magic coq_CSRIdx_finite
  | Coq_pmpcfgidx -> Obj.magic coq_PmpCfgIdx_finite
  | Coq_pmpcfgperm -> Obj.magic coq_PmpCfgPerm_finite
  | Coq_pmpaddridx -> Obj.magic coq_PmpAddrIdx_finite
  | Coq_pmpaddrmatchtype -> Obj.magic coq_PmpAddrMatchType_finite
  | Coq_pmpmatch -> Obj.magic coq_PmpMatch_finite
  | Coq_pmpaddrmatch -> Obj.magic coq_PmpAddrMatch_finite
  | Coq_rop -> Obj.magic coq_ROP_finite
  | Coq_iop -> Obj.magic coq_IOP_finite
  | Coq_sop -> Obj.magic coq_SOP_finite
  | Coq_uop -> Obj.magic coq_UOP_finite
  | Coq_bop -> Obj.magic coq_BOP_finite
  | Coq_csrop -> Obj.magic coq_CSROP_finite
  | Coq_retired -> Obj.magic coq_Retired_finite
  | Coq_wordwidth -> Obj.magic coq_WordWidth_finite
  | Coq_mop -> Obj.magic coq_MOP_finite

  (** val eqdec_union_denote : coq_Unions -> union_denote coq_EqDec **)

  let eqdec_union_denote = function
  | Coq_ast -> Obj.magic coq_AST_EqDec
  | Coq_access_type -> Obj.magic coq_AccessType_EqDec
  | Coq_exception_type -> Obj.magic coq_ExceptionType_EqDec
  | Coq_memory_op_result bytes -> Obj.magic coq_MemoryOpResult_EqDec bytes
  | Coq_fetch_result -> Obj.magic coq_FetchResult_EqDec
  | Coq_ctl_result -> Obj.magic coq_CtlResult_EqDec
  | Coq_interrupt_set -> Obj.magic coq_InterruptSet_EqDec

  (** val eqdec_union_constructor :
      coq_Unions -> union_constructor coq_EqDec **)

  let eqdec_union_constructor = function
  | Coq_ast -> Obj.magic coq_ASTConstructor_EqDec
  | Coq_access_type -> Obj.magic coq_AccessTypeConstructor_EqDec
  | Coq_exception_type -> Obj.magic coq_ExceptionTypeConstructor_EqDec
  | Coq_memory_op_result _ -> Obj.magic coq_MemoryOpResultConstructor_EqDec
  | Coq_fetch_result -> Obj.magic coq_FetchResultConstructor_EqDec
  | Coq_ctl_result -> Obj.magic coq_CtlResultConstructor_EqDec
  | Coq_interrupt_set -> Obj.magic coq_InterruptSetConstructor_EqDec

  (** val finite_union_constructor :
      coq_Unions -> union_constructor coq_Finite **)

  let finite_union_constructor = function
  | Coq_ast -> Obj.magic coq_ASTConstructor_finite
  | Coq_access_type -> Obj.magic coq_AccessTypeConstructor_finite
  | Coq_exception_type -> Obj.magic coq_ExceptionTypeConstructor_finite
  | Coq_memory_op_result _ -> Obj.magic coq_MemoryOpResultConstructor_finite
  | Coq_fetch_result -> Obj.magic coq_FetchResultConstructor_finite
  | Coq_ctl_result -> Obj.magic coq_CtlResultConstructor_finite
  | Coq_interrupt_set -> Obj.magic coq_InterruptSetConstructor_finite

  (** val eqdec_record_denote : coq_Records -> record_denote coq_EqDec **)

  let eqdec_record_denote = function
  | Coq_rpmpcfg_ent -> Obj.magic coq_Pmpcfg_ent_EqDec
  | Coq_rmstatus -> Obj.magic coq_Mstatus_EqDec
  | Coq_rminterrupts -> Obj.magic coq_Minterrupts_EqDec

  (** val union_unfold :
      Coq_ty.unioni -> Coq_ty.uniont -> (union_constructor, Coq_ty.coq_Val)
      sigT **)

  let union_unfold u kv =
    match Obj.magic u with
    | Coq_ast ->
      (match Obj.magic kv with
       | RTYPE (rs2, rs1, rd, op) ->
         Coq_existT ((Obj.magic KRTYPE),
           (Obj.magic (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair (Coq_tt,
             rs2)), rs1)), rd)), op))))
       | ITYPE (imm, rs1, rd, op) ->
         Coq_existT ((Obj.magic KITYPE),
           (Obj.magic (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair (Coq_tt,
             imm)), rs1)), rd)), op))))
       | SHIFTIOP (shamt, rs1, rd, op) ->
         Coq_existT ((Obj.magic KSHIFTIOP),
           (Obj.magic (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair (Coq_tt,
             shamt)), rs1)), rd)), op))))
       | UTYPE (imm, rd, op) ->
         Coq_existT ((Obj.magic KUTYPE),
           (Obj.magic (Coq_pair ((Coq_pair ((Coq_pair (Coq_tt, imm)), rd)),
             op))))
       | BTYPE (imm, rs2, rs1, op) ->
         Coq_existT ((Obj.magic KBTYPE),
           (Obj.magic (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair (Coq_tt,
             imm)), rs2)), rs1)), op))))
       | RISCV_JAL (imm, rd) ->
         Coq_existT ((Obj.magic KRISCV_JAL),
           (Obj.magic (Coq_pair ((Coq_pair (Coq_tt, imm)), rd))))
       | RISCV_JALR (imm, rs1, rd) ->
         Coq_existT ((Obj.magic KRISCV_JALR),
           (Obj.magic (Coq_pair ((Coq_pair ((Coq_pair (Coq_tt, imm)), rs1)),
             rd))))
       | LOAD (imm, rs1, rd, is_unsigned, w) ->
         Coq_existT ((Obj.magic KLOAD),
           (Obj.magic (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair
             (Coq_tt, imm)), rs1)), rd)), is_unsigned)), w))))
       | STORE (imm, rs2, rs1, w) ->
         Coq_existT ((Obj.magic KSTORE),
           (Obj.magic (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair (Coq_tt,
             imm)), rs2)), rs1)), w))))
       | ECALL -> Coq_existT ((Obj.magic KECALL), (Obj.magic Coq_tt))
       | EBREAK -> Coq_existT ((Obj.magic KEBREAK), (Obj.magic Coq_tt))
       | MRET -> Coq_existT ((Obj.magic KMRET), (Obj.magic Coq_tt))
       | CSR (csr, rs1, rd, is_imm, op) ->
         Coq_existT ((Obj.magic KCSR),
           (Obj.magic (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair
             (Coq_tt, csr)), rs1)), rd)), is_imm)), op))))
       | MUL (rs2, rs1, rd, h, s1, s2) ->
         Coq_existT ((Obj.magic KMUL),
           (Obj.magic (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair
             ((Coq_pair (Coq_tt, rs2)), rs1)), rd)), h)), s1)), s2)))))
    | Coq_access_type ->
      (match Obj.magic kv with
       | Read -> Coq_existT ((Obj.magic KRead), (Obj.magic Coq_tt))
       | Write -> Coq_existT ((Obj.magic KWrite), (Obj.magic Coq_tt))
       | ReadWrite -> Coq_existT ((Obj.magic KReadWrite), (Obj.magic Coq_tt))
       | Execute -> Coq_existT ((Obj.magic KExecute), (Obj.magic Coq_tt)))
    | Coq_exception_type ->
      (match Obj.magic kv with
       | E_Fetch_Access_Fault ->
         Coq_existT ((Obj.magic KE_Fetch_Access_Fault), (Obj.magic Coq_tt))
       | E_Load_Access_Fault ->
         Coq_existT ((Obj.magic KE_Load_Access_Fault), (Obj.magic Coq_tt))
       | E_SAMO_Access_Fault ->
         Coq_existT ((Obj.magic KE_SAMO_Access_Fault), (Obj.magic Coq_tt))
       | E_U_EnvCall ->
         Coq_existT ((Obj.magic KE_U_EnvCall), (Obj.magic Coq_tt))
       | E_M_EnvCall ->
         Coq_existT ((Obj.magic KE_M_EnvCall), (Obj.magic Coq_tt))
       | E_Illegal_Instr ->
         Coq_existT ((Obj.magic KE_Illegal_Instr), (Obj.magic Coq_tt)))
    | Coq_memory_op_result _ ->
      (match Obj.magic kv with
       | MemValue v -> Coq_existT ((Obj.magic KMemValue), (Obj.magic v))
       | MemException e ->
         Coq_existT ((Obj.magic KMemException), (Obj.magic e)))
    | Coq_fetch_result ->
      (match Obj.magic kv with
       | F_Base v -> Coq_existT ((Obj.magic KF_Base), (Obj.magic v))
       | F_Error (e, v) ->
         Coq_existT ((Obj.magic KF_Error), (Obj.magic (Coq_pair (e, v)))))
    | Coq_ctl_result ->
      (match Obj.magic kv with
       | CTL_TRAP e -> Coq_existT ((Obj.magic KCTL_TRAP), (Obj.magic e))
       | CTL_MRET -> Coq_existT ((Obj.magic KCTL_MRET), (Obj.magic Coq_tt)))
    | Coq_interrupt_set ->
      (match Obj.magic kv with
       | Ints_Pending v ->
         Coq_existT ((Obj.magic KInts_Pending), (Obj.magic v))
       | Ints_Delegated v ->
         Coq_existT ((Obj.magic KInts_Delegated), (Obj.magic v))
       | Ints_Empty ->
         Coq_existT ((Obj.magic KInts_Empty), (Obj.magic Coq_tt)))

  (** val union_fold :
      Coq_ty.unioni -> (union_constructor, Coq_ty.coq_Val) sigT ->
      Coq_ty.uniont **)

  let union_fold u kv =
    match Obj.magic u with
    | Coq_ast ->
      let Coq_existT (x, v) = kv in
      (match Obj.magic x with
       | KRTYPE ->
         let Coq_pair (e, op) = Obj.magic v in
         let Coq_pair (p, rd) = e in
         let Coq_pair (p0, rs1) = p in
         let Coq_pair (_, rs2) = p0 in Obj.magic (RTYPE (rs2, rs1, rd, op))
       | KITYPE ->
         let Coq_pair (e, op) = Obj.magic v in
         let Coq_pair (p, rd) = e in
         let Coq_pair (p0, rs1) = p in
         let Coq_pair (_, imm) = p0 in Obj.magic (ITYPE (imm, rs1, rd, op))
       | KSHIFTIOP ->
         let Coq_pair (e, op) = Obj.magic v in
         let Coq_pair (p, rd) = e in
         let Coq_pair (p0, rs1) = p in
         let Coq_pair (_, shamt) = p0 in
         Obj.magic (SHIFTIOP (shamt, rs1, rd, op))
       | KUTYPE ->
         let Coq_pair (e, op) = Obj.magic v in
         let Coq_pair (p, rd) = e in
         let Coq_pair (_, imm) = p in Obj.magic (UTYPE (imm, rd, op))
       | KBTYPE ->
         let Coq_pair (e, op) = Obj.magic v in
         let Coq_pair (p, rs1) = e in
         let Coq_pair (p0, rs2) = p in
         let Coq_pair (_, imm) = p0 in Obj.magic (BTYPE (imm, rs2, rs1, op))
       | KRISCV_JAL ->
         let Coq_pair (e, rd) = Obj.magic v in
         let Coq_pair (_, imm) = e in Obj.magic (RISCV_JAL (imm, rd))
       | KRISCV_JALR ->
         let Coq_pair (e, rd) = Obj.magic v in
         let Coq_pair (p, rs1) = e in
         let Coq_pair (_, imm) = p in Obj.magic (RISCV_JALR (imm, rs1, rd))
       | KLOAD ->
         let Coq_pair (e, w) = Obj.magic v in
         let Coq_pair (p, is_unsigned) = e in
         let Coq_pair (p0, rd) = p in
         let Coq_pair (p1, rs1) = p0 in
         let Coq_pair (_, imm) = p1 in
         Obj.magic (LOAD (imm, rs1, rd, is_unsigned, w))
       | KSTORE ->
         let Coq_pair (e, w) = Obj.magic v in
         let Coq_pair (p, rs1) = e in
         let Coq_pair (p0, rs2) = p in
         let Coq_pair (_, imm) = p0 in Obj.magic (STORE (imm, rs2, rs1, w))
       | KECALL -> Obj.magic ECALL
       | KEBREAK -> Obj.magic EBREAK
       | KMRET -> Obj.magic MRET
       | KCSR ->
         let Coq_pair (e, op) = Obj.magic v in
         let Coq_pair (p, is_imm) = e in
         let Coq_pair (p0, rd) = p in
         let Coq_pair (p1, rs1) = p0 in
         let Coq_pair (_, csr) = p1 in
         Obj.magic (CSR (csr, rs1, rd, is_imm, op))
       | KMUL ->
         let Coq_pair (e, s2) = Obj.magic v in
         let Coq_pair (p, s1) = e in
         let Coq_pair (p0, h) = p in
         let Coq_pair (p1, rd) = p0 in
         let Coq_pair (p2, rs1) = p1 in
         let Coq_pair (_, rs2) = p2 in
         Obj.magic (MUL (rs2, rs1, rd, h, s1, s2)))
    | Coq_access_type ->
      let Coq_existT (x, _) = kv in
      (match Obj.magic x with
       | KRead -> Obj.magic Read
       | KWrite -> Obj.magic Write
       | KReadWrite -> Obj.magic ReadWrite
       | KExecute -> Obj.magic Execute)
    | Coq_exception_type ->
      let Coq_existT (x, _) = kv in
      (match Obj.magic x with
       | KE_Fetch_Access_Fault -> Obj.magic E_Fetch_Access_Fault
       | KE_Load_Access_Fault -> Obj.magic E_Load_Access_Fault
       | KE_SAMO_Access_Fault -> Obj.magic E_SAMO_Access_Fault
       | KE_U_EnvCall -> Obj.magic E_U_EnvCall
       | KE_M_EnvCall -> Obj.magic E_M_EnvCall
       | KE_Illegal_Instr -> Obj.magic E_Illegal_Instr)
    | Coq_memory_op_result _ ->
      let Coq_existT (x, e) = kv in
      (match Obj.magic x with
       | KMemValue -> Obj.magic (MemValue (Obj.magic e))
       | KMemException -> Obj.magic (MemException (Obj.magic e)))
    | Coq_fetch_result ->
      let Coq_existT (x, v) = kv in
      (match Obj.magic x with
       | KF_Base -> Obj.magic (F_Base (Obj.magic v))
       | KF_Error ->
         let Coq_pair (e, v0) = Obj.magic v in Obj.magic (F_Error (e, v0)))
    | Coq_ctl_result ->
      let Coq_existT (x, e) = kv in
      (match Obj.magic x with
       | KCTL_TRAP -> Obj.magic (CTL_TRAP (Obj.magic e))
       | KCTL_MRET -> Obj.magic CTL_MRET)
    | Coq_interrupt_set ->
      let Coq_existT (x, v) = kv in
      (match Obj.magic x with
       | KInts_Pending -> Obj.magic (Ints_Pending (Obj.magic v))
       | KInts_Delegated -> Obj.magic (Ints_Delegated (Obj.magic v))
       | KInts_Empty -> Obj.magic Ints_Empty)

  (** val record_field_type :
      Coq_ty.recordi -> (string, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let record_field_type r =
    match Obj.magic r with
    | Coq_rpmpcfg_ent ->
      Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        { Binding.name = (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)), EmptyString));
        Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name = (String
        ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_false)), EmptyString)); Binding.coq_type =
        ty_pmpaddrmatchtype })), { Binding.name = (String ((Ascii (Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_false)), EmptyString)); Binding.coq_type = Coq_ty.Coq_bool })),
        { Binding.name = (String ((Ascii (Coq_true, Coq_true, Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), EmptyString));
        Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name = (String
        ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_false)), EmptyString)); Binding.coq_type =
        Coq_ty.Coq_bool })
    | Coq_rmstatus ->
      Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, { Binding.name = (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_false)), EmptyString))))));
        Binding.coq_type = ty_privilege })), { Binding.name = (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_false)), EmptyString)))))))); Binding.coq_type =
        Coq_ty.Coq_bool })), { Binding.name = (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_false)), EmptyString))))));
        Binding.coq_type = Coq_ty.Coq_bool })
    | Coq_rminterrupts ->
      Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, { Binding.name = (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false)), EmptyString))))));
        Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name = (String
        ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
        EmptyString)))))); Binding.coq_type = Coq_ty.Coq_bool })),
        { Binding.name = (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false)), EmptyString)))))); Binding.coq_type =
        Coq_ty.Coq_bool })), { Binding.name = (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false)), EmptyString))))));
        Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name = (String
        ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
        EmptyString)))))); Binding.coq_type = Coq_ty.Coq_bool })),
        { Binding.name = (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false)), EmptyString)))))); Binding.coq_type = Coq_ty.Coq_bool })

  (** val record_fold :
      Coq_ty.recordi -> (string, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv
      -> Coq_ty.recordt **)

  let record_fold r n =
    match Obj.magic r with
    | Coq_rpmpcfg_ent ->
      (match n with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e, _, db) ->
         (match e with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e0, _, db0) ->
            (match e0 with
             | Coq_env.Coq_nil -> assert false (* absurd case *)
             | Coq_env.Coq_snoc (_, e1, _, db1) ->
               (match e1 with
                | Coq_env.Coq_nil -> assert false (* absurd case *)
                | Coq_env.Coq_snoc (_, e2, _, db2) ->
                  (match e2 with
                   | Coq_env.Coq_nil -> assert false (* absurd case *)
                   | Coq_env.Coq_snoc (_, e3, _, db3) ->
                     (match e3 with
                      | Coq_env.Coq_nil ->
                        Obj.magic { coq_L = (Obj.magic db3); coq_A =
                          (Obj.magic db2); coq_X = (Obj.magic db1); coq_W =
                          (Obj.magic db0); coq_R = (Obj.magic db) }
                      | Coq_env.Coq_snoc (_, _, _, _) ->
                        assert false (* absurd case *)))))))
    | Coq_rmstatus ->
      (match n with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e, _, db) ->
         (match e with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e0, _, db0) ->
            (match e0 with
             | Coq_env.Coq_nil -> assert false (* absurd case *)
             | Coq_env.Coq_snoc (_, e1, _, db1) ->
               (match e1 with
                | Coq_env.Coq_nil ->
                  Obj.magic { coq_MPP = (Obj.magic db1); coq_MPIE =
                    (Obj.magic db0); coq_MIE = (Obj.magic db) }
                | Coq_env.Coq_snoc (_, _, _, _) ->
                  assert false (* absurd case *)))))
    | Coq_rminterrupts ->
      (match n with
       | Coq_env.Coq_nil -> assert false (* absurd case *)
       | Coq_env.Coq_snoc (_, e, _, db) ->
         (match e with
          | Coq_env.Coq_nil -> assert false (* absurd case *)
          | Coq_env.Coq_snoc (_, e0, _, db0) ->
            (match e0 with
             | Coq_env.Coq_nil -> assert false (* absurd case *)
             | Coq_env.Coq_snoc (_, e1, _, db1) ->
               (match e1 with
                | Coq_env.Coq_nil -> assert false (* absurd case *)
                | Coq_env.Coq_snoc (_, e2, _, db2) ->
                  (match e2 with
                   | Coq_env.Coq_nil -> assert false (* absurd case *)
                   | Coq_env.Coq_snoc (_, e3, _, db3) ->
                     (match e3 with
                      | Coq_env.Coq_nil -> assert false (* absurd case *)
                      | Coq_env.Coq_snoc (_, e4, _, db4) ->
                        (match e4 with
                         | Coq_env.Coq_nil ->
                           Obj.magic { coq_MEI = (Obj.magic db4); coq_UEI =
                             (Obj.magic db3); coq_MTI = (Obj.magic db2);
                             coq_UTI = (Obj.magic db1); coq_MSI =
                             (Obj.magic db0); coq_USI = (Obj.magic db) }
                         | Coq_env.Coq_snoc (_, _, _, _) ->
                           assert false (* absurd case *))))))))

  (** val record_unfold :
      Coq_ty.recordi -> Coq_ty.recordt -> (string, Coq_ty.coq_Ty,
      Coq_ty.coq_Val) coq_NamedEnv **)

  let record_unfold r r0 =
    match Obj.magic r with
    | Coq_rpmpcfg_ent ->
      Coq_env.kvsnoc (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false)), EmptyString)); Binding.coq_type = Coq_ty.Coq_bool },
          (Obj.magic r0).coq_L))))),
        (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
          Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
          Coq_false)), EmptyString)); Binding.coq_type =
          ty_pmpaddrmatchtype }, (Obj.magic r0).coq_A))))),
        (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_false,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_false)), EmptyString)); Binding.coq_type = Coq_ty.Coq_bool },
          (Obj.magic r0).coq_X))))),
        (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
          Coq_true, Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
          Coq_false)), EmptyString)); Binding.coq_type = Coq_ty.Coq_bool },
          (Obj.magic r0).coq_W)))))
        (Coq_env.kvsnoc (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
          ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_false)), EmptyString)); Binding.coq_type = Coq_ty.Coq_bool },
            (Obj.magic r0).coq_L))))),
          (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false)), EmptyString)); Binding.coq_type =
            ty_pmpaddrmatchtype }, (Obj.magic r0).coq_A))))),
          (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_false)), EmptyString)); Binding.coq_type = Coq_ty.Coq_bool },
            (Obj.magic r0).coq_X)))))
          (Coq_env.kvsnoc (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
            (Coq_ctx.Coq_nil,
            (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_false,
              Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
              Coq_false)), EmptyString)); Binding.coq_type =
              Coq_ty.Coq_bool }, (Obj.magic r0).coq_L))))),
            (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
              Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
              Coq_true, Coq_false)), EmptyString)); Binding.coq_type =
              ty_pmpaddrmatchtype }, (Obj.magic r0).coq_A)))))
            (Coq_env.kvsnoc (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
              (projT1 (Coq_existT ({ Binding.name = (String ((Ascii
                (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
                Coq_false, Coq_true, Coq_false)), EmptyString));
                Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_L)))))
              (Coq_env.kvsnoc Coq_ctx.Coq_nil Coq_env.Coq_nil (Coq_existT
                ({ Binding.name = (String ((Ascii (Coq_false, Coq_false,
                Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                Coq_false)), EmptyString)); Binding.coq_type =
                Coq_ty.Coq_bool }, (Obj.magic (Obj.magic r0).coq_L))))
              (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
              Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
              Coq_true, Coq_false)), EmptyString)); Binding.coq_type =
              ty_pmpaddrmatchtype }, (Obj.magic (Obj.magic r0).coq_A))))
            (Coq_existT ({ Binding.name = (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_false)), EmptyString)); Binding.coq_type = Coq_ty.Coq_bool },
            (Obj.magic (Obj.magic r0).coq_X))))
          (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true, Coq_true,
          Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)),
          EmptyString)); Binding.coq_type = Coq_ty.Coq_bool },
          (Obj.magic (Obj.magic r0).coq_W))))
        (Coq_existT ({ Binding.name = (String ((Ascii (Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)),
        EmptyString)); Binding.coq_type = Coq_ty.Coq_bool },
        (Obj.magic (Obj.magic r0).coq_R)))
    | Coq_rmstatus ->
      Coq_env.kvsnoc (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_false)), EmptyString))))));
          Binding.coq_type = ty_privilege }, (Obj.magic r0).coq_MPP))))),
        (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
          Coq_false, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
          Coq_false)), EmptyString)))))))); Binding.coq_type =
          Coq_ty.Coq_bool }, (Obj.magic r0).coq_MPIE)))))
        (Coq_env.kvsnoc (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_false)), EmptyString))))));
            Binding.coq_type = ty_privilege }, (Obj.magic r0).coq_MPP)))))
          (Coq_env.kvsnoc Coq_ctx.Coq_nil Coq_env.Coq_nil (Coq_existT
            ({ Binding.name = (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false)), EmptyString)))))); Binding.coq_type =
            ty_privilege }, (Obj.magic (Obj.magic r0).coq_MPP))))
          (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
          (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_false, Coq_true, Coq_false)), (String ((Ascii
          (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
          Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
          Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)),
          EmptyString)))))))); Binding.coq_type = Coq_ty.Coq_bool },
          (Obj.magic (Obj.magic r0).coq_MPIE))))
        (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_false)), EmptyString)))))); Binding.coq_type = Coq_ty.Coq_bool },
        (Obj.magic (Obj.magic r0).coq_MIE)))
    | Coq_rminterrupts ->
      Coq_env.kvsnoc (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_false)), EmptyString))))));
          Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_MEI))))),
        (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_false)), EmptyString))))));
          Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_UEI))))),
        (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_false)), EmptyString))))));
          Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_MTI))))),
        (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
          Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_false)), EmptyString))))));
          Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_UTI))))),
        (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_false)), EmptyString))))));
          Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_MSI)))))
        (Coq_env.kvsnoc (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
          ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false)), EmptyString))))));
            Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_MEI))))),
          (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false)), EmptyString))))));
            Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_UEI))))),
          (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false)), EmptyString))))));
            Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_MTI))))),
          (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false)), EmptyString))))));
            Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_UTI)))))
          (Coq_env.kvsnoc (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
            ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
            (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
              Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
              Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
              Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
              ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
              Coq_false, Coq_true, Coq_false)), EmptyString))))));
              Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_MEI))))),
            (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
              Coq_false, Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
              Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
              Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
              ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
              Coq_false, Coq_true, Coq_false)), EmptyString))))));
              Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_UEI))))),
            (projT1 (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
              Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
              Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
              Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
              ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
              Coq_false, Coq_true, Coq_false)), EmptyString))))));
              Binding.coq_type = Coq_ty.Coq_bool }, (Obj.magic r0).coq_MTI)))))
            (Coq_env.kvsnoc (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
              (Coq_ctx.Coq_nil,
              (projT1 (Coq_existT ({ Binding.name = (String ((Ascii
                (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
                Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                Coq_false, Coq_true, Coq_false, Coq_false, Coq_false,
                Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                Coq_false)), EmptyString)))))); Binding.coq_type =
                Coq_ty.Coq_bool }, (Obj.magic r0).coq_MEI))))),
              (projT1 (Coq_existT ({ Binding.name = (String ((Ascii
                (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
                Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                Coq_false, Coq_true, Coq_false, Coq_false, Coq_false,
                Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                Coq_false)), EmptyString)))))); Binding.coq_type =
                Coq_ty.Coq_bool }, (Obj.magic r0).coq_UEI)))))
              (Coq_env.kvsnoc (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
                (projT1 (Coq_existT ({ Binding.name = (String ((Ascii
                  (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
                  Coq_false, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_false)), EmptyString))))));
                  Binding.coq_type = Coq_ty.Coq_bool },
                  (Obj.magic r0).coq_MEI)))))
                (Coq_env.kvsnoc Coq_ctx.Coq_nil Coq_env.Coq_nil (Coq_existT
                  ({ Binding.name = (String ((Ascii (Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_false)), EmptyString)))))); Binding.coq_type =
                  Coq_ty.Coq_bool }, (Obj.magic (Obj.magic r0).coq_MEI))))
                (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
                Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
                Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
                Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
                Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
                EmptyString)))))); Binding.coq_type = Coq_ty.Coq_bool },
                (Obj.magic (Obj.magic r0).coq_UEI))))
              (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
              Coq_false, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
              Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
              Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
              ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
              Coq_false, Coq_true, Coq_false)), EmptyString))))));
              Binding.coq_type = Coq_ty.Coq_bool },
              (Obj.magic (Obj.magic r0).coq_MTI))))
            (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false)), EmptyString))))));
            Binding.coq_type = Coq_ty.Coq_bool },
            (Obj.magic (Obj.magic r0).coq_UTI))))
          (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
          (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
          Coq_true, Coq_false, Coq_true, Coq_false)), (String ((Ascii
          (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
          Coq_true, Coq_false)), EmptyString)))))); Binding.coq_type =
          Coq_ty.Coq_bool }, (Obj.magic (Obj.magic r0).coq_MSI))))
        (Coq_existT ({ Binding.name = (String ((Ascii (Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false)), EmptyString)))))); Binding.coq_type = Coq_ty.Coq_bool },
        (Obj.magic (Obj.magic r0).coq_USI)))

  (** val typedefkit : Coq_ty.coq_TypeDefKit **)

  let typedefkit =
    { Coq_ty.enum_eqdec = (Obj.magic coq_Enums_EqDec); Coq_ty.union_eqdec =
      (Obj.magic coq_Unions_EqDec); Coq_ty.record_eqdec =
      (Obj.magic coq_Records_EqDec); Coq_ty.enumt_eqdec =
      (Obj.magic eqdec_enum_denote); Coq_ty.enumt_finite =
      (Obj.magic finite_enum_denote); Coq_ty.uniont_eqdec =
      (Obj.magic eqdec_union_denote); Coq_ty.unionk_eqdec =
      (Obj.magic eqdec_union_constructor); Coq_ty.unionk_finite =
      (Obj.magic finite_union_constructor); Coq_ty.unionk_ty =
      (Obj.magic union_constructor_type); Coq_ty.recordt_eqdec =
      (Obj.magic eqdec_record_denote); Coq_ty.recordf_ty =
      (Obj.magic record_field_type); Coq_ty.unionv_fold = union_fold;
      Coq_ty.unionv_unfold = union_unfold; Coq_ty.recordv_fold =
      (Obj.magic record_fold); Coq_ty.recordv_unfold =
      (Obj.magic record_unfold) }

  (** val varkit : coq_VarKit **)

  let varkit =
    coq_DefaultVarKit

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

  (** val coq_Reg_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> Coq_ty.coq_Ty -> coq_Reg -> 'a1 **)

  let coq_Reg_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 _ = function
  | Coq_pc -> f
  | Coq_nextpc -> f0
  | Coq_mstatus -> f1
  | Coq_mie -> f2
  | Coq_mip -> f3
  | Coq_mtvec -> f4
  | Coq_mcause -> f5
  | Coq_mepc -> f6
  | Coq_mscratch -> f7
  | Coq_cur_privilege -> f8
  | Coq_x1 -> f9
  | Coq_x2 -> f10
  | Coq_x3 -> f11
  | Coq_x4 -> f12
  | Coq_x5 -> f13
  | Coq_x6 -> f14
  | Coq_x7 -> f15
  | Coq_x8 -> f16
  | Coq_x9 -> f17
  | Coq_x10 -> f18
  | Coq_x11 -> f19
  | Coq_x12 -> f20
  | Coq_x13 -> f21
  | Coq_x14 -> f22
  | Coq_x15 -> f23
  | Coq_x16 -> f24
  | Coq_x17 -> f25
  | Coq_x18 -> f26
  | Coq_x19 -> f27
  | Coq_x20 -> f28
  | Coq_x21 -> f29
  | Coq_x22 -> f30
  | Coq_x23 -> f31
  | Coq_x24 -> f32
  | Coq_x25 -> f33
  | Coq_x26 -> f34
  | Coq_x27 -> f35
  | Coq_x28 -> f36
  | Coq_x29 -> f37
  | Coq_x30 -> f38
  | Coq_x31 -> f39
  | Coq_pmp0cfg -> f40
  | Coq_pmp1cfg -> f41
  | Coq_pmpaddr0 -> f42
  | Coq_pmpaddr1 -> f43

  (** val coq_Reg_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> Coq_ty.coq_Ty -> coq_Reg -> 'a1 **)

  let coq_Reg_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 _ = function
  | Coq_pc -> f
  | Coq_nextpc -> f0
  | Coq_mstatus -> f1
  | Coq_mie -> f2
  | Coq_mip -> f3
  | Coq_mtvec -> f4
  | Coq_mcause -> f5
  | Coq_mepc -> f6
  | Coq_mscratch -> f7
  | Coq_cur_privilege -> f8
  | Coq_x1 -> f9
  | Coq_x2 -> f10
  | Coq_x3 -> f11
  | Coq_x4 -> f12
  | Coq_x5 -> f13
  | Coq_x6 -> f14
  | Coq_x7 -> f15
  | Coq_x8 -> f16
  | Coq_x9 -> f17
  | Coq_x10 -> f18
  | Coq_x11 -> f19
  | Coq_x12 -> f20
  | Coq_x13 -> f21
  | Coq_x14 -> f22
  | Coq_x15 -> f23
  | Coq_x16 -> f24
  | Coq_x17 -> f25
  | Coq_x18 -> f26
  | Coq_x19 -> f27
  | Coq_x20 -> f28
  | Coq_x21 -> f29
  | Coq_x22 -> f30
  | Coq_x23 -> f31
  | Coq_x24 -> f32
  | Coq_x25 -> f33
  | Coq_x26 -> f34
  | Coq_x27 -> f35
  | Coq_x28 -> f36
  | Coq_x29 -> f37
  | Coq_x30 -> f38
  | Coq_x31 -> f39
  | Coq_pmp0cfg -> f40
  | Coq_pmp1cfg -> f41
  | Coq_pmpaddr0 -> f42
  | Coq_pmpaddr1 -> f43

  (** val reg_convert : coq_RegIdx -> coq_Reg option **)

  let reg_convert idx =
    match Obj.magic Coq_bv.to_bitstring (S (S (S (S (S O))))) idx with
    | Coq_bv.Coq_bitstring.Coq_bO b ->
      (match b with
       | Coq_bv.Coq_bitstring.Coq_bO d ->
         (match d with
          | Coq_bv.Coq_bitstring.Coq_bO d0 ->
            (match d0 with
             | Coq_bv.Coq_bitstring.Coq_bO d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> None
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x1)
             | Coq_bv.Coq_bitstring.Coq_bI d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x2
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x3))
          | Coq_bv.Coq_bitstring.Coq_bI d0 ->
            (match d0 with
             | Coq_bv.Coq_bitstring.Coq_bO d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x4
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x5)
             | Coq_bv.Coq_bitstring.Coq_bI d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x6
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x7)))
       | Coq_bv.Coq_bitstring.Coq_bI d ->
         (match d with
          | Coq_bv.Coq_bitstring.Coq_bO d0 ->
            (match d0 with
             | Coq_bv.Coq_bitstring.Coq_bO d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x8
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x9)
             | Coq_bv.Coq_bitstring.Coq_bI d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x10
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x11))
          | Coq_bv.Coq_bitstring.Coq_bI d0 ->
            (match d0 with
             | Coq_bv.Coq_bitstring.Coq_bO d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x12
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x13)
             | Coq_bv.Coq_bitstring.Coq_bI d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x14
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x15))))
    | Coq_bv.Coq_bitstring.Coq_bI b ->
      (match b with
       | Coq_bv.Coq_bitstring.Coq_bO d ->
         (match d with
          | Coq_bv.Coq_bitstring.Coq_bO d0 ->
            (match d0 with
             | Coq_bv.Coq_bitstring.Coq_bO d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x16
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x17)
             | Coq_bv.Coq_bitstring.Coq_bI d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x18
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x19))
          | Coq_bv.Coq_bitstring.Coq_bI d0 ->
            (match d0 with
             | Coq_bv.Coq_bitstring.Coq_bO d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x20
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x21)
             | Coq_bv.Coq_bitstring.Coq_bI d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x22
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x23)))
       | Coq_bv.Coq_bitstring.Coq_bI d ->
         (match d with
          | Coq_bv.Coq_bitstring.Coq_bO d0 ->
            (match d0 with
             | Coq_bv.Coq_bitstring.Coq_bO d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x24
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x25)
             | Coq_bv.Coq_bitstring.Coq_bI d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x26
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x27))
          | Coq_bv.Coq_bitstring.Coq_bI d0 ->
            (match d0 with
             | Coq_bv.Coq_bitstring.Coq_bO d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x28
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x29)
             | Coq_bv.Coq_bitstring.Coq_bI d1 ->
               (match d1 with
                | Coq_bv.Coq_bitstring.Coq_bO _ -> Some Coq_x30
                | Coq_bv.Coq_bitstring.Coq_bI _ -> Some Coq_x31))))

  type coq_Reg_sig = coq_Reg

  (** val coq_Reg_sig_pack :
      Coq_ty.coq_Ty -> coq_Reg -> Coq_ty.coq_Ty * coq_Reg **)

  let coq_Reg_sig_pack x reg_var =
    x,reg_var

  (** val coq_Reg_Signature :
      Coq_ty.coq_Ty -> (coq_Reg, Coq_ty.coq_Ty, coq_Reg_sig) coq_Signature **)

  let coq_Reg_Signature x reg_var =
    x,reg_var

  (** val coq_NoConfusionPackage_Reg :
      (Coq_ty.coq_Ty * coq_Reg) coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_Reg =
    Build_NoConfusionPackage

  type _UU1d479__UU1d46c__UU1d46e_ = coq_Reg

  (** val _UU1d479__UU1d46c__UU1d46e__eq_dec :
      (Coq_ty.coq_Ty, coq_Reg) sigT coq_EqDec **)

  let _UU1d479__UU1d46c__UU1d46e__eq_dec pat pat0 =
    let Coq_existT (_, x) = pat in
    let Coq_existT (_, y) = pat0 in
    (match x with
     | Coq_pc -> (match y with
                  | Coq_pc -> Coq_left
                  | _ -> Coq_right)
     | Coq_nextpc -> (match y with
                      | Coq_nextpc -> Coq_left
                      | _ -> Coq_right)
     | Coq_mstatus -> (match y with
                       | Coq_mstatus -> Coq_left
                       | _ -> Coq_right)
     | Coq_mie -> (match y with
                   | Coq_mie -> Coq_left
                   | _ -> Coq_right)
     | Coq_mip -> (match y with
                   | Coq_mip -> Coq_left
                   | _ -> Coq_right)
     | Coq_mtvec -> (match y with
                     | Coq_mtvec -> Coq_left
                     | _ -> Coq_right)
     | Coq_mcause -> (match y with
                      | Coq_mcause -> Coq_left
                      | _ -> Coq_right)
     | Coq_mepc -> (match y with
                    | Coq_mepc -> Coq_left
                    | _ -> Coq_right)
     | Coq_mscratch ->
       (match y with
        | Coq_mscratch -> Coq_left
        | _ -> Coq_right)
     | Coq_cur_privilege ->
       (match y with
        | Coq_cur_privilege -> Coq_left
        | _ -> Coq_right)
     | Coq_x1 -> (match y with
                  | Coq_x1 -> Coq_left
                  | _ -> Coq_right)
     | Coq_x2 -> (match y with
                  | Coq_x2 -> Coq_left
                  | _ -> Coq_right)
     | Coq_x3 -> (match y with
                  | Coq_x3 -> Coq_left
                  | _ -> Coq_right)
     | Coq_x4 -> (match y with
                  | Coq_x4 -> Coq_left
                  | _ -> Coq_right)
     | Coq_x5 -> (match y with
                  | Coq_x5 -> Coq_left
                  | _ -> Coq_right)
     | Coq_x6 -> (match y with
                  | Coq_x6 -> Coq_left
                  | _ -> Coq_right)
     | Coq_x7 -> (match y with
                  | Coq_x7 -> Coq_left
                  | _ -> Coq_right)
     | Coq_x8 -> (match y with
                  | Coq_x8 -> Coq_left
                  | _ -> Coq_right)
     | Coq_x9 -> (match y with
                  | Coq_x9 -> Coq_left
                  | _ -> Coq_right)
     | Coq_x10 -> (match y with
                   | Coq_x10 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x11 -> (match y with
                   | Coq_x11 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x12 -> (match y with
                   | Coq_x12 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x13 -> (match y with
                   | Coq_x13 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x14 -> (match y with
                   | Coq_x14 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x15 -> (match y with
                   | Coq_x15 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x16 -> (match y with
                   | Coq_x16 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x17 -> (match y with
                   | Coq_x17 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x18 -> (match y with
                   | Coq_x18 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x19 -> (match y with
                   | Coq_x19 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x20 -> (match y with
                   | Coq_x20 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x21 -> (match y with
                   | Coq_x21 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x22 -> (match y with
                   | Coq_x22 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x23 -> (match y with
                   | Coq_x23 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x24 -> (match y with
                   | Coq_x24 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x25 -> (match y with
                   | Coq_x25 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x26 -> (match y with
                   | Coq_x26 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x27 -> (match y with
                   | Coq_x27 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x28 -> (match y with
                   | Coq_x28 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x29 -> (match y with
                   | Coq_x29 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x30 -> (match y with
                   | Coq_x30 -> Coq_left
                   | _ -> Coq_right)
     | Coq_x31 -> (match y with
                   | Coq_x31 -> Coq_left
                   | _ -> Coq_right)
     | Coq_pmp0cfg -> (match y with
                       | Coq_pmp0cfg -> Coq_left
                       | _ -> Coq_right)
     | Coq_pmp1cfg -> (match y with
                       | Coq_pmp1cfg -> Coq_left
                       | _ -> Coq_right)
     | Coq_pmpaddr0 ->
       (match y with
        | Coq_pmpaddr0 -> Coq_left
        | _ -> Coq_right)
     | Coq_pmpaddr1 ->
       (match y with
        | Coq_pmpaddr1 -> Coq_left
        | _ -> Coq_right))

  (** val _UU1d479__UU1d46c__UU1d46e__finite :
      (Coq_ty.coq_Ty, coq_Reg) sigT coq_Finite **)

  let _UU1d479__UU1d46c__UU1d46e__finite =
    Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_pc)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_nextpc)),
      (Datatypes.Coq_cons ((Coq_existT (ty_mstatus, Coq_mstatus)),
      (Datatypes.Coq_cons ((Coq_existT (ty_Minterrupts, Coq_mie)),
      (Datatypes.Coq_cons ((Coq_existT (ty_Minterrupts, Coq_mip)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_mtvec)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_mscratch)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_mepc)),
      (Datatypes.Coq_cons ((Coq_existT (ty_mcause, Coq_mcause)),
      (Datatypes.Coq_cons ((Coq_existT (ty_privilege, Coq_cur_privilege)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x1)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x2)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x3)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x4)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x5)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x6)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x7)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x8)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x9)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x10)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x11)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x12)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x13)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x14)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x15)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x16)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x17)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x18)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x19)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x20)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x21)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x22)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x23)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x24)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x25)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x26)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x27)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x28)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x29)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x30)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_x31)),
      (Datatypes.Coq_cons ((Coq_existT (ty_pmpcfg_ent, Coq_pmp0cfg)),
      (Datatypes.Coq_cons ((Coq_existT (ty_pmpcfg_ent, Coq_pmp1cfg)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_pmpaddr0)),
      (Datatypes.Coq_cons ((Coq_existT (ty_xlenbits, Coq_pmpaddr1)),
      Datatypes.Coq_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val val_inhabited : Coq_ty.coq_Ty -> Coq_ty.coq_Val coq_Inhabited **)

  let rec val_inhabited = function
  | Coq_ty.Coq_int -> Obj.magic Z.inhabited
  | Coq_ty.Coq_bool -> Obj.magic bool_inhabated
  | Coq_ty.Coq_string -> Obj.magic Strings.String.inhabited
  | Coq_ty.Coq_list _ -> Obj.magic list_inhabited
  | Coq_ty.Coq_prod (_UU03c3_0, _UU03c4_) ->
    Obj.magic prod_inhabited (val_inhabited _UU03c3_0)
      (val_inhabited _UU03c4_)
  | Coq_ty.Coq_sum (_, _UU03c4_) ->
    Obj.magic sum_inhabited_r (val_inhabited _UU03c4_)
  | Coq_ty.Coq_unit -> Obj.magic unit_inhabited
  | Coq_ty.Coq_enum e ->
    (match Obj.magic e with
     | Coq_privilege -> Obj.magic User
     | Coq_interruptType -> Obj.magic I_U_Software
     | Coq_csridx -> Obj.magic MStatus
     | Coq_pmpcfgidx -> Obj.magic PMP0CFG
     | Coq_pmpcfgperm -> Obj.magic PmpO
     | Coq_pmpaddridx -> Obj.magic PMPADDR0
     | Coq_pmpaddrmatchtype -> Obj.magic OFF
     | Coq_pmpmatch -> Obj.magic PMP_Success
     | Coq_pmpaddrmatch -> Obj.magic PMP_NoMatch
     | Coq_rop -> Obj.magic RISCV_ADD
     | Coq_iop -> Obj.magic RISCV_ADDI
     | Coq_sop -> Obj.magic RISCV_SLLI
     | Coq_uop -> Obj.magic RISCV_LUI
     | Coq_bop -> Obj.magic RISCV_BEQ
     | Coq_csrop -> Obj.magic CSRRW
     | Coq_retired -> Obj.magic RETIRE_SUCCESS
     | Coq_wordwidth -> Obj.magic BYTE
     | Coq_mop -> Obj.magic RISCV_MUL)
  | Coq_ty.Coq_bvec n -> Obj.magic Coq_bv.bv_inhabited n
  | Coq_ty.Coq_tuple _UU03c3_s ->
    let rec f c iH =
      match c with
      | Coq_ctx.Coq_nil -> Obj.magic unit_inhabited
      | Coq_ctx.Coq_snoc (_UU0393_, _) ->
        let h = fun _ ->
          match iH with
          | Coq_ctx.Coq_all_nil -> assert false (* absurd case *)
          | Coq_ctx.Coq_all_snoc (_, _, x, x0) ->
            prod_inhabited (f _UU0393_ x) x0
        in
        Obj.magic h __
    in f _UU03c3_s (Coq_ctx.all_intro val_inhabited _UU03c3_s)
  | Coq_ty.Coq_union u ->
    (match Obj.magic u with
     | Coq_ast ->
       Obj.magic (RTYPE ((Coq_bv.bv_inhabited (S (S (S (S (S O)))))),
         (Coq_bv.bv_inhabited (S (S (S (S (S O)))))),
         (Coq_bv.bv_inhabited (S (S (S (S (S O)))))), RISCV_ADD))
     | Coq_access_type -> Obj.magic Read
     | Coq_exception_type -> Obj.magic E_Fetch_Access_Fault
     | Coq_memory_op_result bytes ->
       Obj.magic (MemValue
         (Coq_bv.bv_inhabited (mul bytes (S (S (S (S (S (S (S (S O)))))))))))
     | Coq_fetch_result -> Obj.magic (F_Base (Coq_bv.bv_inhabited word))
     | Coq_ctl_result -> Obj.magic (CTL_TRAP E_Fetch_Access_Fault)
     | Coq_interrupt_set ->
       Obj.magic (Ints_Pending { coq_MEI = Coq_true; coq_UEI = Coq_true;
         coq_MTI = Coq_true; coq_UTI = Coq_true; coq_MSI = Coq_true;
         coq_USI = Coq_true }))
  | Coq_ty.Coq_record r ->
    (match Obj.magic r with
     | Coq_rpmpcfg_ent ->
       Obj.magic { coq_L = Coq_true; coq_A = OFF; coq_X = Coq_true; coq_W =
         Coq_true; coq_R = Coq_true }
     | Coq_rmstatus ->
       Obj.magic { coq_MPP = User; coq_MPIE = Coq_true; coq_MIE = Coq_true }
     | Coq_rminterrupts ->
       Obj.magic { coq_MEI = Coq_true; coq_UEI = Coq_true; coq_MTI =
         Coq_true; coq_UTI = Coq_true; coq_MSI = Coq_true; coq_USI =
         Coq_true })

  type coq_RAM = coq_Addr -> coq_Byte

  type coq_EventTy =
  | IOWrite
  | IORead

  (** val coq_EventTy_rect : 'a1 -> 'a1 -> coq_EventTy -> 'a1 **)

  let coq_EventTy_rect f f0 = function
  | IOWrite -> f
  | IORead -> f0

  (** val coq_EventTy_rec : 'a1 -> 'a1 -> coq_EventTy -> 'a1 **)

  let coq_EventTy_rec f f0 = function
  | IOWrite -> f
  | IORead -> f0

  type coq_Event = { event_type : coq_EventTy; event_addr : coq_Addr;
                     event_nbbytes : nat; event_contents : Coq_bv.bv }

  (** val event_type : coq_Event -> coq_EventTy **)

  let event_type e =
    e.event_type

  (** val event_addr : coq_Event -> coq_Addr **)

  let event_addr e =
    e.event_addr

  (** val event_nbbytes : coq_Event -> nat **)

  let event_nbbytes e =
    e.event_nbbytes

  (** val event_contents : coq_Event -> Coq_bv.bv **)

  let event_contents e =
    e.event_contents

  type coq_Trace = coq_Event list

  type coq_MemoryType = { memory_ram : coq_RAM; memory_trace : coq_Trace;
                          memory_state : coq_State }

  (** val memory_ram : coq_MemoryType -> coq_RAM **)

  let memory_ram m =
    m.memory_ram

  (** val memory_trace : coq_MemoryType -> coq_Trace **)

  let memory_trace m =
    m.memory_trace

  (** val memory_state : coq_MemoryType -> coq_State **)

  let memory_state m =
    m.memory_state

  type coq_Memory = coq_MemoryType

  (** val memory_update_ram : coq_Memory -> coq_RAM -> coq_MemoryType **)

  let memory_update_ram _UU03bc_ r =
    { memory_ram = r; memory_trace = _UU03bc_.memory_trace; memory_state =
      _UU03bc_.memory_state }

  (** val memory_update_trace : coq_Memory -> coq_Trace -> coq_MemoryType **)

  let memory_update_trace _UU03bc_ t0 =
    { memory_ram = _UU03bc_.memory_ram; memory_trace = t0; memory_state =
      _UU03bc_.memory_state }

  (** val memory_append_trace : coq_Memory -> coq_Event -> coq_MemoryType **)

  let memory_append_trace _UU03bc_ e =
    memory_update_trace _UU03bc_ (Datatypes.Coq_cons (e,
      _UU03bc_.memory_trace))

  (** val memory_update_state : coq_Memory -> coq_State -> coq_MemoryType **)

  let memory_update_state _UU03bc_ s =
    { memory_ram = _UU03bc_.memory_ram; memory_trace = _UU03bc_.memory_trace;
      memory_state = s }

  (** val fun_read_ram :
      coq_Memory -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val **)

  let rec fun_read_ram _UU03bc_ data_size addr =
    match data_size with
    | O -> Obj.magic Coq_bv.zero (mul O byte)
    | S n ->
      Obj.magic Coq_bv.app byte (mul n byte)
        (_UU03bc_.memory_ram (Obj.magic addr))
        (fun_read_ram _UU03bc_ n
          (Obj.magic Coq_bv.add xlenbits (Coq_bv.one xlenbits) addr))

  (** val write_byte : coq_RAM -> Coq_ty.coq_Val -> coq_Byte -> coq_RAM **)

  let write_byte r addr data a =
    match eq_dec (Coq_bv.eqdec_bv xlenbits) (Obj.magic addr) a with
    | Coq_left -> data
    | Coq_right -> r a

  (** val fun_write_ram :
      coq_Memory -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> coq_Memory **)

  let rec fun_write_ram _UU03bc_ data_size addr _data =
    match data_size with
    | O -> _UU03bc_
    | S n ->
      let Coq_bv.Coq_isapp (byte0, bytes) =
        Coq_bv.appView (S (S (S (S (S (S (S (S O))))))))
          (mul n (S (S (S (S (S (S (S (S O))))))))) (Obj.magic _data)
      in
      let _UU03bc_' =
        memory_update_ram _UU03bc_ (write_byte _UU03bc_.memory_ram addr byte0)
      in
      fun_write_ram _UU03bc_' n
        (Obj.magic Coq_bv.add xlenbits (Coq_bv.one xlenbits) addr)
        (Obj.magic bytes)

  (** val fun_within_mmio : nat -> Coq_ty.coq_Val -> bool **)

  let fun_within_mmio data_size addr =
    bool_decide
      (and_dec (withinMMIODec (Obj.magic addr) data_size)
        (decide_rel N.lt_dec
          (BinNat.N.add (Obj.magic addr) (BinNat.N.of_nat data_size))
          (BinNat.N.pow (Npos (Coq_xO Coq_xH)) (BinNat.N.of_nat xlenbits))))

  (** val fun_read_mmio :
      coq_Memory -> nat -> Coq_ty.coq_Val -> (coq_Memory, Coq_ty.coq_Val) prod **)

  let fun_read_mmio _UU03bc_ data_size addr =
    match data_size with
    | O -> Coq_pair (_UU03bc_, (Obj.magic Coq_bv.zero (mul data_size byte)))
    | S _ ->
      let Coq_pair (s', readv) =
        mmioenv.state_tra_read _UU03bc_.memory_state (Obj.magic addr)
          data_size
      in
      let mmioev = { event_type = IORead; event_addr = (Obj.magic addr);
        event_nbbytes = data_size; event_contents = readv }
      in
      let _UU03bc_' =
        memory_append_trace (memory_update_state _UU03bc_ s') mmioev
      in
      Coq_pair (_UU03bc_', (Obj.magic readv))

  (** val fun_externalWorldUpdates :
      coq_Memory -> (coq_Minterrupts, coq_Memory) prod **)

  let fun_externalWorldUpdates _UU03bc_ =
    Coq_pair ({ coq_MEI = Coq_false; coq_UEI = Coq_false; coq_MTI =
      Coq_false; coq_UTI = Coq_false; coq_MSI = Coq_false; coq_USI =
      Coq_false }, _UU03bc_)

  (** val fun_write_mmio :
      coq_Memory -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> coq_Memory **)

  let fun_write_mmio _UU03bc_ data_size addr _data =
    match data_size with
    | O -> _UU03bc_
    | S n ->
      let s' =
        mmioenv.state_tra_write _UU03bc_.memory_state (Obj.magic addr) (S n)
          (Obj.magic _data)
      in
      let mmioev = { event_type = IOWrite; event_addr = (Obj.magic addr);
        event_nbbytes = (S n); event_contents = (Obj.magic _data) }
      in
      memory_append_trace (memory_update_state _UU03bc_ s') mmioev

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

  (** val coq_Exp_rect :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar -> Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
      Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Exp -> 'a1 -> coq_Exp -> 'a1
      -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
      coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> coq_Exp list -> __ -> 'a1)
      -> (nat -> coq_Exp t -> __ -> 'a1) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty, coq_Exp) Coq_env.coq_Env -> __ -> 'a1) ->
      (Coq_ty.unioni -> Coq_ty.unionk -> coq_Exp -> 'a1 -> 'a1) ->
      (Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Exp)
      coq_NamedEnv -> __ -> 'a1) -> Coq_ty.coq_Ty -> coq_Exp -> 'a1 **)

  let rec coq_Exp_rect _UU0393_ p_var p_val p_binop p_unop p_list p_bvec p_tuple p_union p_record _ = function
  | Coq_exp_var (x, _UU03c3_, xIn_UU0393_) -> p_var x _UU03c3_ xIn_UU0393_
  | Coq_exp_val (_UU03c3_, l) -> p_val _UU03c3_ l
  | Coq_exp_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, e1, e2) ->
    p_binop _UU03c3_1 _UU03c3_2 _UU03c3_3 op e1
      (coq_Exp_rect _UU0393_ p_var p_val p_binop p_unop p_list p_bvec p_tuple
        p_union p_record _UU03c3_1 e1)
      e2
      (coq_Exp_rect _UU0393_ p_var p_val p_binop p_unop p_list p_bvec p_tuple
        p_union p_record _UU03c3_2 e2)
  | Coq_exp_unop (_UU03c3_1, _UU03c3_2, op, e0) ->
    p_unop _UU03c3_1 _UU03c3_2 op e0
      (coq_Exp_rect _UU0393_ p_var p_val p_binop p_unop p_list p_bvec p_tuple
        p_union p_record _UU03c3_1 e0)
  | Coq_exp_list (_UU03c3_, es) ->
    Obj.magic p_list _UU03c3_ es
      (let rec f = function
       | Datatypes.Coq_nil -> Obj.magic Coq_tt
       | Datatypes.Coq_cons (y, l0) ->
         Coq_pair
           ((coq_Exp_rect _UU0393_ p_var p_val p_binop p_unop p_list p_bvec
              p_tuple p_union p_record _UU03c3_ y),
           (Obj.magic f l0))
       in f es)
  | Coq_exp_bvec (n, es) ->
    Obj.magic p_bvec n es
      (let rec f _ = function
       | Coq_nil -> Obj.magic Coq_tt
       | Coq_cons (h, n0, t1) ->
         Coq_pair
           ((coq_Exp_rect _UU0393_ p_var p_val p_binop p_unop p_list p_bvec
              p_tuple p_union p_record Coq_ty.Coq_bool h),
           (Obj.magic f n0 t1))
       in f n es)
  | Coq_exp_tuple (_UU03c3_s, es) ->
    Obj.magic p_tuple _UU03c3_s es
      (let rec f _ = function
       | Coq_env.Coq_nil -> Obj.magic Coq_tt
       | Coq_env.Coq_snoc (_UU0393_0, e1, b, db) ->
         Coq_pair ((Obj.magic f _UU0393_0 e1),
           (coq_Exp_rect _UU0393_ p_var p_val p_binop p_unop p_list p_bvec
             p_tuple p_union p_record b db))
       in f _UU03c3_s es)
  | Coq_exp_union (u, k, e0) ->
    p_union u k e0
      (coq_Exp_rect _UU0393_ p_var p_val p_binop p_unop p_list p_bvec p_tuple
        p_union p_record (typedefkit.Coq_ty.unionk_ty u k) e0)
  | Coq_exp_record (r, es) ->
    Obj.magic p_record r es
      (let c = typedefkit.Coq_ty.recordf_ty r in
       let rec f _ = function
       | Coq_env.Coq_nil -> Obj.magic Coq_tt
       | Coq_env.Coq_snoc (_UU0393_0, e1, b, db) ->
         Coq_pair ((Obj.magic f _UU0393_0 e1),
           (coq_Exp_rect _UU0393_ p_var p_val p_binop p_unop p_list p_bvec
             p_tuple p_union p_record b.Binding.coq_type db))
       in f c es)

  (** val coq_Exp_rec :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar -> Coq_ty.coq_Ty -> (coq_PVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
      Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Exp -> 'a1 -> coq_Exp -> 'a1
      -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
      coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> coq_Exp list -> __ -> 'a1)
      -> (nat -> coq_Exp t -> __ -> 'a1) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty, coq_Exp) Coq_env.coq_Env -> __ -> 'a1) ->
      (Coq_ty.unioni -> Coq_ty.unionk -> coq_Exp -> 'a1 -> 'a1) ->
      (Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Exp)
      coq_NamedEnv -> __ -> 'a1) -> Coq_ty.coq_Ty -> coq_Exp -> 'a1 **)

  let rec coq_Exp_rec _UU0393_ p_var p_val p_binop p_unop p_list p_bvec p_tuple p_union p_record _ = function
  | Coq_exp_var (x, _UU03c3_, xIn_UU0393_) -> p_var x _UU03c3_ xIn_UU0393_
  | Coq_exp_val (_UU03c3_, l) -> p_val _UU03c3_ l
  | Coq_exp_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, e1, e2) ->
    p_binop _UU03c3_1 _UU03c3_2 _UU03c3_3 op e1
      (coq_Exp_rec _UU0393_ p_var p_val p_binop p_unop p_list p_bvec p_tuple
        p_union p_record _UU03c3_1 e1)
      e2
      (coq_Exp_rec _UU0393_ p_var p_val p_binop p_unop p_list p_bvec p_tuple
        p_union p_record _UU03c3_2 e2)
  | Coq_exp_unop (_UU03c3_1, _UU03c3_2, op, e0) ->
    p_unop _UU03c3_1 _UU03c3_2 op e0
      (coq_Exp_rec _UU0393_ p_var p_val p_binop p_unop p_list p_bvec p_tuple
        p_union p_record _UU03c3_1 e0)
  | Coq_exp_list (_UU03c3_, es) ->
    Obj.magic p_list _UU03c3_ es
      (let rec f = function
       | Datatypes.Coq_nil -> Obj.magic Coq_tt
       | Datatypes.Coq_cons (y, l0) ->
         Coq_pair
           ((coq_Exp_rec _UU0393_ p_var p_val p_binop p_unop p_list p_bvec
              p_tuple p_union p_record _UU03c3_ y),
           (Obj.magic f l0))
       in f es)
  | Coq_exp_bvec (n, es) ->
    Obj.magic p_bvec n es
      (let rec f _ = function
       | Coq_nil -> Obj.magic Coq_tt
       | Coq_cons (h, n0, t1) ->
         Coq_pair
           ((coq_Exp_rec _UU0393_ p_var p_val p_binop p_unop p_list p_bvec
              p_tuple p_union p_record Coq_ty.Coq_bool h),
           (Obj.magic f n0 t1))
       in f n es)
  | Coq_exp_tuple (_UU03c3_s, es) ->
    Obj.magic p_tuple _UU03c3_s es
      (let rec f _ = function
       | Coq_env.Coq_nil -> Obj.magic Coq_tt
       | Coq_env.Coq_snoc (_UU0393_0, e1, b, db) ->
         Coq_pair ((Obj.magic f _UU0393_0 e1),
           (coq_Exp_rec _UU0393_ p_var p_val p_binop p_unop p_list p_bvec
             p_tuple p_union p_record b db))
       in f _UU03c3_s es)
  | Coq_exp_union (u, k, e0) ->
    p_union u k e0
      (coq_Exp_rec _UU0393_ p_var p_val p_binop p_unop p_list p_bvec p_tuple
        p_union p_record (typedefkit.Coq_ty.unionk_ty u k) e0)
  | Coq_exp_record (r, es) ->
    Obj.magic p_record r es
      (let c = typedefkit.Coq_ty.recordf_ty r in
       let rec f _ = function
       | Coq_env.Coq_nil -> Obj.magic Coq_tt
       | Coq_env.Coq_snoc (_UU0393_0, e1, b, db) ->
         Coq_pair ((Obj.magic f _UU0393_0 e1),
           (coq_Exp_rec _UU0393_ p_var p_val p_binop p_unop p_list p_bvec
             p_tuple p_union p_record b.Binding.coq_type db))
       in f c es)

  (** val eval :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Exp -> (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val)
      coq_NamedEnv -> Coq_ty.coq_Val **)

  let rec eval _UU0393_ _ e _UU03b4_ =
    match e with
    | Coq_exp_var (x, _UU03c3_0, xIn_UU0393_) ->
      Coq_env.lookup _UU0393_ _UU03b4_ { Binding.name = x; Binding.coq_type =
        _UU03c3_0 } xIn_UU0393_
    | Coq_exp_val (_, l) -> l
    | Coq_exp_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, e1, e2) ->
      Coq_bop.eval typedeclkit typedenotekit typedefkit _UU03c3_1 _UU03c3_2
        _UU03c3_3 op (eval _UU0393_ _UU03c3_1 e1 _UU03b4_)
        (eval _UU0393_ _UU03c3_2 e2 _UU03b4_)
    | Coq_exp_unop (_UU03c3_1, _UU03c3_2, op, e0) ->
      Coq_uop.eval typedeclkit typedenotekit _UU03c3_1 _UU03c3_2 op
        (eval _UU0393_ _UU03c3_1 e0 _UU03b4_)
    | Coq_exp_list (_UU03c3_0, es) ->
      Obj.magic ListDef.map (fun e0 -> eval _UU0393_ _UU03c3_0 e0 _UU03b4_) es
    | Coq_exp_bvec (n, es) ->
      let rec f _ = function
      | Coq_nil -> Obj.magic Coq_bv.nil
      | Coq_cons (h, n0, t1) ->
        Obj.magic Coq_bv.cons n0 (eval _UU0393_ Coq_ty.Coq_bool h _UU03b4_)
          (f n0 t1)
      in f n es
    | Coq_exp_tuple (_UU03c3_s, es) ->
      let rec f _ = function
      | Coq_env.Coq_nil -> Obj.magic Coq_tt
      | Coq_env.Coq_snoc (_UU0393_0, e1, b, db) ->
        Obj.magic (Coq_pair ((f _UU0393_0 e1), (eval _UU0393_ b db _UU03b4_)))
      in f _UU03c3_s es
    | Coq_exp_union (u, k, e0) ->
      typedefkit.Coq_ty.unionv_fold u (Coq_existT (k,
        (eval _UU0393_ (typedefkit.Coq_ty.unionk_ty u k) e0 _UU03b4_)))
    | Coq_exp_record (r, es) ->
      typedefkit.Coq_ty.recordv_fold r
        (Coq_env.map (fun x_UU03c4_ e0 ->
          eval _UU0393_ x_UU03c4_.Binding.coq_type e0 _UU03b4_)
          (typedefkit.Coq_ty.recordf_ty r) es)

  (** val evals :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_PVar, Coq_ty.coq_Ty, coq_Exp) coq_NamedEnv -> (coq_PVar,
      Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv -> (coq_PVar,
      Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv **)

  let evals _UU0393_ _UU0394_ es _UU03b4_ =
    Coq_env.map (fun x_UU03c4_ e ->
      eval _UU0393_ x_UU03c4_.Binding.coq_type e _UU03b4_) _UU0394_ es

  (** val exp_truncate :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> coq_Exp -> coq_Exp **)

  let exp_truncate _ n m =
    let k = Coq_bv.leview m n in
    (fun x -> Coq_exp_unop ((Coq_ty.Coq_bvec (add m k)), (Coq_ty.Coq_bvec m),
    (Coq_uop.Coq_bvtake (m, k)), x))

  (** val exp_vector_subrange :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> coq_Exp -> coq_Exp **)

  let exp_vector_subrange _ n s l =
    let k = Coq_bv.leview (add s l) n in
    (fun t0 -> Coq_exp_unop ((Coq_ty.Coq_bvec (add s l)), (Coq_ty.Coq_bvec
    l), (Coq_uop.Coq_bvdrop (s, l)), (Coq_exp_unop ((Coq_ty.Coq_bvec
    (add (add s l) k)), (Coq_ty.Coq_bvec (add s l)), (Coq_uop.Coq_bvtake
    ((add s l), k)), t0))))

  (** val exp_update_vector_subrange :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> coq_Exp -> coq_Exp -> coq_Exp **)

  let exp_update_vector_subrange _ n s l =
    let k = Coq_bv.leview (add s l) n in
    (fun t0 u -> Coq_exp_binop ((Coq_ty.Coq_bvec (add s l)), (Coq_ty.Coq_bvec
    k), (Coq_ty.Coq_bvec (add (add s l) k)), (Coq_bop.Coq_bvapp ((add s l),
    k)), (Coq_exp_binop ((Coq_ty.Coq_bvec s), (Coq_ty.Coq_bvec l),
    (Coq_ty.Coq_bvec (add s l)), (Coq_bop.Coq_bvapp (s, l)), (Coq_exp_unop
    ((Coq_ty.Coq_bvec (add s l)), (Coq_ty.Coq_bvec s), (Coq_uop.Coq_bvtake
    (s, l)), (Coq_exp_unop ((Coq_ty.Coq_bvec (add (add s l) k)),
    (Coq_ty.Coq_bvec (add s l)), (Coq_uop.Coq_bvtake ((add s l), k)), t0)))),
    u)), (Coq_exp_unop ((Coq_ty.Coq_bvec (add (add s l) k)), (Coq_ty.Coq_bvec
    k), (Coq_uop.Coq_bvdrop ((add s l), k)), t0))))

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

  (** val coq_NoConfusionPackage_Term :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty * coq_Term) coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_Term _ =
    Build_NoConfusionPackage

  type coq_Term_sig = coq_Term

  (** val coq_Term_sig_pack :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> Coq_ty.coq_Ty * coq_Term **)

  let coq_Term_sig_pack _ x term_var =
    x,term_var

  (** val coq_Term_Signature :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Ty, coq_Term_sig) coq_Signature **)

  let coq_Term_Signature _ x term_var =
    x,term_var

  (** val term_enum :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.enumi -> Coq_ty.enumt -> coq_Term **)

  let term_enum _ e k =
    Coq_term_val ((Coq_ty.Coq_enum e), k)

  (** val term_list :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term list -> coq_Term **)

  let rec term_list _UU03a3_ _UU03c3_ = function
  | Datatypes.Coq_nil ->
    Coq_term_val ((Coq_ty.Coq_list _UU03c3_), (Obj.magic Datatypes.Coq_nil))
  | Datatypes.Coq_cons (t0, ts0) ->
    Coq_term_binop (_UU03c3_, (Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list
      _UU03c3_), (Coq_bop.Coq_cons _UU03c3_), t0,
      (term_list _UU03a3_ _UU03c3_ ts0))

  (** val term_bvec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term t -> coq_Term **)

  let rec term_bvec _UU03a3_ _ = function
  | Coq_nil -> Coq_term_val ((Coq_ty.Coq_bvec O), (Obj.magic Coq_bv.nil))
  | Coq_cons (t0, n0, ts0) ->
    Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec
      (S n0)), (Coq_bop.Coq_bvcons n0), t0, (term_bvec _UU03a3_ n0 ts0))

  (** val term_relop_neg :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> coq_Term **)

  let term_relop_neg _ _ = function
  | Coq_bop.Coq_eq _UU03c3_0 ->
    (fun x x0 -> Coq_term_binop (_UU03c3_0, _UU03c3_0, Coq_ty.Coq_bool,
      (Coq_bop.Coq_relop (_UU03c3_0, (Coq_bop.Coq_neq _UU03c3_0))), x, x0))
  | Coq_bop.Coq_neq _UU03c3_0 ->
    (fun x x0 -> Coq_term_binop (_UU03c3_0, _UU03c3_0, Coq_ty.Coq_bool,
      (Coq_bop.Coq_relop (_UU03c3_0, (Coq_bop.Coq_eq _UU03c3_0))), x, x0))
  | Coq_bop.Coq_le ->
    flip (fun x x0 -> Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
      Coq_ty.Coq_bool, (Coq_bop.Coq_relop (Coq_ty.Coq_int, Coq_bop.Coq_lt)),
      x, x0))
  | Coq_bop.Coq_lt ->
    flip (fun x x0 -> Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
      Coq_ty.Coq_bool, (Coq_bop.Coq_relop (Coq_ty.Coq_int, Coq_bop.Coq_le)),
      x, x0))
  | Coq_bop.Coq_bvsle n ->
    flip (fun x x0 -> Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec
      n), Coq_ty.Coq_bool, (Coq_bop.Coq_relop ((Coq_ty.Coq_bvec n),
      (Coq_bop.Coq_bvslt n))), x, x0))
  | Coq_bop.Coq_bvslt n ->
    flip (fun x x0 -> Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec
      n), Coq_ty.Coq_bool, (Coq_bop.Coq_relop ((Coq_ty.Coq_bvec n),
      (Coq_bop.Coq_bvsle n))), x, x0))
  | Coq_bop.Coq_bvule n ->
    flip (fun x x0 -> Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec
      n), Coq_ty.Coq_bool, (Coq_bop.Coq_relop ((Coq_ty.Coq_bvec n),
      (Coq_bop.Coq_bvult n))), x, x0))
  | Coq_bop.Coq_bvult n ->
    flip (fun x x0 -> Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec
      n), Coq_ty.Coq_bool, (Coq_bop.Coq_relop ((Coq_ty.Coq_bvec n),
      (Coq_bop.Coq_bvule n))), x, x0))

  (** val term_truncate :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> coq_Term -> coq_Term **)

  let term_truncate _ n m =
    let k = Coq_bv.leview m n in
    (fun x -> Coq_term_unop ((Coq_ty.Coq_bvec (add m k)), (Coq_ty.Coq_bvec
    m), (Coq_uop.Coq_bvtake (m, k)), x))

  (** val term_vector_subrange :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> coq_Term -> coq_Term **)

  let term_vector_subrange _ n s l =
    let k = Coq_bv.leview (add s l) n in
    (fun t0 -> Coq_term_unop ((Coq_ty.Coq_bvec (add s l)), (Coq_ty.Coq_bvec
    l), (Coq_uop.Coq_bvdrop (s, l)), (Coq_term_unop ((Coq_ty.Coq_bvec
    (add (add s l) k)), (Coq_ty.Coq_bvec (add s l)), (Coq_uop.Coq_bvtake
    ((add s l), k)), t0))))

  (** val term_update_vector_subrange :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> coq_Term -> coq_Term -> coq_Term **)

  let term_update_vector_subrange _ n s l =
    let k = Coq_bv.leview (add s l) n in
    (fun t0 u -> Coq_term_binop ((Coq_ty.Coq_bvec (add s l)),
    (Coq_ty.Coq_bvec k), (Coq_ty.Coq_bvec (add (add s l) k)),
    (Coq_bop.Coq_bvapp ((add s l), k)), (Coq_term_binop ((Coq_ty.Coq_bvec s),
    (Coq_ty.Coq_bvec l), (Coq_ty.Coq_bvec (add s l)), (Coq_bop.Coq_bvapp (s,
    l)), (Coq_term_unop ((Coq_ty.Coq_bvec (add s l)), (Coq_ty.Coq_bvec s),
    (Coq_uop.Coq_bvtake (s, l)), (Coq_term_unop ((Coq_ty.Coq_bvec
    (add (add s l) k)), (Coq_ty.Coq_bvec (add s l)), (Coq_uop.Coq_bvtake
    ((add s l), k)), t0)))), u)), (Coq_term_unop ((Coq_ty.Coq_bvec
    (add (add s l) k)), (Coq_ty.Coq_bvec k), (Coq_uop.Coq_bvdrop ((add s l),
    k)), t0))))

  (** val coq_Term_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
      Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1 ->
      'a1 -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
      coq_Term -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty, coq_Term,
      'a1) Coq_env.coq_All -> 'a1) -> (Coq_ty.unioni -> Coq_ty.unionk ->
      coq_Term -> 'a1 -> 'a1) -> (Coq_ty.recordi -> (Coq_ty.recordf,
      Coq_ty.coq_Ty, coq_Term) coq_NamedEnv -> ((Coq_ty.recordf,
      Coq_ty.coq_Ty) Binding.coq_Binding, coq_Term, 'a1) Coq_env.coq_All ->
      'a1) -> Coq_ty.coq_Ty -> coq_Term -> 'a1 **)

  let rec coq_Term_rect _UU03a3_ pvar pval pbinop punop ptuple punion precord _ = function
  | Coq_term_var (l, _UU03c3_0, lIn) -> pvar l _UU03c3_0 lIn
  | Coq_term_val (_UU03c3_, v) -> pval _UU03c3_ v
  | Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1, t2) ->
    pbinop _UU03c3_1 _UU03c3_2 _UU03c3_3 op t1 t2
      (coq_Term_rect _UU03a3_ pvar pval pbinop punop ptuple punion precord
        _UU03c3_1 t1)
      (coq_Term_rect _UU03a3_ pvar pval pbinop punop ptuple punion precord
        _UU03c3_2 t2)
  | Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t1) ->
    punop _UU03c3_1 _UU03c3_2 op t1
      (coq_Term_rect _UU03a3_ pvar pval pbinop punop ptuple punion precord
        _UU03c3_1 t1)
  | Coq_term_tuple (_UU03c3_s, ts) ->
    ptuple _UU03c3_s ts
      (Coq_env.all_intro
        (coq_Term_rect _UU03a3_ pvar pval pbinop punop ptuple punion precord)
        _UU03c3_s ts)
  | Coq_term_union (u, k, t1) ->
    punion u k t1
      (coq_Term_rect _UU03a3_ pvar pval pbinop punop ptuple punion precord
        (typedefkit.Coq_ty.unionk_ty u k) t1)
  | Coq_term_record (r, ts) ->
    precord r ts
      (Coq_env.all_intro (fun b ->
        coq_Term_rect _UU03a3_ pvar pval pbinop punop ptuple punion precord
          b.Binding.coq_type)
        (typedefkit.Coq_ty.recordf_ty r) ts)

  (** val coq_Term_rec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
      Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1 ->
      'a1 -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
      coq_Term -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty, coq_Term,
      'a1) Coq_env.coq_All -> 'a1) -> (Coq_ty.unioni -> Coq_ty.unionk ->
      coq_Term -> 'a1 -> 'a1) -> (Coq_ty.recordi -> (Coq_ty.recordf,
      Coq_ty.coq_Ty, coq_Term) coq_NamedEnv -> ((Coq_ty.recordf,
      Coq_ty.coq_Ty) Binding.coq_Binding, coq_Term, 'a1) Coq_env.coq_All ->
      'a1) -> Coq_ty.coq_Ty -> coq_Term -> 'a1 **)

  let rec coq_Term_rec _UU03a3_ pvar pval pbinop punop ptuple punion precord _ = function
  | Coq_term_var (l, _UU03c3_0, lIn) -> pvar l _UU03c3_0 lIn
  | Coq_term_val (_UU03c3_, v) -> pval _UU03c3_ v
  | Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1, t2) ->
    pbinop _UU03c3_1 _UU03c3_2 _UU03c3_3 op t1 t2
      (coq_Term_rec _UU03a3_ pvar pval pbinop punop ptuple punion precord
        _UU03c3_1 t1)
      (coq_Term_rec _UU03a3_ pvar pval pbinop punop ptuple punion precord
        _UU03c3_2 t2)
  | Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t1) ->
    punop _UU03c3_1 _UU03c3_2 op t1
      (coq_Term_rec _UU03a3_ pvar pval pbinop punop ptuple punion precord
        _UU03c3_1 t1)
  | Coq_term_tuple (_UU03c3_s, ts) ->
    ptuple _UU03c3_s ts
      (Coq_env.all_intro
        (coq_Term_rec _UU03a3_ pvar pval pbinop punop ptuple punion precord)
        _UU03c3_s ts)
  | Coq_term_union (u, k, t1) ->
    punion u k t1
      (coq_Term_rec _UU03a3_ pvar pval pbinop punop ptuple punion precord
        (typedefkit.Coq_ty.unionk_ty u k) t1)
  | Coq_term_record (r, ts) ->
    precord r ts
      (Coq_env.all_intro (fun b ->
        coq_Term_rec _UU03a3_ pvar pval pbinop punop ptuple punion precord
          b.Binding.coq_type)
        (typedefkit.Coq_ty.recordf_ty r) ts)

  (** val coq_Term_int_case :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
      coq_Term -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> (coq_Term ->
      coq_Term -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> (coq_Term -> 'a1)
      -> (nat -> coq_Term -> 'a1) -> (nat -> coq_Term -> 'a1) -> coq_Term ->
      'a1 **)

  let coq_Term_int_case _ pvar pval pplus pminus ptimes pland pneg psigned punsigned = function
  | Coq_term_var (l, _, lIn) -> pvar l lIn
  | Coq_term_val (_, v) -> pval v
  | Coq_term_binop (_, _, _, op, t1, t2) ->
    (match op with
     | Coq_bop.Coq_plus -> pplus t1 t2
     | Coq_bop.Coq_minus -> pminus t1 t2
     | Coq_bop.Coq_times -> ptimes t1 t2
     | Coq_bop.Coq_land -> pland t1 t2
     | _ -> assert false (* absurd case *))
  | Coq_term_unop (_, _, op, t1) ->
    (match op with
     | Coq_uop.Coq_neg -> pneg t1
     | Coq_uop.Coq_signed n -> psigned n t1
     | Coq_uop.Coq_unsigned n -> punsigned n t1
     | _ -> assert false (* absurd case *))
  | _ -> assert false (* absurd case *)

  (** val coq_Term_int_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
      coq_Term -> 'a1 -> 'a1 -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1
      -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (coq_Term ->
      coq_Term -> 'a1 -> 'a1 -> 'a1) -> (coq_Term -> 'a1 -> 'a1) -> (nat ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> 'a1) -> coq_Term -> 'a1 **)

  let rec coq_Term_int_rect _UU03a3_ pvar pval pplus pminus ptimes pland pneg psigned punsigned t0 =
    coq_Term_int_case _UU03a3_ pvar pval (fun t1 t2 ->
      pplus t1 t2
        (coq_Term_int_rect _UU03a3_ pvar pval pplus pminus ptimes pland pneg
          psigned punsigned t1)
        (coq_Term_int_rect _UU03a3_ pvar pval pplus pminus ptimes pland pneg
          psigned punsigned t2))
      (fun t1 t2 ->
      pminus t1 t2
        (coq_Term_int_rect _UU03a3_ pvar pval pplus pminus ptimes pland pneg
          psigned punsigned t1)
        (coq_Term_int_rect _UU03a3_ pvar pval pplus pminus ptimes pland pneg
          psigned punsigned t2))
      (fun t1 t2 ->
      ptimes t1 t2
        (coq_Term_int_rect _UU03a3_ pvar pval pplus pminus ptimes pland pneg
          psigned punsigned t1)
        (coq_Term_int_rect _UU03a3_ pvar pval pplus pminus ptimes pland pneg
          psigned punsigned t2))
      (fun t1 t2 ->
      pland t1 t2
        (coq_Term_int_rect _UU03a3_ pvar pval pplus pminus ptimes pland pneg
          psigned punsigned t1)
        (coq_Term_int_rect _UU03a3_ pvar pval pplus pminus ptimes pland pneg
          psigned punsigned t2))
      (fun t1 ->
      pneg t1
        (coq_Term_int_rect _UU03a3_ pvar pval pplus pminus ptimes pland pneg
          psigned punsigned t1))
      psigned punsigned t0

  (** val coq_Term_bool_case :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
      coq_Term -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
      Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> 'a1) -> (coq_Term -> 'a1)
      -> coq_Term -> 'a1 **)

  let coq_Term_bool_case _ pvar pval pand por prel pnot = function
  | Coq_term_var (l, _, lIn) -> pvar l lIn
  | Coq_term_val (_, v) -> pval v
  | Coq_term_binop (_, _, _, op, t1, t2) ->
    (match op with
     | Coq_bop.Coq_and -> pand t1 t2
     | Coq_bop.Coq_or -> por t1 t2
     | Coq_bop.Coq_relop (_UU03c3_, r) -> prel _UU03c3_ r t1 t2
     | _ -> assert false (* absurd case *))
  | Coq_term_unop (_, _, op, t1) ->
    (match op with
     | Coq_uop.Coq_not -> pnot t1
     | _ -> assert false (* absurd case *))
  | _ -> assert false (* absurd case *)

  (** val coq_Term_bool_ind :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
      coq_Term -> 'a1 -> 'a1 -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1
      -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term
      -> 'a1) -> (coq_Term -> 'a1 -> 'a1) -> coq_Term -> 'a1 **)

  let rec coq_Term_bool_ind _UU03a3_ pvar pval pand por prel pnot t0 =
    coq_Term_bool_case _UU03a3_ pvar pval (fun t1 t2 ->
      pand t1 t2 (coq_Term_bool_ind _UU03a3_ pvar pval pand por prel pnot t1)
        (coq_Term_bool_ind _UU03a3_ pvar pval pand por prel pnot t2))
      (fun t1 t2 ->
      por t1 t2 (coq_Term_bool_ind _UU03a3_ pvar pval pand por prel pnot t1)
        (coq_Term_bool_ind _UU03a3_ pvar pval pand por prel pnot t2))
      prel (fun t1 ->
      pnot t1 (coq_Term_bool_ind _UU03a3_ pvar pval pand por prel pnot t1)) t0

  (** val coq_Term_list_case :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1)
      -> (coq_Term -> coq_Term -> 'a1) -> (coq_Term -> coq_Term -> 'a1) ->
      (coq_Term -> 'a1) -> coq_Term -> 'a1 **)

  let coq_Term_list_case _ _ pvar pval pcons pappend prev = function
  | Coq_term_var (l, _, lIn) -> pvar l lIn
  | Coq_term_val (_, v) -> pval v
  | Coq_term_binop (_, _, _, op, t1, t2) ->
    (match op with
     | Coq_bop.Coq_cons _ -> pcons t1 t2
     | Coq_bop.Coq_append _ -> pappend t1 t2
     | _ -> assert false (* absurd case *))
  | Coq_term_unop (_, _, op, t1) ->
    (match op with
     | Coq_uop.Coq_rev _ -> prev t1
     | _ -> assert false (* absurd case *))
  | _ -> assert false (* absurd case *)

  (** val coq_Term_prod_case :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> (coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
      (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> coq_Term ->
      'a1 **)

  let coq_Term_prod_case _ _ _ pvar pval ppair = function
  | Coq_term_var (l, _, lIn) -> pvar l lIn
  | Coq_term_val (_, v) -> pval v
  | Coq_term_binop (_, _, _, op, t1, t2) ->
    (match op with
     | Coq_bop.Coq_pair (_, _) -> ppair t1 t2
     | _ -> assert false (* absurd case *))
  | _ -> assert false (* absurd case *)

  (** val coq_Term_sum_case :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> (coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
      (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> 'a1) -> (coq_Term -> 'a1) ->
      coq_Term -> 'a1 **)

  let coq_Term_sum_case _ _ _ pvar pval pinl pinr = function
  | Coq_term_var (l, _, lIn) -> pvar l lIn
  | Coq_term_val (_, v) -> pval v
  | Coq_term_unop (_, _, op, t1) ->
    (match op with
     | Coq_uop.Coq_inl (_, _) -> pinl t1
     | Coq_uop.Coq_inr (_, _) -> pinr t1
     | _ -> assert false (* absurd case *))
  | _ -> assert false (* absurd case *)

  (** val coq_Term_bvec_case :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat
      -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat
      -> nat -> __ -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      'a1) -> (nat -> coq_Term -> 'a1) -> (nat -> nat -> __ -> coq_Term ->
      'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1) -> (nat -> nat -> nat ->
      __ -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> 'a1) -> (nat ->
      nat -> coq_Term -> 'a1) -> nat -> coq_Term -> 'a1 **)

  let coq_Term_bvec_case _ pvar pval pbvadd pbvsub pbvmul pbvand pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake n = function
  | Coq_term_var (l, _, lIn) -> pvar n l lIn
  | Coq_term_val (_, v) -> pval n v
  | Coq_term_binop (_, _, _, op, t1, t2) ->
    (match op with
     | Coq_bop.Coq_shiftr (_, n0) -> pshiftr n n0 t1 t2
     | Coq_bop.Coq_shiftl (_, n0) -> pshiftl n n0 t1 t2
     | Coq_bop.Coq_bvadd _ -> pbvadd n t1 t2
     | Coq_bop.Coq_bvsub _ -> pbvsub n t1 t2
     | Coq_bop.Coq_bvmul _ -> pbvmul n t1 t2
     | Coq_bop.Coq_bvand _ -> pbvand n t1 t2
     | Coq_bop.Coq_bvor _ -> pbvor n t1 t2
     | Coq_bop.Coq_bvxor _ -> pbvxor n t1 t2
     | Coq_bop.Coq_bvapp (m, n0) -> pbvapp m n0 t1 t2
     | Coq_bop.Coq_bvcons m -> pbvcons m t1 t2
     | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
       pupdate_subrange n s l __ t1 t2
     | _ -> assert false (* absurd case *))
  | Coq_term_unop (_, _, op, t1) ->
    (match op with
     | Coq_uop.Coq_sext (m, _) -> psext n m __ t1
     | Coq_uop.Coq_zext (m, _) -> pzext n m __ t1
     | Coq_uop.Coq_get_slice_int _ -> pgetslice n t1
     | Coq_uop.Coq_truncate (n0, _) -> ptruncate n n0 __ t1
     | Coq_uop.Coq_vector_subrange (n0, s, _) -> psubrange s n n0 __ t1
     | Coq_uop.Coq_bvnot _ -> pbvnot n t1
     | Coq_uop.Coq_bvdrop (m, _) -> pbvdrop m n t1
     | Coq_uop.Coq_bvtake (_, n0) -> pbvtake n n0 t1
     | Coq_uop.Coq_negate _ -> pnegate n t1
     | _ -> assert false (* absurd case *))
  | _ -> assert false (* absurd case *)

  (** val coq_Term_bvec_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1
      -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) ->
      (nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term
      -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term
      -> 'a1 -> 'a1 -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1 ->
      'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 -> 'a1) -> (nat ->
      nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat
      -> coq_Term -> 'a1 -> 'a1) -> (nat -> coq_Term -> 'a1 -> 'a1) -> (nat
      -> nat -> __ -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat -> __ ->
      coq_Term -> 'a1 -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat -> nat ->
      __ -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term
      -> 'a1 -> 'a1) -> (nat -> nat -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat
      -> coq_Term -> 'a1 -> 'a1) -> nat -> coq_Term -> 'a1 **)

  let rec coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake n t0 =
    coq_Term_bvec_case _UU03a3_ pvar pval (fun n0 t1 t2 ->
      pbvadd n0 t1 t2
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t1)
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t2))
      (fun n0 t1 t2 ->
      pbvsub n0 t1 t2
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t1)
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t2))
      (fun n0 t1 t2 ->
      pbvmul n0 t1 t2
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t1)
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t2))
      (fun n0 t1 t2 ->
      pbvand n0 t1 t2
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t1)
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t2))
      (fun n0 t1 t2 ->
      pbvor n0 t1 t2
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t1)
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t2))
      (fun n0 t1 t2 ->
      pbvxor n0 t1 t2
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t1)
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t2))
      (fun n0 m t1 t2 ->
      pshiftr n0 m t1 t2
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t1)
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake m
          t2))
      (fun n0 m t1 t2 ->
      pshiftl n0 m t1 t2
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t1)
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake m
          t2))
      (fun n1 n2 t1 t2 ->
      pbvapp n1 n2 t1 t2
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n1 t1)
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n2 t2))
      (fun n0 t1 t2 ->
      pbvcons n0 t1 t2
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t2))
      (fun n0 s l _ t1 t2 ->
      pupdate_subrange s l n0 __ t1 t2
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t1)
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake l
          t2))
      (fun n0 t1 ->
      pbvnot n0 t1
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t1))
      (fun n0 t1 ->
      pnegate n0 t1
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          n0 t1))
      (fun n0 m _ t1 ->
      psext n0 m __ t1
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake m
          t1))
      (fun n0 m _ t1 ->
      pzext n0 m __ t1
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake m
          t1))
      pgetslice (fun n0 m _ t1 ->
      ptruncate n0 m __ t1
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake m
          t1))
      (fun s l m _ t1 ->
      psubrange s l m __ t1
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake m
          t1))
      (fun m n0 t1 ->
      pbvdrop m n0 t1
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          (add m n0) t1))
      (fun m n0 t1 ->
      pbvtake m n0 t1
        (coq_Term_bvec_rect _UU03a3_ pvar pval pbvadd pbvsub pbvmul pbvand
          pbvor pbvxor pshiftr pshiftl pbvapp pbvcons pupdate_subrange pbvnot
          pnegate psext pzext pgetslice ptruncate psubrange pbvdrop pbvtake
          (add m n0) t1))
      n t0

  (** val coq_Term_tuple_case :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1)
      -> ((Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env -> 'a1) -> coq_Term -> 'a1 **)

  let coq_Term_tuple_case _ _ pvar pval ptuple = function
  | Coq_term_var (l, _, lIn) -> pvar l lIn
  | Coq_term_val (_, v) -> pval v
  | Coq_term_tuple (_, ts) -> ptuple ts
  | _ -> assert false (* absurd case *)

  (** val coq_Term_union_case :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.unioni -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1)
      -> (Coq_ty.unionk -> coq_Term -> 'a1) -> coq_Term -> 'a1 **)

  let coq_Term_union_case _ _ pvar pval punion = function
  | Coq_term_var (l, _, lIn) -> pvar l lIn
  | Coq_term_val (_, v) -> pval v
  | Coq_term_union (_, k, t1) -> punion k t1
  | _ -> assert false (* absurd case *)

  (** val coq_Term_record_case :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.recordi -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1)
      -> ((Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) coq_NamedEnv -> 'a1) ->
      coq_Term -> 'a1 **)

  let coq_Term_record_case _ _ pvar pval precord = function
  | Coq_term_var (l, _, lIn) -> pvar l lIn
  | Coq_term_val (_, v) -> pval v
  | Coq_term_record (_, ts) -> precord ts
  | _ -> assert false (* absurd case *)

  type coq_ListView =
  | Coq_term_list_var of coq_LVar
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_term_list_val of Coq_ty.coq_Val
  | Coq_term_list_cons of coq_Term * coq_Term * coq_ListView
  | Coq_term_list_append of coq_Term * coq_Term * coq_ListView * coq_ListView
  | Coq_term_list_rev of coq_Term * coq_ListView

  (** val coq_ListView_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1)
      -> (coq_Term -> coq_Term -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term ->
      coq_Term -> coq_ListView -> 'a1 -> coq_ListView -> 'a1 -> 'a1) ->
      (coq_Term -> coq_ListView -> 'a1 -> 'a1) -> coq_Term -> coq_ListView ->
      'a1 **)

  let rec coq_ListView_rect _UU03a3_ _UU03c3_ f f0 f1 f2 f3 _ = function
  | Coq_term_list_var (_UU03c2_, _UU03c2_In_UU03a3_) ->
    f _UU03c2_ _UU03c2_In_UU03a3_
  | Coq_term_list_val v -> f0 v
  | Coq_term_list_cons (h, t0, lv) ->
    f1 h t0 lv (coq_ListView_rect _UU03a3_ _UU03c3_ f f0 f1 f2 f3 t0 lv)
  | Coq_term_list_append (t1, t2, lv1, lv2) ->
    f2 t1 t2 lv1 (coq_ListView_rect _UU03a3_ _UU03c3_ f f0 f1 f2 f3 t1 lv1)
      lv2 (coq_ListView_rect _UU03a3_ _UU03c3_ f f0 f1 f2 f3 t2 lv2)
  | Coq_term_list_rev (t0, lv) ->
    f3 t0 lv (coq_ListView_rect _UU03a3_ _UU03c3_ f f0 f1 f2 f3 t0 lv)

  (** val coq_ListView_rec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1)
      -> (coq_Term -> coq_Term -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term ->
      coq_Term -> coq_ListView -> 'a1 -> coq_ListView -> 'a1 -> 'a1) ->
      (coq_Term -> coq_ListView -> 'a1 -> 'a1) -> coq_Term -> coq_ListView ->
      'a1 **)

  let rec coq_ListView_rec _UU03a3_ _UU03c3_ f f0 f1 f2 f3 _ = function
  | Coq_term_list_var (_UU03c2_, _UU03c2_In_UU03a3_) ->
    f _UU03c2_ _UU03c2_In_UU03a3_
  | Coq_term_list_val v -> f0 v
  | Coq_term_list_cons (h, t0, lv) ->
    f1 h t0 lv (coq_ListView_rec _UU03a3_ _UU03c3_ f f0 f1 f2 f3 t0 lv)
  | Coq_term_list_append (t1, t2, lv1, lv2) ->
    f2 t1 t2 lv1 (coq_ListView_rec _UU03a3_ _UU03c3_ f f0 f1 f2 f3 t1 lv1)
      lv2 (coq_ListView_rec _UU03a3_ _UU03c3_ f f0 f1 f2 f3 t2 lv2)
  | Coq_term_list_rev (t0, lv) ->
    f3 t0 lv (coq_ListView_rec _UU03a3_ _UU03c3_ f f0 f1 f2 f3 t0 lv)

  type coq_View = __

  (** val view_var :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_LVar -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> coq_View **)

  let view_var _ l = function
  | Coq_ty.Coq_list _ -> Obj.magic (fun x -> Coq_term_list_var (l, x))
  | _ -> (fun _ -> Obj.magic Coq_tt)

  (** val view_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Val -> coq_View **)

  let view_val _ = function
  | Coq_ty.Coq_list _ -> Obj.magic (fun x -> Coq_term_list_val x)
  | _ -> (fun _ -> Obj.magic Coq_tt)

  (** val view_binop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> coq_View -> coq_View -> coq_View **)

  let view_binop _ _ _ _ = function
  | Coq_bop.Coq_cons _ ->
    (fun t1 t2 _ v2 ->
      Obj.magic (Coq_term_list_cons (t1, t2, (Obj.magic v2))))
  | Coq_bop.Coq_append _ ->
    Obj.magic (fun x x0 x1 x2 -> Coq_term_list_append (x, x0, x1, x2))
  | _ -> (fun _ _ _ _ -> Obj.magic Coq_tt)

  (** val view_unop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      coq_View -> coq_View **)

  let view_unop _ _ _ = function
  | Coq_uop.Coq_rev _ -> Obj.magic (fun x x0 -> Coq_term_list_rev (x, x0))
  | _ -> (fun _ _ -> Obj.magic Coq_tt)

  (** val view :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> coq_View **)

  let rec view _UU03a3_ _ = function
  | Coq_term_var (_UU03c2_, _UU03c3_0, lIn) ->
    view_var _UU03a3_ _UU03c2_ _UU03c3_0 lIn
  | Coq_term_val (_UU03c3_0, v) -> view_val _UU03a3_ _UU03c3_0 v
  | Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1, t2) ->
    view_binop _UU03a3_ _UU03c3_1 _UU03c3_2 _UU03c3_3 op t1 t2
      (view _UU03a3_ _UU03c3_1 t1) (view _UU03a3_ _UU03c3_2 t2)
  | Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t1) ->
    view_unop _UU03a3_ _UU03c3_1 _UU03c3_2 op t1 (view _UU03a3_ _UU03c3_1 t1)
  | _ -> Obj.magic Coq_tt

  (** val coq_Term_eqb_clause_3 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      sumbool -> coq_Term -> coq_Term -> bool **)

  let coq_Term_eqb_clause_3 _ term_eqb _ _UU03c3_2 _UU03c3_3 _ x1 y1 _ _ _ refine x2 y2 =
    match refine with
    | Coq_left ->
      (match term_eqb _UU03c3_2 x1 x2 with
       | Coq_true -> term_eqb _UU03c3_3 y1 y2
       | Coq_false -> Coq_false)
    | Coq_right -> Coq_false

  (** val coq_Term_eqb_clause_4 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> sumbool -> coq_Term -> bool **)

  let coq_Term_eqb_clause_4 _ term_eqb _ _UU03c3_5 _ t1 _ _ refine t2 =
    match refine with
    | Coq_left -> term_eqb _UU03c3_5 t1 t2
    | Coq_right -> Coq_false

  (** val coq_Term_eqb_clause_6 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.unioni ->
      Coq_ty.unionk -> coq_Term -> Coq_ty.unionk -> sumbool -> coq_Term ->
      bool **)

  let coq_Term_eqb_clause_6 _ term_eqb u0 k1 e1 _ refine e2 =
    match refine with
    | Coq_left -> term_eqb (typedefkit.Coq_ty.unionk_ty u0 k1) e1 e2
    | Coq_right -> Coq_false

  (** val coq_Term_eqb :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool **)

  let rec coq_Term_eqb _UU03a3_ _ t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      (match t2 with
       | Coq_term_var (l0, _UU03c3_, lIn0) ->
         Coq_ctx.coq_In_eqb _UU03a3_ { Binding.name = l; Binding.coq_type =
           _UU03c3_ } { Binding.name = l0; Binding.coq_type = _UU03c3_ } lIn
           lIn0
       | _ -> Coq_false)
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_val (_UU03c3_, v0) ->
         (match eq_dec
                  (Coq_ty.coq_Val_eq_dec typedeclkit typedenotekit typedefkit
                    _UU03c3_)
                  v v0 with
          | Coq_left -> Coq_true
          | Coq_right -> Coq_false)
       | _ -> Coq_false)
    | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
      (match t2 with
       | Coq_term_binop (_UU03c3_3, _UU03c3_4, _UU03c3_5, op0, t5, t6) ->
         (match Coq_bop.eqdep_dec typedeclkit typedenotekit typedefkit
                  _UU03c3_1 _UU03c3_2 _UU03c3_5 _UU03c3_3 _UU03c3_4 _UU03c3_5
                  op op0 with
          | Coq_left ->
            (match coq_Term_eqb _UU03a3_ _UU03c3_1 t3 t5 with
             | Coq_true -> coq_Term_eqb _UU03a3_ _UU03c3_2 t4 t6
             | Coq_false -> Coq_false)
          | Coq_right -> Coq_false)
       | _ -> Coq_false)
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      (match t2 with
       | Coq_term_unop (_UU03c3_2, _UU03c3_3, op0, t3) ->
         (match Coq_uop.tel_eq_dec typedeclkit _UU03c3_1 _UU03c3_2 _UU03c3_3
                  op op0 with
          | Coq_left -> coq_Term_eqb _UU03a3_ _UU03c3_1 t0 t3
          | Coq_right -> Coq_false)
       | _ -> Coq_false)
    | Coq_term_tuple (_UU03c3_s, ts) ->
      (match t2 with
       | Coq_term_tuple (_, ts0) ->
         Coq_env.eqb_hom (coq_Term_eqb _UU03a3_) _UU03c3_s ts ts0
       | Coq_term_union (_, _, _) -> assert false (* absurd case *)
       | Coq_term_record (_, _) -> assert false (* absurd case *)
       | _ -> Coq_false)
    | Coq_term_union (u, k, t0) ->
      (match t2 with
       | Coq_term_tuple (_, _) -> assert false (* absurd case *)
       | Coq_term_union (_, k0, t3) ->
         (match eq_dec (typedefkit.Coq_ty.unionk_eqdec u) k k0 with
          | Coq_left ->
            coq_Term_eqb _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k) t0 t3
          | Coq_right -> Coq_false)
       | Coq_term_record (_, _) -> assert false (* absurd case *)
       | _ -> Coq_false)
    | Coq_term_record (r, ts) ->
      (match t2 with
       | Coq_term_tuple (_, _) -> assert false (* absurd case *)
       | Coq_term_union (_, _, _) -> assert false (* absurd case *)
       | Coq_term_record (_, ts0) ->
         Coq_env.eqb_hom (fun b -> coq_Term_eqb _UU03a3_ b.Binding.coq_type)
           (typedefkit.Coq_ty.recordf_ty r) ts ts0
       | _ -> Coq_false)

  (** val coq_Term_eqb_spec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> coq_Term -> reflect **)

  let rec coq_Term_eqb_spec _UU03a3_ _ t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      (match t2 with
       | Coq_term_var (l0, _UU03c3_, lIn0) ->
         Coq_ctx.coq_In_eqb_spec _UU03a3_ { Binding.name = l;
           Binding.coq_type = _UU03c3_ } { Binding.name = l0;
           Binding.coq_type = _UU03c3_ } lIn lIn0
       | _ -> ReflectF)
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_val (_UU03c3_, v0) ->
         let s =
           eq_dec
             (Coq_ty.coq_Val_eq_dec typedeclkit typedenotekit typedefkit
               _UU03c3_)
             v v0
         in
         (match s with
          | Coq_left -> ReflectT
          | Coq_right -> ReflectF)
       | _ -> ReflectF)
    | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
      (match t2 with
       | Coq_term_binop (_UU03c3_3, _UU03c3_4, _UU03c3_5, op0, t5, t6) ->
         let s =
           Coq_bop.eqdep_dec typedeclkit typedenotekit typedefkit _UU03c3_1
             _UU03c3_2 _UU03c3_5 _UU03c3_3 _UU03c3_4 _UU03c3_5 op op0
         in
         (match s with
          | Coq_left ->
            coq_UIP_K _UU03c3_5 (fun _ ->
              let r = coq_Term_eqb_spec _UU03a3_ _UU03c3_1 t3 t5 in
              (match r with
               | ReflectT -> coq_Term_eqb_spec _UU03a3_ _UU03c3_2 t4 t6
               | ReflectF -> ReflectF))
              __
          | Coq_right -> ReflectF)
       | _ -> ReflectF)
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      (match t2 with
       | Coq_term_unop (_UU03c3_2, _UU03c3_3, op0, t3) ->
         let d =
           Coq_uop.tel_eq_dec typedeclkit _UU03c3_1 _UU03c3_2 _UU03c3_3 op op0
         in
         (match d with
          | Coq_left -> coq_Term_eqb_spec _UU03a3_ _UU03c3_1 t0 t3
          | Coq_right -> ReflectF)
       | _ -> ReflectF)
    | Coq_term_tuple (_UU03c3_s, ts) ->
      (match t2 with
       | Coq_term_tuple (_, ts0) ->
         iffP (Coq_env.eqb_hom (coq_Term_eqb _UU03a3_) _UU03c3_s ts ts0)
           (Coq_env.eqb_hom_spec_point (coq_Term_eqb _UU03a3_) _UU03c3_s ts
             (Coq_env.all_intro (fun x x0 x1 ->
               coq_Term_eqb_spec _UU03a3_ x x0 x1) _UU03c3_s ts)
             ts0)
       | Coq_term_union (_, _, _) -> assert false (* absurd case *)
       | Coq_term_record (_, _) -> assert false (* absurd case *)
       | _ -> ReflectF)
    | Coq_term_union (u, k, t0) ->
      (match t2 with
       | Coq_term_tuple (_, _) -> assert false (* absurd case *)
       | Coq_term_union (_, k0, t3) ->
         let s = eq_dec (typedefkit.Coq_ty.unionk_eqdec u) k k0 in
         (match s with
          | Coq_left ->
            internal_eq_rew_r_dep k k0 (fun _ iHt1 -> iHt1 t3) t0 (fun x ->
              coq_Term_eqb_spec _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k) t0
                x)
          | Coq_right -> ReflectF)
       | Coq_term_record (_, _) -> assert false (* absurd case *)
       | _ -> ReflectF)
    | Coq_term_record (r, ts) ->
      (match t2 with
       | Coq_term_tuple (_, _) -> assert false (* absurd case *)
       | Coq_term_union (_, _, _) -> assert false (* absurd case *)
       | Coq_term_record (_, ts0) ->
         iffP
           (Coq_env.eqb_hom (fun b ->
             coq_Term_eqb _UU03a3_ b.Binding.coq_type)
             (typedefkit.Coq_ty.recordf_ty r) ts ts0)
           (Coq_env.eqb_hom_spec_point (fun b ->
             coq_Term_eqb _UU03a3_ b.Binding.coq_type)
             (typedefkit.Coq_ty.recordf_ty r) ts
             (Coq_env.all_intro (fun b x x0 ->
               coq_Term_eqb_spec _UU03a3_ b.Binding.coq_type x x0)
               (typedefkit.Coq_ty.recordf_ty r) ts)
             ts0)
       | _ -> ReflectF)

  type 'a coq_List = 'a list

  type 'a coq_Const = 'a

  type coq_Sub =
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, coq_Term) Coq_env.coq_Env

  type 't coq_Subst =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub
    -> 't

  (** val subst :
      'a1 coq_Subst -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Sub -> 'a1 **)

  let subst subst0 =
    subst0

  (** val sub_term :
      Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Term -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub -> coq_Term **)

  let rec sub_term _ _UU03a3_1 t0 _UU03a3_2 _UU03b6_ =
    match t0 with
    | Coq_term_var (_UU03c2_, _UU03c3_0, lIn) ->
      Coq_env.lookup _UU03a3_1 _UU03b6_ { Binding.name = _UU03c2_;
        Binding.coq_type = _UU03c3_0 } lIn
    | Coq_term_val (_UU03c3_, v) -> Coq_term_val (_UU03c3_, v)
    | Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1, t2) ->
      Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op,
        (sub_term _UU03c3_1 _UU03a3_1 t1 _UU03a3_2 _UU03b6_),
        (sub_term _UU03c3_2 _UU03a3_1 t2 _UU03a3_2 _UU03b6_))
    | Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t1) ->
      Coq_term_unop (_UU03c3_1, _UU03c3_2, op,
        (sub_term _UU03c3_1 _UU03a3_1 t1 _UU03a3_2 _UU03b6_))
    | Coq_term_tuple (_UU03c3_s, ts) ->
      Coq_term_tuple (_UU03c3_s,
        (Coq_env.map (fun b t1 -> sub_term b _UU03a3_1 t1 _UU03a3_2 _UU03b6_)
          _UU03c3_s ts))
    | Coq_term_union (u, k, t1) ->
      Coq_term_union (u, k,
        (sub_term (typedefkit.Coq_ty.unionk_ty u k) _UU03a3_1 t1 _UU03a3_2
          _UU03b6_))
    | Coq_term_record (r, ts) ->
      Coq_term_record (r,
        (Coq_env.map (fun b t1 ->
          sub_term b.Binding.coq_type _UU03a3_1 t1 _UU03a3_2 _UU03b6_)
          (typedefkit.Coq_ty.recordf_ty r) ts))

  (** val coq_SubstTerm : Coq_ty.coq_Ty -> coq_Term coq_Subst **)

  let coq_SubstTerm =
    sub_term

  (** val coq_SubstList : 'a1 coq_Subst -> 'a1 coq_List coq_Subst **)

  let rec coq_SubstList h _UU03a3_1 xs _UU03a3_2 _UU03b6_ =
    match xs with
    | Datatypes.Coq_nil -> Datatypes.Coq_nil
    | Datatypes.Coq_cons (x, xs0) ->
      Datatypes.Coq_cons ((subst h _UU03a3_1 x _UU03a3_2 _UU03b6_),
        (coq_SubstList h _UU03a3_1 xs0 _UU03a3_2 _UU03b6_))

  (** val coq_SubstConst : 'a1 coq_Const coq_Subst **)

  let coq_SubstConst _ x _ _ =
    x

  (** val coq_SubstEnv :
      ('a1 -> 'a2 coq_Subst) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2)
      Coq_env.coq_Env coq_Subst **)

  let coq_SubstEnv h _UU0394_ _UU03a3_1 xs _UU03a3_2 _UU03b6_ =
    Coq_env.map (fun b a -> subst (h b) _UU03a3_1 a _UU03a3_2 _UU03b6_)
      _UU0394_ xs

  (** val sub_id :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub **)

  let sub_id _UU03a3_ =
    Coq_env.tabulate _UU03a3_ (fun pat ->
      let _UU03c2_ = pat.Binding.name in
      let _UU03c3_ = pat.Binding.coq_type in
      (fun _UU03c2_In -> Coq_term_var (_UU03c2_, _UU03c3_, _UU03c2_In)))

  (** val sub_snoc :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Sub -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Term ->
      coq_Sub **)

  let sub_snoc _UU03a3_1 _ _UU03b6_ b t0 =
    Coq_env.Coq_snoc (_UU03a3_1, _UU03b6_, b, t0)

  (** val sub_shift :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Sub **)

  let sub_shift _UU03a3_ b bIn =
    Coq_env.tabulate (Coq_ctx.remove _UU03a3_ b bIn) (fun pat ->
      let x = pat.Binding.name in
      let _UU03c4_ = pat.Binding.coq_type in
      (fun xIn -> Coq_term_var (x, _UU03c4_,
      (Coq_ctx.shift_var b { Binding.name = x; Binding.coq_type = _UU03c4_ }
        _UU03a3_ bIn xIn))))

  (** val sub_wk1 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Sub **)

  let sub_wk1 _UU03a3_ b =
    Coq_env.tabulate _UU03a3_ (fun pat ->
      let _UU03c2_ = pat.Binding.name in
      let _UU03c3_ = pat.Binding.coq_type in
      (fun _UU03c2_In -> Coq_term_var (_UU03c2_, _UU03c3_,
      (Coq_ctx.in_succ { Binding.name = _UU03c2_; Binding.coq_type =
        _UU03c3_ } _UU03a3_ b _UU03c2_In))))

  (** val sub_cat_left :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub **)

  let sub_cat_left _UU03a3_ _UU0394_ =
    Coq_env.tabulate _UU03a3_ (fun pat ->
      let _UU03c2_ = pat.Binding.name in
      let _UU03c3_ = pat.Binding.coq_type in
      (fun _UU03c2_In -> Coq_term_var (_UU03c2_, _UU03c3_,
      (Coq_ctx.in_cat_left { Binding.name = _UU03c2_; Binding.coq_type =
        _UU03c3_ } _UU03a3_ _UU0394_ _UU03c2_In))))

  (** val sub_cat_right :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub **)

  let sub_cat_right _UU03a3_ _UU0394_ =
    Coq_env.tabulate _UU0394_ (fun pat ->
      let _UU03c2_ = pat.Binding.name in
      let _UU03c3_ = pat.Binding.coq_type in
      (fun _UU03c2_In -> Coq_term_var (_UU03c2_, _UU03c3_,
      (Coq_ctx.in_cat_right { Binding.name = _UU03c2_; Binding.coq_type =
        _UU03c3_ } _UU03a3_ _UU0394_ _UU03c2_In))))

  (** val sub_up1 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Sub -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Sub **)

  let sub_up1 _UU03a3_1 _UU03a3_2 _UU03b6_ b =
    sub_snoc _UU03a3_1 (Coq_ctx.Coq_snoc (_UU03a3_2, b))
      (subst
        (coq_SubstEnv (fun b0 -> coq_SubstTerm b0.Binding.coq_type) _UU03a3_1)
        _UU03a3_2 _UU03b6_ (Coq_ctx.Coq_snoc (_UU03a3_2, b))
        (sub_wk1 _UU03a3_2 b))
      b
      (let _UU03c2_ = b.Binding.name in
       let _UU03c3_ = b.Binding.coq_type in
       Coq_term_var (_UU03c2_, _UU03c3_,
       (Coq_ctx.in_zero { Binding.name = _UU03c2_; Binding.coq_type =
         _UU03c3_ } _UU03a3_2)))

  (** val sub_up :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Sub -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Sub **)

  let sub_up _UU03a3_1 _UU03a3_2 _UU03b6_ _UU0394_ =
    Coq_env.cat _UU03a3_1 _UU0394_
      (subst
        (coq_SubstEnv (fun b -> coq_SubstTerm b.Binding.coq_type) _UU03a3_1)
        _UU03a3_2 _UU03b6_ (Coq_ctx.cat _UU03a3_2 _UU0394_)
        (sub_cat_left _UU03a3_2 _UU0394_))
      (sub_cat_right _UU03a3_2 _UU0394_)

  (** val sub_single :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term -> coq_Sub **)

  let sub_single _UU03a3_ x xIn t0 =
    Coq_env.tabulate _UU03a3_ (fun y yIn ->
      match Coq_ctx.occurs_check_view _UU03a3_ x xIn y yIn with
      | Coq_ctx.Same -> t0
      | Coq_ctx.Diff (y0, yIn0) ->
        Coq_term_var (y0.Binding.name, y0.Binding.coq_type, yIn0))

  type 't coq_SubstLaws =
  | Build_SubstLaws

  (** val coq_SubstLawsTerm : Coq_ty.coq_Ty -> coq_Term coq_SubstLaws **)

  let coq_SubstLawsTerm _ =
    Build_SubstLaws

  (** val coq_SubstLawsList :
      'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_List coq_SubstLaws **)

  let coq_SubstLawsList _ _ =
    Build_SubstLaws

  (** val coq_SubstLawsConst : 'a1 coq_Const coq_SubstLaws **)

  let coq_SubstLawsConst =
    Build_SubstLaws

  (** val coq_SubstLawsEnv :
      ('a1 -> 'a2 coq_Subst) -> ('a1 -> 'a2 coq_SubstLaws) -> 'a1
      Coq_ctx.coq_Ctx -> ('a1, 'a2) Coq_env.coq_Env coq_SubstLaws **)

  let coq_SubstLawsEnv _ _ _ =
    Build_SubstLaws

  (** val subst_ctx : 'a1 coq_Subst -> 'a1 Coq_ctx.coq_Ctx coq_Subst **)

  let rec subst_ctx h _UU03a3_ xs _UU03a3_' _UU03b6_ =
    match xs with
    | Coq_ctx.Coq_nil -> Coq_ctx.Coq_nil
    | Coq_ctx.Coq_snoc (xs0, x) ->
      Coq_ctx.Coq_snoc ((subst_ctx h _UU03a3_ xs0 _UU03a3_' _UU03b6_),
        (subst h _UU03a3_ x _UU03a3_' _UU03b6_))

  (** val substlaws_ctx :
      'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 Coq_ctx.coq_Ctx coq_SubstLaws **)

  let substlaws_ctx _ _ =
    Build_SubstLaws

  module SubNotations =
   struct
   end

  type ('a, 'b) coq_Pair = ('a, 'b) prod

  (** val coq_SubstPair :
      'a1 coq_Subst -> 'a2 coq_Subst -> ('a1, 'a2) coq_Pair coq_Subst **)

  let coq_SubstPair h h0 _UU03a3_1 pat _UU03a3_2 _UU03b6_ =
    let Coq_pair (a, b) = pat in
    Coq_pair ((subst h _UU03a3_1 a _UU03a3_2 _UU03b6_),
    (subst h0 _UU03a3_1 b _UU03a3_2 _UU03b6_))

  (** val coq_SubstLawsPair :
      'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a2 coq_Subst -> 'a2
      coq_SubstLaws -> ('a1, 'a2) coq_Pair coq_SubstLaws **)

  let coq_SubstLawsPair _ _ _ _ =
    Build_SubstLaws

  type 'a coq_Option = 'a option

  (** val coq_SubstOption : 'a1 coq_Subst -> 'a1 coq_Option coq_Subst **)

  let coq_SubstOption h _UU03a3_1 ma _UU03a3_2 _UU03b6_ =
    option_map (fun a -> subst h _UU03a3_1 a _UU03a3_2 _UU03b6_) ma

  (** val coq_SubstLawsOption :
      'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_Option coq_SubstLaws **)

  let coq_SubstLawsOption _ _ =
    Build_SubstLaws

  type coq_Unit = coq_unit

  (** val coq_SubstUnit : coq_Unit coq_Subst **)

  let coq_SubstUnit _ t0 _ _ =
    t0

  (** val coq_SubstLawsUnit : coq_Unit coq_SubstLaws **)

  let coq_SubstLawsUnit =
    Build_SubstLaws

  type coq_SStore = (coq_PVar, Coq_ty.coq_Ty, coq_Term) coq_NamedEnv

  (** val subst_localstore :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SStore coq_Subst **)

  let subst_localstore _UU0393_ =
    coq_SubstEnv (fun b -> coq_SubstTerm b.Binding.coq_type) _UU0393_

  (** val substlaws_localstore :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SStore coq_SubstLaws **)

  let substlaws_localstore _UU0393_ =
    coq_SubstLawsEnv (fun b -> coq_SubstTerm b.Binding.coq_type) (fun b ->
      coq_SubstLawsTerm b.Binding.coq_type) _UU0393_

  module TermNotations =
   struct
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

  (** val erase_term :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> coq_ETerm **)

  let rec erase_term _UU03a3_ _ = function
  | Coq_term_var (_UU2113_, _UU03c3_, _UU2113_In) ->
    Coq_eterm_var (_UU2113_, _UU03c3_, _UU2113_In)
  | Coq_term_val (_UU03c3_, v) -> Coq_eterm_val (_UU03c3_, v)
  | Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1, t2) ->
    Coq_eterm_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op,
      (erase_term _UU03a3_ _UU03c3_1 t1), (erase_term _UU03a3_ _UU03c3_2 t2))
  | Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t1) ->
    Coq_eterm_unop (_UU03c3_1, _UU03c3_2, op,
      (erase_term _UU03a3_ _UU03c3_1 t1))
  | Coq_term_tuple (_UU03c3_s, ts) ->
    Coq_eterm_tuple (_UU03c3_s,
      (Coq_env.map (erase_term _UU03a3_) _UU03c3_s ts))
  | Coq_term_union (u, k, t1) ->
    Coq_eterm_union (u, k,
      (erase_term _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k) t1))
  | Coq_term_record (r, ts) ->
    Coq_eterm_record (r,
      (Coq_env.map (fun b -> erase_term _UU03a3_ b.Binding.coq_type)
        (typedefkit.Coq_ty.recordf_ty r) ts))

  (** val erase_SStore :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SStore -> (coq_PVar, Coq_ty.coq_Ty, coq_ETerm) coq_NamedEnv **)

  let rec erase_SStore _ _UU03a3_ = function
  | Coq_env.Coq_nil -> Coq_env.Coq_nil
  | Coq_env.Coq_snoc (_UU0393_0, ts0, b, t0) ->
    Coq_env.Coq_snoc (_UU0393_0, (erase_SStore _UU0393_0 _UU03a3_ ts0), b,
      (erase_term _UU03a3_ b.Binding.coq_type t0))

  type 'n coq_TuplePat =
  | Coq_tuplepat_nil
  | Coq_tuplepat_snoc of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_TuplePat * Coq_ty.coq_Ty * 'n

  (** val coq_TuplePat_rect :
      'a2 -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2 ->
      Coq_ty.coq_Ty -> 'a1 -> 'a2) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat
      -> 'a2 **)

  let rec coq_TuplePat_rect f f0 _ _ = function
  | Coq_tuplepat_nil -> f
  | Coq_tuplepat_snoc (_UU03c3_s, _UU0394_, pat, _UU03c3_, x) ->
    f0 _UU03c3_s _UU0394_ pat (coq_TuplePat_rect f f0 _UU03c3_s _UU0394_ pat)
      _UU03c3_ x

  (** val coq_TuplePat_rec :
      'a2 -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2 ->
      Coq_ty.coq_Ty -> 'a1 -> 'a2) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat
      -> 'a2 **)

  let rec coq_TuplePat_rec f f0 _ _ = function
  | Coq_tuplepat_nil -> f
  | Coq_tuplepat_snoc (_UU03c3_s, _UU0394_, pat, _UU03c3_, x) ->
    f0 _UU03c3_s _UU0394_ pat (coq_TuplePat_rec f f0 _UU03c3_s _UU0394_ pat)
      _UU03c3_ x

  type 'n coq_RecordPat =
  | Coq_recordpat_nil
  | Coq_recordpat_snoc of (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_RecordPat * Coq_ty.recordf * Coq_ty.coq_Ty * 'n

  (** val coq_RecordPat_rect :
      'a2 -> ((Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2 -> Coq_ty.recordf ->
      Coq_ty.coq_Ty -> 'a1 -> 'a2) -> (Coq_ty.recordf, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2 **)

  let rec coq_RecordPat_rect f f0 _ _ = function
  | Coq_recordpat_nil -> f
  | Coq_recordpat_snoc (rfs, _UU0394_, pat, rf, _UU03c4_, x) ->
    f0 rfs _UU0394_ pat (coq_RecordPat_rect f f0 rfs _UU0394_ pat) rf
      _UU03c4_ x

  (** val coq_RecordPat_rec :
      'a2 -> ((Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2 -> Coq_ty.recordf ->
      Coq_ty.coq_Ty -> 'a1 -> 'a2) -> (Coq_ty.recordf, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2 **)

  let rec coq_RecordPat_rec f f0 _ _ = function
  | Coq_recordpat_nil -> f
  | Coq_recordpat_snoc (rfs, _UU0394_, pat, rf, _UU03c4_, x) ->
    f0 rfs _UU0394_ pat (coq_RecordPat_rec f f0 rfs _UU0394_ pat) rf _UU03c4_
      x

  (** val tuple_pattern_match_env :
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat ->
      (Coq_ty.coq_Ty, 'a2) Coq_env.coq_Env -> ('a1, Coq_ty.coq_Ty, 'a2)
      coq_NamedEnv **)

  let rec tuple_pattern_match_env _ _ p x =
    match p with
    | Coq_tuplepat_nil -> Coq_env.Coq_nil
    | Coq_tuplepat_snoc (_UU03c3_s0, _UU0394_0, p0, _UU03c3_, x0) ->
      let Coq_env.Coq_isSnoc (e, v) =
        Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (_UU03c3_s0, _UU03c3_)) x
      in
      Coq_env.Coq_snoc (_UU0394_0,
      (tuple_pattern_match_env _UU03c3_s0 _UU0394_0 p0 e), { Binding.name =
      x0; Binding.coq_type = _UU03c3_ }, v)

  (** val tuple_pattern_match_env_reverse :
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> ('a1,
      Coq_ty.coq_Ty, 'a2) coq_NamedEnv -> (Coq_ty.coq_Ty, 'a2) Coq_env.coq_Env **)

  let rec tuple_pattern_match_env_reverse _ _ p x =
    match p with
    | Coq_tuplepat_nil -> Coq_env.Coq_nil
    | Coq_tuplepat_snoc (_UU03c3_s0, _UU0394_0, p0, _UU03c3_, x0) ->
      let Coq_env.Coq_isSnoc (e, v) =
        Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (_UU0394_0, { Binding.name =
          x0; Binding.coq_type = _UU03c3_ })) x
      in
      Coq_env.Coq_snoc (_UU03c3_s0,
      (tuple_pattern_match_env_reverse _UU03c3_s0 _UU0394_0 p0 e), _UU03c3_,
      v)

  (** val tuple_pattern_match_val :
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat ->
      Coq_ty.coq_Val -> ('a1, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv **)

  let tuple_pattern_match_val _UU03c3_s _UU0394_ p lit =
    tuple_pattern_match_env _UU03c3_s _UU0394_ p
      (Coq_envrec.to_env _UU03c3_s lit)

  (** val record_pattern_match_env :
      (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
      coq_RecordPat -> (Coq_ty.recordf, Coq_ty.coq_Ty, 'a2) coq_NamedEnv ->
      ('a1, Coq_ty.coq_Ty, 'a2) coq_NamedEnv **)

  let rec record_pattern_match_env _ _ p x =
    match p with
    | Coq_recordpat_nil -> Coq_env.Coq_nil
    | Coq_recordpat_snoc (rfs0, _UU0394_0, p0, rf, _UU03c4_, x0) ->
      Coq_env.Coq_snoc (_UU0394_0,
        (record_pattern_match_env rfs0 _UU0394_0 p0
          (Coq_env.tail rfs0 { Binding.name = rf; Binding.coq_type =
            _UU03c4_ } x)),
        { Binding.name = x0; Binding.coq_type = _UU03c4_ },
        (Coq_env.lookup (Coq_ctx.Coq_snoc (rfs0, { Binding.name = rf;
          Binding.coq_type = _UU03c4_ })) x { Binding.name = rf;
          Binding.coq_type = _UU03c4_ }
          (Coq_ctx.in_zero { Binding.name = rf; Binding.coq_type = _UU03c4_ }
            rfs0)))

  (** val record_pattern_match_env_reverse :
      (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
      coq_RecordPat -> ('a1, Coq_ty.coq_Ty, 'a2) coq_NamedEnv ->
      (Coq_ty.recordf, Coq_ty.coq_Ty, 'a2) coq_NamedEnv **)

  let rec record_pattern_match_env_reverse _ _ p x =
    match p with
    | Coq_recordpat_nil -> Coq_env.Coq_nil
    | Coq_recordpat_snoc (rfs0, _UU0394_0, p0, rf, _UU03c4_, x0) ->
      Coq_env.Coq_snoc (rfs0,
        (record_pattern_match_env_reverse rfs0 _UU0394_0 p0
          (Coq_env.tail _UU0394_0 { Binding.name = x0; Binding.coq_type =
            _UU03c4_ } x)),
        { Binding.name = rf; Binding.coq_type = _UU03c4_ },
        (Coq_env.lookup (Coq_ctx.Coq_snoc (_UU0394_0, { Binding.name = x0;
          Binding.coq_type = _UU03c4_ })) x { Binding.name = x0;
          Binding.coq_type = _UU03c4_ }
          (Coq_ctx.in_zero { Binding.name = x0; Binding.coq_type = _UU03c4_ }
            _UU0394_0)))

  (** val record_pattern_match_val :
      Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> Coq_ty.coq_Val -> ('a1,
      Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv **)

  let record_pattern_match_val r _UU0394_ p v =
    record_pattern_match_env (typedefkit.Coq_ty.recordf_ty r) _UU0394_ p
      (typedefkit.Coq_ty.recordv_unfold r v)

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

  (** val coq_Pattern_rect :
      ('a1 -> Coq_ty.coq_Ty -> 'a2) -> 'a2 -> (Coq_ty.coq_Ty -> 'a1 -> 'a1 ->
      'a2) -> ('a1 -> 'a1 -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a2) ->
      (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a1 -> 'a1 -> 'a2) -> 'a2 ->
      (Coq_ty.enumi -> 'a2) -> (nat -> nat -> 'a1 -> 'a1 -> 'a2) -> (nat ->
      'a2) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2) ->
      (Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2) -> (Coq_ty.unioni ->
      (Coq_ty.unionk -> 'a1 coq_Pattern) -> (Coq_ty.unionk -> 'a2) -> 'a2) ->
      Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a2 **)

  let rec coq_Pattern_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 _ = function
  | Coq_pat_var (x, _UU03c3_) -> f x _UU03c3_
  | Coq_pat_bool -> f0
  | Coq_pat_list (_UU03c3_, x, y) -> f1 _UU03c3_ x y
  | Coq_pat_pair (x, y, _UU03c3_, _UU03c4_) -> f2 x y _UU03c3_ _UU03c4_
  | Coq_pat_sum (_UU03c3_, _UU03c4_, x, y) -> f3 _UU03c3_ _UU03c4_ x y
  | Coq_pat_unit -> f4
  | Coq_pat_enum e -> f5 e
  | Coq_pat_bvec_split (m, n, x, y) -> f6 m n x y
  | Coq_pat_bvec_exhaustive m -> f7 m
  | Coq_pat_tuple (_UU03c3_s, _UU0394_, p0) -> f8 _UU03c3_s _UU0394_ p0
  | Coq_pat_record (r, _UU0394_, p0) -> f9 r _UU0394_ p0
  | Coq_pat_union (u, p0) ->
    f10 u p0 (fun k ->
      coq_Pattern_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
        (typedefkit.Coq_ty.unionk_ty u k) (p0 k))

  (** val coq_Pattern_rec :
      ('a1 -> Coq_ty.coq_Ty -> 'a2) -> 'a2 -> (Coq_ty.coq_Ty -> 'a1 -> 'a1 ->
      'a2) -> ('a1 -> 'a1 -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a2) ->
      (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a1 -> 'a1 -> 'a2) -> 'a2 ->
      (Coq_ty.enumi -> 'a2) -> (nat -> nat -> 'a1 -> 'a1 -> 'a2) -> (nat ->
      'a2) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2) ->
      (Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2) -> (Coq_ty.unioni ->
      (Coq_ty.unionk -> 'a1 coq_Pattern) -> (Coq_ty.unionk -> 'a2) -> 'a2) ->
      Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a2 **)

  let rec coq_Pattern_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 _ = function
  | Coq_pat_var (x, _UU03c3_) -> f x _UU03c3_
  | Coq_pat_bool -> f0
  | Coq_pat_list (_UU03c3_, x, y) -> f1 _UU03c3_ x y
  | Coq_pat_pair (x, y, _UU03c3_, _UU03c4_) -> f2 x y _UU03c3_ _UU03c4_
  | Coq_pat_sum (_UU03c3_, _UU03c4_, x, y) -> f3 _UU03c3_ _UU03c4_ x y
  | Coq_pat_unit -> f4
  | Coq_pat_enum e -> f5 e
  | Coq_pat_bvec_split (m, n, x, y) -> f6 m n x y
  | Coq_pat_bvec_exhaustive m -> f7 m
  | Coq_pat_tuple (_UU03c3_s, _UU0394_, p0) -> f8 _UU03c3_s _UU0394_ p0
  | Coq_pat_record (r, _UU0394_, p0) -> f9 r _UU0394_ p0
  | Coq_pat_union (u, p0) ->
    f10 u p0 (fun k ->
      coq_Pattern_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
        (typedefkit.Coq_ty.unionk_ty u k) (p0 k))

  type 'n coq_PatternCase = __

  (** val coq_EqDec_PatternCase :
      Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase coq_EqDec **)

  let rec coq_EqDec_PatternCase _ = function
  | Coq_pat_bool -> Obj.magic bool_EqDec
  | Coq_pat_list (_, _, _) -> Obj.magic bool_EqDec
  | Coq_pat_sum (_, _, _, _) -> Obj.magic bool_EqDec
  | Coq_pat_enum e -> typedefkit.Coq_ty.enumt_eqdec e
  | Coq_pat_bvec_exhaustive m -> Obj.magic Coq_bv.eqdec_bv m
  | Coq_pat_union (u, p) ->
    Obj.magic sigma_eqdec (typedefkit.Coq_ty.unionk_eqdec u) (fun k ->
      coq_EqDec_PatternCase (typedefkit.Coq_ty.unionk_ty u k) (p k))
  | _ -> Obj.magic unit_EqDec

  (** val coq_Finite_PatternCase :
      Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase coq_Finite **)

  let rec coq_Finite_PatternCase _ = function
  | Coq_pat_bool -> Obj.magic coq_Finite_bool
  | Coq_pat_list (_, _, _) -> Obj.magic coq_Finite_bool
  | Coq_pat_sum (_, _, _, _) -> Obj.magic coq_Finite_bool
  | Coq_pat_enum e -> typedefkit.Coq_ty.enumt_finite e
  | Coq_pat_bvec_exhaustive m -> Obj.magic Coq_bv.Coq_finite.finite_bv m
  | Coq_pat_union (u, p) ->
    Obj.magic coq_Finite_sigT (typedefkit.Coq_ty.unionk_eqdec u)
      (typedefkit.Coq_ty.unionk_finite u) (fun k ->
      coq_EqDec_PatternCase (typedefkit.Coq_ty.unionk_ty u k) (p k))
      (fun k ->
      coq_Finite_PatternCase (typedefkit.Coq_ty.unionk_ty u k) (p k))
  | _ -> Obj.magic unit_finite

  (** val coq_PatternCaseCtx :
      Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx **)

  let rec coq_PatternCaseCtx _ p x =
    match p with
    | Coq_pat_var (x0, _UU03c3_) ->
      Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name = x0;
        Binding.coq_type = _UU03c3_ })
    | Coq_pat_list (_UU03c3_, x0, y) ->
      (match Obj.magic x with
       | Coq_true -> Coq_ctx.Coq_nil
       | Coq_false ->
         Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
           { Binding.name = x0; Binding.coq_type = _UU03c3_ })),
           { Binding.name = y; Binding.coq_type = (Coq_ty.Coq_list
           _UU03c3_) }))
    | Coq_pat_pair (x0, y, _UU03c3_, _UU03c4_) ->
      Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
        x0; Binding.coq_type = _UU03c3_ })), { Binding.name = y;
        Binding.coq_type = _UU03c4_ })
    | Coq_pat_sum (_UU03c3_, _UU03c4_, x0, y) ->
      (match Obj.magic x with
       | Coq_true ->
         Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name = x0;
           Binding.coq_type = _UU03c3_ })
       | Coq_false ->
         Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name = y;
           Binding.coq_type = _UU03c4_ }))
    | Coq_pat_bvec_split (m, n, x0, y) ->
      Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
        x0; Binding.coq_type = (Coq_ty.Coq_bvec m) })), { Binding.name = y;
        Binding.coq_type = (Coq_ty.Coq_bvec n) })
    | Coq_pat_tuple (_, _UU0394_, _) -> _UU0394_
    | Coq_pat_record (_, _UU0394_, _) -> _UU0394_
    | Coq_pat_union (u, p0) ->
      let Coq_existT (k, pc) = Obj.magic x in
      coq_PatternCaseCtx (typedefkit.Coq_ty.unionk_ty u k) (p0 k) pc
    | _ -> Coq_ctx.Coq_nil

  type 'n coq_MatchResult =
    ('n coq_PatternCase, ('n, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv)
    sigT

  (** val pattern_match_val :
      Coq_ty.coq_Ty -> 'a1 coq_Pattern -> Coq_ty.coq_Val -> 'a1
      coq_MatchResult **)

  let rec pattern_match_val _ p v =
    match p with
    | Coq_pat_var (x, _UU03c3_0) ->
      Coq_existT ((Obj.magic Coq_tt), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
        Coq_env.Coq_nil, { Binding.name = x; Binding.coq_type = _UU03c3_0 },
        v)))
    | Coq_pat_list (_UU03c3_, x, y) ->
      (match Obj.magic v with
       | Datatypes.Coq_nil ->
         Coq_existT ((Obj.magic Coq_true), Coq_env.Coq_nil)
       | Datatypes.Coq_cons (v0, vs) ->
         Coq_existT ((Obj.magic Coq_false), (Coq_env.Coq_snoc
           ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name = x;
           Binding.coq_type = _UU03c3_ })), (Coq_env.Coq_snoc
           (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x;
           Binding.coq_type = _UU03c3_ }, v0)), { Binding.name = y;
           Binding.coq_type = (Coq_ty.Coq_list _UU03c3_) }, (Obj.magic vs)))))
    | Coq_pat_pair (x, y, _UU03c3_0, _UU03c4_) ->
      let Coq_pair (a, b) = Obj.magic v in
      Coq_existT ((Obj.magic Coq_tt), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name = x; Binding.coq_type = _UU03c3_0 })),
      (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      x; Binding.coq_type = _UU03c3_0 }, a)), { Binding.name = y;
      Binding.coq_type = _UU03c4_ }, b)))
    | Coq_pat_sum (_UU03c3_, _UU03c4_, x, y) ->
      (match Obj.magic v with
       | Coq_inl a ->
         Coq_existT ((Obj.magic Coq_true), (Coq_env.Coq_snoc
           (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x;
           Binding.coq_type = _UU03c3_ }, a)))
       | Coq_inr b ->
         Coq_existT ((Obj.magic Coq_false), (Coq_env.Coq_snoc
           (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = y;
           Binding.coq_type = _UU03c4_ }, b))))
    | Coq_pat_unit -> Coq_existT ((Obj.magic Coq_tt), Coq_env.Coq_nil)
    | Coq_pat_bvec_split (m, n, x, y) ->
      let Coq_bv.Coq_isapp (xs, ys) = Coq_bv.appView m n (Obj.magic v) in
      Coq_existT ((Obj.magic Coq_tt), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name = x; Binding.coq_type =
      (Coq_ty.Coq_bvec m) })), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
      Coq_env.Coq_nil, { Binding.name = x; Binding.coq_type =
      (Coq_ty.Coq_bvec m) }, (Obj.magic xs))), { Binding.name = y;
      Binding.coq_type = (Coq_ty.Coq_bvec n) }, (Obj.magic ys))))
    | Coq_pat_tuple (_UU03c3_s, _UU0394_, p0) ->
      Coq_existT ((Obj.magic Coq_tt),
        (tuple_pattern_match_val _UU03c3_s _UU0394_ p0 v))
    | Coq_pat_record (r, _UU0394_, p0) ->
      Coq_existT ((Obj.magic Coq_tt),
        (record_pattern_match_val r _UU0394_ p0 v))
    | Coq_pat_union (u, p0) ->
      let Coq_existT (k, u0) = typedefkit.Coq_ty.unionv_unfold u v in
      let Coq_existT (pc, _UU03b4_pc) =
        pattern_match_val (typedefkit.Coq_ty.unionk_ty u k) (p0 k) u0
      in
      Coq_existT ((Obj.magic (Coq_existT (k, pc))), _UU03b4_pc)
    | _ -> Coq_existT (v, Coq_env.Coq_nil)

  (** val pattern_match_val_reverse :
      Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
      Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv -> Coq_ty.coq_Val **)

  let rec pattern_match_val_reverse _ p c vs =
    match p with
    | Coq_pat_var (x, _UU03c3_0) ->
      Coq_env.head Coq_ctx.Coq_nil { Binding.name = x; Binding.coq_type =
        _UU03c3_0 } vs
    | Coq_pat_list (_UU03c3_, x, y) ->
      (match Obj.magic c with
       | Coq_true -> Obj.magic Datatypes.Coq_nil
       | Coq_false ->
         let Coq_env.Coq_isSnoc (eh, t0) =
           Obj.magic Coq_env.view
             (coq_PatternCaseCtx (Coq_ty.Coq_list _UU03c3_) (Coq_pat_list
               (_UU03c3_, x, y)) (Obj.magic Coq_false))
             vs
         in
         let Coq_env.Coq_isSnoc (_, h) =
           Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             { Binding.name = x; Binding.coq_type = _UU03c3_ })) eh
         in
         Obj.magic (Datatypes.Coq_cons (h, t0)))
    | Coq_pat_pair (x, y, _UU03c3_0, _UU03c4_) ->
      let Coq_env.Coq_isSnoc (ex, vy) =
        Obj.magic Coq_env.view
          (coq_PatternCaseCtx (Coq_ty.Coq_prod (_UU03c3_0, _UU03c4_))
            (Coq_pat_pair (x, y, _UU03c3_0, _UU03c4_)) c)
          vs
      in
      let Coq_env.Coq_isSnoc (_, vx) =
        Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          { Binding.name = x; Binding.coq_type = _UU03c3_0 })) ex
      in
      Obj.magic (Coq_pair (vx, vy))
    | Coq_pat_sum (_UU03c3_, _UU03c4_, x, y) ->
      (match Obj.magic c with
       | Coq_true ->
         Obj.magic (Coq_inl
           (Coq_env.head Coq_ctx.Coq_nil { Binding.name = x;
             Binding.coq_type = _UU03c3_ } vs))
       | Coq_false ->
         Obj.magic (Coq_inr
           (Coq_env.head Coq_ctx.Coq_nil { Binding.name = y;
             Binding.coq_type = _UU03c4_ } vs)))
    | Coq_pat_unit -> Obj.magic Coq_tt
    | Coq_pat_bvec_split (m, n, x, y) ->
      let Coq_env.Coq_isSnoc (ex, vy) =
        Obj.magic Coq_env.view
          (coq_PatternCaseCtx (Coq_ty.Coq_bvec (add m n)) (Coq_pat_bvec_split
            (m, n, x, y)) c)
          vs
      in
      let Coq_env.Coq_isSnoc (_, vx) =
        Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          { Binding.name = x; Binding.coq_type = (Coq_ty.Coq_bvec m) })) ex
      in
      Obj.magic Coq_bv.app m n vx vy
    | Coq_pat_tuple (_UU03c3_s, _UU0394_, p0) ->
      Coq_envrec.of_env _UU03c3_s
        (tuple_pattern_match_env_reverse _UU03c3_s _UU0394_ p0 vs)
    | Coq_pat_record (r, _UU0394_, p0) ->
      typedefkit.Coq_ty.recordv_fold r
        (record_pattern_match_env_reverse (typedefkit.Coq_ty.recordf_ty r)
          _UU0394_ p0 vs)
    | Coq_pat_union (u, p0) ->
      let Coq_existT (k, pc) = Obj.magic c in
      typedefkit.Coq_ty.unionv_fold u (Coq_existT (k,
        (pattern_match_val_reverse (typedefkit.Coq_ty.unionk_ty u k) 
          (p0 k) pc vs)))
    | _ -> c

  (** val pattern_match_val_reverse' :
      Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_MatchResult ->
      Coq_ty.coq_Val **)

  let pattern_match_val_reverse' _UU03c3_ p c =
    pattern_match_val_reverse _UU03c3_ p (projT1 c) (projT2 c)

  type ('n, 'r) coq_PatternCaseCurried = __

  (** val of_pattern_case_curried :
      ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> 'a1 coq_Pattern -> ('a1, 'a2) coq_PatternCaseCurried
      -> 'a1 coq_PatternCase -> 'a2 **)

  let rec of_pattern_case_curried _UU0393_ _ pat rhs =
    match pat with
    | Coq_pat_bool -> Obj.magic rhs
    | Coq_pat_list (_, _, _) ->
      (fun pc ->
        let Coq_pair (a, b) = Obj.magic rhs in
        (match Obj.magic pc with
         | Coq_true -> a
         | Coq_false -> b))
    | Coq_pat_sum (_, _, _, _) ->
      (fun pc ->
        let Coq_pair (a, b) = Obj.magic rhs in
        (match Obj.magic pc with
         | Coq_true -> a
         | Coq_false -> b))
    | Coq_pat_enum _ -> Obj.magic rhs
    | Coq_pat_bvec_exhaustive _ -> Obj.magic rhs
    | Coq_pat_union (u, p0) ->
      (fun pat0 ->
        let Coq_existT (k, pc) = Obj.magic pat0 in
        of_pattern_case_curried _UU0393_ (typedefkit.Coq_ty.unionk_ty u k)
          (p0 k) (Obj.magic rhs k) pc)
    | _ -> (fun _ -> Obj.magic rhs)

  type ('n, 'r) coq_Alternative = { alt_pat : 'n coq_Pattern;
                                    alt_rhs : ('n, 'r) coq_PatternCaseCurried }

  (** val alt_pat :
      ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> ('a1, 'a2) coq_Alternative -> 'a1 coq_Pattern **)

  let alt_pat _ _ a =
    a.alt_pat

  (** val alt_rhs :
      ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> ('a1, 'a2) coq_Alternative -> ('a1, 'a2)
      coq_PatternCaseCurried **)

  let alt_rhs _ _ a =
    a.alt_rhs

  (** val freshen_ctx :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let rec freshen_ctx n _UU03a3_ = function
  | Coq_ctx.Coq_nil -> Coq_ctx.Coq_nil
  | Coq_ctx.Coq_snoc (_UU0393_, b) ->
    let x = b.Binding.name in
    let _UU03c3_ = b.Binding.coq_type in
    let _UU0393_' = freshen_ctx n _UU03a3_ _UU0393_ in
    let x' = fresh_lvar varkit (Coq_ctx.cat _UU03a3_ _UU0393_') (Some (n x))
    in
    Coq_ctx.Coq_snoc (_UU0393_', { Binding.name = x'; Binding.coq_type =
    _UU03c3_ })

  (** val unfreshen_namedenv :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty, 'a2) coq_NamedEnv -> ('a1,
      Coq_ty.coq_Ty, 'a2) coq_NamedEnv **)

  let rec unfreshen_namedenv n _UU03a3_ _UU0394_ x =
    match _UU0394_ with
    | Coq_ctx.Coq_nil -> Coq_env.Coq_nil
    | Coq_ctx.Coq_snoc (_UU0393_, b) ->
      let Coq_env.Coq_isSnoc (e_UU0393_, tb) =
        Obj.magic Coq_env.view (Coq_ctx.Coq_snoc
          ((freshen_ctx n _UU03a3_ _UU0393_), { Binding.name =
          (fresh_lvar varkit
            (Coq_ctx.cat _UU03a3_ (freshen_ctx n _UU03a3_ _UU0393_)) (Some
            (n b.Binding.name)));
          Binding.coq_type = b.Binding.coq_type })) x
      in
      Coq_env.Coq_snoc (_UU0393_,
      (unfreshen_namedenv n _UU03a3_ _UU0393_ e_UU0393_), b, tb)

  (** val freshen_namedenv :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty, 'a2) coq_NamedEnv -> (coq_LVar,
      Coq_ty.coq_Ty, 'a2) coq_NamedEnv **)

  let rec freshen_namedenv n _UU03a3_ _ = function
  | Coq_env.Coq_nil -> Coq_env.Coq_nil
  | Coq_env.Coq_snoc (_UU0393_, e0, b, d) ->
    let e' = freshen_namedenv n _UU03a3_ _UU0393_ e0 in
    let x' =
      fresh_lvar varkit
        (Coq_ctx.cat _UU03a3_
          (let rec freshen_ctx0 _UU03a3_0 = function
           | Coq_ctx.Coq_nil -> Coq_ctx.Coq_nil
           | Coq_ctx.Coq_snoc (_UU0393_0, b0) ->
             Coq_ctx.Coq_snoc ((freshen_ctx0 _UU03a3_0 _UU0393_0),
               { Binding.name =
               (fresh_lvar varkit
                 (Coq_ctx.cat _UU03a3_0 (freshen_ctx0 _UU03a3_0 _UU0393_0))
                 (Some (n b0.Binding.name)));
               Binding.coq_type = b0.Binding.coq_type })
           in freshen_ctx0 _UU03a3_ _UU0393_))
        (Some (n b.Binding.name))
    in
    Coq_env.Coq_snoc ((freshen_ctx n _UU03a3_ _UU0393_), e', { Binding.name =
    x'; Binding.coq_type = b.Binding.coq_type }, d)

  (** val freshen_tuplepat :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat
      -> coq_LVar coq_TuplePat **)

  let rec freshen_tuplepat n _UU03a3_ _ _ = function
  | Coq_tuplepat_nil -> Coq_tuplepat_nil
  | Coq_tuplepat_snoc (_UU03c3_s0, _UU0394_0, pat, _UU03c3_, x) ->
    Coq_tuplepat_snoc (_UU03c3_s0, (freshen_ctx n _UU03a3_ _UU0394_0),
      (freshen_tuplepat n _UU03a3_ _UU03c3_s0 _UU0394_0 pat), _UU03c3_,
      (fresh_lvar varkit
        (Coq_ctx.cat _UU03a3_ (freshen_ctx n _UU03a3_ _UU0394_0)) (Some
        (n x))))

  (** val freshen_recordpat :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> coq_LVar coq_RecordPat **)

  let rec freshen_recordpat n _UU03a3_ _ _ = function
  | Coq_recordpat_nil -> Coq_recordpat_nil
  | Coq_recordpat_snoc (rfs0, _UU0394_0, pat, rf, _UU03c4_, x) ->
    Coq_recordpat_snoc (rfs0, (freshen_ctx n _UU03a3_ _UU0394_0),
      (freshen_recordpat n _UU03a3_ rfs0 _UU0394_0 pat), rf, _UU03c4_,
      (fresh_lvar varkit
        (Coq_ctx.cat _UU03a3_ (freshen_ctx n _UU03a3_ _UU0394_0)) (Some
        (n x))))

  (** val freshen_pattern :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> coq_LVar
      coq_Pattern **)

  let rec freshen_pattern n _UU03a3_ _ = function
  | Coq_pat_var (x, _UU03c3_0) ->
    Coq_pat_var ((fresh_lvar varkit _UU03a3_ (Some (n x))), _UU03c3_0)
  | Coq_pat_bool -> Coq_pat_bool
  | Coq_pat_list (_UU03c3_, x, y) ->
    let x' = fresh_lvar varkit _UU03a3_ (Some (n x)) in
    let y' =
      fresh_lvar varkit (Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name = x';
        Binding.coq_type = _UU03c3_ })) (Some (n y))
    in
    Coq_pat_list (_UU03c3_, x', y')
  | Coq_pat_pair (x, y, _UU03c3_, _UU03c4_) ->
    let x' = fresh_lvar varkit _UU03a3_ (Some (n x)) in
    let y' =
      fresh_lvar varkit (Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name = x';
        Binding.coq_type = _UU03c3_ })) (Some (n y))
    in
    Coq_pat_pair (x', y', _UU03c3_, _UU03c4_)
  | Coq_pat_sum (_UU03c3_, _UU03c4_, x, y) ->
    Coq_pat_sum (_UU03c3_, _UU03c4_,
      (fresh_lvar varkit _UU03a3_ (Some (n x))),
      (fresh_lvar varkit _UU03a3_ (Some (n y))))
  | Coq_pat_unit -> Coq_pat_unit
  | Coq_pat_enum e -> Coq_pat_enum e
  | Coq_pat_bvec_split (m, n0, x, y) ->
    let x' = fresh_lvar varkit _UU03a3_ (Some (n x)) in
    let y' =
      fresh_lvar varkit (Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name = x';
        Binding.coq_type = (Coq_ty.Coq_bvec m) })) (Some (n y))
    in
    Coq_pat_bvec_split (m, n0, x', y')
  | Coq_pat_bvec_exhaustive m -> Coq_pat_bvec_exhaustive m
  | Coq_pat_tuple (_UU03c3_s, _UU0394_, p0) ->
    Coq_pat_tuple (_UU03c3_s, (freshen_ctx n _UU03a3_ _UU0394_),
      (freshen_tuplepat n _UU03a3_ _UU03c3_s _UU0394_ p0))
  | Coq_pat_record (r, _UU0394_, p0) ->
    Coq_pat_record (r, (freshen_ctx n _UU03a3_ _UU0394_),
      (freshen_recordpat n _UU03a3_ (typedefkit.Coq_ty.recordf_ty r) _UU0394_
        p0))
  | Coq_pat_union (u, p0) ->
    Coq_pat_union (u, (fun k ->
      freshen_pattern n _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k) (p0 k)))

  (** val unfreshen_patterncase :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> coq_LVar
      coq_PatternCase -> 'a1 coq_PatternCase **)

  let rec unfreshen_patterncase n _UU03a3_ _ p pc =
    match p with
    | Coq_pat_union (u, p0) ->
      let Coq_existT (k, pc0) = Obj.magic pc in
      Obj.magic (Coq_existT (k,
        (unfreshen_patterncase n _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k)
          (p0 k) pc0)))
    | _ -> pc

  (** val freshen_patterncase :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
      coq_PatternCase -> coq_LVar coq_PatternCase **)

  let rec freshen_patterncase n _UU03a3_ _ p pc =
    match p with
    | Coq_pat_union (u, p0) ->
      let Coq_existT (k, pc0) = Obj.magic pc in
      Obj.magic (Coq_existT (k,
        (freshen_patterncase n _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k)
          (p0 k) pc0)))
    | _ -> pc

  (** val unfreshen_patterncaseenv' :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> coq_LVar
      coq_PatternCase -> (coq_LVar, Coq_ty.coq_Ty, 'a2) coq_NamedEnv -> ('a1,
      Coq_ty.coq_Ty, 'a2) coq_NamedEnv **)

  let unfreshen_patterncaseenv' n _UU03a3_ _UU03c3_ p pc e =
    unfreshen_namedenv n _UU03a3_
      (coq_PatternCaseCtx _UU03c3_ p
        (unfreshen_patterncase n _UU03a3_ _UU03c3_ p pc))
      e

  (** val freshen_patterncaseenv :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
      coq_PatternCase -> ('a1, Coq_ty.coq_Ty, 'a2) coq_NamedEnv -> (coq_LVar,
      Coq_ty.coq_Ty, 'a2) coq_NamedEnv **)

  let rec freshen_patterncaseenv n _UU03a3_ _ p pc x =
    match p with
    | Coq_pat_var (x0, _UU03c3_0) ->
      let Coq_env.Coq_isSnoc (_, t0) =
        Obj.magic Coq_env.view
          (coq_PatternCaseCtx _UU03c3_0 (Coq_pat_var (x0, _UU03c3_0)) pc) x
      in
      Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (fresh_lvar varkit _UU03a3_ (Some (n x0))); Binding.coq_type =
      _UU03c3_0 }, t0)
    | Coq_pat_list (_UU03c3_, x0, y) ->
      (match Obj.magic pc with
       | Coq_true -> Coq_env.Coq_nil
       | Coq_false ->
         let Coq_env.Coq_isSnoc (ts1, t0) =
           Obj.magic Coq_env.view
             (coq_PatternCaseCtx (Coq_ty.Coq_list _UU03c3_) (Coq_pat_list
               (_UU03c3_, x0, y)) (Obj.magic Coq_false))
             x
         in
         let Coq_env.Coq_isSnoc (_, h) =
           Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             { Binding.name = x0; Binding.coq_type = _UU03c3_ })) ts1
         in
         Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         { Binding.name = (fresh_lvar varkit _UU03a3_ (Some (n x0)));
         Binding.coq_type = _UU03c3_ })), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, { Binding.name =
         (fresh_lvar varkit _UU03a3_ (Some (n x0))); Binding.coq_type =
         _UU03c3_ }, h)), { Binding.name =
         (fresh_lvar varkit (Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name =
           (fresh_lvar varkit _UU03a3_ (Some (n x0))); Binding.coq_type =
           _UU03c3_ })) (Some (n y)));
         Binding.coq_type = (Coq_ty.Coq_list _UU03c3_) }, t0))
    | Coq_pat_pair (x0, y, _UU03c3_0, _UU03c4_) ->
      let Coq_env.Coq_isSnoc (ts1, v) =
        Obj.magic Coq_env.view
          (coq_PatternCaseCtx (Coq_ty.Coq_prod (_UU03c3_0, _UU03c4_))
            (Coq_pat_pair (x0, y, _UU03c3_0, _UU03c4_)) pc)
          x
      in
      let Coq_env.Coq_isSnoc (_, v0) =
        Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          { Binding.name = x0; Binding.coq_type = _UU03c3_0 })) ts1
      in
      Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (fresh_lvar varkit _UU03a3_ (Some (n x0))); Binding.coq_type =
      _UU03c3_0 })), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      { Binding.name = (fresh_lvar varkit _UU03a3_ (Some (n x0)));
      Binding.coq_type = _UU03c3_0 }, v0)), { Binding.name =
      (fresh_lvar varkit (Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name =
        (fresh_lvar varkit _UU03a3_ (Some (n x0))); Binding.coq_type =
        _UU03c3_0 })) (Some (n y)));
      Binding.coq_type = _UU03c4_ }, v)
    | Coq_pat_sum (_UU03c3_, _UU03c4_, x0, y) ->
      (match Obj.magic pc with
       | Coq_true ->
         let Coq_env.Coq_isSnoc (_, v) =
           Obj.magic Coq_env.view
             (coq_PatternCaseCtx (Coq_ty.Coq_sum (_UU03c3_, _UU03c4_))
               (Coq_pat_sum (_UU03c3_, _UU03c4_, x0, y)) (Obj.magic Coq_true))
             x
         in
         Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
         (fresh_lvar varkit _UU03a3_ (Some (n x0))); Binding.coq_type =
         _UU03c3_ }, v)
       | Coq_false ->
         let Coq_env.Coq_isSnoc (_, v) =
           Obj.magic Coq_env.view
             (coq_PatternCaseCtx (Coq_ty.Coq_sum (_UU03c3_, _UU03c4_))
               (Coq_pat_sum (_UU03c3_, _UU03c4_, x0, y))
               (Obj.magic Coq_false))
             x
         in
         Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
         (fresh_lvar varkit _UU03a3_ (Some (n y))); Binding.coq_type =
         _UU03c4_ }, v))
    | Coq_pat_bvec_split (m, n0, x0, y) ->
      let Coq_env.Coq_isSnoc (ts1, vy) =
        Obj.magic Coq_env.view
          (coq_PatternCaseCtx (Coq_ty.Coq_bvec (add m n0))
            (Coq_pat_bvec_split (m, n0, x0, y)) pc)
          x
      in
      let Coq_env.Coq_isSnoc (_, vx) =
        Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          { Binding.name = x0; Binding.coq_type = (Coq_ty.Coq_bvec m) })) ts1
      in
      Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (fresh_lvar varkit _UU03a3_ (Some (n x0))); Binding.coq_type =
      (Coq_ty.Coq_bvec m) })), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
      Coq_env.Coq_nil, { Binding.name =
      (fresh_lvar varkit _UU03a3_ (Some (n x0))); Binding.coq_type =
      (Coq_ty.Coq_bvec m) }, vx)), { Binding.name =
      (fresh_lvar varkit (Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name =
        (fresh_lvar varkit _UU03a3_ (Some (n x0))); Binding.coq_type =
        (Coq_ty.Coq_bvec m) })) (Some (n y)));
      Binding.coq_type = (Coq_ty.Coq_bvec n0) }, vy)
    | Coq_pat_tuple (_UU03c3_s, _UU0394_, p0) ->
      freshen_namedenv n _UU03a3_
        (coq_PatternCaseCtx (Coq_ty.Coq_tuple _UU03c3_s) (Coq_pat_tuple
          (_UU03c3_s, _UU0394_, p0)) pc)
        x
    | Coq_pat_record (r, _UU0394_, p0) ->
      freshen_namedenv n _UU03a3_
        (coq_PatternCaseCtx (Coq_ty.Coq_record r) (Coq_pat_record (r,
          _UU0394_, p0)) pc)
        x
    | Coq_pat_union (u, p0) ->
      let Coq_existT (k, pc0) = Obj.magic pc in
      freshen_patterncaseenv n _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k)
        (p0 k) pc0 x
    | _ -> Coq_env.Coq_nil

  (** val unfreshen_patterncaseenv :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> coq_LVar
      coq_PatternCase -> (coq_LVar, Coq_ty.coq_Ty, 'a2) coq_NamedEnv -> ('a1,
      Coq_ty.coq_Ty, 'a2) coq_NamedEnv **)

  let rec unfreshen_patterncaseenv n _UU03a3_ _ p pc x =
    match p with
    | Coq_pat_var (x0, _UU03c3_0) ->
      let Coq_env.Coq_isSnoc (_, t0) =
        Obj.magic Coq_env.view
          (coq_PatternCaseCtx _UU03c3_0
            (freshen_pattern n _UU03a3_ _UU03c3_0 (Coq_pat_var (x0,
              _UU03c3_0)))
            pc)
          x
      in
      Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      x0; Binding.coq_type = _UU03c3_0 }, t0)
    | Coq_pat_list (_UU03c3_, x0, y) ->
      (match Obj.magic pc with
       | Coq_true -> Coq_env.Coq_nil
       | Coq_false ->
         let Coq_env.Coq_isSnoc (ts1, t0) =
           Obj.magic Coq_env.view
             (coq_PatternCaseCtx (Coq_ty.Coq_list _UU03c3_)
               (freshen_pattern n _UU03a3_ (Coq_ty.Coq_list _UU03c3_)
                 (Coq_pat_list (_UU03c3_, x0, y)))
               (Obj.magic Coq_false))
             x
         in
         let Coq_env.Coq_isSnoc (_, h) =
           Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             { Binding.name = (fresh_lvar varkit _UU03a3_ (Some (n x0)));
             Binding.coq_type = _UU03c3_ })) ts1
         in
         Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         { Binding.name = x0; Binding.coq_type = _UU03c3_ })),
         (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
         { Binding.name = x0; Binding.coq_type = _UU03c3_ }, h)),
         { Binding.name = y; Binding.coq_type = (Coq_ty.Coq_list _UU03c3_) },
         t0))
    | Coq_pat_pair (x0, y, _UU03c3_0, _UU03c4_) ->
      let Coq_env.Coq_isSnoc (ts1, v) =
        Obj.magic Coq_env.view
          (coq_PatternCaseCtx (Coq_ty.Coq_prod (_UU03c3_0, _UU03c4_))
            (freshen_pattern n _UU03a3_ (Coq_ty.Coq_prod (_UU03c3_0,
              _UU03c4_)) (Coq_pat_pair (x0, y, _UU03c3_0, _UU03c4_)))
            pc)
          x
      in
      let Coq_env.Coq_isSnoc (_, v0) =
        Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          { Binding.name = (fresh_lvar varkit _UU03a3_ (Some (n x0)));
          Binding.coq_type = _UU03c3_0 })) ts1
      in
      Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      x0; Binding.coq_type = _UU03c3_0 })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x0;
      Binding.coq_type = _UU03c3_0 }, v0)), { Binding.name = y;
      Binding.coq_type = _UU03c4_ }, v)
    | Coq_pat_sum (_UU03c3_, _UU03c4_, x0, y) ->
      (match Obj.magic pc with
       | Coq_true ->
         let Coq_env.Coq_isSnoc (_, v) =
           Obj.magic Coq_env.view
             (coq_PatternCaseCtx (Coq_ty.Coq_sum (_UU03c3_, _UU03c4_))
               (freshen_pattern n _UU03a3_ (Coq_ty.Coq_sum (_UU03c3_,
                 _UU03c4_)) (Coq_pat_sum (_UU03c3_, _UU03c4_, x0, y)))
               (Obj.magic Coq_true))
             x
         in
         Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
         x0; Binding.coq_type = _UU03c3_ }, v)
       | Coq_false ->
         let Coq_env.Coq_isSnoc (_, v) =
           Obj.magic Coq_env.view
             (coq_PatternCaseCtx (Coq_ty.Coq_sum (_UU03c3_, _UU03c4_))
               (freshen_pattern n _UU03a3_ (Coq_ty.Coq_sum (_UU03c3_,
                 _UU03c4_)) (Coq_pat_sum (_UU03c3_, _UU03c4_, x0, y)))
               (Obj.magic Coq_false))
             x
         in
         Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
         y; Binding.coq_type = _UU03c4_ }, v))
    | Coq_pat_bvec_split (m, n0, x0, y) ->
      let Coq_env.Coq_isSnoc (ts1, vy) =
        Obj.magic Coq_env.view
          (coq_PatternCaseCtx (Coq_ty.Coq_bvec (add m n0))
            (freshen_pattern n _UU03a3_ (Coq_ty.Coq_bvec (add m n0))
              (Coq_pat_bvec_split (m, n0, x0, y)))
            pc)
          x
      in
      let Coq_env.Coq_isSnoc (_, vx) =
        Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          { Binding.name = (fresh_lvar varkit _UU03a3_ (Some (n x0)));
          Binding.coq_type = (Coq_ty.Coq_bvec m) })) ts1
      in
      Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      x0; Binding.coq_type = (Coq_ty.Coq_bvec m) })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name = x0;
      Binding.coq_type = (Coq_ty.Coq_bvec m) }, vx)), { Binding.name = y;
      Binding.coq_type = (Coq_ty.Coq_bvec n0) }, vy)
    | Coq_pat_tuple (_, _UU0394_, _) ->
      unfreshen_namedenv n _UU03a3_ _UU0394_ x
    | Coq_pat_record (_, _UU0394_, _) ->
      unfreshen_namedenv n _UU03a3_ _UU0394_ x
    | Coq_pat_union (u, p0) ->
      let Coq_existT (k, pc0) = Obj.magic pc in
      unfreshen_patterncaseenv n _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k)
        (p0 k) pc0 x
    | _ -> Coq_env.Coq_nil

  (** val freshen_matchresult :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
      coq_MatchResult -> coq_LVar coq_MatchResult **)

  let freshen_matchresult n _UU03a3_ _UU03c3_ p = function
  | Coq_existT (pc, vs) ->
    Coq_existT ((freshen_patterncase n _UU03a3_ _UU03c3_ p pc),
      (freshen_patterncaseenv n _UU03a3_ _UU03c3_ p pc vs))

  (** val unfreshen_matchresult :
      ('a1 -> coq_LVar) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> coq_LVar
      coq_MatchResult -> 'a1 coq_MatchResult **)

  let unfreshen_matchresult n _UU03a3_ _UU03c3_ p = function
  | Coq_existT (pc, vs) ->
    Coq_existT ((unfreshen_patterncase n _UU03a3_ _UU03c3_ p pc),
      (unfreshen_patterncaseenv n _UU03a3_ _UU03c3_ p pc vs))

  type 't coq_OccursCheck =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 't -> 't option

  (** val occurs_check :
      'a1 coq_OccursCheck -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 ->
      'a1 option **)

  let occurs_check occursCheck =
    occursCheck

  (** val coq_OccursCheck_Const : 'a1 coq_Const coq_OccursCheck **)

  let coq_OccursCheck_Const _ _ _ v =
    Some v

  (** val occurs_check_env :
      ('a1 -> 'a2 coq_OccursCheck) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2)
      Coq_env.coq_Env coq_OccursCheck **)

  let rec occurs_check_env oCT _ _UU03a3_ x xIn = function
  | Coq_env.Coq_nil -> Some Coq_env.Coq_nil
  | Coq_env.Coq_snoc (_UU0393_0, ts0, b, t0) ->
    Coq_option.bind
      (occurs_check (occurs_check_env oCT _UU0393_0) _UU03a3_ x xIn ts0)
      (fun ts' ->
      Coq_option.bind (occurs_check (oCT b) _UU03a3_ x xIn t0) (fun t' ->
        Some (Coq_env.Coq_snoc (_UU0393_0, ts', b, t'))))

  (** val occurs_check_term : Coq_ty.coq_Ty -> coq_Term coq_OccursCheck **)

  let rec occurs_check_term _ _UU03a3_ x xIn = function
  | Coq_term_var (l, _UU03c3_, yIn) ->
    (match Coq_ctx.occurs_check_view _UU03a3_ x xIn { Binding.name = l;
             Binding.coq_type = _UU03c3_ } yIn with
     | Coq_ctx.Same -> None
     | Coq_ctx.Diff (y, yIn') ->
       Some (Coq_term_var (y.Binding.name, y.Binding.coq_type, yIn')))
  | Coq_term_val (_UU03c3_, v) -> Some (Coq_term_val (_UU03c3_, v))
  | Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1, t2) ->
    Coq_option.bind (occurs_check_term _UU03c3_1 _UU03a3_ x xIn t1)
      (fun t1' ->
      Coq_option.bind (occurs_check_term _UU03c3_2 _UU03a3_ x xIn t2)
        (fun t2' -> Some (Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3,
        op, t1', t2'))))
  | Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t1) ->
    Coq_option.bind (occurs_check_term _UU03c3_1 _UU03a3_ x xIn t1)
      (fun t' -> Some (Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t')))
  | Coq_term_tuple (_UU03c3_s, ts) ->
    Coq_option.map (fun x0 -> Coq_term_tuple (_UU03c3_s, x0))
      (occurs_check (occurs_check_env occurs_check_term _UU03c3_s) _UU03a3_ x
        xIn ts)
  | Coq_term_union (u, k, t1) ->
    Coq_option.map (fun x0 -> Coq_term_union (u, k, x0))
      (occurs_check_term (typedefkit.Coq_ty.unionk_ty u k) _UU03a3_ x xIn t1)
  | Coq_term_record (r, ts) ->
    let oCTerm = fun xt -> occurs_check_term xt.Binding.coq_type in
    Coq_option.map (fun x0 -> Coq_term_record (r, x0))
      (occurs_check
        (occurs_check_env oCTerm (typedefkit.Coq_ty.recordf_ty r)) _UU03a3_ x
        xIn ts)

  (** val occurs_check_list :
      'a1 coq_OccursCheck -> 'a1 coq_List coq_OccursCheck **)

  let occurs_check_list h _UU03a3_ x xIn =
    Coq_option.traverse_list (occurs_check h _UU03a3_ x xIn)

  (** val occurs_check_sub :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Sub coq_OccursCheck **)

  let occurs_check_sub _UU03a3_ =
    occurs_check_env (fun i -> occurs_check_term i.Binding.coq_type) _UU03a3_

  (** val occurs_check_pair :
      'a1 coq_OccursCheck -> 'a2 coq_OccursCheck -> ('a1, 'a2) coq_Pair
      coq_OccursCheck **)

  let occurs_check_pair h h0 _UU03a3_ x xIn = function
  | Coq_pair (a, b) ->
    Coq_option.bind (occurs_check h _UU03a3_ x xIn a) (fun a' ->
      Coq_option.bind (occurs_check h0 _UU03a3_ x xIn b) (fun b' -> Some
        (Coq_pair (a', b'))))

  (** val occurs_check_option :
      'a1 coq_OccursCheck -> 'a1 coq_Option coq_OccursCheck **)

  let occurs_check_option h _UU03a3_ x xIn = function
  | Some a ->
    Coq_option.map (fun x0 -> Some x0) (occurs_check h _UU03a3_ x xIn a)
  | None -> Some None

  (** val occurs_check_unit : coq_Unit coq_OccursCheck **)

  let occurs_check_unit _ _ _ _ =
    Some Coq_tt

  (** val occurscheck_ctx :
      'a1 coq_OccursCheck -> 'a1 Coq_ctx.coq_Ctx coq_OccursCheck **)

  let rec occurscheck_ctx h _UU03a3_ x xIn = function
  | Coq_ctx.Coq_nil -> Some Coq_ctx.Coq_nil
  | Coq_ctx.Coq_snoc (ys0, y) ->
    Coq_option.bind (occurscheck_ctx h _UU03a3_ x xIn ys0) (fun ys' ->
      Coq_option.bind (occurs_check h _UU03a3_ x xIn y) (fun y' -> Some
        (Coq_ctx.Coq_snoc (ys', y'))))

  module Experimental =
   struct
    type 't coq_OccursCheckView =
    | Succ of 't
    | Fail of 't

    (** val coq_OccursCheckView_rect :
        'a1 coq_Subst -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ('a1
        -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 coq_OccursCheckView -> 'a2 **)

    let coq_OccursCheckView_rect _ _ _ _ f f0 _ = function
    | Succ t0 -> f t0
    | Fail t0 -> f0 t0

    (** val coq_OccursCheckView_rec :
        'a1 coq_Subst -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ('a1
        -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 coq_OccursCheckView -> 'a2 **)

    let coq_OccursCheckView_rec _ _ _ _ f f0 _ = function
    | Succ t0 -> f t0
    | Fail t0 -> f0 t0

    type 't coq_OccursCheck =
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 't -> 't
      coq_OccursCheckView

    (** val occurs_check_view :
        'a1 coq_Subst -> 'a1 coq_OccursCheck -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
        Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_In -> 'a1 -> 'a1 coq_OccursCheckView **)

    let occurs_check_view _ occursCheck =
      occursCheck

    (** val coq_OccursCheckEnv :
        ('a1 -> 'a2 coq_Subst) -> ('a1 -> 'a2 coq_OccursCheck) -> 'a1
        Coq_ctx.coq_Ctx -> ('a1, 'a2) Coq_env.coq_Env coq_OccursCheck **)

    let rec coq_OccursCheckEnv sBT oCT _ _UU03a3_ x xIn = function
    | Coq_env.Coq_nil -> Succ Coq_env.Coq_nil
    | Coq_env.Coq_snoc (_UU0393_0, ts0, b, t0) ->
      (match coq_OccursCheckEnv sBT oCT _UU0393_0 _UU03a3_ x xIn ts0 with
       | Succ ts' ->
         (match occurs_check_view (sBT b) (oCT b) _UU03a3_ x xIn t0 with
          | Succ t1 -> Succ (Coq_env.Coq_snoc (_UU0393_0, ts', b, t1))
          | Fail t1 ->
            Fail (Coq_env.Coq_snoc (_UU0393_0,
              (subst (coq_SubstEnv sBT _UU0393_0)
                (Coq_ctx.remove _UU03a3_ x xIn) ts' _UU03a3_
                (sub_shift _UU03a3_ x xIn)),
              b, t1)))
       | Fail ts1 -> Fail (Coq_env.Coq_snoc (_UU0393_0, ts1, b, t0)))
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

  (** val initSU :
      'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 **)

  let initSU substUniv =
    substUniv.initSU

  (** val transSU :
      'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 -> 'a1 -> 'a1 **)

  let transSU substUniv =
    substUniv.transSU

  (** val interpSU :
      'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 -> coq_Sub **)

  let interpSU substUniv =
    substUniv.interpSU

  type ('sb, 't) coq_SubstSU =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't ->
    'sb -> 't

  (** val substSU :
      ('a1, 'a2) coq_SubstSU -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a2 -> 'a1 -> 'a2 **)

  let substSU substSU0 =
    substSU0

  (** val substSU_term :
      'a1 coq_SubstUniv -> Coq_ty.coq_Ty -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term -> 'a1 -> coq_Term **)

  let rec substSU_term h _ _UU03a3_1 _UU03a3_2 t0 _UU03b6_ =
    match t0 with
    | Coq_term_var (_UU03c2_, _UU03c3_0, lIn) ->
      Coq_env.lookup _UU03a3_1 (h.interpSU _UU03a3_1 _UU03a3_2 _UU03b6_)
        { Binding.name = _UU03c2_; Binding.coq_type = _UU03c3_0 } lIn
    | Coq_term_val (_UU03c3_, v) -> Coq_term_val (_UU03c3_, v)
    | Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1, t2) ->
      Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op,
        (substSU_term h _UU03c3_1 _UU03a3_1 _UU03a3_2 t1 _UU03b6_),
        (substSU_term h _UU03c3_2 _UU03a3_1 _UU03a3_2 t2 _UU03b6_))
    | Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t1) ->
      Coq_term_unop (_UU03c3_1, _UU03c3_2, op,
        (substSU_term h _UU03c3_1 _UU03a3_1 _UU03a3_2 t1 _UU03b6_))
    | Coq_term_tuple (_UU03c3_s, ts) ->
      Coq_term_tuple (_UU03c3_s,
        (Coq_env.map (fun b t1 ->
          substSU_term h b _UU03a3_1 _UU03a3_2 t1 _UU03b6_) _UU03c3_s ts))
    | Coq_term_union (u, k, t1) ->
      Coq_term_union (u, k,
        (substSU_term h (typedefkit.Coq_ty.unionk_ty u k) _UU03a3_1 _UU03a3_2
          t1 _UU03b6_))
    | Coq_term_record (r, ts) ->
      Coq_term_record (r,
        (Coq_env.map (fun b t1 ->
          substSU_term h b.Binding.coq_type _UU03a3_1 _UU03a3_2 t1 _UU03b6_)
          (typedefkit.Coq_ty.recordf_ty r) ts))

  (** val coq_SubstSUTerm :
      'a1 coq_SubstUniv -> Coq_ty.coq_Ty -> ('a1, coq_Term) coq_SubstSU **)

  let coq_SubstSUTerm =
    substSU_term

  (** val substSU_option :
      ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 coq_Option) coq_SubstSU **)

  let substSU_option h _UU03a3_1 _UU03a3_2 t0 _UU03c3_ =
    match t0 with
    | Some t' -> Some (substSU h _UU03a3_1 _UU03a3_2 t' _UU03c3_)
    | None -> None

  type 'sb coq_MeetResult = { _UU03a3_12 : (coq_LVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding Coq_ctx.coq_Ctx;
                              meetLeft : 'sb; meetRight : 'sb; meetUp : 
                              'sb }

  (** val _UU03a3_12 :
      'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx **)

  let _UU03a3_12 _ _ _ _ m =
    m._UU03a3_12

  (** val meetLeft :
      'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1 **)

  let meetLeft _ _ _ _ m =
    m.meetLeft

  (** val meetRight :
      'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1 **)

  let meetRight _ _ _ _ m =
    m.meetRight

  (** val meetUp :
      'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1 **)

  let meetUp _ _ _ _ m =
    m.meetUp

  type 'sb coq_SubstUnivMeet =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'sb ->
    'sb -> 'sb coq_MeetResult

  (** val meetSU :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a1 -> 'a1 coq_MeetResult **)

  let meetSU _ substUnivMeet =
    substUnivMeet

  (** val coq_SubstSU_env :
      'a1 coq_SubstUniv -> 'a2 Coq_ctx.coq_Ctx -> ('a2 -> ('a1, 'a3)
      coq_SubstSU) -> ('a1, ('a2, 'a3) Coq_env.coq_Env) coq_SubstSU **)

  let coq_SubstSU_env _ _UU0394_ suT _UU03a3_1 _UU03a3_2 ts _UU03b6_ =
    Coq_env.map (fun b t0 -> suT b _UU03a3_1 _UU03a3_2 t0 _UU03b6_) _UU0394_
      ts

  (** val coq_SubstSU_sub :
      'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, coq_Sub) coq_SubstSU **)

  let coq_SubstSU_sub h _UU0394_ _UU03a3_1 _UU03a3_2 =
    coq_SubstSU_env h _UU0394_ (fun b ->
      coq_SubstSUTerm h b.Binding.coq_type) _UU03a3_1 _UU03a3_2

  (** val substSU_pair :
      ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU -> ('a1, ('a2, 'a3)
      coq_Pair) coq_SubstSU **)

  let substSU_pair h h0 _UU03a3_1 _UU03a3_2 pat _UU03c3_ =
    let Coq_pair (t1, t2) = pat in
    Coq_pair ((substSU h _UU03a3_1 _UU03a3_2 t1 _UU03c3_),
    (substSU h0 _UU03a3_1 _UU03a3_2 t2 _UU03c3_))

  (** val substSU_list :
      ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 coq_List) coq_SubstSU **)

  let substSU_list h _UU03a3_1 _UU03a3_2 ts _UU03b6_ =
    ListDef.map (fun t0 -> substSU h _UU03a3_1 _UU03a3_2 t0 _UU03b6_) ts

  (** val substSU_Const : ('a1, 'a2 coq_Const) coq_SubstSU **)

  let substSU_Const _ _ v _ =
    v

  type 'sb coq_SubstUnivVar =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'sb

  (** val suVar :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 **)

  let suVar _ _ substUnivVar =
    substUnivVar

  type 'sb coq_SubstUnivVarUp =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> 'sb -> 'sb

  (** val upSU :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar ->
      'a1 coq_SubstUnivVarUp -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1
      -> 'a1 **)

  let upSU _ _ _ substUnivVarUp =
    substUnivVarUp

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

  (** val wkVarSU :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar ->
      'a1 coq_SubstUnivVarDown -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1 -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In **)

  let wkVarSU _ _ _ substUnivVarDown =
    substUnivVarDown.wkVarSU

  (** val downSU :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar ->
      'a1 coq_SubstUnivVarDown -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1 -> 'a1 **)

  let downSU _ _ _ substUnivVarDown =
    substUnivVarDown.downSU

  type ('sb, 't) coq_BoxSb =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'sb -> 't
    (* singleton inductive, whose constructor was MkBoxSb *)

  (** val unboxSb :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
      'a2) coq_BoxSb -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 -> 'a2 **)

  let unboxSb _ b =
    b

  (** val boxSb :
      ('a1, 'a2) coq_SubstSU -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_BoxSb **)

  let boxSb h _UU03a3_ t0 _UU03a3_' =
    substSU h _UU03a3_ _UU03a3_' t0

  (** val substSU_BoxSb :
      ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> ('a1, ('a1, 'a2)
      coq_BoxSb) coq_SubstSU **)

  let substSU_BoxSb _ h0 _UU03a3_1 _UU03a3_2 t0 _UU03b6_ _UU03a3_' _UU03b6_' =
    t0 _UU03a3_' (h0.transSU _UU03a3_1 _UU03a3_2 _UU03a3_' _UU03b6_ _UU03b6_')

  type ('sb, 't) coq_Weakened = { _UU03a3_supp : (coq_LVar, Coq_ty.coq_Ty)
                                                 Binding.coq_Binding
                                                 Coq_ctx.coq_Ctx;
                                  embedSupport : 'sb;
                                  wkVal : ('sb, 't) coq_BoxSb }

  (** val _UU03a3_supp :
      'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2)
      coq_Weakened -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx **)

  let _UU03a3_supp _ _ _ w =
    w._UU03a3_supp

  (** val embedSupport :
      'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2)
      coq_Weakened -> 'a1 **)

  let embedSupport _ _ _ w =
    w.embedSupport

  (** val wkVal :
      'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2)
      coq_Weakened -> ('a1, 'a2) coq_BoxSb **)

  let wkVal _ _ _ w =
    w.wkVal

  (** val unWeaken :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
      coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2) coq_Weakened ->
      'a2 **)

  let unWeaken _UU03a3_ _ _ wv =
    let { _UU03a3_supp = _; embedSupport = _UU03b6_; wkVal = v } = wv in
    v _UU03a3_ _UU03b6_

  (** val liftBoxUnOp :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
      -> 'a2) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a3, 'a1) coq_BoxSb -> ('a3, 'a2) coq_BoxSb **)

  let liftBoxUnOp f _ bv0 _UU03a3_' _UU03b6_ =
    f _UU03a3_' (bv0 _UU03a3_' _UU03b6_)

  (** val liftBoxBinOp :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
      -> 'a2 -> 'a3) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a4, 'a1) coq_BoxSb -> ('a4, 'a2) coq_BoxSb ->
      ('a4, 'a3) coq_BoxSb **)

  let liftBoxBinOp f _ bv1 bv2 _UU03a3_' _UU03b6_ =
    f _UU03a3_' (bv1 _UU03a3_' _UU03b6_) (bv2 _UU03a3_' _UU03b6_)

  (** val weakenInit :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU ->
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_Weakened **)

  let weakenInit _ _ h1 h2 _ _UU03a3_ v =
    { _UU03a3_supp = Coq_ctx.Coq_nil; embedSupport = (h2.initSU _UU03a3_);
      wkVal = (boxSb h1 Coq_ctx.Coq_nil v) }

  type ('sb, 't) coq_GenOccursCheck =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't ->
    ('sb, 't) coq_Weakened

  (** val gen_occurs_check :
      'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2)
      coq_GenOccursCheck -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_Weakened **)

  let gen_occurs_check _ _ genOccursCheck =
    genOccursCheck

  (** val coq_GenOccursCheck_Const :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
      coq_SubstUnivMeet -> ('a1, 'a2 coq_Const) coq_GenOccursCheck **)

  let coq_GenOccursCheck_Const _ _ h1 h2 _UU03a3_ v =
    weakenInit h1 h2 substSU_Const h1 h2 _UU03a3_ v

  (** val liftUnOp :
      'a1 coq_SubstUniv -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2
      -> 'a3) -> ('a1, 'a2) coq_Weakened -> ('a1, 'a3) coq_Weakened **)

  let liftUnOp _ _ _ _ f wv1 =
    let { _UU03a3_supp = wildcard'; embedSupport = _UU03c3_1; wkVal = v1 } =
      wv1
    in
    { _UU03a3_supp = wildcard'; embedSupport = _UU03c3_1; wkVal =
    (liftBoxUnOp f wildcard' v1) }

  (** val liftBinOp :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
      coq_SubstUnivMeet -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
      ('a1, 'a4) coq_SubstSU -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2)
      coq_Weakened -> ('a1, 'a3) coq_Weakened -> ('a1, 'a4) coq_Weakened **)

  let liftBinOp _ _ h1 h2 _UU03a3_ sSbT1 sSbT2 _ f wv1 wv2 =
    let { _UU03a3_supp = wildcard'; embedSupport = _UU03c3_1; wkVal = v1 } =
      wv1
    in
    let { _UU03a3_supp = wildcard'0; embedSupport = _UU03c3_2; wkVal = v2 } =
      wv2
    in
    let filtered_var =
      meetSU h1 h2 _UU03a3_ wildcard' wildcard'0 _UU03c3_1 _UU03c3_2
    in
    let { _UU03a3_12 = _UU03a3_13; meetLeft = _UU03c3_1'; meetRight =
      _UU03c3_2'; meetUp = _UU03c3_' } = filtered_var
    in
    { _UU03a3_supp = _UU03a3_13; embedSupport = _UU03c3_'; wkVal =
    (liftBoxBinOp f _UU03a3_13
      (substSU (substSU_BoxSb sSbT1 h1) wildcard' _UU03a3_13 v1 _UU03c3_1')
      (substSU (substSU_BoxSb sSbT2 h1) wildcard'0 _UU03a3_13 v2 _UU03c3_2')) }

  (** val liftTernOp :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
      coq_SubstUnivMeet -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
      ('a1, 'a4) coq_SubstSU -> ('a1, 'a5) coq_SubstSU -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 -> 'a3 -> 'a4
      -> 'a5) -> ('a1, 'a2) coq_Weakened -> ('a1, 'a3) coq_Weakened -> ('a1,
      'a4) coq_Weakened -> ('a1, 'a5) coq_Weakened **)

  let liftTernOp _ _ h1 h2 _UU03a3_ x x0 x1 x2 f wv1 wv2 wv3 =
    liftBinOp h1 h2 h1 h2 _UU03a3_ (substSU_pair x x0) x1 x2
      (fun _UU03a3_' pat v3 ->
      let Coq_pair (v1, v2) = pat in f _UU03a3_' v1 v2 v3)
      (liftBinOp h1 h2 h1 h2 _UU03a3_ x x0 (substSU_pair x x0)
        (fun _ v1 v2 -> Coq_pair (v1, v2)) wv1 wv2)
      wv3

  (** val gen_occurs_check_env :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
      coq_SubstUnivMeet -> ('a2 -> ('a1, 'a3) coq_SubstSU) -> ('a2 -> ('a1,
      'a3) coq_GenOccursCheck) -> 'a2 Coq_ctx.coq_Ctx -> ('a1, ('a2, 'a3)
      Coq_env.coq_Env) coq_GenOccursCheck **)

  let rec gen_occurs_check_env h h0 h1 h2 sT oCT _ _UU03a3_ = function
  | Coq_env.Coq_nil ->
    weakenInit h1 h2 (coq_SubstSU_env h1 Coq_ctx.Coq_nil sT) h1 h2 _UU03a3_
      Coq_env.Coq_nil
  | Coq_env.Coq_snoc (_UU0393_0, ts0, b, t0) ->
    liftBinOp h1 h2 h1 h2 _UU03a3_ (coq_SubstSU_env h1 _UU0393_0 sT) 
      (sT b) (coq_SubstSU_env h1 (Coq_ctx.Coq_snoc (_UU0393_0, b)) sT)
      (fun _ ts' t' -> Coq_env.Coq_snoc (_UU0393_0, ts', b, t'))
      (gen_occurs_check_env h h0 h1 h2 sT oCT _UU0393_0 _UU03a3_ ts0)
      (gen_occurs_check h1 (sT b) (oCT b) _UU03a3_ t0)

  (** val gen_occurs_check_term :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar ->
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
      coq_SubstUnivMeet -> Coq_ty.coq_Ty -> ('a1, coq_Term) coq_GenOccursCheck **)

  let rec gen_occurs_check_term h h0 h1 h2 h3 h4 h5 _ _UU03a3_ = function
  | Coq_term_var (l, _UU03c3_, xIn) ->
    { _UU03a3_supp = (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name = l;
      Binding.coq_type = _UU03c3_ })); embedSupport =
      (suVar h h0 h1 { Binding.name = l; Binding.coq_type = _UU03c3_ }
        _UU03a3_ xIn);
      wkVal =
      (boxSb (coq_SubstSUTerm h4 _UU03c3_) (Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, { Binding.name = l; Binding.coq_type = _UU03c3_ }))
        (Coq_term_var (l, _UU03c3_,
        (Coq_ctx.in_zero { Binding.name = l; Binding.coq_type = _UU03c3_ }
          Coq_ctx.Coq_nil)))) }
  | Coq_term_val (_UU03c3_, v) ->
    weakenInit h4 h5 (coq_SubstSUTerm h4 _UU03c3_) h4 h5 _UU03a3_
      (Coq_term_val (_UU03c3_, v))
  | Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1, t2) ->
    liftBinOp h4 h5 h4 h5 _UU03a3_ (coq_SubstSUTerm h4 _UU03c3_1)
      (coq_SubstSUTerm h4 _UU03c3_2) (coq_SubstSUTerm h4 _UU03c3_3)
      (fun _ x x0 -> Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, x,
      x0)) (gen_occurs_check_term h h0 h1 h2 h3 h4 h5 _UU03c3_1 _UU03a3_ t1)
      (gen_occurs_check_term h h0 h1 h2 h3 h4 h5 _UU03c3_2 _UU03a3_ t2)
  | Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t1) ->
    liftUnOp h4 _UU03a3_ (coq_SubstSUTerm h4 _UU03c3_1)
      (coq_SubstSUTerm h4 _UU03c3_2) (fun _ x -> Coq_term_unop (_UU03c3_1,
      _UU03c3_2, op, x))
      (gen_occurs_check_term h h0 h1 h2 h3 h4 h5 _UU03c3_1 _UU03a3_ t1)
  | Coq_term_tuple (_UU03c3_s, ts) ->
    liftUnOp h4 _UU03a3_ (coq_SubstSU_env h4 _UU03c3_s (coq_SubstSUTerm h4))
      (coq_SubstSUTerm h4 (Coq_ty.Coq_tuple _UU03c3_s)) (fun _ x ->
      Coq_term_tuple (_UU03c3_s, x))
      (gen_occurs_check_env h4 h5 h4 h5 (coq_SubstSUTerm h4)
        (gen_occurs_check_term h h0 h1 h2 h3 h4 h5) _UU03c3_s _UU03a3_ ts)
  | Coq_term_union (u, k, t1) ->
    liftUnOp h4 _UU03a3_
      (coq_SubstSUTerm h4 (typedefkit.Coq_ty.unionk_ty u k))
      (coq_SubstSUTerm h4 (Coq_ty.Coq_union u)) (fun _ x -> Coq_term_union
      (u, k, x))
      (gen_occurs_check_term h h0 h1 h2 h3 h4 h5
        (typedefkit.Coq_ty.unionk_ty u k) _UU03a3_ t1)
  | Coq_term_record (r, ts) ->
    liftUnOp h4 _UU03a3_
      (coq_SubstSU_env h4 (typedefkit.Coq_ty.recordf_ty r) (fun x ->
        coq_SubstSUTerm h4 x.Binding.coq_type))
      (coq_SubstSUTerm h4 (Coq_ty.Coq_record r)) (fun _ x -> Coq_term_record
      (r, x))
      (gen_occurs_check_env h4 h5 h4 h5 (fun x ->
        coq_SubstSUTerm h4 x.Binding.coq_type) (fun i ->
        gen_occurs_check_term h h0 h1 h2 h3 h4 h5 i.Binding.coq_type)
        (typedefkit.Coq_ty.recordf_ty r) _UU03a3_ ts)

  (** val gen_occurs_check_list :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
      coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2)
      coq_GenOccursCheck -> ('a1, 'a2 coq_List) coq_GenOccursCheck **)

  let rec gen_occurs_check_list h h0 h1 h2 sT ocT _UU03a3_ = function
  | Datatypes.Coq_nil ->
    weakenInit h1 h2 (substSU_list sT) h1 h2 _UU03a3_ Datatypes.Coq_nil
  | Datatypes.Coq_cons (l, ls0) ->
    liftBinOp h1 h2 h1 h2 _UU03a3_ sT (substSU_list sT) (substSU_list sT)
      (fun _ x x0 -> Datatypes.Coq_cons (x, x0))
      (gen_occurs_check h1 sT ocT _UU03a3_ l)
      (gen_occurs_check_list h h0 h1 h2 sT ocT _UU03a3_ ls0)

  (** val gen_occurs_check_pair :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
      coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU
      -> ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a3) coq_GenOccursCheck ->
      ('a1, ('a2, 'a3) coq_Pair) coq_GenOccursCheck **)

  let gen_occurs_check_pair _ _ h1 h2 x x0 x1 x2 _UU03a3_ = function
  | Coq_pair (a, b) ->
    liftBinOp h1 h2 h1 h2 _UU03a3_ x x0 (substSU_pair x x0) (fun _ x3 x4 ->
      Coq_pair (x3, x4)) (gen_occurs_check h1 x x1 _UU03a3_ a)
      (gen_occurs_check h1 x0 x2 _UU03a3_ b)

  (** val gen_occurs_check_option :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
      coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> 'a1
      coq_SubstUnivMeet -> ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a2
      coq_Option) coq_GenOccursCheck **)

  let gen_occurs_check_option _ _ _ _ h4 h5 h6 x _UU03a3_ = function
  | Some a ->
    liftUnOp h5 _UU03a3_ h4 (substSU_option h4) (fun _ x0 -> Some x0)
      (gen_occurs_check h5 h4 x _UU03a3_ a)
  | None -> weakenInit h5 h6 (substSU_option h4) h5 h6 _UU03a3_ None

  (** val substSU_ctx :
      ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 Coq_ctx.coq_Ctx) coq_SubstSU **)

  let rec substSU_ctx h _UU03a3_1 _UU03a3_2 ts _UU03b6_ =
    match ts with
    | Coq_ctx.Coq_nil -> Coq_ctx.Coq_nil
    | Coq_ctx.Coq_snoc (ts0, t0) ->
      Coq_ctx.Coq_snoc ((substSU_ctx h _UU03a3_1 _UU03a3_2 ts0 _UU03b6_),
        (substSU h _UU03a3_1 _UU03a3_2 t0 _UU03b6_))

  (** val gen_occurscheck_ctx :
      ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet ->
      ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a2 Coq_ctx.coq_Ctx)
      coq_GenOccursCheck **)

  let rec gen_occurscheck_ctx h h0 h1 ocA _UU03a3_ = function
  | Coq_ctx.Coq_nil ->
    weakenInit h0 h1 (substSU_ctx h) h0 h1 _UU03a3_ Coq_ctx.Coq_nil
  | Coq_ctx.Coq_snoc (ys0, y) ->
    liftBinOp h0 h1 h0 h1 _UU03a3_ (substSU_ctx h) h (substSU_ctx h)
      (fun _ x x0 -> Coq_ctx.Coq_snoc (x, x0))
      (gen_occurscheck_ctx h h0 h1 ocA _UU03a3_ ys0) (ocA _UU03a3_ y)

  (** val gen_occurs_check_unit :
      'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
      coq_SubstUnivMeet -> ('a1, coq_Unit) coq_GenOccursCheck **)

  let gen_occurs_check_unit _ _ h1 h2 _UU03a3_ _ =
    weakenInit h1 h2 substSU_Const h1 h2 _UU03a3_ Coq_tt

  type coq_WeakensTo =
  | WkNil
  | WkSkipVar of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
  | WkKeepVar of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo

  (** val coq_WeakensTo_rect :
      'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1
      -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      coq_WeakensTo -> 'a1 -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1 **)

  let rec coq_WeakensTo_rect f f0 f1 _ _ = function
  | WkNil -> f
  | WkSkipVar (_UU03a3_1, _UU03a3_2, x, w0) ->
    f0 _UU03a3_1 _UU03a3_2 x w0
      (coq_WeakensTo_rect f f0 f1 _UU03a3_1 _UU03a3_2 w0)
  | WkKeepVar (_UU03a3_1, _UU03a3_2, x, w0) ->
    f1 _UU03a3_1 _UU03a3_2 x w0
      (coq_WeakensTo_rect f f0 f1 _UU03a3_1 _UU03a3_2 w0)

  (** val coq_WeakensTo_rec :
      'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1
      -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      coq_WeakensTo -> 'a1 -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1 **)

  let rec coq_WeakensTo_rec f f0 f1 _ _ = function
  | WkNil -> f
  | WkSkipVar (_UU03a3_1, _UU03a3_2, x, w0) ->
    f0 _UU03a3_1 _UU03a3_2 x w0
      (coq_WeakensTo_rec f f0 f1 _UU03a3_1 _UU03a3_2 w0)
  | WkKeepVar (_UU03a3_1, _UU03a3_2, x, w0) ->
    f1 _UU03a3_1 _UU03a3_2 x w0
      (coq_WeakensTo_rec f f0 f1 _UU03a3_1 _UU03a3_2 w0)

  (** val wkRefl :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo **)

  let rec wkRefl = function
  | Coq_ctx.Coq_nil -> WkNil
  | Coq_ctx.Coq_snoc (_UU03a3_0, x) ->
    WkKeepVar (_UU03a3_0, _UU03a3_0, x, (wkRefl _UU03a3_0))

  (** val wk1 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo **)

  let wk1 _UU03a3_ b =
    WkSkipVar (_UU03a3_, _UU03a3_, b, (wkRefl _UU03a3_))

  (** val interpWk :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_Sub **)

  let rec interpWk _ _ = function
  | WkNil -> Coq_env.Coq_nil
  | WkSkipVar (_UU03a3_0, _UU03a3_3, x, wk0) ->
    subst
      (coq_SubstEnv (fun b -> coq_SubstTerm b.Binding.coq_type) _UU03a3_0)
      _UU03a3_3 (interpWk _UU03a3_0 _UU03a3_3 wk0) (Coq_ctx.Coq_snoc
      (_UU03a3_3, x)) (sub_wk1 _UU03a3_3 x)
  | WkKeepVar (_UU03a3_0, _UU03a3_3, x, wk0) ->
    sub_up1 _UU03a3_0 _UU03a3_3 (interpWk _UU03a3_0 _UU03a3_3 wk0) x

  (** val transWk :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo **)

  let rec transWk _UU03a3_1 _ _ wk12 = function
  | WkNil ->
    (match wk12 with
     | WkNil -> WkNil
     | _ -> assert false (* absurd case *))
  | WkSkipVar (_UU03a3_2, _UU03a3_3, x, w) ->
    WkSkipVar (_UU03a3_1, _UU03a3_3, x,
      (transWk _UU03a3_1 _UU03a3_2 _UU03a3_3 wk12 w))
  | WkKeepVar (_, _UU03a3_2, _, w) ->
    (match wk12 with
     | WkNil -> assert false (* absurd case *)
     | WkSkipVar (_UU03a3_3, _UU03a3_4, x, w0) ->
       WkSkipVar (_UU03a3_3, _UU03a3_2, x,
         (transWk _UU03a3_3 _UU03a3_4 _UU03a3_2 w0 w))
     | WkKeepVar (_UU03a3_3, _UU03a3_4, x, w0) ->
       WkKeepVar (_UU03a3_3, _UU03a3_2, x,
         (transWk _UU03a3_3 _UU03a3_4 _UU03a3_2 w0 w)))

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

  (** val transWk_graph_rect :
      'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
      coq_WeakensTo -> transWk_graph -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo
      -> transWk_graph -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> transWk_graph ->
      'a1 -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo ->
      transWk_graph -> 'a1 **)

  let rec transWk_graph_rect f f0 f1 f2 _ _ _ _ _ _ = function
  | Coq_transWk_graph_equation_1 -> f
  | Coq_transWk_graph_equation_2 (_UU03a3_1, _UU03a3_2, _UU03a3_5, x, wk2,
                                  wk3, hind) ->
    f0 _UU03a3_1 _UU03a3_2 _UU03a3_5 x wk2 wk3 hind
      (transWk_graph_rect f f0 f1 f2 _UU03a3_1 _UU03a3_2 _UU03a3_5 wk2 wk3
        (transWk _UU03a3_1 _UU03a3_2 _UU03a3_5 wk2 wk3) hind)
  | Coq_transWk_graph_equation_3 (_UU03a3_1, _UU03a3_3, x, _UU03a3_7, wk2,
                                  wk3, hind) ->
    f1 _UU03a3_1 _UU03a3_3 x _UU03a3_7 wk2 wk3 hind
      (transWk_graph_rect f f0 f1 f2 _UU03a3_1 _UU03a3_3 _UU03a3_7 wk2 wk3
        (transWk _UU03a3_1 _UU03a3_3 _UU03a3_7 wk2 wk3) hind)
  | Coq_transWk_graph_equation_4 (_UU03a3_4, x, _UU03a3_5, _UU03a3_7, wk2,
                                  wk3, hind) ->
    f2 _UU03a3_4 x _UU03a3_5 _UU03a3_7 wk2 wk3 hind
      (transWk_graph_rect f f0 f1 f2 _UU03a3_4 _UU03a3_5 _UU03a3_7 wk2 wk3
        (transWk _UU03a3_4 _UU03a3_5 _UU03a3_7 wk2 wk3) hind)

  (** val transWk_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakensTo -> transWk_graph **)

  let rec transWk_graph_correct _UU03a3_1 _ _ wk12 = function
  | WkNil ->
    (match wk12 with
     | WkNil -> Coq_transWk_graph_equation_1
     | _ -> assert false (* absurd case *))
  | WkSkipVar (_UU03a3_2, _UU03a3_3, x, w) ->
    Coq_transWk_graph_equation_2 (_UU03a3_1, _UU03a3_2, _UU03a3_3, x, wk12,
      w, (transWk_graph_correct _UU03a3_1 _UU03a3_2 _UU03a3_3 wk12 w))
  | WkKeepVar (_, _UU03a3_2, _, w) ->
    (match wk12 with
     | WkNil -> assert false (* absurd case *)
     | WkSkipVar (_UU03a3_3, _UU03a3_4, x, w0) ->
       Coq_transWk_graph_equation_3 (_UU03a3_3, _UU03a3_4, x, _UU03a3_2, w0,
         w, (transWk_graph_correct _UU03a3_3 _UU03a3_4 _UU03a3_2 w0 w))
     | WkKeepVar (_UU03a3_3, _UU03a3_4, x, w0) ->
       Coq_transWk_graph_equation_4 (_UU03a3_3, x, _UU03a3_4, _UU03a3_2, w0,
         w, (transWk_graph_correct _UU03a3_3 _UU03a3_4 _UU03a3_2 w0 w)))

  (** val transWk_elim :
      'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
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
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo
      -> 'a1 **)

  let transWk_elim f f0 f1 f2 _UU03a3_1 _UU03a3_2 _UU03a3_3 wk12 wk23 =
    let rec f3 _ _ _ _ _ _ = function
    | Coq_transWk_graph_equation_1 -> f
    | Coq_transWk_graph_equation_2 (_UU03a3_4, _UU03a3_5, _UU03a3_6, x, wk2,
                                    wk3, hind) ->
      f0 _UU03a3_4 _UU03a3_5 _UU03a3_6 x wk2 wk3
        (f3 _UU03a3_4 _UU03a3_5 _UU03a3_6 wk2 wk3
          (transWk _UU03a3_4 _UU03a3_5 _UU03a3_6 wk2 wk3) hind)
    | Coq_transWk_graph_equation_3 (_UU03a3_4, _UU03a3_5, x, _UU03a3_7, wk2,
                                    wk3, hind) ->
      f1 _UU03a3_4 _UU03a3_5 x _UU03a3_7 wk2 wk3
        (f3 _UU03a3_4 _UU03a3_5 _UU03a3_7 wk2 wk3
          (transWk _UU03a3_4 _UU03a3_5 _UU03a3_7 wk2 wk3) hind)
    | Coq_transWk_graph_equation_4 (_UU03a3_4, x, _UU03a3_5, _UU03a3_7, wk2,
                                    wk3, hind) ->
      f2 _UU03a3_4 x _UU03a3_5 _UU03a3_7 wk2 wk3
        (f3 _UU03a3_4 _UU03a3_5 _UU03a3_7 wk2 wk3
          (transWk _UU03a3_4 _UU03a3_5 _UU03a3_7 wk2 wk3) hind)
    in f3 _UU03a3_1 _UU03a3_2 _UU03a3_3 wk12 wk23
         (transWk _UU03a3_1 _UU03a3_2 _UU03a3_3 wk12 wk23)
         (transWk_graph_correct _UU03a3_1 _UU03a3_2 _UU03a3_3 wk12 wk23)

  (** val coq_FunctionalElimination_transWk :
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
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo
      -> __ **)

  let coq_FunctionalElimination_transWk =
    transWk_elim

  (** val coq_FunctionalInduction_transWk :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo) coq_FunctionalInduction **)

  let coq_FunctionalInduction_transWk =
    Obj.magic transWk_graph_correct

  (** val wkNilInit :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo **)

  let rec wkNilInit = function
  | Coq_ctx.Coq_nil -> WkNil
  | Coq_ctx.Coq_snoc (_UU03a3_0, x) ->
    WkSkipVar (Coq_ctx.Coq_nil, _UU03a3_0, x, (wkNilInit _UU03a3_0))

  (** val wkKeepCtx :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_WeakensTo **)

  let rec wkKeepCtx _UU03a3_1 _UU03a3_2 _UU03b6_ = function
  | Coq_ctx.Coq_nil -> _UU03b6_
  | Coq_ctx.Coq_snoc (_UU0394_', x) ->
    WkKeepVar ((Coq_ctx.cat _UU03a3_1 _UU0394_'),
      (Coq_ctx.cat _UU03a3_2 _UU0394_'), x,
      (wkKeepCtx _UU03a3_1 _UU03a3_2 _UU03b6_ _UU0394_'))

  type coq_WeakenZeroView =
  | VarUnused of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo
  | VarUsed of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo

  (** val coq_WeakenZeroView_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> coq_WeakensTo -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      coq_WeakenZeroView -> 'a1 **)

  let coq_WeakenZeroView_rect _ _ f f0 _ _ = function
  | VarUnused (_UU03a3_1, wk) -> f _UU03a3_1 wk
  | VarUsed (_UU03a3_1, wk) -> f0 _UU03a3_1 wk

  (** val coq_WeakenZeroView_rec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> coq_WeakensTo -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      coq_WeakenZeroView -> 'a1 **)

  let coq_WeakenZeroView_rec _ _ f f0 _ _ = function
  | VarUnused (_UU03a3_1, wk) -> f _UU03a3_1 wk
  | VarUsed (_UU03a3_1, wk) -> f0 _UU03a3_1 wk

  (** val weakenZeroView :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
      coq_WeakenZeroView **)

  let weakenZeroView _ _ _ = function
  | WkNil -> assert false (* absurd case *)
  | WkSkipVar (_UU03a3_1, _, _, w) -> VarUnused (_UU03a3_1, w)
  | WkKeepVar (_UU03a3_1, _, _, w) -> VarUsed (_UU03a3_1, w)

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

  (** val weakenZeroView_graph_rect :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1)
      -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
      coq_WeakenZeroView -> weakenZeroView_graph -> 'a1 **)

  let weakenZeroView_graph_rect f f0 _ _ _ _ _ = function
  | Coq_weakenZeroView_graph_equation_1 (_UU03a3_1, _UU03a3_2, b, wk) ->
    f _UU03a3_1 _UU03a3_2 b wk
  | Coq_weakenZeroView_graph_equation_2 (_UU03a3_5, b, _UU03a3_2, wk) ->
    f0 _UU03a3_5 b _UU03a3_2 wk

  (** val weakenZeroView_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
      weakenZeroView_graph **)

  let weakenZeroView_graph_correct _ _ _ = function
  | WkNil -> assert false (* absurd case *)
  | WkSkipVar (_UU03a3_1, _UU03a3_2, x, w) ->
    Coq_weakenZeroView_graph_equation_1 (_UU03a3_1, _UU03a3_2, x, w)
  | WkKeepVar (_UU03a3_1, _UU03a3_2, x, w) ->
    Coq_weakenZeroView_graph_equation_2 (_UU03a3_1, x, _UU03a3_2, w)

  (** val weakenZeroView_elim :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1)
      -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 **)

  let weakenZeroView_elim f f0 _UU03a3_1 _UU03a3_2 b wk =
    match weakenZeroView_graph_correct _UU03a3_1 _UU03a3_2 b wk with
    | Coq_weakenZeroView_graph_equation_1 (_UU03a3_3, _UU03a3_4, b0, wk0) ->
      f _UU03a3_3 _UU03a3_4 b0 wk0
    | Coq_weakenZeroView_graph_equation_2 (_UU03a3_5, b0, _UU03a3_3, wk0) ->
      f0 _UU03a3_5 b0 _UU03a3_3 wk0

  (** val coq_FunctionalElimination_weakenZeroView :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __)
      -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      __) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __ **)

  let coq_FunctionalElimination_weakenZeroView =
    weakenZeroView_elim

  (** val coq_FunctionalInduction_weakenZeroView :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
      coq_WeakenZeroView) coq_FunctionalInduction **)

  let coq_FunctionalInduction_weakenZeroView =
    Obj.magic weakenZeroView_graph_correct

  type coq_WeakenNilView =
  | WkNilViewNil

  (** val coq_WeakenNilView_rect :
      'a1 -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakenNilView -> 'a1 **)

  let coq_WeakenNilView_rect f _ _ _ =
    f

  (** val coq_WeakenNilView_rec :
      'a1 -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakenNilView -> 'a1 **)

  let coq_WeakenNilView_rec f _ _ _ =
    f

  (** val weakenNilView :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakenNilView **)

  let weakenNilView _ = function
  | WkNil -> WkNilViewNil
  | _ -> assert false (* absurd case *)

  type weakenNilView_graph =
  | Coq_weakenNilView_graph_equation_1

  (** val weakenNilView_graph_rect :
      'a1 -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakenNilView -> weakenNilView_graph -> 'a1 **)

  let weakenNilView_graph_rect f _ _ _ _ =
    f

  (** val weakenNilView_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> weakenNilView_graph **)

  let weakenNilView_graph_correct _ = function
  | WkNil -> Coq_weakenNilView_graph_equation_1
  | _ -> assert false (* absurd case *)

  (** val weakenNilView_elim :
      'a1 -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> 'a1 **)

  let weakenNilView_elim f _ _ =
    f

  (** val coq_FunctionalElimination_weakenNilView :
      __ -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> __ **)

  let coq_FunctionalElimination_weakenNilView =
    weakenNilView_elim

  (** val coq_FunctionalInduction_weakenNilView :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakenNilView) coq_FunctionalInduction **)

  let coq_FunctionalInduction_weakenNilView =
    Obj.magic weakenNilView_graph_correct

  (** val wkRemove :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo **)

  let rec wkRemove _UU03a3_ b bIn =
    Coq_ctx.coq_In_case (fun b0 _UU03a3_0 -> WkSkipVar
      ((Coq_ctx.remove (Coq_ctx.Coq_snoc (_UU03a3_0, b0)) b0
         (Coq_ctx.in_zero b0 _UU03a3_0)),
      (Coq_ctx.remove (Coq_ctx.Coq_snoc (_UU03a3_0, b0)) b0
        (Coq_ctx.in_zero b0 _UU03a3_0)),
      b0,
      (wkRefl
        (Coq_ctx.remove (Coq_ctx.Coq_snoc (_UU03a3_0, b0)) b0
          (Coq_ctx.in_zero b0 _UU03a3_0)))))
      (fun b' _UU03a3_0 b0 bIn0 -> WkKeepVar
      ((Coq_ctx.remove _UU03a3_0 b0 bIn0), _UU03a3_0, b',
      (wkRemove _UU03a3_0 b0 bIn0))) b _UU03a3_ bIn

  (** val wkSingleton :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo **)

  let rec wkSingleton _UU03a3_ b bIn =
    Coq_ctx.coq_In_case (fun b0 _UU03a3_0 -> WkKeepVar (Coq_ctx.Coq_nil,
      _UU03a3_0, b0, (wkNilInit _UU03a3_0))) (fun b' _UU03a3_0 b0 bIn0 ->
      WkSkipVar ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, b0)), _UU03a3_0, b',
      (wkSingleton _UU03a3_0 b0 bIn0))) b _UU03a3_ bIn

  (** val wkVarZeroIn :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In **)

  let rec wkVarZeroIn _ _UU03a3_' b = function
  | WkNil -> assert false (* absurd case *)
  | WkSkipVar (_, _UU03a3_2, x, w) ->
    Coq_ctx.in_succ b _UU03a3_2 x (wkVarZeroIn _UU03a3_2 _UU03a3_' b w)
  | WkKeepVar (_, _UU03a3_2, x, _) -> Coq_ctx.in_zero x _UU03a3_2

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

  (** val wkVarZeroIn_graph_rect :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
      wkVarZeroIn_graph -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> wkVarZeroIn_graph -> 'a1 **)

  let rec wkVarZeroIn_graph_rect f f0 _ _ _ _ _ = function
  | Coq_wkVarZeroIn_graph_equation_1 (_UU03a3_2, x, _UU03a3_', b, wk, hind) ->
    f _UU03a3_2 x _UU03a3_' b wk hind
      (wkVarZeroIn_graph_rect f f0 _UU03a3_2 _UU03a3_' b wk
        (wkVarZeroIn _UU03a3_2 _UU03a3_' b wk) hind)
  | Coq_wkVarZeroIn_graph_equation_2 (b, _UU03a3_4, _UU03a3_', w0) ->
    f0 b _UU03a3_4 _UU03a3_' w0

  (** val wkVarZeroIn_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
      wkVarZeroIn_graph **)

  let rec wkVarZeroIn_graph_correct _ _UU03a3_' b = function
  | WkNil -> assert false (* absurd case *)
  | WkSkipVar (_, _UU03a3_2, x, w) ->
    Coq_wkVarZeroIn_graph_equation_1 (_UU03a3_2, x, _UU03a3_', b, w,
      (wkVarZeroIn_graph_correct _UU03a3_2 _UU03a3_' b w))
  | WkKeepVar (_UU03a3_1, _UU03a3_2, x, w) ->
    Coq_wkVarZeroIn_graph_equation_2 (x, _UU03a3_2, _UU03a3_1, w)

  (** val wkVarZeroIn_elim :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 **)

  let wkVarZeroIn_elim f f0 _UU03a3_ _UU03a3_' b _UU03c3_ =
    let rec f1 _ _ _ _ _ = function
    | Coq_wkVarZeroIn_graph_equation_1 (_UU03a3_2, x, _UU03a3_'0, b0, wk, hind) ->
      f _UU03a3_2 x _UU03a3_'0 b0 wk
        (f1 _UU03a3_2 _UU03a3_'0 b0 wk
          (wkVarZeroIn _UU03a3_2 _UU03a3_'0 b0 wk) hind)
    | Coq_wkVarZeroIn_graph_equation_2 (b0, _UU03a3_4, _UU03a3_'0, w0) ->
      f0 b0 _UU03a3_4 _UU03a3_'0 w0
    in f1 _UU03a3_ _UU03a3_' b _UU03c3_
         (wkVarZeroIn _UU03a3_ _UU03a3_' b _UU03c3_)
         (wkVarZeroIn_graph_correct _UU03a3_ _UU03a3_' b _UU03c3_)

  (** val coq_FunctionalElimination_wkVarZeroIn :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __ -> __) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      __) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __ **)

  let coq_FunctionalElimination_wkVarZeroIn =
    wkVarZeroIn_elim

  (** val coq_FunctionalInduction_wkVarZeroIn :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In)
      coq_FunctionalInduction **)

  let coq_FunctionalInduction_wkVarZeroIn =
    Obj.magic wkVarZeroIn_graph_correct

  (** val weakenIn :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In **)

  let rec weakenIn _ _ _UU03c3_ b bIn =
    match _UU03c3_ with
    | WkNil -> assert false (* absurd case *)
    | WkSkipVar (_UU03a3_0, _UU03a3_3, x, _UU03c3_') ->
      Coq_ctx.in_succ b _UU03a3_3 x
        (weakenIn _UU03a3_0 _UU03a3_3 _UU03c3_' b bIn)
    | WkKeepVar (_UU03a3_0, _UU03a3_3, x, _UU03c3_') ->
      (match Obj.magic Coq_ctx.view b (Coq_ctx.Coq_snoc (_UU03a3_0, x)) bIn with
       | Coq_ctx.Coq_isZero -> Coq_ctx.in_zero x _UU03a3_3
       | Coq_ctx.Coq_isSucc (b0, bIn') ->
         Coq_ctx.in_succ b0 _UU03a3_3 x
           (weakenIn _UU03a3_0 _UU03a3_3 _UU03c3_' b0 bIn'))

  (** val weakenRemovePres :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      coq_WeakensTo **)

  let rec weakenRemovePres _ _ w b bIn =
    match w with
    | WkNil -> assert false (* absurd case *)
    | WkSkipVar (_UU03a3_1, _UU03a3_2, x, w0) ->
      WkSkipVar ((Coq_ctx.remove _UU03a3_1 b bIn),
        (let rec remove0 _UU0393_ b0 bIn0 =
           Coq_ctx.coq_In_case (fun _ _UU0393_0 -> _UU0393_0)
             (fun b' _UU0393_0 b1 bIn1 -> Coq_ctx.Coq_snoc
             ((remove0 _UU0393_0 b1 bIn1), b')) b0 _UU0393_ bIn0
         in remove0 _UU03a3_2 b
              (let rec weakenIn0 _ _ _UU03c3_ b0 bIn0 =
                 match _UU03c3_ with
                 | WkNil -> assert false (* absurd case *)
                 | WkSkipVar (_UU03a3_0, _UU03a3_3, x0, _UU03c3_') ->
                   Coq_ctx.in_succ b0 _UU03a3_3 x0
                     (weakenIn0 _UU03a3_0 _UU03a3_3 _UU03c3_' b0 bIn0)
                 | WkKeepVar (_UU03a3_0, _UU03a3_3, x0, _UU03c3_') ->
                   (match Obj.magic Coq_ctx.view b0 (Coq_ctx.Coq_snoc
                            (_UU03a3_0, x0)) bIn0 with
                    | Coq_ctx.Coq_isZero -> Coq_ctx.in_zero x0 _UU03a3_3
                    | Coq_ctx.Coq_isSucc (b1, bIn') ->
                      Coq_ctx.in_succ b1 _UU03a3_3 x0
                        (weakenIn0 _UU03a3_0 _UU03a3_3 _UU03c3_' b1 bIn'))
               in weakenIn0 _UU03a3_1 _UU03a3_2 w0 b bIn)),
        x, (weakenRemovePres _UU03a3_1 _UU03a3_2 w0 b bIn))
    | WkKeepVar (_UU03a3_1, _UU03a3_2, x, w0) ->
      let y = Coq_ctx.view b (Coq_ctx.Coq_snoc (_UU03a3_1, x)) bIn in
      (match Obj.magic y with
       | Coq_ctx.Coq_isZero -> w0
       | Coq_ctx.Coq_isSucc (b0, i) ->
         WkKeepVar
           ((let rec remove0 _UU0393_ b1 bIn0 =
               Coq_ctx.coq_In_case (fun _ _UU0393_0 -> _UU0393_0)
                 (fun b' _UU0393_0 b2 bIn1 -> Coq_ctx.Coq_snoc
                 ((remove0 _UU0393_0 b2 bIn1), b')) b1 _UU0393_ bIn0
             in remove0 _UU03a3_1 b0 i),
           (let rec remove0 _UU0393_ b1 bIn0 =
              Coq_ctx.coq_In_case (fun _ _UU0393_0 -> _UU0393_0)
                (fun b' _UU0393_0 b2 bIn1 -> Coq_ctx.Coq_snoc
                ((remove0 _UU0393_0 b2 bIn1), b')) b1 _UU0393_ bIn0
            in remove0 _UU03a3_2 b0
                 (let rec weakenIn0 _ _ _UU03c3_ b1 bIn0 =
                    match _UU03c3_ with
                    | WkNil -> assert false (* absurd case *)
                    | WkSkipVar (_UU03a3_0, _UU03a3_3, x0, _UU03c3_') ->
                      Coq_ctx.in_succ b1 _UU03a3_3 x0
                        (weakenIn0 _UU03a3_0 _UU03a3_3 _UU03c3_' b1 bIn0)
                    | WkKeepVar (_UU03a3_0, _UU03a3_3, x0, _UU03c3_') ->
                      (match Obj.magic Coq_ctx.view b1 (Coq_ctx.Coq_snoc
                               (_UU03a3_0, x0)) bIn0 with
                       | Coq_ctx.Coq_isZero -> Coq_ctx.in_zero x0 _UU03a3_3
                       | Coq_ctx.Coq_isSucc (b2, bIn') ->
                         Coq_ctx.in_succ b2 _UU03a3_3 x0
                           (weakenIn0 _UU03a3_0 _UU03a3_3 _UU03c3_' b2 bIn'))
                  in weakenIn0 _UU03a3_1 _UU03a3_2 w0 b0 i)),
           x, (weakenRemovePres _UU03a3_1 _UU03a3_2 w0 b0 i)))

  type coq_WeakenRemoveView =
  | MkWeakenRemoveView of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo

  (** val coq_WeakenRemoveView_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
      'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      coq_WeakensTo -> coq_WeakenRemoveView -> 'a1 **)

  let coq_WeakenRemoveView_rect _ _ f _ _ _ = function
  | MkWeakenRemoveView (_UU03a3_1', bIn', _UU03c3_1') ->
    f _UU03a3_1' bIn' _UU03c3_1'

  (** val coq_WeakenRemoveView_rec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
      'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      coq_WeakensTo -> coq_WeakenRemoveView -> 'a1 **)

  let coq_WeakenRemoveView_rec _ _ f _ _ _ = function
  | MkWeakenRemoveView (_UU03a3_1', bIn', _UU03c3_1') ->
    f _UU03a3_1' bIn' _UU03c3_1'

  (** val weakenRemoveView :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      coq_WeakenRemoveView **)

  let rec weakenRemoveView b _UU0393_ bIn =
    Coq_ctx.coq_In_case (fun b0 _UU03a3_ _UU03a3_' _UU03c3_ ->
      MkWeakenRemoveView ((Coq_ctx.Coq_snoc (_UU03a3_', b0)),
      (Coq_ctx.in_zero b0 _UU03a3_'), (WkKeepVar (_UU03a3_',
      (Coq_ctx.remove (Coq_ctx.Coq_snoc (_UU03a3_, b0)) b0
        (Coq_ctx.in_zero b0 _UU03a3_)),
      b0, _UU03c3_)))) (fun b' _UU0393_0 b0 bIn0 _UU03a3_1 _UU03c3_ ->
      match weakenZeroView _UU03a3_1
              (let rec remove0 _UU0393_1 b1 bIn1 =
                 Coq_ctx.coq_In_case (fun _ _UU0393_2 -> _UU0393_2)
                   (fun b'0 _UU0393_2 b2 bIn2 -> Coq_ctx.Coq_snoc
                   ((remove0 _UU0393_2 b2 bIn2), b'0)) b1 _UU0393_1 bIn1
               in remove0 _UU0393_0 b0 bIn0)
              b' _UU03c3_ with
      | VarUnused (_UU03a3_0, _UU03c3_') ->
        let MkWeakenRemoveView (_UU03a3_1', bIn', _UU03c3_1') =
          weakenRemoveView b0 _UU0393_0 bIn0 _UU03a3_0 _UU03c3_'
        in
        MkWeakenRemoveView (_UU03a3_1', bIn', (WkSkipVar (_UU03a3_1',
        _UU0393_0, b', _UU03c3_1')))
      | VarUsed (_UU03a3_0, _UU03c3_') ->
        let MkWeakenRemoveView (_UU03a3_1', bIn', _UU03c3_1') =
          weakenRemoveView b0 _UU0393_0 bIn0 _UU03a3_0 _UU03c3_'
        in
        MkWeakenRemoveView ((Coq_ctx.Coq_snoc (_UU03a3_1', b')),
        (Coq_ctx.in_succ b0 _UU03a3_1' b' bIn'), (WkKeepVar (_UU03a3_1',
        _UU0393_0, b', _UU03c3_1'))))
      b _UU0393_ bIn

  type coq_WeakenVarView =
  | WeakenVarUnused of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                       Coq_ctx.coq_Ctx
     * coq_WeakensTo
  | WeakenVarUsed of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
                     Coq_ctx.coq_Ctx
     * (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo

  (** val coq_WeakenVarView_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      coq_WeakensTo -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakenVarView -> 'a1 **)

  let coq_WeakenVarView_rect _ _ _ f f0 _ _ = function
  | WeakenVarUnused (_UU03a3_1, wk) -> f _UU03a3_1 wk
  | WeakenVarUsed (_UU03a3_1, bIn', wk) -> f0 _UU03a3_1 bIn' wk

  (** val coq_WeakenVarView_rec :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
      'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      coq_WeakensTo -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakenVarView -> 'a1 **)

  let coq_WeakenVarView_rec _ _ _ f f0 _ _ = function
  | WeakenVarUnused (_UU03a3_1, wk) -> f _UU03a3_1 wk
  | WeakenVarUsed (_UU03a3_1, bIn', wk) -> f0 _UU03a3_1 bIn' wk

  (** val weakenVarView_obligations_obligation_1 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
      coq_WeakenVarView **)

  let weakenVarView_obligations_obligation_1 _UU03a3_1 _ _ wk =
    WeakenVarUnused (_UU03a3_1, wk)

  (** val weakenVarView_obligations_obligation_2 :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
      coq_WeakenVarView) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      coq_WeakenVarView **)

  let weakenVarView_obligations_obligation_2 weakenVarView0 _UU03a3_1 _UU03a3_4 x wk b0 bIn2' =
    let hind = weakenVarView0 _UU03a3_1 _UU03a3_4 b0 bIn2' wk in
    (match hind with
     | WeakenVarUnused (_UU03a3_2, wk0) ->
       WeakenVarUnused (_UU03a3_2, (WkSkipVar (_UU03a3_2,
         (Coq_ctx.remove _UU03a3_4 b0 bIn2'), x, wk0)))
     | WeakenVarUsed (_UU03a3_2, bIn', wk0) ->
       WeakenVarUsed (_UU03a3_2, bIn', (WkSkipVar (_UU03a3_2, _UU03a3_4, x,
         wk0))))

  (** val weakenVarView_obligations_obligation_3 :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
      coq_WeakenVarView) -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      coq_WeakenVarView **)

  let weakenVarView_obligations_obligation_3 weakenVarView0 _UU03a3_5 x0 _UU03a3_6 wk b0 bIn2' =
    let hind = weakenVarView0 _UU03a3_5 _UU03a3_6 b0 bIn2' wk in
    (match hind with
     | WeakenVarUnused (_UU03a3_1, wk0) ->
       WeakenVarUnused ((Coq_ctx.Coq_snoc (_UU03a3_1, x0)), (WkKeepVar
         (_UU03a3_1, (Coq_ctx.remove _UU03a3_6 b0 bIn2'), x0, wk0)))
     | WeakenVarUsed (_UU03a3_1, bIn', wk0) ->
       WeakenVarUsed ((Coq_ctx.Coq_snoc (_UU03a3_1, x0)),
         (Coq_ctx.in_succ b0 _UU03a3_1 x0 bIn'), (WkKeepVar (_UU03a3_1,
         _UU03a3_6, x0, wk0))))

  (** val weakenVarView :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
      coq_WeakenVarView **)

  let rec weakenVarView _ _ b bIn2 = function
  | WkNil -> assert false (* absurd case *)
  | WkSkipVar (_UU03a3_1, _UU03a3_2, x, w) ->
    (match Obj.magic Coq_ctx.view b (Coq_ctx.Coq_snoc (_UU03a3_2, x)) bIn2 with
     | Coq_ctx.Coq_isZero ->
       weakenVarView_obligations_obligation_1 _UU03a3_1 _UU03a3_2 x w
     | Coq_ctx.Coq_isSucc (b0, bIn2') ->
       weakenVarView_obligations_obligation_2 weakenVarView _UU03a3_1
         _UU03a3_2 x w b0 bIn2')
  | WkKeepVar (_UU03a3_1, _UU03a3_2, x, w) ->
    (match Obj.magic Coq_ctx.view b (Coq_ctx.Coq_snoc (_UU03a3_2, x)) bIn2 with
     | Coq_ctx.Coq_isZero ->
       WeakenVarUsed ((Coq_ctx.Coq_snoc (_UU03a3_1, x)),
         (Coq_ctx.in_zero x _UU03a3_1), (WkKeepVar (_UU03a3_1, _UU03a3_2, x,
         w)))
     | Coq_ctx.Coq_isSucc (b0, bIn2') ->
       weakenVarView_obligations_obligation_3 weakenVarView _UU03a3_1 x
         _UU03a3_2 w b0 bIn2')

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

  (** val weakenVarView_graph_rect :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> weakenVarView_graph) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> weakenVarView_graph) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> 'a1) ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
      coq_WeakenVarView -> weakenVarView_graph -> 'a1 **)

  let rec weakenVarView_graph_rect f f0 f1 _ _ _ _ _ _ = function
  | Coq_weakenVarView_graph_equation_1 (b, bIn2) -> f b bIn2
  | Coq_weakenVarView_graph_equation_2 (_UU03a3_1, _UU03a3_4, x, b, bIn2, wk,
                                        hind) ->
    f0 _UU03a3_1 _UU03a3_4 x b bIn2 wk hind (fun b0 bIn2' ->
      weakenVarView_graph_rect f f0 f1 _UU03a3_1 _UU03a3_4 b0 bIn2' wk
        (weakenVarView _UU03a3_1 _UU03a3_4 b0 bIn2' wk) (hind b0 bIn2'))
  | Coq_weakenVarView_graph_equation_3 (_UU03a3_5, x0, _UU03a3_6, b, bIn2,
                                        wk, hind) ->
    f1 _UU03a3_5 x0 _UU03a3_6 b bIn2 wk hind (fun b0 bIn2' ->
      weakenVarView_graph_rect f f0 f1 _UU03a3_5 _UU03a3_6 b0 bIn2' wk
        (weakenVarView _UU03a3_5 _UU03a3_6 b0 bIn2' wk) (hind b0 bIn2'))

  (** val weakenVarView_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
      weakenVarView_graph **)

  let rec weakenVarView_graph_correct _ _ b bIn2 = function
  | WkNil -> Coq_weakenVarView_graph_equation_1 (b, bIn2)
  | WkSkipVar (_UU03a3_1, _UU03a3_2, x, w) ->
    Coq_weakenVarView_graph_equation_2 (_UU03a3_1, _UU03a3_2, x, b, bIn2, w,
      (fun b0 bIn2' ->
      weakenVarView_graph_correct _UU03a3_1 _UU03a3_2 b0 bIn2' w))
  | WkKeepVar (_UU03a3_1, _UU03a3_2, x, w) ->
    Coq_weakenVarView_graph_equation_3 (_UU03a3_1, x, _UU03a3_2, b, bIn2, w,
      (fun b0 bIn2' ->
      weakenVarView_graph_correct _UU03a3_1 _UU03a3_2 b0 bIn2' w))

  (** val weakenVarView_elim :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_WeakensTo -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> 'a1) -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_WeakensTo -> 'a1 **)

  let weakenVarView_elim f f0 f1 _UU03a3_1 _UU03a3_2 b bIn2 wk =
    let rec f2 _ _ _ _ _ _ = function
    | Coq_weakenVarView_graph_equation_1 (b0, bIn3) -> f b0 bIn3
    | Coq_weakenVarView_graph_equation_2 (_UU03a3_3, _UU03a3_4, x, b0, bIn3,
                                          wk0, hind) ->
      f0 _UU03a3_3 _UU03a3_4 x b0 bIn3 wk0 (fun b1 bIn2' ->
        f2 _UU03a3_3 _UU03a3_4 b1 bIn2' wk0
          (weakenVarView _UU03a3_3 _UU03a3_4 b1 bIn2' wk0) (hind b1 bIn2'))
    | Coq_weakenVarView_graph_equation_3 (_UU03a3_5, x0, _UU03a3_6, b0, bIn3,
                                          wk0, hind) ->
      f1 _UU03a3_5 x0 _UU03a3_6 b0 bIn3 wk0 (fun b1 bIn2' ->
        f2 _UU03a3_5 _UU03a3_6 b1 bIn2' wk0
          (weakenVarView _UU03a3_5 _UU03a3_6 b1 bIn2' wk0) (hind b1 bIn2'))
    in f2 _UU03a3_1 _UU03a3_2 b bIn2 wk
         (weakenVarView _UU03a3_1 _UU03a3_2 b bIn2 wk)
         (weakenVarView_graph_correct _UU03a3_1 _UU03a3_2 b bIn2 wk)

  (** val coq_FunctionalElimination_weakenVarView :
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
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> __ **)

  let coq_FunctionalElimination_weakenVarView =
    weakenVarView_elim

  (** val coq_FunctionalInduction_weakenVarView :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
      coq_WeakenVarView) coq_FunctionalInduction **)

  let coq_FunctionalInduction_weakenVarView =
    Obj.magic weakenVarView_graph_correct

  (** val substUniv_weaken : coq_WeakensTo coq_SubstUniv **)

  let substUniv_weaken =
    { initSU = wkNilInit; transSU = transWk; interpSU = interpWk }

  (** val extendMeetSkipSkip :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo
      coq_MeetResult -> coq_WeakensTo coq_MeetResult **)

  let extendMeetSkipSkip _ _ _UU03a3_3 x meet =
    let { _UU03a3_12 = _UU03a3_13; meetLeft = _UU03c3_1'; meetRight =
      _UU03c3_2'; meetUp = _UU03c3_' } = meet
    in
    { _UU03a3_12 = _UU03a3_13; meetLeft = _UU03c3_1'; meetRight = _UU03c3_2';
    meetUp = (WkSkipVar (_UU03a3_13, _UU03a3_3, x, _UU03c3_')) }

  (** val extendMeetSkipKeep :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo
      coq_MeetResult -> coq_WeakensTo coq_MeetResult **)

  let extendMeetSkipKeep _UU03a3_1 _UU03a3_2 _UU03a3_3 x meet =
    let { _UU03a3_12 = _UU03a3_13; meetLeft = _UU03c3_1'; meetRight =
      _UU03c3_2'; meetUp = _UU03c3_' } = meet
    in
    { _UU03a3_12 = (Coq_ctx.Coq_snoc (_UU03a3_13, x)); meetLeft = (WkSkipVar
    (_UU03a3_1, _UU03a3_13, x, _UU03c3_1')); meetRight = (WkKeepVar
    (_UU03a3_2, _UU03a3_13, x, _UU03c3_2')); meetUp = (WkKeepVar (_UU03a3_13,
    _UU03a3_3, x, _UU03c3_')) }

  (** val extendMeetKeepSkip :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo
      coq_MeetResult -> coq_WeakensTo coq_MeetResult **)

  let extendMeetKeepSkip _UU03a3_1 _UU03a3_2 _UU03a3_3 x meet =
    let { _UU03a3_12 = _UU03a3_13; meetLeft = _UU03c3_1'; meetRight =
      _UU03c3_2'; meetUp = _UU03c3_' } = meet
    in
    { _UU03a3_12 = (Coq_ctx.Coq_snoc (_UU03a3_13, x)); meetLeft = (WkKeepVar
    (_UU03a3_1, _UU03a3_13, x, _UU03c3_1')); meetRight = (WkSkipVar
    (_UU03a3_2, _UU03a3_13, x, _UU03c3_2')); meetUp = (WkKeepVar (_UU03a3_13,
    _UU03a3_3, x, _UU03c3_')) }

  (** val extendMeetKeepKeep :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo
      coq_MeetResult -> coq_WeakensTo coq_MeetResult **)

  let extendMeetKeepKeep _UU03a3_1 _UU03a3_2 _UU03a3_3 x meet =
    let { _UU03a3_12 = _UU03a3_13; meetLeft = _UU03c3_1'; meetRight =
      _UU03c3_2'; meetUp = _UU03c3_' } = meet
    in
    { _UU03a3_12 = (Coq_ctx.Coq_snoc (_UU03a3_13, x)); meetLeft = (WkKeepVar
    (_UU03a3_1, _UU03a3_13, x, _UU03c3_1')); meetRight = (WkKeepVar
    (_UU03a3_2, _UU03a3_13, x, _UU03c3_2')); meetUp = (WkKeepVar (_UU03a3_13,
    _UU03a3_3, x, _UU03c3_')) }

  (** val meetWk :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo coq_MeetResult **)

  let rec meetWk _ _ _ wk13 wk23 =
    match wk13 with
    | WkNil ->
      (match wk23 with
       | WkNil ->
         { _UU03a3_12 = Coq_ctx.Coq_nil; meetLeft = WkNil; meetRight = WkNil;
           meetUp = WkNil }
       | _ -> assert false (* absurd case *))
    | WkSkipVar (_UU03a3_1, _, _, w) ->
      (match wk23 with
       | WkNil -> assert false (* absurd case *)
       | WkSkipVar (_UU03a3_2, _UU03a3_3, x, w0) ->
         extendMeetSkipSkip _UU03a3_1 _UU03a3_2 _UU03a3_3 x
           (meetWk _UU03a3_1 _UU03a3_2 _UU03a3_3 w w0)
       | WkKeepVar (_UU03a3_2, _UU03a3_3, x, w0) ->
         extendMeetSkipKeep _UU03a3_1 _UU03a3_2 _UU03a3_3 x
           (meetWk _UU03a3_1 _UU03a3_2 _UU03a3_3 w w0))
    | WkKeepVar (_UU03a3_1, _, x, w) ->
      (match wk23 with
       | WkNil -> assert false (* absurd case *)
       | WkSkipVar (_UU03a3_2, _UU03a3_3, _, w0) ->
         extendMeetKeepSkip _UU03a3_1 _UU03a3_2 _UU03a3_3 x
           (meetWk _UU03a3_1 _UU03a3_2 _UU03a3_3 w w0)
       | WkKeepVar (_UU03a3_2, _UU03a3_3, _, w0) ->
         extendMeetKeepKeep _UU03a3_1 _UU03a3_2 _UU03a3_3 x
           (meetWk _UU03a3_1 _UU03a3_2 _UU03a3_3 w w0))

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

  (** val meetWk_graph_rect :
      'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
      coq_WeakensTo -> meetWk_graph -> 'a1 -> 'a1) -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo
      -> meetWk_graph -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> meetWk_graph ->
      'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakensTo -> meetWk_graph -> 'a1 -> 'a1) ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo coq_MeetResult ->
      meetWk_graph -> 'a1 **)

  let rec meetWk_graph_rect f f0 f1 f2 f3 _ _ _ _ _ _ = function
  | Coq_meetWk_graph_equation_1 -> f
  | Coq_meetWk_graph_equation_2 (_UU03a3_1, _UU03a3_2, _UU03a3_3, x, wk2,
                                 wk3, hind) ->
    f0 _UU03a3_1 _UU03a3_2 _UU03a3_3 x wk2 wk3 hind
      (meetWk_graph_rect f f0 f1 f2 f3 _UU03a3_1 _UU03a3_2 _UU03a3_3 wk2 wk3
        (meetWk _UU03a3_1 _UU03a3_2 _UU03a3_3 wk2 wk3) hind)
  | Coq_meetWk_graph_equation_3 (_UU03a3_1, _UU03a3_6, x, _UU03a3_7, wk2,
                                 wk3, hind) ->
    f1 _UU03a3_1 _UU03a3_6 x _UU03a3_7 wk2 wk3 hind
      (meetWk_graph_rect f f0 f1 f2 f3 _UU03a3_1 _UU03a3_6 _UU03a3_7 wk2 wk3
        (meetWk _UU03a3_1 _UU03a3_6 _UU03a3_7 wk2 wk3) hind)
  | Coq_meetWk_graph_equation_4 (_UU03a3_6, x, _UU03a3_2, _UU03a3_3, wk2,
                                 wk3, hind) ->
    f2 _UU03a3_6 x _UU03a3_2 _UU03a3_3 wk2 wk3 hind
      (meetWk_graph_rect f f0 f1 f2 f3 _UU03a3_6 _UU03a3_2 _UU03a3_3 wk2 wk3
        (meetWk _UU03a3_6 _UU03a3_2 _UU03a3_3 wk2 wk3) hind)
  | Coq_meetWk_graph_equation_5 (_UU03a3_6, x, _UU03a3_4, _UU03a3_5, wk2,
                                 wk3, hind) ->
    f3 _UU03a3_6 x _UU03a3_4 _UU03a3_5 wk2 wk3 hind
      (meetWk_graph_rect f f0 f1 f2 f3 _UU03a3_6 _UU03a3_4 _UU03a3_5 wk2 wk3
        (meetWk _UU03a3_6 _UU03a3_4 _UU03a3_5 wk2 wk3) hind)

  (** val meetWk_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakensTo -> meetWk_graph **)

  let rec meetWk_graph_correct _ _ _ wk13 wk23 =
    match wk13 with
    | WkNil ->
      (match wk23 with
       | WkNil -> Coq_meetWk_graph_equation_1
       | _ -> assert false (* absurd case *))
    | WkSkipVar (_UU03a3_1, _, _, w) ->
      (match wk23 with
       | WkNil -> assert false (* absurd case *)
       | WkSkipVar (_UU03a3_2, _UU03a3_3, x, w0) ->
         Coq_meetWk_graph_equation_2 (_UU03a3_1, _UU03a3_2, _UU03a3_3, x, w,
           w0, (meetWk_graph_correct _UU03a3_1 _UU03a3_2 _UU03a3_3 w w0))
       | WkKeepVar (_UU03a3_2, _UU03a3_3, x, w0) ->
         Coq_meetWk_graph_equation_3 (_UU03a3_1, _UU03a3_2, x, _UU03a3_3, w,
           w0, (meetWk_graph_correct _UU03a3_1 _UU03a3_2 _UU03a3_3 w w0)))
    | WkKeepVar (_UU03a3_1, _, x, w) ->
      (match wk23 with
       | WkNil -> assert false (* absurd case *)
       | WkSkipVar (_UU03a3_2, _UU03a3_3, _, w0) ->
         Coq_meetWk_graph_equation_4 (_UU03a3_1, x, _UU03a3_2, _UU03a3_3, w,
           w0, (meetWk_graph_correct _UU03a3_1 _UU03a3_2 _UU03a3_3 w w0))
       | WkKeepVar (_UU03a3_2, _UU03a3_3, _, w0) ->
         Coq_meetWk_graph_equation_5 (_UU03a3_1, x, _UU03a3_2, _UU03a3_3, w,
           w0, (meetWk_graph_correct _UU03a3_1 _UU03a3_2 _UU03a3_3 w w0)))

  (** val meetWk_elim :
      'a1 -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
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
      coq_WeakensTo -> coq_WeakensTo -> 'a1 **)

  let meetWk_elim f f0 f1 f2 f3 _UU03a3_1 _UU03a3_2 _UU03a3_3 wk13 wk23 =
    let rec f4 _ _ _ _ _ _ = function
    | Coq_meetWk_graph_equation_1 -> f
    | Coq_meetWk_graph_equation_2 (_UU03a3_4, _UU03a3_5, _UU03a3_6, x, wk2,
                                   wk3, hind) ->
      f0 _UU03a3_4 _UU03a3_5 _UU03a3_6 x wk2 wk3
        (f4 _UU03a3_4 _UU03a3_5 _UU03a3_6 wk2 wk3
          (meetWk _UU03a3_4 _UU03a3_5 _UU03a3_6 wk2 wk3) hind)
    | Coq_meetWk_graph_equation_3 (_UU03a3_4, _UU03a3_6, x, _UU03a3_7, wk2,
                                   wk3, hind) ->
      f1 _UU03a3_4 _UU03a3_6 x _UU03a3_7 wk2 wk3
        (f4 _UU03a3_4 _UU03a3_6 _UU03a3_7 wk2 wk3
          (meetWk _UU03a3_4 _UU03a3_6 _UU03a3_7 wk2 wk3) hind)
    | Coq_meetWk_graph_equation_4 (_UU03a3_6, x, _UU03a3_4, _UU03a3_5, wk2,
                                   wk3, hind) ->
      f2 _UU03a3_6 x _UU03a3_4 _UU03a3_5 wk2 wk3
        (f4 _UU03a3_6 _UU03a3_4 _UU03a3_5 wk2 wk3
          (meetWk _UU03a3_6 _UU03a3_4 _UU03a3_5 wk2 wk3) hind)
    | Coq_meetWk_graph_equation_5 (_UU03a3_6, x, _UU03a3_4, _UU03a3_5, wk2,
                                   wk3, hind) ->
      f3 _UU03a3_6 x _UU03a3_4 _UU03a3_5 wk2 wk3
        (f4 _UU03a3_6 _UU03a3_4 _UU03a3_5 wk2 wk3
          (meetWk _UU03a3_6 _UU03a3_4 _UU03a3_5 wk2 wk3) hind)
    in f4 _UU03a3_1 _UU03a3_2 _UU03a3_3 wk13 wk23
         (meetWk _UU03a3_1 _UU03a3_2 _UU03a3_3 wk13 wk23)
         (meetWk_graph_correct _UU03a3_1 _UU03a3_2 _UU03a3_3 wk13 wk23)

  (** val coq_FunctionalElimination_meetWk :
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
      coq_WeakensTo -> coq_WeakensTo -> __ **)

  let coq_FunctionalElimination_meetWk =
    meetWk_elim

  (** val coq_FunctionalInduction_meetWk :
      ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo coq_MeetResult)
      coq_FunctionalInduction **)

  let coq_FunctionalInduction_meetWk =
    Obj.magic meetWk_graph_correct

  (** val substUnivMeet_weaken : coq_WeakensTo coq_SubstUnivMeet **)

  let substUnivMeet_weaken _UU03a3_ _UU03a3_1 _UU03a3_2 =
    meetWk _UU03a3_1 _UU03a3_2 _UU03a3_

  (** val wkVar :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo **)

  let rec wkVar b _UU0393_ bIn =
    Coq_ctx.coq_In_case (fun x _UU03a3_ -> WkKeepVar (Coq_ctx.Coq_nil,
      _UU03a3_, x, (wkNilInit _UU03a3_))) (fun b' _UU0393_0 b0 bIn0 ->
      WkSkipVar ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, b0)), _UU0393_0, b',
      (wkVar b0 _UU0393_0 bIn0))) b _UU0393_ bIn

  (** val coq_FunctionalInduction_transWk_assoc :
      __ coq_FunctionalInduction **)

  let coq_FunctionalInduction_transWk_assoc =
    Obj.magic __

  (** val substUnivVar_weaken : coq_WeakensTo coq_SubstUnivVar **)

  let substUnivVar_weaken =
    wkVar

  (** val substUnivVarUp_weaken : coq_WeakensTo coq_SubstUnivVarUp **)

  let substUnivVarUp_weaken _UU03a3_1 _UU03a3_2 x _UU03c3_ =
    WkKeepVar (_UU03a3_1, _UU03a3_2, x, _UU03c3_)

  (** val substUnivVarDown_weaken : coq_WeakensTo coq_SubstUnivVarDown **)

  let substUnivVarDown_weaken =
    { wkVarSU = (fun _UU03a3_1 _UU03a3_2 x xIn _UU03c3_ ->
      weakenIn _UU03a3_1 _UU03a3_2 _UU03c3_ x xIn); downSU =
      (fun _UU03a3_1 _UU03a3_2 x xIn _UU03c3_ ->
      weakenRemovePres _UU03a3_1 _UU03a3_2 _UU03c3_ x xIn) }

  (** val restrictEnv :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_WeakensTo -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, 'a1)
      Coq_env.coq_Env -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, 'a1)
      Coq_env.coq_Env **)

  let rec restrictEnv _ _ w h =
    match w with
    | WkNil -> h
    | WkSkipVar (_UU03a3_1, _UU03a3_2, x, w0) ->
      restrictEnv _UU03a3_1 _UU03a3_2 w0 (Coq_env.tail _UU03a3_2 x h)
    | WkKeepVar (_UU03a3_1, _UU03a3_2, x, w0) ->
      let y = Coq_env.view (Coq_ctx.Coq_snoc (_UU03a3_2, x)) h in
      let Coq_env.Coq_isSnoc (e, v) = Obj.magic y in
      Coq_env.Coq_snoc (_UU03a3_1, (restrictEnv _UU03a3_1 _UU03a3_2 w0 e), x,
      v)

  (** val elimWeakenedVarZero :
      (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 -> 'a1) -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a1) -> (coq_WeakensTo,
      'a1) coq_Weakened -> (coq_WeakensTo, 'a1) coq_Weakened **)

  let elimWeakenedVarZero x _UU03a3_ b funused fused wv =
    let { _UU03a3_supp = wildcard'; embedSupport = _UU03c3_1; wkVal = v } = wv
    in
    (match weakenZeroView wildcard' _UU03a3_ b _UU03c3_1 with
     | VarUnused (_UU03a3_1, _UU03c3_1') ->
       { _UU03a3_supp = _UU03a3_1; embedSupport = _UU03c3_1'; wkVal =
         (liftBoxUnOp funused _UU03a3_1 v) }
     | VarUsed (_UU03a3_1, _UU03c3_1') ->
       { _UU03a3_supp = _UU03a3_1; embedSupport = _UU03c3_1'; wkVal =
         (boxSb x _UU03a3_1
           (fused _UU03a3_1
             (v (Coq_ctx.Coq_snoc (_UU03a3_1, b))
               (wkRefl (Coq_ctx.Coq_snoc (_UU03a3_1, b)))))) })

  (** val elimWeakenedVar :
      (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a2) coq_SubstSU ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ((coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> 'a2) ->
      (coq_WeakensTo, 'a1) coq_Weakened -> (coq_WeakensTo, 'a2) coq_Weakened **)

  let elimWeakenedVar _ x _UU03a3_ b bIn f wv =
    let { _UU03a3_supp = wildcard'; embedSupport = _UU03c3_1; wkVal = v } = wv
    in
    let MkWeakenRemoveView (_UU03a3_1', bIn', _UU03c3_1') =
      weakenRemoveView b _UU03a3_ bIn wildcard' _UU03c3_1
    in
    { _UU03a3_supp = _UU03a3_1'; embedSupport = _UU03c3_1'; wkVal =
    (boxSb x _UU03a3_1'
      (f _UU03a3_1' bIn'
        (v (Coq_ctx.remove _UU03a3_1' b bIn')
          (wkRefl (Coq_ctx.remove _UU03a3_1' b bIn'))))) }

  (** val old_occurs_check :
      (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a1)
      coq_GenOccursCheck -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 ->
      'a1 option **)

  let old_occurs_check sT gocT _UU03a3_ x xIn t0 =
    let { _UU03a3_supp = _UU03a3_supp0; embedSupport = _UU03b6_; wkVal =
      t' } = gen_occurs_check substUniv_weaken sT gocT _UU03a3_ t0
    in
    (match weakenVarView _UU03a3_supp0 _UU03a3_ x xIn _UU03b6_ with
     | WeakenVarUnused (_, _UU03b6_') ->
       Some (t' (Coq_ctx.remove _UU03a3_ x xIn) _UU03b6_')
     | WeakenVarUsed (_, _, _) -> None)

  type ('t, 'a) coq_Inst =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't ->
    ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
    Coq_env.coq_Env -> 'a

  (** val inst :
      ('a1, 'a2) coq_Inst -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 -> ((coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> 'a2 **)

  let inst inst0 =
    inst0

  type ('t, 'a) coq_Lift =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a -> 't

  (** val lift :
      ('a1, 'a2) coq_Lift -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a2 -> 'a1 **)

  let lift lift0 =
    lift0

  (** val inst_list :
      ('a1, 'a2) coq_Inst -> ('a1 coq_List, 'a2 list) coq_Inst **)

  let inst_list h _UU03a3_ xs _UU03b9_ =
    ListDef.map (fun x -> inst h _UU03a3_ x _UU03b9_) xs

  (** val lift_list :
      ('a1, 'a2) coq_Lift -> ('a1 coq_List, 'a2 list) coq_Lift **)

  let lift_list h _UU03a3_ =
    ListDef.map (lift h _UU03a3_)

  (** val inst_const : ('a1 coq_Const, 'a1) coq_Inst **)

  let inst_const _ x _ =
    x

  (** val lift_const : ('a1 coq_Const, 'a1) coq_Lift **)

  let lift_const _ x =
    x

  (** val inst_env :
      ('a1 -> ('a2, 'a3) coq_Inst) -> 'a1 Coq_ctx.coq_Ctx -> (('a1, 'a2)
      Coq_env.coq_Env, ('a1, 'a3) Coq_env.coq_Env) coq_Inst **)

  let inst_env instSA _UU0393_ _UU03a3_ xs _UU03b9_ =
    Coq_env.map (fun b s -> inst (instSA b) _UU03a3_ s _UU03b9_) _UU0393_ xs

  (** val lift_env :
      ('a1 -> ('a2, 'a3) coq_Lift) -> 'a1 Coq_ctx.coq_Ctx -> (('a1, 'a2)
      Coq_env.coq_Env, ('a1, 'a3) Coq_env.coq_Env) coq_Lift **)

  let lift_env instSA _UU0393_ _UU03a3_ =
    Coq_env.map (fun b a -> lift (instSA b) _UU03a3_ a) _UU0393_

  (** val inst_term : Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Val) coq_Inst **)

  let rec inst_term _ _UU03a3_ t0 _UU03b9_ =
    match t0 with
    | Coq_term_var (l, _UU03c3_0, bIn) ->
      Coq_env.lookup _UU03a3_ _UU03b9_ { Binding.name = l; Binding.coq_type =
        _UU03c3_0 } bIn
    | Coq_term_val (_, v) -> v
    | Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1, t2) ->
      Coq_bop.eval typedeclkit typedenotekit typedefkit _UU03c3_1 _UU03c3_2
        _UU03c3_3 op (inst (inst_term _UU03c3_1) _UU03a3_ t1 _UU03b9_)
        (inst (inst_term _UU03c3_2) _UU03a3_ t2 _UU03b9_)
    | Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t1) ->
      Coq_uop.eval typedeclkit typedenotekit _UU03c3_1 _UU03c3_2 op
        (inst (inst_term _UU03c3_1) _UU03a3_ t1 _UU03b9_)
    | Coq_term_tuple (_UU03c3_s, ts) ->
      Coq_envrec.of_env _UU03c3_s
        (inst (inst_env inst_term _UU03c3_s) _UU03a3_ ts _UU03b9_)
    | Coq_term_union (u, k, t1) ->
      typedefkit.Coq_ty.unionv_fold u (Coq_existT (k,
        (inst (inst_term (typedefkit.Coq_ty.unionk_ty u k)) _UU03a3_ t1
          _UU03b9_)))
    | Coq_term_record (r, ts) ->
      let instTerm = fun xt -> inst_term xt.Binding.coq_type in
      typedefkit.Coq_ty.recordv_fold r
        (inst (inst_env instTerm (typedefkit.Coq_ty.recordf_ty r)) _UU03a3_
          ts _UU03b9_)

  (** val lift_term : Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Val) coq_Lift **)

  let lift_term _UU03c3_ _ v =
    Coq_term_val (_UU03c3_, v)

  (** val inst_sub :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_Sub, ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding,
      Coq_ty.coq_Val) Coq_env.coq_Env) coq_Inst **)

  let inst_sub _UU03a3_ =
    inst_env (fun _UU03c4_ -> inst_term _UU03c4_.Binding.coq_type) _UU03a3_

  (** val inst_unit : (coq_Unit, coq_unit) coq_Inst **)

  let inst_unit _ x _ =
    x

  (** val lift_unit : (coq_Unit, coq_unit) coq_Lift **)

  let lift_unit _ x =
    x

  (** val inst_pair :
      ('a1, 'a3) coq_Inst -> ('a2, 'a4) coq_Inst -> (('a1, 'a2) coq_Pair,
      ('a3, 'a4) prod) coq_Inst **)

  let inst_pair h h0 _UU03a3_ pat _UU03b9_ =
    let Coq_pair (a, b) = pat in
    Coq_pair ((inst h _UU03a3_ a _UU03b9_), (inst h0 _UU03a3_ b _UU03b9_))

  (** val lift_pair :
      ('a1, 'a3) coq_Lift -> ('a2, 'a4) coq_Lift -> (('a1, 'a2) coq_Pair,
      ('a3, 'a4) prod) coq_Lift **)

  let lift_pair h h0 _UU03a3_ = function
  | Coq_pair (a, b) -> Coq_pair ((lift h _UU03a3_ a), (lift h0 _UU03a3_ b))

  (** val inst_option :
      ('a1, 'a2) coq_Inst -> ('a1 coq_Option, 'a2 option) coq_Inst **)

  let inst_option h _UU03a3_ ma _UU03b9_ =
    option_map (fun a -> inst h _UU03a3_ a _UU03b9_) ma

  (** val lift_option :
      ('a1, 'a2) coq_Lift -> ('a1 coq_Option, 'a2 option) coq_Lift **)

  let lift_option h _UU03a3_ ma =
    option_map (lift h _UU03a3_) ma

  (** val inst_store :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_SStore, (coq_PVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv)
      coq_Inst **)

  let inst_store _UU0393_ =
    inst_env (fun _UU03c4_ -> inst_term _UU03c4_.Binding.coq_type) _UU0393_

  (** val term_get_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> Coq_ty.coq_Val option **)

  let term_get_val _ _ = function
  | Coq_term_val (_, v) -> Some v
  | _ -> None

  (** val term_get_pair :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Term -> (coq_Term, coq_Term) prod
      option **)

  let term_get_pair _ _UU03c3_1 _UU03c3_2 = function
  | Coq_term_var (_, _, _) -> None
  | Coq_term_val (_, v) ->
    let Coq_pair (v0, v1) = Obj.magic v in
    Some (Coq_pair ((Coq_term_val (_UU03c3_1, v0)), (Coq_term_val (_UU03c3_2,
    v1))))
  | Coq_term_binop (_, _, _, op, t1, t2) ->
    (match op with
     | Coq_bop.Coq_pair (_, _) -> Some (Coq_pair (t1, t2))
     | _ -> assert false (* absurd case *))
  | Coq_term_unop (_, _, _, _) -> None
  | _ -> assert false (* absurd case *)

  (** val term_get_sum :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Term -> (coq_Term, coq_Term) sum
      option **)

  let term_get_sum _ _UU03c3_1 _UU03c3_2 = function
  | Coq_term_var (_, _, _) -> None
  | Coq_term_val (_, v) ->
    (match Obj.magic v with
     | Coq_inl v0 -> Some (Coq_inl (Coq_term_val (_UU03c3_1, v0)))
     | Coq_inr v0 -> Some (Coq_inr (Coq_term_val (_UU03c3_2, v0))))
  | Coq_term_binop (_, _, _, _, _, _) -> None
  | Coq_term_unop (_, _, op, t1) ->
    (match op with
     | Coq_uop.Coq_inl (_, _) -> Some (Coq_inl t1)
     | Coq_uop.Coq_inr (_, _) -> Some (Coq_inr t1)
     | _ -> assert false (* absurd case *))
  | _ -> assert false (* absurd case *)

  (** val term_get_list :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> ((coq_Term, coq_Term) prod, coq_unit) sum
      option **)

  let term_get_list _ _UU03c3_ = function
  | Coq_term_var (_, _, _) -> None
  | Coq_term_val (_, v) ->
    (match Obj.magic v with
     | Datatypes.Coq_nil -> Some (Coq_inr Coq_tt)
     | Datatypes.Coq_cons (v0, l) ->
       Some (Coq_inl (Coq_pair ((Coq_term_val (_UU03c3_, v0)), (Coq_term_val
         ((Coq_ty.Coq_list _UU03c3_), (Obj.magic l)))))))
  | Coq_term_binop (_, _, _, op, t1, t2) ->
    (match op with
     | Coq_bop.Coq_cons _ -> Some (Coq_inl (Coq_pair (t1, t2)))
     | Coq_bop.Coq_append _ -> None
     | _ -> assert false (* absurd case *))
  | Coq_term_unop (_, _, _, _) -> None
  | _ -> assert false (* absurd case *)

  (** val term_get_union :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.unioni -> coq_Term -> (Coq_ty.unionk, coq_Term) sigT option **)

  let term_get_union _ u = function
  | Coq_term_val (_, v) ->
    Some
      (let Coq_existT (k, p) = typedefkit.Coq_ty.unionv_unfold u v in
       Coq_existT (k, (Coq_term_val ((typedefkit.Coq_ty.unionk_ty u k), p))))
  | Coq_term_tuple (_, _) -> assert false (* absurd case *)
  | Coq_term_union (_, k, t1) -> Some (Coq_existT (k, t1))
  | Coq_term_record (_, _) -> assert false (* absurd case *)
  | _ -> None

  (** val term_get_record :
      Coq_ty.recordi -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Term -> (Coq_ty.recordf, Coq_ty.coq_Ty,
      coq_Term) coq_NamedEnv option **)

  let term_get_record r _ = function
  | Coq_term_val (_, v) ->
    Some
      (Coq_env.map (fun b v0 -> Coq_term_val (b.Binding.coq_type, v0))
        (typedefkit.Coq_ty.recordf_ty r)
        (typedefkit.Coq_ty.recordv_unfold r v))
  | Coq_term_tuple (_, _) -> assert false (* absurd case *)
  | Coq_term_union (_, _, _) -> assert false (* absurd case *)
  | Coq_term_record (_, ts) -> Some ts
  | _ -> None

  (** val term_get_tuple :
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term -> (Coq_ty.coq_Ty,
      coq_Term) Coq_env.coq_Env option **)

  let term_get_tuple _ _ _ =
    None

  module Entailment =
   struct
    module Coq_tactics =
     struct
     end
   end

  type ('t, 'tE) coq_Erase =
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't -> 'tE

  (** val erase :
      ('a1, 'a2) coq_Erase -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> 'a1 -> 'a2 **)

  let erase erase0 =
    erase0

  (** val erase_Unit : (coq_Unit, coq_unit) coq_Erase **)

  let erase_Unit _ _ =
    Coq_tt

  (** val erase_Const : ('a1 coq_Const, 'a1) coq_Erase **)

  let erase_Const _ t0 =
    t0

  (** val erase_Ctx :
      ('a1, 'a2) coq_Erase -> ('a1 Coq_ctx.coq_Ctx, 'a2 list) coq_Erase **)

  let rec erase_Ctx h x = function
  | Coq_ctx.Coq_nil -> Datatypes.Coq_nil
  | Coq_ctx.Coq_snoc (ts, t1) ->
    Datatypes.Coq_cons ((erase h x t1), (erase_Ctx h x ts))

  (** val erase_List :
      ('a1, 'a2) coq_Erase -> ('a1 list, 'a2 list) coq_Erase **)

  let rec erase_List h x = function
  | Datatypes.Coq_nil -> Datatypes.Coq_nil
  | Datatypes.Coq_cons (t1, ts) ->
    Datatypes.Coq_cons ((erase h x t1), (erase_List h x ts))

  (** val erase_Term : Coq_ty.coq_Ty -> (coq_Term, coq_ETerm) coq_Erase **)

  let erase_Term _UU03c3_ _UU03a3_ =
    erase_term _UU03a3_ _UU03c3_

  (** val coq_EraseSStore :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_SStore, (coq_PVar, Coq_ty.coq_Ty, coq_ETerm) coq_NamedEnv)
      coq_Erase **)

  let coq_EraseSStore =
    erase_SStore

  module Coq_amsg =
   struct
    type 'm coq_CloseMessage =
    | Coq_there of (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding * 'm

    (** val coq_CloseMessage_rect :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1 -> 'a2) -> 'a1
        coq_CloseMessage -> 'a2 **)

    let coq_CloseMessage_rect _ f = function
    | Coq_there (b, msg) -> f b msg

    (** val coq_CloseMessage_rec :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        ((coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1 -> 'a2) -> 'a1
        coq_CloseMessage -> 'a2 **)

    let coq_CloseMessage_rec _ f = function
    | Coq_there (b, msg) -> f b msg

    (** val subst_closemessage :
        'a1 coq_Subst -> 'a1 coq_CloseMessage coq_Subst **)

    let subst_closemessage h _UU03a3_ m _UU03a3_2 _UU03b6_ =
      let Coq_there (b, msg) = m in
      Coq_there (b,
      (subst h (Coq_ctx.Coq_snoc (_UU03a3_, b)) msg (Coq_ctx.Coq_snoc
        (_UU03a3_2, b)) (sub_up1 _UU03a3_ _UU03a3_2 _UU03b6_ b)))

    (** val substSU_closemessage :
        (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a1
        coq_CloseMessage) coq_SubstSU **)

    let substSU_closemessage h _UU03a3_ _UU03a3_2 m _UU03b6_ =
      let Coq_there (b, msg) = m in
      Coq_there (b,
      (substSU h (Coq_ctx.Coq_snoc (_UU03a3_, b)) (Coq_ctx.Coq_snoc
        (_UU03a3_2, b)) msg (WkKeepVar (_UU03a3_, _UU03a3_2, b, _UU03b6_))))

    (** val substlaws_closemessage :
        'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_CloseMessage
        coq_SubstLaws **)

    let substlaws_closemessage _ _ =
      Build_SubstLaws

    (** val occurscheck_closemessage :
        'a1 coq_OccursCheck -> 'a1 coq_CloseMessage coq_OccursCheck **)

    let occurscheck_closemessage h _UU03a3_ x xIn = function
    | Coq_there (b, msg) ->
      Coq_option.map (fun x0 -> Coq_there (b, x0))
        (occurs_check h (Coq_ctx.Coq_snoc (_UU03a3_, b)) x
          (Coq_ctx.in_succ x _UU03a3_ b xIn) msg)

    (** val erase_closemessage :
        ('a1, 'a2) coq_Erase -> ('a1 coq_CloseMessage, 'a2) coq_Erase **)

    let erase_closemessage h _UU03a3_ = function
    | Coq_there (b, msg) -> erase h (Coq_ctx.Coq_snoc (_UU03a3_, b)) msg

    type coq_AMessage =
    | Coq_mk of __ coq_Subst * (coq_WeakensTo, __) coq_SubstSU
       * __ coq_SubstLaws * __ coq_OccursCheck * (__, __) coq_Erase * 
       __

    (** val coq_AMessage_rect :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (__
        -> __ coq_Subst -> (coq_WeakensTo, __) coq_SubstSU -> __ -> __
        coq_SubstLaws -> __ coq_OccursCheck -> __ -> (__, __) coq_Erase -> __
        -> 'a1) -> coq_AMessage -> 'a1 **)

    let coq_AMessage_rect _ f = function
    | Coq_mk (subM, wkM, subLM, occM, eM, msg) ->
      f __ subM wkM __ subLM occM __ eM msg

    (** val coq_AMessage_rec :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (__
        -> __ coq_Subst -> (coq_WeakensTo, __) coq_SubstSU -> __ -> __
        coq_SubstLaws -> __ coq_OccursCheck -> __ -> (__, __) coq_Erase -> __
        -> 'a1) -> coq_AMessage -> 'a1 **)

    let coq_AMessage_rec _ f = function
    | Coq_mk (subM, wkM, subLM, occM, eM, msg) ->
      f __ subM wkM __ subLM occM __ eM msg

    (** val empty :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_AMessage **)

    let empty _ =
      Coq_mk ((Obj.magic coq_SubstUnit), substSU_Const,
        (Obj.magic coq_SubstLawsUnit), (Obj.magic occurs_check_unit),
        erase_Const, (Obj.magic Coq_tt))

    (** val closeAux :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_WeakensTo, 'a1) coq_SubstSU -> 'a1 coq_Subst -> 'a1
        coq_SubstLaws -> 'a1 coq_OccursCheck -> ('a1, 'a2) coq_Erase -> 'a1
        -> coq_AMessage **)

    let rec closeAux _UU03a3_ _UU03a3__UU0394_ suM subM subLM occM eM msg =
      match _UU03a3__UU0394_ with
      | Coq_ctx.Coq_nil ->
        Coq_mk ((Obj.magic subM), (Obj.magic suM), (Obj.magic subLM),
          (Obj.magic occM), (Obj.magic eM), (Obj.magic msg))
      | Coq_ctx.Coq_snoc (_UU03a3__UU0394_0, b) ->
        closeAux _UU03a3_ _UU03a3__UU0394_0
          (Obj.magic substSU_closemessage suM)
          (Obj.magic subst_closemessage subM)
          (Obj.magic substlaws_closemessage subM subLM)
          (Obj.magic occurscheck_closemessage occM)
          (Obj.magic erase_closemessage eM) (Obj.magic (Coq_there (b, msg)))

    (** val close :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_AMessage -> coq_AMessage **)

    let close _UU03a3_ _UU03a3__UU0394_ = function
    | Coq_mk (subM, wkM, subLM, occM, eM, msg0) ->
      closeAux _UU03a3_ _UU03a3__UU0394_ wkM subM subLM occM eM msg0

    (** val subst_amessage : coq_AMessage coq_Subst **)

    let rec subst_amessage _UU03a3_ m _UU03a3_2 _UU03b6_ =
      let Coq_mk (subM, wkM, subLM, occM, eM, msg) = m in
      Coq_mk (subM, wkM, subLM, occM, eM,
      (subst subM _UU03a3_ msg _UU03a3_2 _UU03b6_))

    (** val substSU_amessage : (coq_WeakensTo, coq_AMessage) coq_SubstSU **)

    let rec substSU_amessage _UU03a3_ _UU03a3_2 m _UU03b6_ =
      let Coq_mk (subM, wkM, subLM, occM, eM, msg) = m in
      Coq_mk (subM, wkM, subLM, occM, eM,
      (substSU wkM _UU03a3_ _UU03a3_2 msg _UU03b6_))

    (** val substlaws_amessage : coq_AMessage coq_SubstLaws **)

    let substlaws_amessage =
      Build_SubstLaws

    (** val occurscheck_amessage :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (coq_LVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_AMessage ->
        coq_AMessage option **)

    let rec occurscheck_amessage _UU03a3_ x xIn = function
    | Coq_mk (subM, wkM, subLM, occM, eM, msg) ->
      Coq_option.map (fun x0 -> Coq_mk (subM, wkM, subLM, occM, eM, x0))
        (occurs_check occM _UU03a3_ x xIn msg)

    type coq_EAMessage =
      __
      (* singleton inductive, whose constructor was MkEAMessage *)

    (** val coq_EAMessage_rect : (__ -> __ -> 'a1) -> coq_EAMessage -> 'a1 **)

    let coq_EAMessage_rect f e =
      f __ e

    (** val coq_EAMessage_rec : (__ -> __ -> 'a1) -> coq_EAMessage -> 'a1 **)

    let coq_EAMessage_rec f e =
      f __ e

    (** val erase_amessage : (coq_AMessage, coq_EAMessage) coq_Erase **)

    let erase_amessage _UU03a3_ = function
    | Coq_mk (_, _, _, _, eM, m) -> erase eM _UU03a3_ m

    (** val boxMsg :
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_AMessage -> coq_AMessage **)

    let boxMsg _UU03a3_ _ = function
    | Coq_mk (_, _, _, _, eM, msg0) ->
      Coq_mk (coq_SubstConst, substSU_Const, coq_SubstLawsConst,
        coq_OccursCheck_Const, erase_Const, (erase eM _UU03a3_ msg0))

    (** val genoccurscheck_amessage :
        (coq_WeakensTo, coq_AMessage) coq_GenOccursCheck **)

    let genoccurscheck_amessage _UU03a3_ m =
      weakenInit substUniv_weaken substUnivMeet_weaken substSU_amessage
        substUniv_weaken substUnivMeet_weaken _UU03a3_
        (boxMsg _UU03a3_ Coq_ctx.Coq_nil m)
   end

  type coq_TermRing = { tmr_zero : Coq_ty.coq_Val; tmr_one : Coq_ty.coq_Val;
                        tmr_plus : Coq_bop.coq_BinOp;
                        tmr_times : Coq_bop.coq_BinOp;
                        tmr_minus : Coq_bop.coq_BinOp;
                        tmr_negate : Coq_uop.coq_UnOp;
                        tmr_of_Z : (coq_Z -> Coq_ty.coq_Val) }

  (** val tmr_zero :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_TermRing -> Coq_ty.coq_Val **)

  let tmr_zero _ _ termRing =
    termRing.tmr_zero

  (** val tmr_one :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_TermRing -> Coq_ty.coq_Val **)

  let tmr_one _ _ termRing =
    termRing.tmr_one

  (** val tmr_plus :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp **)

  let tmr_plus _ _ termRing =
    termRing.tmr_plus

  (** val tmr_times :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp **)

  let tmr_times _ _ termRing =
    termRing.tmr_times

  (** val tmr_minus :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp **)

  let tmr_minus _ _ termRing =
    termRing.tmr_minus

  (** val tmr_negate :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_TermRing -> Coq_uop.coq_UnOp **)

  let tmr_negate _ _ termRing =
    termRing.tmr_negate

  (** val tmr_of_Z :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_TermRing -> coq_Z -> Coq_ty.coq_Val **)

  let tmr_of_Z _ _ termRing =
    termRing.tmr_of_Z

  (** val coq_TermRing_int :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_TermRing **)

  let coq_TermRing_int _ =
    { tmr_zero = (Obj.magic Z0); tmr_one = (Obj.magic (Zpos Coq_xH));
      tmr_plus = Coq_bop.Coq_plus; tmr_times = Coq_bop.Coq_times; tmr_minus =
      Coq_bop.Coq_minus; tmr_negate = Coq_uop.Coq_neg; tmr_of_Z =
      (Obj.magic id) }

  (** val coq_TermRing_bv :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_TermRing **)

  let coq_TermRing_bv _ n =
    { tmr_zero = (Obj.magic Coq_bv.zero n); tmr_one =
      (Obj.magic Coq_bv.one n); tmr_plus = (Coq_bop.Coq_bvadd n); tmr_times =
      (Coq_bop.Coq_bvmul n); tmr_minus = (Coq_bop.Coq_bvsub n); tmr_negate =
      (Coq_uop.Coq_negate n); tmr_of_Z = (Obj.magic Coq_bv.of_Z n) }

  (** val evalPExprTm :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_TermRing -> coq_Term list -> coq_Z coq_PExpr ->
      coq_Term **)

  let evalPExprTm _ _UU03c3_ h =
    coq_PEeval (Coq_term_val (_UU03c3_, h.tmr_zero)) (Coq_term_val (_UU03c3_,
      h.tmr_one)) (fun x x0 -> Coq_term_binop (_UU03c3_, _UU03c3_, _UU03c3_,
      h.tmr_plus, x, x0)) (fun x x0 -> Coq_term_binop (_UU03c3_, _UU03c3_,
      _UU03c3_, h.tmr_times, x, x0)) (fun x x0 -> Coq_term_binop (_UU03c3_,
      _UU03c3_, _UU03c3_, h.tmr_minus, x, x0)) (fun x -> Coq_term_unop
      (_UU03c3_, _UU03c3_, h.tmr_negate, x)) (fun c -> Coq_term_val
      (_UU03c3_, (h.tmr_of_Z c))) id_phi_N
      (pow_N (Coq_term_val (_UU03c3_, h.tmr_one)) (fun x x0 -> Coq_term_binop
        (_UU03c3_, _UU03c3_, _UU03c3_, h.tmr_times, x, x0)))

  type coq_RQuote =
    coq_Term list -> positive -> (coq_Z coq_PExpr, coq_Term list) prod

  (** val coq_Term_Quote_def :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> coq_RQuote **)

  let coq_Term_Quote_def _UU03a3_ _UU03c3_ t0 ts o =
    match find_index (fun t' -> coq_Term_eqb _UU03a3_ _UU03c3_ t0 t') ts with
    | Some i -> Coq_pair ((PEX (Pos.of_succ_nat i)), Datatypes.Coq_nil)
    | None -> Coq_pair ((PEX o), (Datatypes.Coq_cons (t0, Datatypes.Coq_nil)))

  (** val coq_Term_Quote_unop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> (coq_Z coq_PExpr -> coq_Z coq_PExpr) -> coq_RQuote ->
      coq_RQuote **)

  let coq_Term_Quote_unop _ _ comb q1 ts o =
    let Coq_pair (pol1, ts1) = q1 ts o in Coq_pair ((comb pol1), ts1)

  (** val coq_Term_Quote_bin :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_TermRing -> (coq_Z coq_PExpr -> coq_Z coq_PExpr ->
      coq_Z coq_PExpr) -> coq_RQuote -> coq_RQuote -> coq_RQuote **)

  let coq_Term_Quote_bin _ _ _ comb q1 q2 ts o =
    let Coq_pair (pol1, ts1) = q1 ts o in
    let Coq_pair (pol2, ts2) = q2 (app ts ts1) (plusNatPos (length ts1) o) in
    Coq_pair ((comb pol1 pol2), (app ts1 ts2))

  type coq_CanonTerm = __

  (** val peval_append :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> coq_Term -> coq_Term **)

  let peval_append _ _UU03c3_ t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      Coq_term_binop ((Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list _UU03c3_),
        (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_append _UU03c3_),
        (Coq_term_var (l, (Coq_ty.Coq_list _UU03c3_), lIn)), t2)
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         (match Obj.magic v with
          | Datatypes.Coq_nil ->
            Coq_term_var (l, (Coq_ty.Coq_list _UU03c3_), lIn)
          | Datatypes.Coq_cons (v0, l0) ->
            Coq_term_binop (_UU03c3_, (Coq_ty.Coq_list _UU03c3_),
              (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_cons _UU03c3_),
              (Coq_term_val (_UU03c3_, v0)), (Coq_term_binop
              ((Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list _UU03c3_),
              (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_append _UU03c3_),
              (Coq_term_val ((Coq_ty.Coq_list _UU03c3_), (Obj.magic l0))),
              (Coq_term_var (l, (Coq_ty.Coq_list _UU03c3_), lIn))))))
       | Coq_term_val (_, v0) ->
         Coq_term_val ((Coq_ty.Coq_list _UU03c3_), (Obj.magic app v v0))
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         (match Obj.magic v with
          | Datatypes.Coq_nil ->
            Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_list _UU03c3_),
              op, t3, t4)
          | Datatypes.Coq_cons (v0, l) ->
            Coq_term_binop (_UU03c3_, (Coq_ty.Coq_list _UU03c3_),
              (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_cons _UU03c3_),
              (Coq_term_val (_UU03c3_, v0)), (Coq_term_binop
              ((Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list _UU03c3_),
              (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_append _UU03c3_),
              (Coq_term_val ((Coq_ty.Coq_list _UU03c3_), (Obj.magic l))),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_list
              _UU03c3_), op, t3, t4))))))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         (match Obj.magic v with
          | Datatypes.Coq_nil ->
            Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_list _UU03c3_), op, t0)
          | Datatypes.Coq_cons (v0, l) ->
            Coq_term_binop (_UU03c3_, (Coq_ty.Coq_list _UU03c3_),
              (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_cons _UU03c3_),
              (Coq_term_val (_UU03c3_, v0)), (Coq_term_binop
              ((Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list _UU03c3_),
              (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_append _UU03c3_),
              (Coq_term_val ((Coq_ty.Coq_list _UU03c3_), (Obj.magic l))),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_list _UU03c3_), op,
              t0))))))
       | _ -> assert false (* absurd case *))
    | Coq_term_binop (_, _, _, op, t3, t4) ->
      (match op with
       | Coq_bop.Coq_cons _ ->
         Coq_term_binop (_UU03c3_, (Coq_ty.Coq_list _UU03c3_),
           (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_cons _UU03c3_), t3,
           (Coq_term_binop ((Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list
           _UU03c3_), (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_append
           _UU03c3_), t4, t2)))
       | Coq_bop.Coq_append _ ->
         Coq_term_binop ((Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list
           _UU03c3_), (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_append
           _UU03c3_), (Coq_term_binop ((Coq_ty.Coq_list _UU03c3_),
           (Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list _UU03c3_),
           (Coq_bop.Coq_append _UU03c3_), t3, t4)), t2)
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      Coq_term_binop ((Coq_ty.Coq_list _UU03c3_), (Coq_ty.Coq_list _UU03c3_),
        (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_append _UU03c3_),
        (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_list _UU03c3_), op, t0)), t2)
    | _ -> assert false (* absurd case *)

  (** val peval_and_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term **)

  let peval_and_val _ t0 v =
    match Obj.magic v with
    | Coq_true -> t0
    | Coq_false -> Coq_term_val (Coq_ty.Coq_bool, (Obj.magic Coq_false))

  (** val peval_or_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term **)

  let peval_or_val _ t0 v =
    match Obj.magic v with
    | Coq_true -> Coq_term_val (Coq_ty.Coq_bool, (Obj.magic Coq_true))
    | Coq_false -> t0

  (** val peval_and :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Term -> coq_Term -> coq_Term **)

  let peval_and _UU03a3_ t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      (match t2 with
       | Coq_term_var (l0, _, lIn0) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_and, (Coq_term_var (l, Coq_ty.Coq_bool, lIn)),
           (Coq_term_var (l0, Coq_ty.Coq_bool, lIn0)))
       | Coq_term_val (_, v) ->
         peval_and_val _UU03a3_ (Coq_term_var (l, Coq_ty.Coq_bool, lIn)) v
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_and, (Coq_term_var (l, Coq_ty.Coq_bool, lIn)),
           (Coq_term_binop (_UU03c3_1, _UU03c3_2, Coq_ty.Coq_bool, op, t3,
           t4)))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_and, (Coq_term_var (l, Coq_ty.Coq_bool, lIn)),
           (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_bool, op, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_val (_, v) -> peval_and_val _UU03a3_ t2 v
    | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_and, (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           Coq_ty.Coq_bool, op, t3, t4)), (Coq_term_var (l, Coq_ty.Coq_bool,
           lIn)))
       | Coq_term_val (_, v) ->
         peval_and_val _UU03a3_ (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           Coq_ty.Coq_bool, op, t3, t4)) v
       | Coq_term_binop (_UU03c3_3, _UU03c3_4, _, op0, t5, t6) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_and, (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           Coq_ty.Coq_bool, op, t3, t4)), (Coq_term_binop (_UU03c3_3,
           _UU03c3_4, Coq_ty.Coq_bool, op0, t5, t6)))
       | Coq_term_unop (_UU03c3_3, _, op0, t0) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_and, (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           Coq_ty.Coq_bool, op, t3, t4)), (Coq_term_unop (_UU03c3_3,
           Coq_ty.Coq_bool, op0, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_and, (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_bool, op,
           t0)), (Coq_term_var (l, Coq_ty.Coq_bool, lIn)))
       | Coq_term_val (_, v) ->
         peval_and_val _UU03a3_ (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_bool,
           op, t0)) v
       | Coq_term_binop (_UU03c3_2, _UU03c3_3, _, op0, t3, t4) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_and, (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_bool, op,
           t0)), (Coq_term_binop (_UU03c3_2, _UU03c3_3, Coq_ty.Coq_bool, op0,
           t3, t4)))
       | Coq_term_unop (_UU03c3_2, _, op0, t3) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_and, (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_bool, op,
           t0)), (Coq_term_unop (_UU03c3_2, Coq_ty.Coq_bool, op0, t3)))
       | _ -> assert false (* absurd case *))
    | _ -> assert false (* absurd case *)

  (** val peval_or :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Term -> coq_Term -> coq_Term **)

  let peval_or _UU03a3_ t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      (match t2 with
       | Coq_term_var (l0, _, lIn0) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_or, (Coq_term_var (l, Coq_ty.Coq_bool, lIn)),
           (Coq_term_var (l0, Coq_ty.Coq_bool, lIn0)))
       | Coq_term_val (_, v) ->
         peval_or_val _UU03a3_ (Coq_term_var (l, Coq_ty.Coq_bool, lIn)) v
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_or, (Coq_term_var (l, Coq_ty.Coq_bool, lIn)),
           (Coq_term_binop (_UU03c3_1, _UU03c3_2, Coq_ty.Coq_bool, op, t3,
           t4)))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_or, (Coq_term_var (l, Coq_ty.Coq_bool, lIn)),
           (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_bool, op, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_val (_, v) -> peval_or_val _UU03a3_ t2 v
    | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_or, (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           Coq_ty.Coq_bool, op, t3, t4)), (Coq_term_var (l, Coq_ty.Coq_bool,
           lIn)))
       | Coq_term_val (_, v) ->
         peval_or_val _UU03a3_ (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           Coq_ty.Coq_bool, op, t3, t4)) v
       | Coq_term_binop (_UU03c3_3, _UU03c3_4, _, op0, t5, t6) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_or, (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           Coq_ty.Coq_bool, op, t3, t4)), (Coq_term_binop (_UU03c3_3,
           _UU03c3_4, Coq_ty.Coq_bool, op0, t5, t6)))
       | Coq_term_unop (_UU03c3_3, _, op0, t0) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_or, (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           Coq_ty.Coq_bool, op, t3, t4)), (Coq_term_unop (_UU03c3_3,
           Coq_ty.Coq_bool, op0, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_or, (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_bool, op,
           t0)), (Coq_term_var (l, Coq_ty.Coq_bool, lIn)))
       | Coq_term_val (_, v) ->
         peval_or_val _UU03a3_ (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_bool,
           op, t0)) v
       | Coq_term_binop (_UU03c3_2, _UU03c3_3, _, op0, t3, t4) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_or, (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_bool, op,
           t0)), (Coq_term_binop (_UU03c3_2, _UU03c3_3, Coq_ty.Coq_bool, op0,
           t3, t4)))
       | Coq_term_unop (_UU03c3_2, _, op0, t3) ->
         Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
           Coq_bop.Coq_or, (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_bool, op,
           t0)), (Coq_term_unop (_UU03c3_2, Coq_ty.Coq_bool, op0, t3)))
       | _ -> assert false (* absurd case *))
    | _ -> assert false (* absurd case *)

  (** val peval_plus :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Term -> coq_Term -> coq_Term **)

  let peval_plus _ t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      (match t2 with
       | Coq_term_var (l0, _, lIn0) ->
         Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
           Coq_bop.Coq_plus, (Coq_term_var (l, Coq_ty.Coq_int, lIn)),
           (Coq_term_var (l0, Coq_ty.Coq_int, lIn0)))
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | Z0 -> Coq_term_var (l, Coq_ty.Coq_int, lIn)
          | x ->
            Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
              Coq_bop.Coq_plus, (Coq_term_val (Coq_ty.Coq_int,
              (Obj.magic x))), (Coq_term_var (l, Coq_ty.Coq_int, lIn))))
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
           Coq_bop.Coq_plus, (Coq_term_var (l, Coq_ty.Coq_int, lIn)),
           (Coq_term_binop (_UU03c3_1, _UU03c3_2, Coq_ty.Coq_int, op, t3,
           t4)))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
           Coq_bop.Coq_plus, (Coq_term_var (l, Coq_ty.Coq_int, lIn)),
           (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_int, op, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         (match Obj.magic v with
          | Z0 -> Coq_term_var (l, Coq_ty.Coq_int, lIn)
          | x ->
            Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
              Coq_bop.Coq_plus, (Coq_term_val (Coq_ty.Coq_int,
              (Obj.magic x))), (Coq_term_var (l, Coq_ty.Coq_int, lIn))))
       | Coq_term_val (_, v0) ->
         Coq_term_val (Coq_ty.Coq_int, (Obj.magic BinInt.Z.add v v0))
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         (match Obj.magic v with
          | Z0 ->
            Coq_term_binop (_UU03c3_1, _UU03c3_2, Coq_ty.Coq_int, op, t3, t4)
          | x ->
            Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
              Coq_bop.Coq_plus, (Coq_term_val (Coq_ty.Coq_int,
              (Obj.magic x))), (Coq_term_binop (_UU03c3_1, _UU03c3_2,
              Coq_ty.Coq_int, op, t3, t4))))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         (match Obj.magic v with
          | Z0 -> Coq_term_unop (_UU03c3_1, Coq_ty.Coq_int, op, t0)
          | x ->
            Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
              Coq_bop.Coq_plus, (Coq_term_val (Coq_ty.Coq_int,
              (Obj.magic x))), (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_int, op,
              t0))))
       | _ -> assert false (* absurd case *))
    | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
           Coq_bop.Coq_plus, (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           Coq_ty.Coq_int, op, t3, t4)), (Coq_term_var (l, Coq_ty.Coq_int,
           lIn)))
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | Z0 ->
            Coq_term_binop (_UU03c3_1, _UU03c3_2, Coq_ty.Coq_int, op, t3, t4)
          | x ->
            Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
              Coq_bop.Coq_plus, (Coq_term_val (Coq_ty.Coq_int,
              (Obj.magic x))), (Coq_term_binop (_UU03c3_1, _UU03c3_2,
              Coq_ty.Coq_int, op, t3, t4))))
       | Coq_term_binop (_UU03c3_3, _UU03c3_4, _, op0, t5, t6) ->
         Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
           Coq_bop.Coq_plus, (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           Coq_ty.Coq_int, op, t3, t4)), (Coq_term_binop (_UU03c3_3,
           _UU03c3_4, Coq_ty.Coq_int, op0, t5, t6)))
       | Coq_term_unop (_UU03c3_3, _, op0, t0) ->
         Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
           Coq_bop.Coq_plus, (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           Coq_ty.Coq_int, op, t3, t4)), (Coq_term_unop (_UU03c3_3,
           Coq_ty.Coq_int, op0, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
           Coq_bop.Coq_plus, (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_int, op,
           t0)), (Coq_term_var (l, Coq_ty.Coq_int, lIn)))
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | Z0 -> Coq_term_unop (_UU03c3_1, Coq_ty.Coq_int, op, t0)
          | x ->
            Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
              Coq_bop.Coq_plus, (Coq_term_val (Coq_ty.Coq_int,
              (Obj.magic x))), (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_int, op,
              t0))))
       | Coq_term_binop (_UU03c3_2, _UU03c3_3, _, op0, t3, t4) ->
         Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
           Coq_bop.Coq_plus, (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_int, op,
           t0)), (Coq_term_binop (_UU03c3_2, _UU03c3_3, Coq_ty.Coq_int, op0,
           t3, t4)))
       | Coq_term_unop (_UU03c3_2, _, op0, t3) ->
         Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
           Coq_bop.Coq_plus, (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_int, op,
           t0)), (Coq_term_unop (_UU03c3_2, Coq_ty.Coq_int, op0, t3)))
       | _ -> assert false (* absurd case *))
    | _ -> assert false (* absurd case *)

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

  (** val peval_plus_graph_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (coq_LVar
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      positive -> 'a1) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> positive -> 'a1) -> (coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
      -> coq_Term -> 'a1) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (positive -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
      (positive -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) ->
      (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (positive ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      'a1) -> (positive -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      'a1) -> (positive -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
      (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive -> 'a1) ->
      (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
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
      coq_Term -> 'a1) -> coq_Term -> coq_Term -> coq_Term ->
      peval_plus_graph -> 'a1 **)

  let peval_plus_graph_rect _ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 _ _ _ = function
  | Coq_peval_plus_graph_equation_1 (l, lIn, l0, lIn0) -> f l lIn l0 lIn0
  | Coq_peval_plus_graph_equation_2 (l, lIn) -> f0 l lIn
  | Coq_peval_plus_graph_equation_3 (l, lIn, p0) -> f1 l lIn p0
  | Coq_peval_plus_graph_equation_4 (l, lIn, p0) -> f2 l lIn p0
  | Coq_peval_plus_graph_equation_5 (l, lIn, _UU03c3_1, _UU03c3_2, op, t1, t2) ->
    f3 l lIn _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_plus_graph_equation_6 (l, lIn, _UU03c3_4, op0, t0) ->
    f4 l lIn _UU03c3_4 op0 t0
  | Coq_peval_plus_graph_equation_7 (l, lIn) -> f5 l lIn
  | Coq_peval_plus_graph_equation_8 (p0, l, lIn) -> f6 p0 l lIn
  | Coq_peval_plus_graph_equation_9 (p0, l, lIn) -> f7 p0 l lIn
  | Coq_peval_plus_graph_equation_10 (v1, v2) -> f8 v1 v2
  | Coq_peval_plus_graph_equation_11 (_UU03c3_1, _UU03c3_2, op, t1, t2) ->
    f9 _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_plus_graph_equation_12 (p0, _UU03c3_1, _UU03c3_2, op, t1, t2) ->
    f10 p0 _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_plus_graph_equation_13 (p0, _UU03c3_1, _UU03c3_2, op, t1, t2) ->
    f11 p0 _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_plus_graph_equation_14 (_UU03c3_4, op0, t0) ->
    f12 _UU03c3_4 op0 t0
  | Coq_peval_plus_graph_equation_15 (p0, _UU03c3_4, op0, t0) ->
    f13 p0 _UU03c3_4 op0 t0
  | Coq_peval_plus_graph_equation_16 (p0, _UU03c3_4, op0, t0) ->
    f14 p0 _UU03c3_4 op0 t0
  | Coq_peval_plus_graph_equation_17 (_UU03c3_1, _UU03c3_2, op, t1, t3, l, lIn) ->
    f15 _UU03c3_1 _UU03c3_2 op t1 t3 l lIn
  | Coq_peval_plus_graph_equation_18 (_UU03c3_1, _UU03c3_2, op, t1, t3) ->
    f16 _UU03c3_1 _UU03c3_2 op t1 t3
  | Coq_peval_plus_graph_equation_19 (_UU03c3_1, _UU03c3_2, op, t1, t3, p0) ->
    f17 _UU03c3_1 _UU03c3_2 op t1 t3 p0
  | Coq_peval_plus_graph_equation_20 (_UU03c3_1, _UU03c3_2, op, t1, t3, p0) ->
    f18 _UU03c3_1 _UU03c3_2 op t1 t3 p0
  | Coq_peval_plus_graph_equation_21 (_UU03c3_1, _UU03c3_2, op, t1, t3,
                                      _UU03c3_3, _UU03c3_4, op0, t2, t4) ->
    f19 _UU03c3_1 _UU03c3_2 op t1 t3 _UU03c3_3 _UU03c3_4 op0 t2 t4
  | Coq_peval_plus_graph_equation_22 (_UU03c3_1, _UU03c3_2, op, t1, t3,
                                      _UU03c3_6, op1, t0) ->
    f20 _UU03c3_1 _UU03c3_2 op t1 t3 _UU03c3_6 op1 t0
  | Coq_peval_plus_graph_equation_23 (_UU03c3_4, op0, t0, l, lIn) ->
    f21 _UU03c3_4 op0 t0 l lIn
  | Coq_peval_plus_graph_equation_24 (_UU03c3_4, op0, t0) ->
    f22 _UU03c3_4 op0 t0
  | Coq_peval_plus_graph_equation_25 (_UU03c3_4, op0, t0, p0) ->
    f23 _UU03c3_4 op0 t0 p0
  | Coq_peval_plus_graph_equation_26 (_UU03c3_4, op0, t0, p0) ->
    f24 _UU03c3_4 op0 t0 p0
  | Coq_peval_plus_graph_equation_27 (_UU03c3_4, op0, t0, _UU03c3_1,
                                      _UU03c3_2, op, t1, t2) ->
    f25 _UU03c3_4 op0 t0 _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_plus_graph_equation_28 (_UU03c3_4, op0, t0, _UU03c3_5, op1, t1) ->
    f26 _UU03c3_4 op0 t0 _UU03c3_5 op1 t1

  (** val peval_plus_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Term -> coq_Term -> peval_plus_graph **)

  let peval_plus_graph_correct _ t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      (match t2 with
       | Coq_term_var (l0, _, lIn0) ->
         Coq_peval_plus_graph_equation_1 (l, lIn, l0, lIn0)
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | Z0 -> Coq_peval_plus_graph_equation_2 (l, lIn)
          | Zpos p -> Coq_peval_plus_graph_equation_3 (l, lIn, p)
          | Zneg p -> Coq_peval_plus_graph_equation_4 (l, lIn, p))
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         Coq_peval_plus_graph_equation_5 (l, lIn, _UU03c3_1, _UU03c3_2, op,
           t3, t4)
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_peval_plus_graph_equation_6 (l, lIn, _UU03c3_1, op, t0)
       | _ -> assert false (* absurd case *))
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         (match Obj.magic v with
          | Z0 -> Coq_peval_plus_graph_equation_7 (l, lIn)
          | Zpos p -> Coq_peval_plus_graph_equation_8 (p, l, lIn)
          | Zneg p -> Coq_peval_plus_graph_equation_9 (p, l, lIn))
       | Coq_term_val (_, v0) -> Coq_peval_plus_graph_equation_10 (v, v0)
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         (match Obj.magic v with
          | Z0 ->
            Coq_peval_plus_graph_equation_11 (_UU03c3_1, _UU03c3_2, op, t3,
              t4)
          | Zpos p ->
            Coq_peval_plus_graph_equation_12 (p, _UU03c3_1, _UU03c3_2, op,
              t3, t4)
          | Zneg p ->
            Coq_peval_plus_graph_equation_13 (p, _UU03c3_1, _UU03c3_2, op,
              t3, t4))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         (match Obj.magic v with
          | Z0 -> Coq_peval_plus_graph_equation_14 (_UU03c3_1, op, t0)
          | Zpos p -> Coq_peval_plus_graph_equation_15 (p, _UU03c3_1, op, t0)
          | Zneg p -> Coq_peval_plus_graph_equation_16 (p, _UU03c3_1, op, t0))
       | _ -> assert false (* absurd case *))
    | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_peval_plus_graph_equation_17 (_UU03c3_1, _UU03c3_2, op, t3, t4,
           l, lIn)
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | Z0 ->
            Coq_peval_plus_graph_equation_18 (_UU03c3_1, _UU03c3_2, op, t3,
              t4)
          | Zpos p ->
            Coq_peval_plus_graph_equation_19 (_UU03c3_1, _UU03c3_2, op, t3,
              t4, p)
          | Zneg p ->
            Coq_peval_plus_graph_equation_20 (_UU03c3_1, _UU03c3_2, op, t3,
              t4, p))
       | Coq_term_binop (_UU03c3_3, _UU03c3_4, _, op0, t5, t6) ->
         Coq_peval_plus_graph_equation_21 (_UU03c3_1, _UU03c3_2, op, t3, t4,
           _UU03c3_3, _UU03c3_4, op0, t5, t6)
       | Coq_term_unop (_UU03c3_3, _, op0, t0) ->
         Coq_peval_plus_graph_equation_22 (_UU03c3_1, _UU03c3_2, op, t3, t4,
           _UU03c3_3, op0, t0)
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_peval_plus_graph_equation_23 (_UU03c3_1, op, t0, l, lIn)
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | Z0 -> Coq_peval_plus_graph_equation_24 (_UU03c3_1, op, t0)
          | Zpos p -> Coq_peval_plus_graph_equation_25 (_UU03c3_1, op, t0, p)
          | Zneg p -> Coq_peval_plus_graph_equation_26 (_UU03c3_1, op, t0, p))
       | Coq_term_binop (_UU03c3_2, _UU03c3_3, _, op0, t3, t4) ->
         Coq_peval_plus_graph_equation_27 (_UU03c3_1, op, t0, _UU03c3_2,
           _UU03c3_3, op0, t3, t4)
       | Coq_term_unop (_UU03c3_2, _, op0, t3) ->
         Coq_peval_plus_graph_equation_28 (_UU03c3_1, op, t0, _UU03c3_2, op0,
           t3)
       | _ -> assert false (* absurd case *))
    | _ -> assert false (* absurd case *)

  (** val peval_plus_elim :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (coq_LVar
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      positive -> 'a1) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> positive -> 'a1) -> (coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
      -> coq_Term -> 'a1) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (positive -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
      (positive -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) ->
      (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (positive ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      'a1) -> (positive -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      'a1) -> (positive -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
      (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive -> 'a1) ->
      (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
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
      coq_Term -> 'a1) -> coq_Term -> coq_Term -> 'a1 **)

  let peval_plus_elim _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 t1 t2 =
    match peval_plus_graph_correct _UU03a3_ t1 t2 with
    | Coq_peval_plus_graph_equation_1 (l, lIn, l0, lIn0) -> f l lIn l0 lIn0
    | Coq_peval_plus_graph_equation_2 (l, lIn) -> f0 l lIn
    | Coq_peval_plus_graph_equation_3 (l, lIn, p) -> f1 l lIn p
    | Coq_peval_plus_graph_equation_4 (l, lIn, p0) -> f2 l lIn p0
    | Coq_peval_plus_graph_equation_5 (l, lIn, _UU03c3_1, _UU03c3_2, op, t3,
                                       t4) ->
      f3 l lIn _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_plus_graph_equation_6 (l, lIn, _UU03c3_4, op0, t0) ->
      f4 l lIn _UU03c3_4 op0 t0
    | Coq_peval_plus_graph_equation_7 (l, lIn) -> f5 l lIn
    | Coq_peval_plus_graph_equation_8 (p, l, lIn) -> f6 p l lIn
    | Coq_peval_plus_graph_equation_9 (p0, l, lIn) -> f7 p0 l lIn
    | Coq_peval_plus_graph_equation_10 (v1, v2) -> f8 v1 v2
    | Coq_peval_plus_graph_equation_11 (_UU03c3_1, _UU03c3_2, op, t3, t4) ->
      f9 _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_plus_graph_equation_12 (p, _UU03c3_1, _UU03c3_2, op, t3, t4) ->
      f10 p _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_plus_graph_equation_13 (p0, _UU03c3_1, _UU03c3_2, op, t3, t4) ->
      f11 p0 _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_plus_graph_equation_14 (_UU03c3_4, op0, t0) ->
      f12 _UU03c3_4 op0 t0
    | Coq_peval_plus_graph_equation_15 (p, _UU03c3_4, op0, t0) ->
      f13 p _UU03c3_4 op0 t0
    | Coq_peval_plus_graph_equation_16 (p0, _UU03c3_4, op0, t0) ->
      f14 p0 _UU03c3_4 op0 t0
    | Coq_peval_plus_graph_equation_17 (_UU03c3_1, _UU03c3_2, op, t3, t4, l,
                                        lIn) ->
      f15 _UU03c3_1 _UU03c3_2 op t3 t4 l lIn
    | Coq_peval_plus_graph_equation_18 (_UU03c3_1, _UU03c3_2, op, t3, t4) ->
      f16 _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_plus_graph_equation_19 (_UU03c3_1, _UU03c3_2, op, t3, t4, p) ->
      f17 _UU03c3_1 _UU03c3_2 op t3 t4 p
    | Coq_peval_plus_graph_equation_20 (_UU03c3_1, _UU03c3_2, op, t3, t4, p0) ->
      f18 _UU03c3_1 _UU03c3_2 op t3 t4 p0
    | Coq_peval_plus_graph_equation_21 (_UU03c3_1, _UU03c3_2, op, t3, t4,
                                        _UU03c3_3, _UU03c3_4, op0, t5, t6) ->
      f19 _UU03c3_1 _UU03c3_2 op t3 t4 _UU03c3_3 _UU03c3_4 op0 t5 t6
    | Coq_peval_plus_graph_equation_22 (_UU03c3_1, _UU03c3_2, op, t3, t4,
                                        _UU03c3_6, op1, t0) ->
      f20 _UU03c3_1 _UU03c3_2 op t3 t4 _UU03c3_6 op1 t0
    | Coq_peval_plus_graph_equation_23 (_UU03c3_4, op0, t0, l, lIn) ->
      f21 _UU03c3_4 op0 t0 l lIn
    | Coq_peval_plus_graph_equation_24 (_UU03c3_4, op0, t0) ->
      f22 _UU03c3_4 op0 t0
    | Coq_peval_plus_graph_equation_25 (_UU03c3_4, op0, t0, p) ->
      f23 _UU03c3_4 op0 t0 p
    | Coq_peval_plus_graph_equation_26 (_UU03c3_4, op0, t0, p0) ->
      f24 _UU03c3_4 op0 t0 p0
    | Coq_peval_plus_graph_equation_27 (_UU03c3_4, op0, t0, _UU03c3_1,
                                        _UU03c3_2, op, t3, t4) ->
      f25 _UU03c3_4 op0 t0 _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_plus_graph_equation_28 (_UU03c3_4, op0, t0, _UU03c3_5, op1, t3) ->
      f26 _UU03c3_4 op0 t0 _UU03c3_5 op1 t3

  (** val coq_FunctionalElimination_peval_plus :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (coq_LVar
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      positive -> __) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> positive -> __) -> (coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> __) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
      -> coq_Term -> __) -> (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (positive -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
      (positive -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> __) -> (Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) ->
      (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> __) -> (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (positive ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      __) -> (positive -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      __) -> (positive -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
      -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
      (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> positive -> __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive -> __) ->
      (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> __) -> (Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> __) -> (Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> positive -> __) -> (Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> positive -> __) -> (Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
      coq_Term -> __) -> coq_Term -> coq_Term -> __ **)

  let coq_FunctionalElimination_peval_plus =
    peval_plus_elim

  (** val coq_FunctionalInduction_peval_plus :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_Term -> coq_Term -> coq_Term) coq_FunctionalInduction **)

  let coq_FunctionalInduction_peval_plus _UU03a3_ =
    Obj.magic peval_plus_graph_correct _UU03a3_

  (** val peval_bvadd :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> coq_Term -> coq_Term **)

  let peval_bvadd _ n t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      (match t2 with
       | Coq_term_var (l0, _, lIn0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_var (l,
           (Coq_ty.Coq_bvec n), lIn)), (Coq_term_var (l0, (Coq_ty.Coq_bvec
           n), lIn0)))
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | N0 -> Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)
          | Npos p ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), (Obj.magic (Npos p)))), (Coq_term_var (l,
              (Coq_ty.Coq_bvec n), lIn))))
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_var (l,
           (Coq_ty.Coq_bvec n), lIn)), (Coq_term_binop (_UU03c3_1, _UU03c3_2,
           (Coq_ty.Coq_bvec n), op, t3, t4)))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_var (l,
           (Coq_ty.Coq_bvec n), lIn)), (Coq_term_unop (_UU03c3_1,
           (Coq_ty.Coq_bvec n), op, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         (match Obj.magic v with
          | N0 -> Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)
          | Npos p ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), (Obj.magic (Npos p)))), (Coq_term_var (l,
              (Coq_ty.Coq_bvec n), lIn))))
       | Coq_term_val (_, v0) ->
         Coq_term_val ((Coq_ty.Coq_bvec n), (Obj.magic Coq_bv.add n v v0))
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         (match Obj.magic v with
          | N0 ->
            Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n), op,
              t3, t4)
          | Npos p ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), (Obj.magic (Npos p)))), (Coq_term_binop
              (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n), op, t3, t4))))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         (match Obj.magic v with
          | N0 -> Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n), op, t0)
          | Npos p ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), (Obj.magic (Npos p)))), (Coq_term_unop
              (_UU03c3_1, (Coq_ty.Coq_bvec n), op, t0))))
       | _ -> assert false (* absurd case *))
    | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_binop
           (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n), op, t3, t4)),
           (Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)))
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | N0 ->
            Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n), op,
              t3, t4)
          | Npos p ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), (Obj.magic (Npos p)))), (Coq_term_binop
              (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n), op, t3, t4))))
       | Coq_term_binop (_UU03c3_3, _UU03c3_4, _, op0, t5, t6) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_binop
           (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n), op, t3, t4)),
           (Coq_term_binop (_UU03c3_3, _UU03c3_4, (Coq_ty.Coq_bvec n), op0,
           t5, t6)))
       | Coq_term_unop (_UU03c3_3, _, op0, t0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_binop
           (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n), op, t3, t4)),
           (Coq_term_unop (_UU03c3_3, (Coq_ty.Coq_bvec n), op0, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_unop
           (_UU03c3_1, (Coq_ty.Coq_bvec n), op, t0)), (Coq_term_var (l,
           (Coq_ty.Coq_bvec n), lIn)))
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | N0 -> Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n), op, t0)
          | Npos p ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), (Obj.magic (Npos p)))), (Coq_term_unop
              (_UU03c3_1, (Coq_ty.Coq_bvec n), op, t0))))
       | Coq_term_binop (_UU03c3_2, _UU03c3_3, _, op0, t3, t4) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_unop
           (_UU03c3_1, (Coq_ty.Coq_bvec n), op, t0)), (Coq_term_binop
           (_UU03c3_2, _UU03c3_3, (Coq_ty.Coq_bvec n), op0, t3, t4)))
       | Coq_term_unop (_UU03c3_2, _, op0, t3) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvadd n), (Coq_term_unop
           (_UU03c3_1, (Coq_ty.Coq_bvec n), op, t0)), (Coq_term_unop
           (_UU03c3_2, (Coq_ty.Coq_bvec n), op0, t3)))
       | _ -> assert false (* absurd case *))
    | _ -> assert false (* absurd case *)

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

  (** val peval_bvadd_graph_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __ ->
      'a1) -> (nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> positive -> __ -> 'a1) -> (nat ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
      -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> __ -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
      (nat -> positive -> __ -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
      -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      positive -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
      -> coq_Term -> coq_Term -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> positive -> __ ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat ->
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
      (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty
      -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> coq_Term -> coq_Term
      -> coq_Term -> peval_bvadd_graph -> 'a1 **)

  let peval_bvadd_graph_rect _ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 _ _ _ _ = function
  | Coq_peval_bvadd_graph_equation_1 (n, l, lIn, l0, lIn0) ->
    f n l lIn l0 lIn0
  | Coq_peval_bvadd_graph_equation_2 (n, l, lIn) -> f0 n l lIn __
  | Coq_peval_bvadd_graph_equation_3 (n, l, lIn, p0) -> f1 n l lIn p0 __
  | Coq_peval_bvadd_graph_equation_4 (n, l, lIn, _UU03c3_1, _UU03c3_2, op,
                                      t1, t2) ->
    f2 n l lIn _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_bvadd_graph_equation_5 (n, l, lIn, _UU03c3_4, op0, t0) ->
    f3 n l lIn _UU03c3_4 op0 t0
  | Coq_peval_bvadd_graph_equation_6 (n, l, lIn) -> f4 n __ l lIn
  | Coq_peval_bvadd_graph_equation_7 (n, p0, l, lIn) -> f5 n p0 __ l lIn
  | Coq_peval_bvadd_graph_equation_8 (n, v1, v2) -> f6 n v1 v2
  | Coq_peval_bvadd_graph_equation_9 (n, _UU03c3_1, _UU03c3_2, op, t1, t2) ->
    f7 n __ _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_bvadd_graph_equation_10 (n, p0, _UU03c3_1, _UU03c3_2, op, t1, t2) ->
    f8 n p0 __ _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_bvadd_graph_equation_11 (n, _UU03c3_4, op0, t0) ->
    f9 n __ _UU03c3_4 op0 t0
  | Coq_peval_bvadd_graph_equation_12 (n, p0, _UU03c3_4, op0, t0) ->
    f10 n p0 __ _UU03c3_4 op0 t0
  | Coq_peval_bvadd_graph_equation_13 (n, _UU03c3_1, _UU03c3_2, op, t1, t3,
                                       l, lIn) ->
    f11 n _UU03c3_1 _UU03c3_2 op t1 t3 l lIn
  | Coq_peval_bvadd_graph_equation_14 (n, _UU03c3_1, _UU03c3_2, op, t1, t3) ->
    f12 n _UU03c3_1 _UU03c3_2 op t1 t3 __
  | Coq_peval_bvadd_graph_equation_15 (n, _UU03c3_1, _UU03c3_2, op, t1, t3, p0) ->
    f13 n _UU03c3_1 _UU03c3_2 op t1 t3 p0 __
  | Coq_peval_bvadd_graph_equation_16 (n, _UU03c3_1, _UU03c3_2, op, t1, t3,
                                       _UU03c3_3, _UU03c3_4, op0, t2, t4) ->
    f14 n _UU03c3_1 _UU03c3_2 op t1 t3 _UU03c3_3 _UU03c3_4 op0 t2 t4
  | Coq_peval_bvadd_graph_equation_17 (n, _UU03c3_1, _UU03c3_2, op, t1, t3,
                                       _UU03c3_6, op1, t0) ->
    f15 n _UU03c3_1 _UU03c3_2 op t1 t3 _UU03c3_6 op1 t0
  | Coq_peval_bvadd_graph_equation_18 (n, _UU03c3_4, op0, t0, l, lIn) ->
    f16 n _UU03c3_4 op0 t0 l lIn
  | Coq_peval_bvadd_graph_equation_19 (n, _UU03c3_4, op0, t0) ->
    f17 n _UU03c3_4 op0 t0 __
  | Coq_peval_bvadd_graph_equation_20 (n, _UU03c3_4, op0, t0, p0) ->
    f18 n _UU03c3_4 op0 t0 p0 __
  | Coq_peval_bvadd_graph_equation_21 (n, _UU03c3_4, op0, t0, _UU03c3_1,
                                       _UU03c3_2, op, t1, t2) ->
    f19 n _UU03c3_4 op0 t0 _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_bvadd_graph_equation_22 (n, _UU03c3_4, op0, t0, _UU03c3_5, op1,
                                       t1) ->
    f20 n _UU03c3_4 op0 t0 _UU03c3_5 op1 t1

  (** val peval_bvadd_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> coq_Term -> peval_bvadd_graph **)

  let peval_bvadd_graph_correct _ n t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      (match t2 with
       | Coq_term_var (l0, _, lIn0) ->
         Coq_peval_bvadd_graph_equation_1 (n, l, lIn, l0, lIn0)
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | N0 -> Coq_peval_bvadd_graph_equation_2 (n, l, lIn)
          | Npos p -> Coq_peval_bvadd_graph_equation_3 (n, l, lIn, p))
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         Coq_peval_bvadd_graph_equation_4 (n, l, lIn, _UU03c3_1, _UU03c3_2,
           op, t3, t4)
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_peval_bvadd_graph_equation_5 (n, l, lIn, _UU03c3_1, op, t0)
       | _ -> assert false (* absurd case *))
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         (match Obj.magic v with
          | N0 -> Coq_peval_bvadd_graph_equation_6 (n, l, lIn)
          | Npos p -> Coq_peval_bvadd_graph_equation_7 (n, p, l, lIn))
       | Coq_term_val (_, v0) -> Coq_peval_bvadd_graph_equation_8 (n, v, v0)
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         (match Obj.magic v with
          | N0 ->
            Coq_peval_bvadd_graph_equation_9 (n, _UU03c3_1, _UU03c3_2, op,
              t3, t4)
          | Npos p ->
            Coq_peval_bvadd_graph_equation_10 (n, p, _UU03c3_1, _UU03c3_2,
              op, t3, t4))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         (match Obj.magic v with
          | N0 -> Coq_peval_bvadd_graph_equation_11 (n, _UU03c3_1, op, t0)
          | Npos p ->
            Coq_peval_bvadd_graph_equation_12 (n, p, _UU03c3_1, op, t0))
       | _ -> assert false (* absurd case *))
    | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_peval_bvadd_graph_equation_13 (n, _UU03c3_1, _UU03c3_2, op, t3,
           t4, l, lIn)
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | N0 ->
            Coq_peval_bvadd_graph_equation_14 (n, _UU03c3_1, _UU03c3_2, op,
              t3, t4)
          | Npos p ->
            Coq_peval_bvadd_graph_equation_15 (n, _UU03c3_1, _UU03c3_2, op,
              t3, t4, p))
       | Coq_term_binop (_UU03c3_3, _UU03c3_4, _, op0, t5, t6) ->
         Coq_peval_bvadd_graph_equation_16 (n, _UU03c3_1, _UU03c3_2, op, t3,
           t4, _UU03c3_3, _UU03c3_4, op0, t5, t6)
       | Coq_term_unop (_UU03c3_3, _, op0, t0) ->
         Coq_peval_bvadd_graph_equation_17 (n, _UU03c3_1, _UU03c3_2, op, t3,
           t4, _UU03c3_3, op0, t0)
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_peval_bvadd_graph_equation_18 (n, _UU03c3_1, op, t0, l, lIn)
       | Coq_term_val (_, v) ->
         (match Obj.magic v with
          | N0 -> Coq_peval_bvadd_graph_equation_19 (n, _UU03c3_1, op, t0)
          | Npos p ->
            Coq_peval_bvadd_graph_equation_20 (n, _UU03c3_1, op, t0, p))
       | Coq_term_binop (_UU03c3_2, _UU03c3_3, _, op0, t3, t4) ->
         Coq_peval_bvadd_graph_equation_21 (n, _UU03c3_1, op, t0, _UU03c3_2,
           _UU03c3_3, op0, t3, t4)
       | Coq_term_unop (_UU03c3_2, _, op0, t3) ->
         Coq_peval_bvadd_graph_equation_22 (n, _UU03c3_1, op, t0, _UU03c3_2,
           op0, t3)
       | _ -> assert false (* absurd case *))
    | _ -> assert false (* absurd case *)

  (** val peval_bvadd_elim :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __ ->
      'a1) -> (nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> positive -> __ -> 'a1) -> (nat ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
      -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> __ -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
      (nat -> positive -> __ -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
      -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      positive -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
      -> coq_Term -> coq_Term -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> positive -> __ ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat ->
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
      (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty
      -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> coq_Term -> coq_Term
      -> 'a1 **)

  let peval_bvadd_elim _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 n t1 t2 =
    match peval_bvadd_graph_correct _UU03a3_ n t1 t2 with
    | Coq_peval_bvadd_graph_equation_1 (n0, l, lIn, l0, lIn0) ->
      f n0 l lIn l0 lIn0
    | Coq_peval_bvadd_graph_equation_2 (n0, l, lIn) -> f0 n0 l lIn __
    | Coq_peval_bvadd_graph_equation_3 (n0, l, lIn, p) -> f1 n0 l lIn p __
    | Coq_peval_bvadd_graph_equation_4 (n0, l, lIn, _UU03c3_1, _UU03c3_2, op,
                                        t3, t4) ->
      f2 n0 l lIn _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_bvadd_graph_equation_5 (n0, l, lIn, _UU03c3_4, op0, t0) ->
      f3 n0 l lIn _UU03c3_4 op0 t0
    | Coq_peval_bvadd_graph_equation_6 (n0, l, lIn) -> f4 n0 __ l lIn
    | Coq_peval_bvadd_graph_equation_7 (n0, p, l, lIn) -> f5 n0 p __ l lIn
    | Coq_peval_bvadd_graph_equation_8 (n0, v1, v2) -> f6 n0 v1 v2
    | Coq_peval_bvadd_graph_equation_9 (n0, _UU03c3_1, _UU03c3_2, op, t3, t4) ->
      f7 n0 __ _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_bvadd_graph_equation_10 (n0, p, _UU03c3_1, _UU03c3_2, op, t3,
                                         t4) ->
      f8 n0 p __ _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_bvadd_graph_equation_11 (n0, _UU03c3_4, op0, t0) ->
      f9 n0 __ _UU03c3_4 op0 t0
    | Coq_peval_bvadd_graph_equation_12 (n0, p, _UU03c3_4, op0, t0) ->
      f10 n0 p __ _UU03c3_4 op0 t0
    | Coq_peval_bvadd_graph_equation_13 (n0, _UU03c3_1, _UU03c3_2, op, t3,
                                         t4, l, lIn) ->
      f11 n0 _UU03c3_1 _UU03c3_2 op t3 t4 l lIn
    | Coq_peval_bvadd_graph_equation_14 (n0, _UU03c3_1, _UU03c3_2, op, t3, t4) ->
      f12 n0 _UU03c3_1 _UU03c3_2 op t3 t4 __
    | Coq_peval_bvadd_graph_equation_15 (n0, _UU03c3_1, _UU03c3_2, op, t3,
                                         t4, p) ->
      f13 n0 _UU03c3_1 _UU03c3_2 op t3 t4 p __
    | Coq_peval_bvadd_graph_equation_16 (n0, _UU03c3_1, _UU03c3_2, op, t3,
                                         t4, _UU03c3_3, _UU03c3_4, op0, t5, t6) ->
      f14 n0 _UU03c3_1 _UU03c3_2 op t3 t4 _UU03c3_3 _UU03c3_4 op0 t5 t6
    | Coq_peval_bvadd_graph_equation_17 (n0, _UU03c3_1, _UU03c3_2, op, t3,
                                         t4, _UU03c3_6, op1, t0) ->
      f15 n0 _UU03c3_1 _UU03c3_2 op t3 t4 _UU03c3_6 op1 t0
    | Coq_peval_bvadd_graph_equation_18 (n0, _UU03c3_4, op0, t0, l, lIn) ->
      f16 n0 _UU03c3_4 op0 t0 l lIn
    | Coq_peval_bvadd_graph_equation_19 (n0, _UU03c3_4, op0, t0) ->
      f17 n0 _UU03c3_4 op0 t0 __
    | Coq_peval_bvadd_graph_equation_20 (n0, _UU03c3_4, op0, t0, p) ->
      f18 n0 _UU03c3_4 op0 t0 p __
    | Coq_peval_bvadd_graph_equation_21 (n0, _UU03c3_4, op0, t0, _UU03c3_1,
                                         _UU03c3_2, op, t3, t4) ->
      f19 n0 _UU03c3_4 op0 t0 _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_bvadd_graph_equation_22 (n0, _UU03c3_4, op0, t0, _UU03c3_5,
                                         op1, t3) ->
      f20 n0 _UU03c3_4 op0 t0 _UU03c3_5 op1 t3

  (** val coq_FunctionalElimination_peval_bvadd :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __ ->
      __) -> (nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> positive -> __ -> __) -> (nat ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
      -> coq_Term -> coq_Term -> __) -> (nat -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> __ -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
      (nat -> positive -> __ -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Val ->
      Coq_ty.coq_Val -> __) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
      -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> positive
      -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> __) -> (nat -> __ -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> positive -> __ ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __ -> __) -> (nat ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> positive -> __ -> __) -> (nat -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> __) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> __ -> __) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> positive -> __ -> __) -> (nat ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
      (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty
      -> Coq_uop.coq_UnOp -> coq_Term -> __) -> nat -> coq_Term -> coq_Term
      -> __ **)

  let coq_FunctionalElimination_peval_bvadd =
    peval_bvadd_elim

  (** val coq_FunctionalInduction_peval_bvadd :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_Term -> coq_Term -> coq_Term) coq_FunctionalInduction **)

  let coq_FunctionalInduction_peval_bvadd _UU03a3_ =
    Obj.magic peval_bvadd_graph_correct _UU03a3_

  (** val peval_bvand_val_default :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term **)

  let peval_bvand_val_default _ m t0 v =
    let z = Coq_bv.zero m in
    (match eq_dec (Obj.magic Coq_bv.eqdec_bv m) (Obj.magic z) v with
     | Coq_left -> Coq_term_val ((Coq_ty.Coq_bvec m), (Obj.magic z))
     | Coq_right ->
       (match eq_dec (Obj.magic Coq_bv.eqdec_bv m) (Obj.magic Coq_bv.ones m) v with
        | Coq_left -> t0
        | Coq_right ->
          Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
            (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvand m), t0, (Coq_term_val
            ((Coq_ty.Coq_bvec m), v)))))

  (** val peval_bvand_bvapp_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term **)

  let peval_bvand_bvapp_val _ peval_bvand_val0 m1 m2 t1 t2 v =
    let Coq_bv.Coq_isapp (v1, v2) = Coq_bv.appView m1 m2 (Obj.magic v) in
    Coq_term_binop ((Coq_ty.Coq_bvec m1), (Coq_ty.Coq_bvec m2),
    (Coq_ty.Coq_bvec (add m1 m2)), (Coq_bop.Coq_bvapp (m1, m2)),
    (Obj.magic peval_bvand_val0 m1 t1 v1),
    (Obj.magic peval_bvand_val0 m2 t2 v2))

  (** val peval_bvand_bvcons_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term **)

  let peval_bvand_bvcons_val _UU03a3_ peval_bvand_val0 m t1 t2 v =
    let Coq_bv.Coq_cvcons (v1, v2) = Obj.magic Coq_bv.view (S m) v in
    Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec (S
    m)), (Coq_bop.Coq_bvcons m), (peval_and_val _UU03a3_ t1 (Obj.magic v1)),
    (Obj.magic peval_bvand_val0 m t2 v2))

  (** val peval_bvand_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term **)

  let rec peval_bvand_val _UU03a3_ m t0 v =
    match t0 with
    | Coq_term_var (l, _, lIn) ->
      peval_bvand_val_default _UU03a3_ m (Coq_term_var (l, (Coq_ty.Coq_bvec
        m), lIn)) v
    | Coq_term_val (_, v0) ->
      Coq_term_val ((Coq_ty.Coq_bvec m), (Obj.magic Coq_bv.coq_land m v0 v))
    | Coq_term_binop (_, _, _, op, t1, t2) ->
      (match op with
       | Coq_bop.Coq_shiftr (_, n) ->
         peval_bvand_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftr
           (m, n)), t1, t2)) v
       | Coq_bop.Coq_shiftl (_, n) ->
         peval_bvand_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftl
           (m, n)), t1, t2)) v
       | Coq_bop.Coq_bvadd _ ->
         peval_bvand_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvadd
           m), t1, t2)) v
       | Coq_bop.Coq_bvsub _ ->
         peval_bvand_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvsub
           m), t1, t2)) v
       | Coq_bop.Coq_bvmul _ ->
         peval_bvand_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvmul
           m), t1, t2)) v
       | Coq_bop.Coq_bvand _ ->
         peval_bvand_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvand
           m), t1, t2)) v
       | Coq_bop.Coq_bvor _ ->
         peval_bvand_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvor
           m), t1, t2)) v
       | Coq_bop.Coq_bvxor _ ->
         peval_bvand_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvxor
           m), t1, t2)) v
       | Coq_bop.Coq_bvapp (m0, n) ->
         peval_bvand_bvapp_val _UU03a3_ (peval_bvand_val _UU03a3_) m0 n t1 t2
           v
       | Coq_bop.Coq_bvcons m0 ->
         peval_bvand_bvcons_val _UU03a3_ (peval_bvand_val _UU03a3_) m0 t1 t2 v
       | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
         peval_bvand_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec l), (Coq_ty.Coq_bvec m),
           (Coq_bop.Coq_update_vector_subrange (m, s, l)), t1, t2)) v
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t1) ->
      peval_bvand_val_default _UU03a3_ m (Coq_term_unop (_UU03c3_1,
        (Coq_ty.Coq_bvec m), op, t1)) v
    | _ -> assert false (* absurd case *)

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

  (** val peval_bvand_val_graph_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term -> peval_bvand_val_graph -> 'a1 **)

  let peval_bvand_val_graph_rect _ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 _ _ _ _ = function
  | Coq_peval_bvand_val_graph_equation_1 (m, l, lIn, v) -> f m l lIn v
  | Coq_peval_bvand_val_graph_equation_2 (m, v1, v2) -> f0 m v1 v2
  | Coq_peval_bvand_val_graph_equation_3 (m, n, t1, t2, v) -> f1 m n t1 t2 v
  | Coq_peval_bvand_val_graph_equation_4 (m, n0, t1, t2, v) -> f2 m n0 t1 t2 v
  | Coq_peval_bvand_val_graph_equation_5 (m, t1, t2, v) -> f3 m t1 t2 v
  | Coq_peval_bvand_val_graph_equation_6 (m, t1, t2, v) -> f4 m t1 t2 v
  | Coq_peval_bvand_val_graph_equation_7 (m, t1, t2, v) -> f5 m t1 t2 v
  | Coq_peval_bvand_val_graph_equation_8 (m, t1, t2, v) -> f6 m t1 t2 v
  | Coq_peval_bvand_val_graph_equation_9 (m, t1, t2, v) -> f7 m t1 t2 v
  | Coq_peval_bvand_val_graph_equation_10 (m, t1, t2, v) -> f8 m t1 t2 v
  | Coq_peval_bvand_val_graph_equation_11 (m2, n7, t1, t2, v) ->
    f9 m2 n7 t1 t2 v
  | Coq_peval_bvand_val_graph_equation_12 (m3, t1, t2, v) -> f10 m3 t1 t2 v
  | Coq_peval_bvand_val_graph_equation_13 (m, l, s, t1, t2, v) ->
    f11 m l s __ t1 t2 v
  | Coq_peval_bvand_val_graph_equation_14 (m, _UU03c3_4, op0, t0, v) ->
    f12 m _UU03c3_4 op0 t0 v

  (** val peval_bvand_val_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> Coq_ty.coq_Val -> peval_bvand_val_graph **)

  let peval_bvand_val_graph_correct _ m t0 v =
    match t0 with
    | Coq_term_var (l, _, lIn) ->
      Coq_peval_bvand_val_graph_equation_1 (m, l, lIn, v)
    | Coq_term_val (_, v0) -> Coq_peval_bvand_val_graph_equation_2 (m, v0, v)
    | Coq_term_binop (_, _, _, op, t1, t2) ->
      (match op with
       | Coq_bop.Coq_shiftr (_, n) ->
         Coq_peval_bvand_val_graph_equation_3 (m, n, t1, t2, v)
       | Coq_bop.Coq_shiftl (_, n) ->
         Coq_peval_bvand_val_graph_equation_4 (m, n, t1, t2, v)
       | Coq_bop.Coq_bvadd _ ->
         Coq_peval_bvand_val_graph_equation_5 (m, t1, t2, v)
       | Coq_bop.Coq_bvsub _ ->
         Coq_peval_bvand_val_graph_equation_6 (m, t1, t2, v)
       | Coq_bop.Coq_bvmul _ ->
         Coq_peval_bvand_val_graph_equation_7 (m, t1, t2, v)
       | Coq_bop.Coq_bvand _ ->
         Coq_peval_bvand_val_graph_equation_8 (m, t1, t2, v)
       | Coq_bop.Coq_bvor _ ->
         Coq_peval_bvand_val_graph_equation_9 (m, t1, t2, v)
       | Coq_bop.Coq_bvxor _ ->
         Coq_peval_bvand_val_graph_equation_10 (m, t1, t2, v)
       | Coq_bop.Coq_bvapp (m0, n) ->
         Coq_peval_bvand_val_graph_equation_11 (m0, n, t1, t2, v)
       | Coq_bop.Coq_bvcons m0 ->
         Coq_peval_bvand_val_graph_equation_12 (m0, t1, t2, v)
       | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
         Coq_peval_bvand_val_graph_equation_13 (m, l, s, t1, t2, v)
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t1) ->
      Coq_peval_bvand_val_graph_equation_14 (m, _UU03c3_1, op, t1, v)
    | _ -> assert false (* absurd case *)

  (** val peval_bvand_val_elim :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
      coq_Term -> Coq_ty.coq_Val -> 'a1 **)

  let peval_bvand_val_elim _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 m t0 v =
    match peval_bvand_val_graph_correct _UU03a3_ m t0 v with
    | Coq_peval_bvand_val_graph_equation_1 (m0, l, lIn, v0) -> f m0 l lIn v0
    | Coq_peval_bvand_val_graph_equation_2 (m0, v1, v2) -> f0 m0 v1 v2
    | Coq_peval_bvand_val_graph_equation_3 (m0, n, t1, t2, v0) ->
      f1 m0 n t1 t2 v0
    | Coq_peval_bvand_val_graph_equation_4 (m0, n0, t1, t2, v0) ->
      f2 m0 n0 t1 t2 v0
    | Coq_peval_bvand_val_graph_equation_5 (m0, t1, t2, v0) -> f3 m0 t1 t2 v0
    | Coq_peval_bvand_val_graph_equation_6 (m0, t1, t2, v0) -> f4 m0 t1 t2 v0
    | Coq_peval_bvand_val_graph_equation_7 (m0, t1, t2, v0) -> f5 m0 t1 t2 v0
    | Coq_peval_bvand_val_graph_equation_8 (m0, t1, t2, v0) -> f6 m0 t1 t2 v0
    | Coq_peval_bvand_val_graph_equation_9 (m0, t1, t2, v0) -> f7 m0 t1 t2 v0
    | Coq_peval_bvand_val_graph_equation_10 (m0, t1, t2, v0) -> f8 m0 t1 t2 v0
    | Coq_peval_bvand_val_graph_equation_11 (m2, n7, t1, t2, v0) ->
      f9 m2 n7 t1 t2 v0
    | Coq_peval_bvand_val_graph_equation_12 (m3, t1, t2, v0) ->
      f10 m3 t1 t2 v0
    | Coq_peval_bvand_val_graph_equation_13 (m0, l, s, t1, t2, v0) ->
      f11 m0 l s __ t1 t2 v0
    | Coq_peval_bvand_val_graph_equation_14 (m0, _UU03c3_4, op0, t1, v0) ->
      f12 m0 _UU03c3_4 op0 t1 v0

  (** val coq_FunctionalElimination_peval_bvand_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val ->
      Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
      -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
      -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
      -> __) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __)
      -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat
      -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
      -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val ->
      __) -> nat -> coq_Term -> Coq_ty.coq_Val -> __ **)

  let coq_FunctionalElimination_peval_bvand_val =
    peval_bvand_val_elim

  (** val coq_FunctionalInduction_peval_bvand_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_Term -> Coq_ty.coq_Val -> coq_Term) coq_FunctionalInduction **)

  let coq_FunctionalInduction_peval_bvand_val _UU03a3_ =
    Obj.magic peval_bvand_val_graph_correct _UU03a3_

  (** val peval_bvand :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> coq_Term -> coq_Term **)

  let peval_bvand _UU03a3_ n t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
        (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_var (l,
        (Coq_ty.Coq_bvec n), lIn)), t2)
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_val
           ((Coq_ty.Coq_bvec n), v)), (Coq_term_var (l, (Coq_ty.Coq_bvec n),
           lIn)))
       | Coq_term_val (_, v0) ->
         Coq_term_val ((Coq_ty.Coq_bvec n),
           (Obj.magic Coq_bv.coq_land n v v0))
       | Coq_term_binop (_, _, _, op, t3, t4) ->
         (match op with
          | Coq_bop.Coq_shiftr (_, n0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_shiftr (n, n0)), t3, t4)))
          | Coq_bop.Coq_shiftl (_, n0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_shiftl (n, n0)), t3, t4)))
          | Coq_bop.Coq_bvadd _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_bvadd n), t3, t4)))
          | Coq_bop.Coq_bvsub _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_bvsub n), t3, t4)))
          | Coq_bop.Coq_bvmul _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_bvmul n), t3, t4)))
          | Coq_bop.Coq_bvand _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_bvand n), t3, t4)))
          | Coq_bop.Coq_bvor _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor
              n), t3, t4)))
          | Coq_bop.Coq_bvxor _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_bvxor n), t3, t4)))
          | Coq_bop.Coq_bvapp (m, n0) ->
            peval_bvand_bvapp_val _UU03a3_ (peval_bvand_val _UU03a3_) m n0 t3
              t4 v
          | Coq_bop.Coq_bvcons m ->
            peval_bvand_bvcons_val _UU03a3_ (peval_bvand_val _UU03a3_) m t3
              t4 v
          | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec l), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_update_vector_subrange (n, s, l)), t3, t4)))
          | _ -> assert false (* absurd case *))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_val
           ((Coq_ty.Coq_bvec n), v)), (Coq_term_unop (_UU03c3_1,
           (Coq_ty.Coq_bvec n), op, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_binop (_, _, _, op, t3, t4) ->
      (match op with
       | Coq_bop.Coq_shiftr (_, n0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_shiftr (n, n0)), t3, t4)), t2)
       | Coq_bop.Coq_shiftl (_, n0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_shiftl (n, n0)), t3, t4)), t2)
       | Coq_bop.Coq_bvadd _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvadd n), t3, t4)), t2)
       | Coq_bop.Coq_bvsub _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvsub n), t3, t4)), t2)
       | Coq_bop.Coq_bvmul _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvmul n), t3, t4)), t2)
       | Coq_bop.Coq_bvand _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvand n), t3, t4)), t2)
       | Coq_bop.Coq_bvor _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvor n), t3, t4)), t2)
       | Coq_bop.Coq_bvxor _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvxor n), t3, t4)), t2)
       | Coq_bop.Coq_bvapp (m, n0) ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (add m n0)), (Coq_ty.Coq_bvec
              (add m n0)), (Coq_ty.Coq_bvec (add m n0)), (Coq_bop.Coq_bvand
              (add m n0)), (Coq_term_binop ((Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec (add m n0)),
              (Coq_bop.Coq_bvapp (m, n0)), t3, t4)), (Coq_term_var (l,
              (Coq_ty.Coq_bvec (add m n0)), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvand_bvapp_val _UU03a3_ (peval_bvand_val _UU03a3_) m n0 t3
              t4 v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (add m n0)), (Coq_ty.Coq_bvec
              (add m n0)), (Coq_ty.Coq_bvec (add m n0)), (Coq_bop.Coq_bvand
              (add m n0)), (Coq_term_binop ((Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec (add m n0)),
              (Coq_bop.Coq_bvapp (m, n0)), t3, t4)), (Coq_term_binop
              (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec (add m n0)), op0, t5,
              t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (add m n0)), (Coq_ty.Coq_bvec
              (add m n0)), (Coq_ty.Coq_bvec (add m n0)), (Coq_bop.Coq_bvand
              (add m n0)), (Coq_term_binop ((Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec (add m n0)),
              (Coq_bop.Coq_bvapp (m, n0)), t3, t4)), (Coq_term_unop
              (_UU03c3_1, (Coq_ty.Coq_bvec (add m n0)), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvcons m ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (S m)), (Coq_ty.Coq_bvec (S m)),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvand (S m)),
              (Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvcons m), t3, t4)),
              (Coq_term_var (l, (Coq_ty.Coq_bvec (S m)), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvand_bvcons_val _UU03a3_ (peval_bvand_val _UU03a3_) m t3
              t4 v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (S m)), (Coq_ty.Coq_bvec (S m)),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvand (S m)),
              (Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvcons m), t3, t4)),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec (S m)),
              op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (S m)), (Coq_ty.Coq_bvec (S m)),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvand (S m)),
              (Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvcons m), t3, t4)),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec (S m)), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec l), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_update_vector_subrange (n, s, l)), t3, t4)), t2)
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
        (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvand n), (Coq_term_unop
        (_UU03c3_1, (Coq_ty.Coq_bvec n), op, t0)), t2)
    | _ -> assert false (* absurd case *)

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

  (** val peval_bvand_graph_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
      'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> 'a1)
      -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
      -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
      coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
      coq_Term -> coq_Term -> peval_bvand_graph -> 'a1 **)

  let peval_bvand_graph_rect _ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 _ _ _ _ = function
  | Coq_peval_bvand_graph_equation_1 (n, l, lIn, t2) -> f n l lIn t2
  | Coq_peval_bvand_graph_equation_2 (n, v, l, lIn) -> f0 n v l lIn
  | Coq_peval_bvand_graph_equation_3 (n, v1, v2) -> f1 n v1 v2
  | Coq_peval_bvand_graph_equation_4 (n, v, n0, t1, t2) -> f2 n v n0 t1 t2
  | Coq_peval_bvand_graph_equation_5 (n, v, n1, t1, t2) -> f3 n v n1 t1 t2
  | Coq_peval_bvand_graph_equation_6 (n, v, t1, t2) -> f4 n v t1 t2
  | Coq_peval_bvand_graph_equation_7 (n, v, t1, t2) -> f5 n v t1 t2
  | Coq_peval_bvand_graph_equation_8 (n, v, t1, t2) -> f6 n v t1 t2
  | Coq_peval_bvand_graph_equation_9 (n, v, t1, t2) -> f7 n v t1 t2
  | Coq_peval_bvand_graph_equation_10 (n, v, t1, t2) -> f8 n v t1 t2
  | Coq_peval_bvand_graph_equation_11 (n, v, t1, t2) -> f9 n v t1 t2
  | Coq_peval_bvand_graph_equation_12 (m1, n8, v, t1, t2) -> f10 m1 n8 v t1 t2
  | Coq_peval_bvand_graph_equation_13 (m2, v, t1, t2) -> f11 m2 v t1 t2
  | Coq_peval_bvand_graph_equation_14 (n, v, l, s, t1, t2) ->
    f12 n v l s __ t1 t2
  | Coq_peval_bvand_graph_equation_15 (n, v, _UU03c3_4, op0, t0) ->
    f13 n v _UU03c3_4 op0 t0
  | Coq_peval_bvand_graph_equation_16 (n, n0, t1, t3, t2) -> f14 n n0 t1 t3 t2
  | Coq_peval_bvand_graph_equation_17 (n, n1, t1, t3, t2) -> f15 n n1 t1 t3 t2
  | Coq_peval_bvand_graph_equation_18 (n, t1, t3, t2) -> f16 n t1 t3 t2
  | Coq_peval_bvand_graph_equation_19 (n, t1, t3, t2) -> f17 n t1 t3 t2
  | Coq_peval_bvand_graph_equation_20 (n, t1, t3, t2) -> f18 n t1 t3 t2
  | Coq_peval_bvand_graph_equation_21 (n, t1, t3, t2) -> f19 n t1 t3 t2
  | Coq_peval_bvand_graph_equation_22 (n, t1, t3, t2) -> f20 n t1 t3 t2
  | Coq_peval_bvand_graph_equation_23 (n, t1, t3, t2) -> f21 n t1 t3 t2
  | Coq_peval_bvand_graph_equation_24 (m1, n8, t1, t3, l, lIn) ->
    f22 m1 n8 t1 t3 l lIn
  | Coq_peval_bvand_graph_equation_25 (m1, n8, t1, t2, v) -> f23 m1 n8 t1 t2 v
  | Coq_peval_bvand_graph_equation_26 (m1, n8, t1, t3, _UU03c3_1, _UU03c3_2,
                                       op, t2, t4) ->
    f24 m1 n8 t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvand_graph_equation_27 (m1, n8, t1, t3, _UU03c3_4, op0, t0) ->
    f25 m1 n8 t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvand_graph_equation_28 (m2, t1, t3, l, lIn) ->
    f26 m2 t1 t3 l lIn
  | Coq_peval_bvand_graph_equation_29 (m2, t1, t2, v) -> f27 m2 t1 t2 v
  | Coq_peval_bvand_graph_equation_30 (m2, t1, t3, _UU03c3_1, _UU03c3_2, op,
                                       t2, t4) ->
    f28 m2 t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvand_graph_equation_31 (m2, t1, t3, _UU03c3_4, op0, t0) ->
    f29 m2 t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvand_graph_equation_32 (n, l, s, t1, t3, t2) ->
    f30 n l s __ t1 t3 t2
  | Coq_peval_bvand_graph_equation_33 (n, _UU03c3_4, op0, t0, t2) ->
    f31 n _UU03c3_4 op0 t0 t2

  (** val peval_bvand_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> coq_Term -> peval_bvand_graph **)

  let peval_bvand_graph_correct _ n t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      Coq_peval_bvand_graph_equation_1 (n, l, lIn, t2)
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_peval_bvand_graph_equation_2 (n, v, l, lIn)
       | Coq_term_val (_, v0) -> Coq_peval_bvand_graph_equation_3 (n, v, v0)
       | Coq_term_binop (_, _, _, op, t3, t4) ->
         (match op with
          | Coq_bop.Coq_shiftr (_, n0) ->
            Coq_peval_bvand_graph_equation_4 (n, v, n0, t3, t4)
          | Coq_bop.Coq_shiftl (_, n0) ->
            Coq_peval_bvand_graph_equation_5 (n, v, n0, t3, t4)
          | Coq_bop.Coq_bvadd _ ->
            Coq_peval_bvand_graph_equation_6 (n, v, t3, t4)
          | Coq_bop.Coq_bvsub _ ->
            Coq_peval_bvand_graph_equation_7 (n, v, t3, t4)
          | Coq_bop.Coq_bvmul _ ->
            Coq_peval_bvand_graph_equation_8 (n, v, t3, t4)
          | Coq_bop.Coq_bvand _ ->
            Coq_peval_bvand_graph_equation_9 (n, v, t3, t4)
          | Coq_bop.Coq_bvor _ ->
            Coq_peval_bvand_graph_equation_10 (n, v, t3, t4)
          | Coq_bop.Coq_bvxor _ ->
            Coq_peval_bvand_graph_equation_11 (n, v, t3, t4)
          | Coq_bop.Coq_bvapp (m, n0) ->
            Coq_peval_bvand_graph_equation_12 (m, n0, v, t3, t4)
          | Coq_bop.Coq_bvcons m ->
            Coq_peval_bvand_graph_equation_13 (m, v, t3, t4)
          | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
            Coq_peval_bvand_graph_equation_14 (n, v, l, s, t3, t4)
          | _ -> assert false (* absurd case *))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_peval_bvand_graph_equation_15 (n, v, _UU03c3_1, op, t0)
       | _ -> assert false (* absurd case *))
    | Coq_term_binop (_, _, _, op, t3, t4) ->
      (match op with
       | Coq_bop.Coq_shiftr (_, n0) ->
         Coq_peval_bvand_graph_equation_16 (n, n0, t3, t4, t2)
       | Coq_bop.Coq_shiftl (_, n0) ->
         Coq_peval_bvand_graph_equation_17 (n, n0, t3, t4, t2)
       | Coq_bop.Coq_bvadd _ ->
         Coq_peval_bvand_graph_equation_18 (n, t3, t4, t2)
       | Coq_bop.Coq_bvsub _ ->
         Coq_peval_bvand_graph_equation_19 (n, t3, t4, t2)
       | Coq_bop.Coq_bvmul _ ->
         Coq_peval_bvand_graph_equation_20 (n, t3, t4, t2)
       | Coq_bop.Coq_bvand _ ->
         Coq_peval_bvand_graph_equation_21 (n, t3, t4, t2)
       | Coq_bop.Coq_bvor _ ->
         Coq_peval_bvand_graph_equation_22 (n, t3, t4, t2)
       | Coq_bop.Coq_bvxor _ ->
         Coq_peval_bvand_graph_equation_23 (n, t3, t4, t2)
       | Coq_bop.Coq_bvapp (m, n0) ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvand_graph_equation_24 (m, n0, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvand_graph_equation_25 (m, n0, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvand_graph_equation_26 (m, n0, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvand_graph_equation_27 (m, n0, t3, t4, _UU03c3_1, op0,
              t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvcons m ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvand_graph_equation_28 (m, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvand_graph_equation_29 (m, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvand_graph_equation_30 (m, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvand_graph_equation_31 (m, t3, t4, _UU03c3_1, op0, t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
         Coq_peval_bvand_graph_equation_32 (n, l, s, t3, t4, t2)
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      Coq_peval_bvand_graph_equation_33 (n, _UU03c3_1, op, t0, t2)
    | _ -> assert false (* absurd case *)

  (** val peval_bvand_elim :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
      'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> 'a1)
      -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
      -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
      coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
      coq_Term -> 'a1 **)

  let peval_bvand_elim _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 n t1 t2 =
    match peval_bvand_graph_correct _UU03a3_ n t1 t2 with
    | Coq_peval_bvand_graph_equation_1 (n0, l, lIn, t3) -> f n0 l lIn t3
    | Coq_peval_bvand_graph_equation_2 (n0, v, l, lIn) -> f0 n0 v l lIn
    | Coq_peval_bvand_graph_equation_3 (n0, v1, v2) -> f1 n0 v1 v2
    | Coq_peval_bvand_graph_equation_4 (n0, v, n1, t3, t4) -> f2 n0 v n1 t3 t4
    | Coq_peval_bvand_graph_equation_5 (n0, v, n1, t3, t4) -> f3 n0 v n1 t3 t4
    | Coq_peval_bvand_graph_equation_6 (n0, v, t3, t4) -> f4 n0 v t3 t4
    | Coq_peval_bvand_graph_equation_7 (n0, v, t3, t4) -> f5 n0 v t3 t4
    | Coq_peval_bvand_graph_equation_8 (n0, v, t3, t4) -> f6 n0 v t3 t4
    | Coq_peval_bvand_graph_equation_9 (n0, v, t3, t4) -> f7 n0 v t3 t4
    | Coq_peval_bvand_graph_equation_10 (n0, v, t3, t4) -> f8 n0 v t3 t4
    | Coq_peval_bvand_graph_equation_11 (n0, v, t3, t4) -> f9 n0 v t3 t4
    | Coq_peval_bvand_graph_equation_12 (m1, n8, v, t3, t4) ->
      f10 m1 n8 v t3 t4
    | Coq_peval_bvand_graph_equation_13 (m2, v, t3, t4) -> f11 m2 v t3 t4
    | Coq_peval_bvand_graph_equation_14 (n0, v, l, s, t3, t4) ->
      f12 n0 v l s __ t3 t4
    | Coq_peval_bvand_graph_equation_15 (n0, v, _UU03c3_4, op0, t0) ->
      f13 n0 v _UU03c3_4 op0 t0
    | Coq_peval_bvand_graph_equation_16 (n0, n1, t3, t4, t5) ->
      f14 n0 n1 t3 t4 t5
    | Coq_peval_bvand_graph_equation_17 (n0, n1, t3, t4, t5) ->
      f15 n0 n1 t3 t4 t5
    | Coq_peval_bvand_graph_equation_18 (n0, t3, t4, t5) -> f16 n0 t3 t4 t5
    | Coq_peval_bvand_graph_equation_19 (n0, t3, t4, t5) -> f17 n0 t3 t4 t5
    | Coq_peval_bvand_graph_equation_20 (n0, t3, t4, t5) -> f18 n0 t3 t4 t5
    | Coq_peval_bvand_graph_equation_21 (n0, t3, t4, t5) -> f19 n0 t3 t4 t5
    | Coq_peval_bvand_graph_equation_22 (n0, t3, t4, t5) -> f20 n0 t3 t4 t5
    | Coq_peval_bvand_graph_equation_23 (n0, t3, t4, t5) -> f21 n0 t3 t4 t5
    | Coq_peval_bvand_graph_equation_24 (m1, n8, t3, t4, l, lIn) ->
      f22 m1 n8 t3 t4 l lIn
    | Coq_peval_bvand_graph_equation_25 (m1, n8, t3, t4, v) ->
      f23 m1 n8 t3 t4 v
    | Coq_peval_bvand_graph_equation_26 (m1, n8, t3, t4, _UU03c3_1,
                                         _UU03c3_2, op, t5, t6) ->
      f24 m1 n8 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvand_graph_equation_27 (m1, n8, t3, t4, _UU03c3_4, op0, t0) ->
      f25 m1 n8 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvand_graph_equation_28 (m2, t3, t4, l, lIn) ->
      f26 m2 t3 t4 l lIn
    | Coq_peval_bvand_graph_equation_29 (m2, t3, t4, v) -> f27 m2 t3 t4 v
    | Coq_peval_bvand_graph_equation_30 (m2, t3, t4, _UU03c3_1, _UU03c3_2,
                                         op, t5, t6) ->
      f28 m2 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvand_graph_equation_31 (m2, t3, t4, _UU03c3_4, op0, t0) ->
      f29 m2 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvand_graph_equation_32 (n0, l, s, t3, t4, t5) ->
      f30 n0 l s __ t3 t4 t5
    | Coq_peval_bvand_graph_equation_33 (n0, _UU03c3_4, op0, t0, t3) ->
      f31 n0 _UU03c3_4 op0 t0 t3

  (** val coq_FunctionalElimination_peval_bvand :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_LVar
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
      -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) -> (nat ->
      Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> __) -> (nat ->
      Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> __) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val
      -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
      coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
      __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val
      -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> nat -> nat
      -> __ -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term
      -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
      coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term
      -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __)
      -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat -> nat -> __ ->
      coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> __) -> nat -> coq_Term ->
      coq_Term -> __ **)

  let coq_FunctionalElimination_peval_bvand =
    peval_bvand_elim

  (** val coq_FunctionalInduction_peval_bvand :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_Term -> coq_Term -> coq_Term) coq_FunctionalInduction **)

  let coq_FunctionalInduction_peval_bvand _UU03a3_ =
    Obj.magic peval_bvand_graph_correct _UU03a3_

  (** val peval_bvor_val_default :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term **)

  let peval_bvor_val_default _ m t0 v =
    let o = Coq_bv.ones m in
    (match eq_dec (Obj.magic Coq_bv.eqdec_bv m) (Obj.magic o) v with
     | Coq_left -> Coq_term_val ((Coq_ty.Coq_bvec m), (Obj.magic o))
     | Coq_right ->
       (match eq_dec (Obj.magic Coq_bv.eqdec_bv m) (Obj.magic Coq_bv.zero m) v with
        | Coq_left -> t0
        | Coq_right ->
          Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
            (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvor m), t0, (Coq_term_val
            ((Coq_ty.Coq_bvec m), v)))))

  (** val peval_bvor_bvapp_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term **)

  let peval_bvor_bvapp_val _ peval_bvor_val0 m1 m2 t1 t2 v =
    let Coq_bv.Coq_isapp (v1, v2) = Coq_bv.appView m1 m2 (Obj.magic v) in
    Coq_term_binop ((Coq_ty.Coq_bvec m1), (Coq_ty.Coq_bvec m2),
    (Coq_ty.Coq_bvec (add m1 m2)), (Coq_bop.Coq_bvapp (m1, m2)),
    (Obj.magic peval_bvor_val0 m1 t1 v1),
    (Obj.magic peval_bvor_val0 m2 t2 v2))

  (** val peval_bvor_bvcons_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term **)

  let peval_bvor_bvcons_val _UU03a3_ peval_bvor_val0 m t1 t2 v =
    let Coq_bv.Coq_cvcons (v1, v2) = Obj.magic Coq_bv.view (S m) v in
    Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec (S
    m)), (Coq_bop.Coq_bvcons m), (peval_or_val _UU03a3_ t1 (Obj.magic v1)),
    (Obj.magic peval_bvor_val0 m t2 v2))

  (** val peval_bvor_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term **)

  let rec peval_bvor_val _UU03a3_ m t0 v =
    match t0 with
    | Coq_term_var (l, _, lIn) ->
      peval_bvor_val_default _UU03a3_ m (Coq_term_var (l, (Coq_ty.Coq_bvec
        m), lIn)) v
    | Coq_term_val (_, v0) ->
      Coq_term_val ((Coq_ty.Coq_bvec m), (Obj.magic Coq_bv.coq_lor m v0 v))
    | Coq_term_binop (_, _, _, op, t1, t2) ->
      (match op with
       | Coq_bop.Coq_shiftr (_, n) ->
         peval_bvor_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftr
           (m, n)), t1, t2)) v
       | Coq_bop.Coq_shiftl (_, n) ->
         peval_bvor_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftl
           (m, n)), t1, t2)) v
       | Coq_bop.Coq_bvadd _ ->
         peval_bvor_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvadd
           m), t1, t2)) v
       | Coq_bop.Coq_bvsub _ ->
         peval_bvor_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvsub
           m), t1, t2)) v
       | Coq_bop.Coq_bvmul _ ->
         peval_bvor_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvmul
           m), t1, t2)) v
       | Coq_bop.Coq_bvand _ ->
         peval_bvor_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvand
           m), t1, t2)) v
       | Coq_bop.Coq_bvor _ ->
         peval_bvor_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvor
           m), t1, t2)) v
       | Coq_bop.Coq_bvxor _ ->
         peval_bvor_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvxor
           m), t1, t2)) v
       | Coq_bop.Coq_bvapp (m0, n) ->
         peval_bvor_bvapp_val _UU03a3_ (peval_bvor_val _UU03a3_) m0 n t1 t2 v
       | Coq_bop.Coq_bvcons m0 ->
         peval_bvor_bvcons_val _UU03a3_ (peval_bvor_val _UU03a3_) m0 t1 t2 v
       | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
         peval_bvor_val_default _UU03a3_ m (Coq_term_binop ((Coq_ty.Coq_bvec
           m), (Coq_ty.Coq_bvec l), (Coq_ty.Coq_bvec m),
           (Coq_bop.Coq_update_vector_subrange (m, s, l)), t1, t2)) v
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t1) ->
      peval_bvor_val_default _UU03a3_ m (Coq_term_unop (_UU03c3_1,
        (Coq_ty.Coq_bvec m), op, t1)) v
    | _ -> assert false (* absurd case *)

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

  (** val peval_bvor_val_graph_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
      coq_Term -> Coq_ty.coq_Val -> coq_Term -> peval_bvor_val_graph -> 'a1 **)

  let peval_bvor_val_graph_rect _ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 _ _ _ _ = function
  | Coq_peval_bvor_val_graph_equation_1 (m, l, lIn, v) -> f m l lIn v
  | Coq_peval_bvor_val_graph_equation_2 (m, v1, v2) -> f0 m v1 v2
  | Coq_peval_bvor_val_graph_equation_3 (m, n, t1, t2, v) -> f1 m n t1 t2 v
  | Coq_peval_bvor_val_graph_equation_4 (m, n0, t1, t2, v) -> f2 m n0 t1 t2 v
  | Coq_peval_bvor_val_graph_equation_5 (m, t1, t2, v) -> f3 m t1 t2 v
  | Coq_peval_bvor_val_graph_equation_6 (m, t1, t2, v) -> f4 m t1 t2 v
  | Coq_peval_bvor_val_graph_equation_7 (m, t1, t2, v) -> f5 m t1 t2 v
  | Coq_peval_bvor_val_graph_equation_8 (m, t1, t2, v) -> f6 m t1 t2 v
  | Coq_peval_bvor_val_graph_equation_9 (m, t1, t2, v) -> f7 m t1 t2 v
  | Coq_peval_bvor_val_graph_equation_10 (m, t1, t2, v) -> f8 m t1 t2 v
  | Coq_peval_bvor_val_graph_equation_11 (m2, n7, t1, t2, v) ->
    f9 m2 n7 t1 t2 v
  | Coq_peval_bvor_val_graph_equation_12 (m3, t1, t2, v) -> f10 m3 t1 t2 v
  | Coq_peval_bvor_val_graph_equation_13 (m, l, s, t1, t2, v) ->
    f11 m l s __ t1 t2 v
  | Coq_peval_bvor_val_graph_equation_14 (m, _UU03c3_4, op0, t0, v) ->
    f12 m _UU03c3_4 op0 t0 v

  (** val peval_bvor_val_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> Coq_ty.coq_Val -> peval_bvor_val_graph **)

  let peval_bvor_val_graph_correct _ m t0 v =
    match t0 with
    | Coq_term_var (l, _, lIn) ->
      Coq_peval_bvor_val_graph_equation_1 (m, l, lIn, v)
    | Coq_term_val (_, v0) -> Coq_peval_bvor_val_graph_equation_2 (m, v0, v)
    | Coq_term_binop (_, _, _, op, t1, t2) ->
      (match op with
       | Coq_bop.Coq_shiftr (_, n) ->
         Coq_peval_bvor_val_graph_equation_3 (m, n, t1, t2, v)
       | Coq_bop.Coq_shiftl (_, n) ->
         Coq_peval_bvor_val_graph_equation_4 (m, n, t1, t2, v)
       | Coq_bop.Coq_bvadd _ ->
         Coq_peval_bvor_val_graph_equation_5 (m, t1, t2, v)
       | Coq_bop.Coq_bvsub _ ->
         Coq_peval_bvor_val_graph_equation_6 (m, t1, t2, v)
       | Coq_bop.Coq_bvmul _ ->
         Coq_peval_bvor_val_graph_equation_7 (m, t1, t2, v)
       | Coq_bop.Coq_bvand _ ->
         Coq_peval_bvor_val_graph_equation_8 (m, t1, t2, v)
       | Coq_bop.Coq_bvor _ ->
         Coq_peval_bvor_val_graph_equation_9 (m, t1, t2, v)
       | Coq_bop.Coq_bvxor _ ->
         Coq_peval_bvor_val_graph_equation_10 (m, t1, t2, v)
       | Coq_bop.Coq_bvapp (m0, n) ->
         Coq_peval_bvor_val_graph_equation_11 (m0, n, t1, t2, v)
       | Coq_bop.Coq_bvcons m0 ->
         Coq_peval_bvor_val_graph_equation_12 (m0, t1, t2, v)
       | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
         Coq_peval_bvor_val_graph_equation_13 (m, l, s, t1, t2, v)
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t1) ->
      Coq_peval_bvor_val_graph_equation_14 (m, _UU03c3_1, op, t1, v)
    | _ -> assert false (* absurd case *)

  (** val peval_bvor_val_elim :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
      coq_Term -> Coq_ty.coq_Val -> 'a1 **)

  let peval_bvor_val_elim _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 m t0 v =
    match peval_bvor_val_graph_correct _UU03a3_ m t0 v with
    | Coq_peval_bvor_val_graph_equation_1 (m0, l, lIn, v0) -> f m0 l lIn v0
    | Coq_peval_bvor_val_graph_equation_2 (m0, v1, v2) -> f0 m0 v1 v2
    | Coq_peval_bvor_val_graph_equation_3 (m0, n, t1, t2, v0) ->
      f1 m0 n t1 t2 v0
    | Coq_peval_bvor_val_graph_equation_4 (m0, n0, t1, t2, v0) ->
      f2 m0 n0 t1 t2 v0
    | Coq_peval_bvor_val_graph_equation_5 (m0, t1, t2, v0) -> f3 m0 t1 t2 v0
    | Coq_peval_bvor_val_graph_equation_6 (m0, t1, t2, v0) -> f4 m0 t1 t2 v0
    | Coq_peval_bvor_val_graph_equation_7 (m0, t1, t2, v0) -> f5 m0 t1 t2 v0
    | Coq_peval_bvor_val_graph_equation_8 (m0, t1, t2, v0) -> f6 m0 t1 t2 v0
    | Coq_peval_bvor_val_graph_equation_9 (m0, t1, t2, v0) -> f7 m0 t1 t2 v0
    | Coq_peval_bvor_val_graph_equation_10 (m0, t1, t2, v0) -> f8 m0 t1 t2 v0
    | Coq_peval_bvor_val_graph_equation_11 (m2, n7, t1, t2, v0) ->
      f9 m2 n7 t1 t2 v0
    | Coq_peval_bvor_val_graph_equation_12 (m3, t1, t2, v0) -> f10 m3 t1 t2 v0
    | Coq_peval_bvor_val_graph_equation_13 (m0, l, s, t1, t2, v0) ->
      f11 m0 l s __ t1 t2 v0
    | Coq_peval_bvor_val_graph_equation_14 (m0, _UU03c3_4, op0, t1, v0) ->
      f12 m0 _UU03c3_4 op0 t1 v0

  (** val coq_FunctionalElimination_peval_bvor_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val ->
      Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
      -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
      -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
      -> __) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __)
      -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat
      -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
      -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val ->
      __) -> nat -> coq_Term -> Coq_ty.coq_Val -> __ **)

  let coq_FunctionalElimination_peval_bvor_val =
    peval_bvor_val_elim

  (** val coq_FunctionalInduction_peval_bvor_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_Term -> Coq_ty.coq_Val -> coq_Term) coq_FunctionalInduction **)

  let coq_FunctionalInduction_peval_bvor_val _UU03a3_ =
    Obj.magic peval_bvor_val_graph_correct _UU03a3_

  (** val peval_bvor :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> coq_Term -> coq_Term **)

  let peval_bvor _UU03a3_ n t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
        (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_var (l,
        (Coq_ty.Coq_bvec n), lIn)), t2)
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_val
           ((Coq_ty.Coq_bvec n), v)), (Coq_term_var (l, (Coq_ty.Coq_bvec n),
           lIn)))
       | Coq_term_val (_, v0) ->
         Coq_term_val ((Coq_ty.Coq_bvec n), (Obj.magic Coq_bv.coq_lor n v v0))
       | Coq_term_binop (_, _, _, op, t3, t4) ->
         (match op with
          | Coq_bop.Coq_shiftr (_, n0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_shiftr (n, n0)), t3, t4)))
          | Coq_bop.Coq_shiftl (_, n0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_shiftl (n, n0)), t3, t4)))
          | Coq_bop.Coq_bvadd _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_bvadd n), t3, t4)))
          | Coq_bop.Coq_bvsub _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_bvsub n), t3, t4)))
          | Coq_bop.Coq_bvmul _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_bvmul n), t3, t4)))
          | Coq_bop.Coq_bvand _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_bvand n), t3, t4)))
          | Coq_bop.Coq_bvor _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor
              n), t3, t4)))
          | Coq_bop.Coq_bvxor _ ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_bvxor n), t3, t4)))
          | Coq_bop.Coq_bvapp (m, n0) ->
            peval_bvor_bvapp_val _UU03a3_ (peval_bvor_val _UU03a3_) m n0 t3
              t4 v
          | Coq_bop.Coq_bvcons m ->
            peval_bvor_bvcons_val _UU03a3_ (peval_bvor_val _UU03a3_) m t3 t4 v
          | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
            Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_val
              ((Coq_ty.Coq_bvec n), v)), (Coq_term_binop ((Coq_ty.Coq_bvec
              n), (Coq_ty.Coq_bvec l), (Coq_ty.Coq_bvec n),
              (Coq_bop.Coq_update_vector_subrange (n, s, l)), t3, t4)))
          | _ -> assert false (* absurd case *))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_val
           ((Coq_ty.Coq_bvec n), v)), (Coq_term_unop (_UU03c3_1,
           (Coq_ty.Coq_bvec n), op, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_binop (_, _, _, op, t3, t4) ->
      (match op with
       | Coq_bop.Coq_shiftr (_, n0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_shiftr (n, n0)), t3, t4)), t2)
       | Coq_bop.Coq_shiftl (_, n0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_shiftl (n, n0)), t3, t4)), t2)
       | Coq_bop.Coq_bvadd _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvadd n), t3, t4)), t2)
       | Coq_bop.Coq_bvsub _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvsub n), t3, t4)), t2)
       | Coq_bop.Coq_bvmul _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvmul n), t3, t4)), t2)
       | Coq_bop.Coq_bvand _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvand n), t3, t4)), t2)
       | Coq_bop.Coq_bvor _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvor n), t3, t4)), t2)
       | Coq_bop.Coq_bvxor _ ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_bvxor n), t3, t4)), t2)
       | Coq_bop.Coq_bvapp (m, n0) ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (add m n0)), (Coq_ty.Coq_bvec
              (add m n0)), (Coq_ty.Coq_bvec (add m n0)), (Coq_bop.Coq_bvor
              (add m n0)), (Coq_term_binop ((Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec (add m n0)),
              (Coq_bop.Coq_bvapp (m, n0)), t3, t4)), (Coq_term_var (l,
              (Coq_ty.Coq_bvec (add m n0)), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvor_bvapp_val _UU03a3_ (peval_bvor_val _UU03a3_) m n0 t3
              t4 v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (add m n0)), (Coq_ty.Coq_bvec
              (add m n0)), (Coq_ty.Coq_bvec (add m n0)), (Coq_bop.Coq_bvor
              (add m n0)), (Coq_term_binop ((Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec (add m n0)),
              (Coq_bop.Coq_bvapp (m, n0)), t3, t4)), (Coq_term_binop
              (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec (add m n0)), op0, t5,
              t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (add m n0)), (Coq_ty.Coq_bvec
              (add m n0)), (Coq_ty.Coq_bvec (add m n0)), (Coq_bop.Coq_bvor
              (add m n0)), (Coq_term_binop ((Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec (add m n0)),
              (Coq_bop.Coq_bvapp (m, n0)), t3, t4)), (Coq_term_unop
              (_UU03c3_1, (Coq_ty.Coq_bvec (add m n0)), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvcons m ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (S m)), (Coq_ty.Coq_bvec (S m)),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvor (S m)),
              (Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvcons m), t3, t4)),
              (Coq_term_var (l, (Coq_ty.Coq_bvec (S m)), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvor_bvcons_val _UU03a3_ (peval_bvor_val _UU03a3_) m t3 t4 v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (S m)), (Coq_ty.Coq_bvec (S m)),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvor (S m)),
              (Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvcons m), t3, t4)),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec (S m)),
              op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (S m)), (Coq_ty.Coq_bvec (S m)),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvor (S m)),
              (Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec (S m)), (Coq_bop.Coq_bvcons m), t3, t4)),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec (S m)), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
         Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_binop
           ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec l), (Coq_ty.Coq_bvec n),
           (Coq_bop.Coq_update_vector_subrange (n, s, l)), t3, t4)), t2)
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      Coq_term_binop ((Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec n),
        (Coq_ty.Coq_bvec n), (Coq_bop.Coq_bvor n), (Coq_term_unop (_UU03c3_1,
        (Coq_ty.Coq_bvec n), op, t0)), t2)
    | _ -> assert false (* absurd case *)

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

  (** val peval_bvor_graph_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
      'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> 'a1)
      -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
      -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
      coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
      coq_Term -> coq_Term -> peval_bvor_graph -> 'a1 **)

  let peval_bvor_graph_rect _ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 _ _ _ _ = function
  | Coq_peval_bvor_graph_equation_1 (n, l, lIn, t2) -> f n l lIn t2
  | Coq_peval_bvor_graph_equation_2 (n, v, l, lIn) -> f0 n v l lIn
  | Coq_peval_bvor_graph_equation_3 (n, v1, v2) -> f1 n v1 v2
  | Coq_peval_bvor_graph_equation_4 (n, v, n0, t1, t2) -> f2 n v n0 t1 t2
  | Coq_peval_bvor_graph_equation_5 (n, v, n1, t1, t2) -> f3 n v n1 t1 t2
  | Coq_peval_bvor_graph_equation_6 (n, v, t1, t2) -> f4 n v t1 t2
  | Coq_peval_bvor_graph_equation_7 (n, v, t1, t2) -> f5 n v t1 t2
  | Coq_peval_bvor_graph_equation_8 (n, v, t1, t2) -> f6 n v t1 t2
  | Coq_peval_bvor_graph_equation_9 (n, v, t1, t2) -> f7 n v t1 t2
  | Coq_peval_bvor_graph_equation_10 (n, v, t1, t2) -> f8 n v t1 t2
  | Coq_peval_bvor_graph_equation_11 (n, v, t1, t2) -> f9 n v t1 t2
  | Coq_peval_bvor_graph_equation_12 (m1, n8, v, t1, t2) -> f10 m1 n8 v t1 t2
  | Coq_peval_bvor_graph_equation_13 (m2, v, t1, t2) -> f11 m2 v t1 t2
  | Coq_peval_bvor_graph_equation_14 (n, v, l, s, t1, t2) ->
    f12 n v l s __ t1 t2
  | Coq_peval_bvor_graph_equation_15 (n, v, _UU03c3_4, op0, t0) ->
    f13 n v _UU03c3_4 op0 t0
  | Coq_peval_bvor_graph_equation_16 (n, n0, t1, t3, t2) -> f14 n n0 t1 t3 t2
  | Coq_peval_bvor_graph_equation_17 (n, n1, t1, t3, t2) -> f15 n n1 t1 t3 t2
  | Coq_peval_bvor_graph_equation_18 (n, t1, t3, t2) -> f16 n t1 t3 t2
  | Coq_peval_bvor_graph_equation_19 (n, t1, t3, t2) -> f17 n t1 t3 t2
  | Coq_peval_bvor_graph_equation_20 (n, t1, t3, t2) -> f18 n t1 t3 t2
  | Coq_peval_bvor_graph_equation_21 (n, t1, t3, t2) -> f19 n t1 t3 t2
  | Coq_peval_bvor_graph_equation_22 (n, t1, t3, t2) -> f20 n t1 t3 t2
  | Coq_peval_bvor_graph_equation_23 (n, t1, t3, t2) -> f21 n t1 t3 t2
  | Coq_peval_bvor_graph_equation_24 (m1, n8, t1, t3, l, lIn) ->
    f22 m1 n8 t1 t3 l lIn
  | Coq_peval_bvor_graph_equation_25 (m1, n8, t1, t2, v) -> f23 m1 n8 t1 t2 v
  | Coq_peval_bvor_graph_equation_26 (m1, n8, t1, t3, _UU03c3_1, _UU03c3_2,
                                      op, t2, t4) ->
    f24 m1 n8 t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvor_graph_equation_27 (m1, n8, t1, t3, _UU03c3_4, op0, t0) ->
    f25 m1 n8 t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvor_graph_equation_28 (m2, t1, t3, l, lIn) ->
    f26 m2 t1 t3 l lIn
  | Coq_peval_bvor_graph_equation_29 (m2, t1, t2, v) -> f27 m2 t1 t2 v
  | Coq_peval_bvor_graph_equation_30 (m2, t1, t3, _UU03c3_1, _UU03c3_2, op,
                                      t2, t4) ->
    f28 m2 t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvor_graph_equation_31 (m2, t1, t3, _UU03c3_4, op0, t0) ->
    f29 m2 t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvor_graph_equation_32 (n, l, s, t1, t3, t2) ->
    f30 n l s __ t1 t3 t2
  | Coq_peval_bvor_graph_equation_33 (n, _UU03c3_4, op0, t0, t2) ->
    f31 n _UU03c3_4 op0 t0 t2

  (** val peval_bvor_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> coq_Term -> peval_bvor_graph **)

  let peval_bvor_graph_correct _ n t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      Coq_peval_bvor_graph_equation_1 (n, l, lIn, t2)
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_peval_bvor_graph_equation_2 (n, v, l, lIn)
       | Coq_term_val (_, v0) -> Coq_peval_bvor_graph_equation_3 (n, v, v0)
       | Coq_term_binop (_, _, _, op, t3, t4) ->
         (match op with
          | Coq_bop.Coq_shiftr (_, n0) ->
            Coq_peval_bvor_graph_equation_4 (n, v, n0, t3, t4)
          | Coq_bop.Coq_shiftl (_, n0) ->
            Coq_peval_bvor_graph_equation_5 (n, v, n0, t3, t4)
          | Coq_bop.Coq_bvadd _ ->
            Coq_peval_bvor_graph_equation_6 (n, v, t3, t4)
          | Coq_bop.Coq_bvsub _ ->
            Coq_peval_bvor_graph_equation_7 (n, v, t3, t4)
          | Coq_bop.Coq_bvmul _ ->
            Coq_peval_bvor_graph_equation_8 (n, v, t3, t4)
          | Coq_bop.Coq_bvand _ ->
            Coq_peval_bvor_graph_equation_9 (n, v, t3, t4)
          | Coq_bop.Coq_bvor _ ->
            Coq_peval_bvor_graph_equation_10 (n, v, t3, t4)
          | Coq_bop.Coq_bvxor _ ->
            Coq_peval_bvor_graph_equation_11 (n, v, t3, t4)
          | Coq_bop.Coq_bvapp (m, n0) ->
            Coq_peval_bvor_graph_equation_12 (m, n0, v, t3, t4)
          | Coq_bop.Coq_bvcons m ->
            Coq_peval_bvor_graph_equation_13 (m, v, t3, t4)
          | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
            Coq_peval_bvor_graph_equation_14 (n, v, l, s, t3, t4)
          | _ -> assert false (* absurd case *))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_peval_bvor_graph_equation_15 (n, v, _UU03c3_1, op, t0)
       | _ -> assert false (* absurd case *))
    | Coq_term_binop (_, _, _, op, t3, t4) ->
      (match op with
       | Coq_bop.Coq_shiftr (_, n0) ->
         Coq_peval_bvor_graph_equation_16 (n, n0, t3, t4, t2)
       | Coq_bop.Coq_shiftl (_, n0) ->
         Coq_peval_bvor_graph_equation_17 (n, n0, t3, t4, t2)
       | Coq_bop.Coq_bvadd _ ->
         Coq_peval_bvor_graph_equation_18 (n, t3, t4, t2)
       | Coq_bop.Coq_bvsub _ ->
         Coq_peval_bvor_graph_equation_19 (n, t3, t4, t2)
       | Coq_bop.Coq_bvmul _ ->
         Coq_peval_bvor_graph_equation_20 (n, t3, t4, t2)
       | Coq_bop.Coq_bvand _ ->
         Coq_peval_bvor_graph_equation_21 (n, t3, t4, t2)
       | Coq_bop.Coq_bvor _ ->
         Coq_peval_bvor_graph_equation_22 (n, t3, t4, t2)
       | Coq_bop.Coq_bvxor _ ->
         Coq_peval_bvor_graph_equation_23 (n, t3, t4, t2)
       | Coq_bop.Coq_bvapp (m, n0) ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvor_graph_equation_24 (m, n0, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvor_graph_equation_25 (m, n0, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvor_graph_equation_26 (m, n0, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvor_graph_equation_27 (m, n0, t3, t4, _UU03c3_1, op0,
              t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvcons m ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvor_graph_equation_28 (m, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvor_graph_equation_29 (m, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvor_graph_equation_30 (m, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvor_graph_equation_31 (m, t3, t4, _UU03c3_1, op0, t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
         Coq_peval_bvor_graph_equation_32 (n, l, s, t3, t4, t2)
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      Coq_peval_bvor_graph_equation_33 (n, _UU03c3_1, op, t0, t2)
    | _ -> assert false (* absurd case *)

  (** val peval_bvor_elim :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
      'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> 'a1)
      -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
      -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
      coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
      coq_Term -> 'a1 **)

  let peval_bvor_elim _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 n t1 t2 =
    match peval_bvor_graph_correct _UU03a3_ n t1 t2 with
    | Coq_peval_bvor_graph_equation_1 (n0, l, lIn, t3) -> f n0 l lIn t3
    | Coq_peval_bvor_graph_equation_2 (n0, v, l, lIn) -> f0 n0 v l lIn
    | Coq_peval_bvor_graph_equation_3 (n0, v1, v2) -> f1 n0 v1 v2
    | Coq_peval_bvor_graph_equation_4 (n0, v, n1, t3, t4) -> f2 n0 v n1 t3 t4
    | Coq_peval_bvor_graph_equation_5 (n0, v, n1, t3, t4) -> f3 n0 v n1 t3 t4
    | Coq_peval_bvor_graph_equation_6 (n0, v, t3, t4) -> f4 n0 v t3 t4
    | Coq_peval_bvor_graph_equation_7 (n0, v, t3, t4) -> f5 n0 v t3 t4
    | Coq_peval_bvor_graph_equation_8 (n0, v, t3, t4) -> f6 n0 v t3 t4
    | Coq_peval_bvor_graph_equation_9 (n0, v, t3, t4) -> f7 n0 v t3 t4
    | Coq_peval_bvor_graph_equation_10 (n0, v, t3, t4) -> f8 n0 v t3 t4
    | Coq_peval_bvor_graph_equation_11 (n0, v, t3, t4) -> f9 n0 v t3 t4
    | Coq_peval_bvor_graph_equation_12 (m1, n8, v, t3, t4) ->
      f10 m1 n8 v t3 t4
    | Coq_peval_bvor_graph_equation_13 (m2, v, t3, t4) -> f11 m2 v t3 t4
    | Coq_peval_bvor_graph_equation_14 (n0, v, l, s, t3, t4) ->
      f12 n0 v l s __ t3 t4
    | Coq_peval_bvor_graph_equation_15 (n0, v, _UU03c3_4, op0, t0) ->
      f13 n0 v _UU03c3_4 op0 t0
    | Coq_peval_bvor_graph_equation_16 (n0, n1, t3, t4, t5) ->
      f14 n0 n1 t3 t4 t5
    | Coq_peval_bvor_graph_equation_17 (n0, n1, t3, t4, t5) ->
      f15 n0 n1 t3 t4 t5
    | Coq_peval_bvor_graph_equation_18 (n0, t3, t4, t5) -> f16 n0 t3 t4 t5
    | Coq_peval_bvor_graph_equation_19 (n0, t3, t4, t5) -> f17 n0 t3 t4 t5
    | Coq_peval_bvor_graph_equation_20 (n0, t3, t4, t5) -> f18 n0 t3 t4 t5
    | Coq_peval_bvor_graph_equation_21 (n0, t3, t4, t5) -> f19 n0 t3 t4 t5
    | Coq_peval_bvor_graph_equation_22 (n0, t3, t4, t5) -> f20 n0 t3 t4 t5
    | Coq_peval_bvor_graph_equation_23 (n0, t3, t4, t5) -> f21 n0 t3 t4 t5
    | Coq_peval_bvor_graph_equation_24 (m1, n8, t3, t4, l, lIn) ->
      f22 m1 n8 t3 t4 l lIn
    | Coq_peval_bvor_graph_equation_25 (m1, n8, t3, t4, v) ->
      f23 m1 n8 t3 t4 v
    | Coq_peval_bvor_graph_equation_26 (m1, n8, t3, t4, _UU03c3_1, _UU03c3_2,
                                        op, t5, t6) ->
      f24 m1 n8 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvor_graph_equation_27 (m1, n8, t3, t4, _UU03c3_4, op0, t0) ->
      f25 m1 n8 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvor_graph_equation_28 (m2, t3, t4, l, lIn) ->
      f26 m2 t3 t4 l lIn
    | Coq_peval_bvor_graph_equation_29 (m2, t3, t4, v) -> f27 m2 t3 t4 v
    | Coq_peval_bvor_graph_equation_30 (m2, t3, t4, _UU03c3_1, _UU03c3_2, op,
                                        t5, t6) ->
      f28 m2 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvor_graph_equation_31 (m2, t3, t4, _UU03c3_4, op0, t0) ->
      f29 m2 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvor_graph_equation_32 (n0, l, s, t3, t4, t5) ->
      f30 n0 l s __ t3 t4 t5
    | Coq_peval_bvor_graph_equation_33 (n0, _UU03c3_4, op0, t0, t3) ->
      f31 n0 _UU03c3_4 op0 t0 t3

  (** val coq_FunctionalElimination_peval_bvor :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_LVar
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
      -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) -> (nat ->
      Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> __) -> (nat ->
      Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term -> __) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val
      -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
      coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
      __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
      Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val
      -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> nat -> nat
      -> __ -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term
      -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
      coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term
      -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __)
      -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat -> nat -> __ ->
      coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> __) -> nat -> coq_Term ->
      coq_Term -> __ **)

  let coq_FunctionalElimination_peval_bvor =
    peval_bvor_elim

  (** val coq_FunctionalInduction_peval_bvor :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_Term -> coq_Term -> coq_Term) coq_FunctionalInduction **)

  let coq_FunctionalInduction_peval_bvor _UU03a3_ =
    Obj.magic peval_bvor_graph_correct _UU03a3_

  (** val peval_bvapp_val_r :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> coq_Term -> Coq_ty.coq_Val -> coq_Term **)

  let peval_bvapp_val_r _ m n t1 v =
    match eq_dec nat_EqDec n O with
    | Coq_left -> t1
    | Coq_right ->
      Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
        (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)), t1,
        (Coq_term_val ((Coq_ty.Coq_bvec n), v)))

  (** val peval_bvapp :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> coq_Term -> coq_Term -> coq_Term **)

  let peval_bvapp _UU03a3_ m n t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      (match t2 with
       | Coq_term_var (l0, _, lIn0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
           (Coq_term_var (l, (Coq_ty.Coq_bvec m), lIn)), (Coq_term_var (l0,
           (Coq_ty.Coq_bvec n), lIn0)))
       | Coq_term_val (_, v) ->
         peval_bvapp_val_r _UU03a3_ m n (Coq_term_var (l, (Coq_ty.Coq_bvec
           m), lIn)) v
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
           (Coq_term_var (l, (Coq_ty.Coq_bvec m), lIn)), (Coq_term_binop
           (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n), op, t3, t4)))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
           (Coq_term_var (l, (Coq_ty.Coq_bvec m), lIn)), (Coq_term_unop
           (_UU03c3_1, (Coq_ty.Coq_bvec n), op, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
           (Coq_term_val ((Coq_ty.Coq_bvec m), v)), (Coq_term_var (l,
           (Coq_ty.Coq_bvec n), lIn)))
       | Coq_term_val (_, v0) ->
         Coq_term_val ((Coq_ty.Coq_bvec (add m n)),
           (Obj.magic Coq_bv.app m n v v0))
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
           (Coq_term_val ((Coq_ty.Coq_bvec m), v)), (Coq_term_binop
           (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n), op, t3, t4)))
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
           (Coq_term_val ((Coq_ty.Coq_bvec m), v)), (Coq_term_unop
           (_UU03c3_1, (Coq_ty.Coq_bvec n), op, t0)))
       | _ -> assert false (* absurd case *))
    | Coq_term_binop (_, _, _, op, t3, t4) ->
      (match op with
       | Coq_bop.Coq_shiftr (_, n0) ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n0),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftr (m, n0)), t3, t4)),
              (Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvapp_val_r _UU03a3_ m n (Coq_term_binop ((Coq_ty.Coq_bvec
              m), (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec m),
              (Coq_bop.Coq_shiftr (m, n0)), t3, t4)) v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n0),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftr (m, n0)), t3, t4)),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n),
              op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n0),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftr (m, n0)), t3, t4)),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_shiftl (_, n0) ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n0),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftl (m, n0)), t3, t4)),
              (Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvapp_val_r _UU03a3_ m n (Coq_term_binop ((Coq_ty.Coq_bvec
              m), (Coq_ty.Coq_bvec n0), (Coq_ty.Coq_bvec m),
              (Coq_bop.Coq_shiftl (m, n0)), t3, t4)) v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n0),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftl (m, n0)), t3, t4)),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n),
              op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n0),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftl (m, n0)), t3, t4)),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvadd _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvadd m), t3, t4)),
              (Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvapp_val_r _UU03a3_ m n (Coq_term_binop ((Coq_ty.Coq_bvec
              m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_bop.Coq_bvadd m), t3, t4)) v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvadd m), t3, t4)),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n),
              op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvadd m), t3, t4)),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvsub _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvsub m), t3, t4)),
              (Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvapp_val_r _UU03a3_ m n (Coq_term_binop ((Coq_ty.Coq_bvec
              m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_bop.Coq_bvsub m), t3, t4)) v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvsub m), t3, t4)),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n),
              op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvsub m), t3, t4)),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvmul _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvmul m), t3, t4)),
              (Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvapp_val_r _UU03a3_ m n (Coq_term_binop ((Coq_ty.Coq_bvec
              m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_bop.Coq_bvmul m), t3, t4)) v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvmul m), t3, t4)),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n),
              op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvmul m), t3, t4)),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvand _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvand m), t3, t4)),
              (Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvapp_val_r _UU03a3_ m n (Coq_term_binop ((Coq_ty.Coq_bvec
              m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_bop.Coq_bvand m), t3, t4)) v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvand m), t3, t4)),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n),
              op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvand m), t3, t4)),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvor _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvor m), t3, t4)),
              (Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvapp_val_r _UU03a3_ m n (Coq_term_binop ((Coq_ty.Coq_bvec
              m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvor
              m), t3, t4)) v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvor m), t3, t4)),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n),
              op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvor m), t3, t4)),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvxor _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvxor m), t3, t4)),
              (Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvapp_val_r _UU03a3_ m n (Coq_term_binop ((Coq_ty.Coq_bvec
              m), (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_bop.Coq_bvxor m), t3, t4)) v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvxor m), t3, t4)),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n),
              op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvxor m), t3, t4)),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvapp (m0, n0) ->
         Coq_term_binop ((Coq_ty.Coq_bvec m0), (Coq_ty.Coq_bvec (add n0 n)),
           (Coq_ty.Coq_bvec (add m0 (add n0 n))), (Coq_bop.Coq_bvapp (m0,
           (add n0 n))), t3, (Coq_term_binop ((Coq_ty.Coq_bvec n0),
           (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec (add n0 n)),
           (Coq_bop.Coq_bvapp (n0, n)), t4, t2)))
       | Coq_bop.Coq_bvcons m0 ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (S m0)), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add (S m0) n)), (Coq_bop.Coq_bvapp ((S m0),
              n)), (Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m0),
              (Coq_ty.Coq_bvec (S m0)), (Coq_bop.Coq_bvcons m0), t3, t4)),
              (Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvapp_val_r _UU03a3_ (S m0) n (Coq_term_binop
              (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m0), (Coq_ty.Coq_bvec (S
              m0)), (Coq_bop.Coq_bvcons m0), t3, t4)) v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (S m0)), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add (S m0) n)), (Coq_bop.Coq_bvapp ((S m0),
              n)), (Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m0),
              (Coq_ty.Coq_bvec (S m0)), (Coq_bop.Coq_bvcons m0), t3, t4)),
              (Coq_term_binop (_UU03c3_1, _UU03c3_2, (Coq_ty.Coq_bvec n),
              op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec (S m0)), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add (S m0) n)), (Coq_bop.Coq_bvapp ((S m0),
              n)), (Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m0),
              (Coq_ty.Coq_bvec (S m0)), (Coq_bop.Coq_bvcons m0), t3, t4)),
              (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n), op0, t0)))
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
         (match t2 with
          | Coq_term_var (l0, _, lIn) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec l),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_update_vector_subrange (m, s,
              l)), t3, t4)), (Coq_term_var (l0, (Coq_ty.Coq_bvec n), lIn)))
          | Coq_term_val (_, v) ->
            peval_bvapp_val_r _UU03a3_ m n (Coq_term_binop ((Coq_ty.Coq_bvec
              m), (Coq_ty.Coq_bvec l), (Coq_ty.Coq_bvec m),
              (Coq_bop.Coq_update_vector_subrange (m, s, l)), t3, t4)) v
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec l),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_update_vector_subrange (m, s,
              l)), t3, t4)), (Coq_term_binop (_UU03c3_1, _UU03c3_2,
              (Coq_ty.Coq_bvec n), op0, t5, t6)))
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
              (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
              (Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec l),
              (Coq_ty.Coq_bvec m), (Coq_bop.Coq_update_vector_subrange (m, s,
              l)), t3, t4)), (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec n),
              op0, t0)))
          | _ -> assert false (* absurd case *))
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
           (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec m), op, t0)),
           (Coq_term_var (l, (Coq_ty.Coq_bvec n), lIn)))
       | Coq_term_val (_, v) ->
         peval_bvapp_val_r _UU03a3_ m n (Coq_term_unop (_UU03c3_1,
           (Coq_ty.Coq_bvec m), op, t0)) v
       | Coq_term_binop (_UU03c3_2, _UU03c3_3, _, op0, t3, t4) ->
         Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
           (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec m), op, t0)),
           (Coq_term_binop (_UU03c3_2, _UU03c3_3, (Coq_ty.Coq_bvec n), op0,
           t3, t4)))
       | Coq_term_unop (_UU03c3_2, _, op0, t3) ->
         Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
           (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)),
           (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec m), op, t0)),
           (Coq_term_unop (_UU03c3_2, (Coq_ty.Coq_bvec n), op0, t3)))
       | _ -> assert false (* absurd case *))
    | _ -> assert false (* absurd case *)

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

  (** val peval_bvapp_graph_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_LVar
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
      -> coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
      (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat
      -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
      Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
      -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
      nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
      nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat
      -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
      coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      nat -> nat -> __ -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
      nat -> nat -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Val ->
      'a1) -> (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> nat -> nat -> nat -> __ -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) ->
      (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat
      -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> nat ->
      coq_Term -> coq_Term -> coq_Term -> peval_bvapp_graph -> 'a1 **)

  let peval_bvapp_graph_rect _ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 _ _ _ _ _ = function
  | Coq_peval_bvapp_graph_equation_1 (m, n, l, lIn, l0, lIn0) ->
    f m n l lIn l0 lIn0
  | Coq_peval_bvapp_graph_equation_2 (m, n, l, lIn, v2) -> f0 m n l lIn v2
  | Coq_peval_bvapp_graph_equation_3 (m, n, l, lIn, _UU03c3_1, _UU03c3_2, op,
                                      t1, t2) ->
    f1 m n l lIn _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_bvapp_graph_equation_4 (m, n, l, lIn, _UU03c3_4, op0, t0) ->
    f2 m n l lIn _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_5 (m, n, v, l, lIn) -> f3 m n v l lIn
  | Coq_peval_bvapp_graph_equation_6 (m, n, v1, v2) -> f4 m n v1 v2
  | Coq_peval_bvapp_graph_equation_7 (m, n, v, _UU03c3_1, _UU03c3_2, op, t1,
                                      t2) ->
    f5 m n v _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_bvapp_graph_equation_8 (m, n, v, _UU03c3_4, op0, t0) ->
    f6 m n v _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_9 (m, n, n0, t1, t3, l, lIn) ->
    f7 m n n0 t1 t3 l lIn
  | Coq_peval_bvapp_graph_equation_10 (m, n, n0, t1, t3, v2) ->
    f8 m n n0 t1 t3 v2
  | Coq_peval_bvapp_graph_equation_11 (m, n, n0, t1, t3, _UU03c3_1,
                                       _UU03c3_2, op, t2, t4) ->
    f9 m n n0 t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvapp_graph_equation_12 (m, n, n0, t1, t3, _UU03c3_4, op0, t0) ->
    f10 m n n0 t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_13 (m, n, n1, t1, t3, l, lIn) ->
    f11 m n n1 t1 t3 l lIn
  | Coq_peval_bvapp_graph_equation_14 (m, n, n1, t1, t3, v2) ->
    f12 m n n1 t1 t3 v2
  | Coq_peval_bvapp_graph_equation_15 (m, n, n1, t1, t3, _UU03c3_1,
                                       _UU03c3_2, op, t2, t4) ->
    f13 m n n1 t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvapp_graph_equation_16 (m, n, n1, t1, t3, _UU03c3_4, op0, t0) ->
    f14 m n n1 t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_17 (m, n, t1, t3, l, lIn) ->
    f15 m n t1 t3 l lIn
  | Coq_peval_bvapp_graph_equation_18 (m, n, t1, t3, v2) -> f16 m n t1 t3 v2
  | Coq_peval_bvapp_graph_equation_19 (m, n, t1, t3, _UU03c3_1, _UU03c3_2,
                                       op, t2, t4) ->
    f17 m n t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvapp_graph_equation_20 (m, n, t1, t3, _UU03c3_4, op0, t0) ->
    f18 m n t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_21 (m, n, t1, t3, l, lIn) ->
    f19 m n t1 t3 l lIn
  | Coq_peval_bvapp_graph_equation_22 (m, n, t1, t3, v2) -> f20 m n t1 t3 v2
  | Coq_peval_bvapp_graph_equation_23 (m, n, t1, t3, _UU03c3_1, _UU03c3_2,
                                       op, t2, t4) ->
    f21 m n t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvapp_graph_equation_24 (m, n, t1, t3, _UU03c3_4, op0, t0) ->
    f22 m n t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_25 (m, n, t1, t3, l, lIn) ->
    f23 m n t1 t3 l lIn
  | Coq_peval_bvapp_graph_equation_26 (m, n, t1, t3, v2) -> f24 m n t1 t3 v2
  | Coq_peval_bvapp_graph_equation_27 (m, n, t1, t3, _UU03c3_1, _UU03c3_2,
                                       op, t2, t4) ->
    f25 m n t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvapp_graph_equation_28 (m, n, t1, t3, _UU03c3_4, op0, t0) ->
    f26 m n t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_29 (m, n, t1, t3, l, lIn) ->
    f27 m n t1 t3 l lIn
  | Coq_peval_bvapp_graph_equation_30 (m, n, t1, t3, v2) -> f28 m n t1 t3 v2
  | Coq_peval_bvapp_graph_equation_31 (m, n, t1, t3, _UU03c3_1, _UU03c3_2,
                                       op, t2, t4) ->
    f29 m n t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvapp_graph_equation_32 (m, n, t1, t3, _UU03c3_4, op0, t0) ->
    f30 m n t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_33 (m, n, t1, t3, l, lIn) ->
    f31 m n t1 t3 l lIn
  | Coq_peval_bvapp_graph_equation_34 (m, n, t1, t3, v2) -> f32 m n t1 t3 v2
  | Coq_peval_bvapp_graph_equation_35 (m, n, t1, t3, _UU03c3_1, _UU03c3_2,
                                       op, t2, t4) ->
    f33 m n t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvapp_graph_equation_36 (m, n, t1, t3, _UU03c3_4, op0, t0) ->
    f34 m n t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_37 (m, n, t1, t3, l, lIn) ->
    f35 m n t1 t3 l lIn
  | Coq_peval_bvapp_graph_equation_38 (m, n, t1, t3, v2) -> f36 m n t1 t3 v2
  | Coq_peval_bvapp_graph_equation_39 (m, n, t1, t3, _UU03c3_1, _UU03c3_2,
                                       op, t2, t4) ->
    f37 m n t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvapp_graph_equation_40 (m, n, t1, t3, _UU03c3_4, op0, t0) ->
    f38 m n t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_41 (m2, n8, n, t11, t12, t2) ->
    f39 m2 n8 n t11 t12 t2
  | Coq_peval_bvapp_graph_equation_42 (m3, n, t1, t3, l, lIn) ->
    f40 m3 n t1 t3 l lIn
  | Coq_peval_bvapp_graph_equation_43 (m3, n, t1, t3, v2) -> f41 m3 n t1 t3 v2
  | Coq_peval_bvapp_graph_equation_44 (m3, n, t1, t3, _UU03c3_1, _UU03c3_2,
                                       op, t2, t4) ->
    f42 m3 n t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvapp_graph_equation_45 (m3, n, t1, t3, _UU03c3_4, op0, t0) ->
    f43 m3 n t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_46 (m, n, l, s, t1, t3, l0, lIn) ->
    f44 m n l s __ t1 t3 l0 lIn
  | Coq_peval_bvapp_graph_equation_47 (m, n, l, s, t1, t3, v2) ->
    f45 m n l s __ t1 t3 v2
  | Coq_peval_bvapp_graph_equation_48 (m, n, l, s, t1, t3, _UU03c3_1,
                                       _UU03c3_2, op, t2, t4) ->
    f46 m n l s __ t1 t3 _UU03c3_1 _UU03c3_2 op t2 t4
  | Coq_peval_bvapp_graph_equation_49 (m, n, l, s, t1, t3, _UU03c3_4, op0, t0) ->
    f47 m n l s __ t1 t3 _UU03c3_4 op0 t0
  | Coq_peval_bvapp_graph_equation_50 (m, n, _UU03c3_4, op0, t0, l, lIn) ->
    f48 m n _UU03c3_4 op0 t0 l lIn
  | Coq_peval_bvapp_graph_equation_51 (m, n, _UU03c3_4, op0, t0, v2) ->
    f49 m n _UU03c3_4 op0 t0 v2
  | Coq_peval_bvapp_graph_equation_52 (m, n, _UU03c3_4, op0, t0, _UU03c3_1,
                                       _UU03c3_2, op, t1, t2) ->
    f50 m n _UU03c3_4 op0 t0 _UU03c3_1 _UU03c3_2 op t1 t2
  | Coq_peval_bvapp_graph_equation_53 (m, n, _UU03c3_4, op0, t0, _UU03c3_5,
                                       op1, t1) ->
    f51 m n _UU03c3_4 op0 t0 _UU03c3_5 op1 t1

  (** val peval_bvapp_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> coq_Term -> coq_Term -> peval_bvapp_graph **)

  let peval_bvapp_graph_correct _ m n t1 t2 =
    match t1 with
    | Coq_term_var (l, _, lIn) ->
      (match t2 with
       | Coq_term_var (l0, _, lIn0) ->
         Coq_peval_bvapp_graph_equation_1 (m, n, l, lIn, l0, lIn0)
       | Coq_term_val (_, v) ->
         Coq_peval_bvapp_graph_equation_2 (m, n, l, lIn, v)
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         Coq_peval_bvapp_graph_equation_3 (m, n, l, lIn, _UU03c3_1,
           _UU03c3_2, op, t3, t4)
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_peval_bvapp_graph_equation_4 (m, n, l, lIn, _UU03c3_1, op, t0)
       | _ -> assert false (* absurd case *))
    | Coq_term_val (_, v) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_peval_bvapp_graph_equation_5 (m, n, v, l, lIn)
       | Coq_term_val (_, v0) ->
         Coq_peval_bvapp_graph_equation_6 (m, n, v, v0)
       | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op, t3, t4) ->
         Coq_peval_bvapp_graph_equation_7 (m, n, v, _UU03c3_1, _UU03c3_2, op,
           t3, t4)
       | Coq_term_unop (_UU03c3_1, _, op, t0) ->
         Coq_peval_bvapp_graph_equation_8 (m, n, v, _UU03c3_1, op, t0)
       | _ -> assert false (* absurd case *))
    | Coq_term_binop (_, _, _, op, t3, t4) ->
      (match op with
       | Coq_bop.Coq_shiftr (_, n0) ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvapp_graph_equation_9 (m, n, n0, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvapp_graph_equation_10 (m, n, n0, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvapp_graph_equation_11 (m, n, n0, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvapp_graph_equation_12 (m, n, n0, t3, t4, _UU03c3_1,
              op0, t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_shiftl (_, n0) ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvapp_graph_equation_13 (m, n, n0, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvapp_graph_equation_14 (m, n, n0, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvapp_graph_equation_15 (m, n, n0, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvapp_graph_equation_16 (m, n, n0, t3, t4, _UU03c3_1,
              op0, t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvadd _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvapp_graph_equation_17 (m, n, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvapp_graph_equation_18 (m, n, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvapp_graph_equation_19 (m, n, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvapp_graph_equation_20 (m, n, t3, t4, _UU03c3_1, op0,
              t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvsub _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvapp_graph_equation_21 (m, n, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvapp_graph_equation_22 (m, n, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvapp_graph_equation_23 (m, n, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvapp_graph_equation_24 (m, n, t3, t4, _UU03c3_1, op0,
              t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvmul _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvapp_graph_equation_25 (m, n, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvapp_graph_equation_26 (m, n, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvapp_graph_equation_27 (m, n, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvapp_graph_equation_28 (m, n, t3, t4, _UU03c3_1, op0,
              t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvand _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvapp_graph_equation_29 (m, n, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvapp_graph_equation_30 (m, n, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvapp_graph_equation_31 (m, n, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvapp_graph_equation_32 (m, n, t3, t4, _UU03c3_1, op0,
              t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvor _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvapp_graph_equation_33 (m, n, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvapp_graph_equation_34 (m, n, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvapp_graph_equation_35 (m, n, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvapp_graph_equation_36 (m, n, t3, t4, _UU03c3_1, op0,
              t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvxor _ ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvapp_graph_equation_37 (m, n, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvapp_graph_equation_38 (m, n, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvapp_graph_equation_39 (m, n, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvapp_graph_equation_40 (m, n, t3, t4, _UU03c3_1, op0,
              t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_bvapp (m0, n0) ->
         Coq_peval_bvapp_graph_equation_41 (m0, n0, n, t3, t4, t2)
       | Coq_bop.Coq_bvcons m0 ->
         (match t2 with
          | Coq_term_var (l, _, lIn) ->
            Coq_peval_bvapp_graph_equation_42 (m0, n, t3, t4, l, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvapp_graph_equation_43 (m0, n, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvapp_graph_equation_44 (m0, n, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvapp_graph_equation_45 (m0, n, t3, t4, _UU03c3_1, op0,
              t0)
          | _ -> assert false (* absurd case *))
       | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
         (match t2 with
          | Coq_term_var (l0, _, lIn) ->
            Coq_peval_bvapp_graph_equation_46 (m, n, l, s, t3, t4, l0, lIn)
          | Coq_term_val (_, v) ->
            Coq_peval_bvapp_graph_equation_47 (m, n, l, s, t3, t4, v)
          | Coq_term_binop (_UU03c3_1, _UU03c3_2, _, op0, t5, t6) ->
            Coq_peval_bvapp_graph_equation_48 (m, n, l, s, t3, t4, _UU03c3_1,
              _UU03c3_2, op0, t5, t6)
          | Coq_term_unop (_UU03c3_1, _, op0, t0) ->
            Coq_peval_bvapp_graph_equation_49 (m, n, l, s, t3, t4, _UU03c3_1,
              op0, t0)
          | _ -> assert false (* absurd case *))
       | _ -> assert false (* absurd case *))
    | Coq_term_unop (_UU03c3_1, _, op, t0) ->
      (match t2 with
       | Coq_term_var (l, _, lIn) ->
         Coq_peval_bvapp_graph_equation_50 (m, n, _UU03c3_1, op, t0, l, lIn)
       | Coq_term_val (_, v) ->
         Coq_peval_bvapp_graph_equation_51 (m, n, _UU03c3_1, op, t0, v)
       | Coq_term_binop (_UU03c3_2, _UU03c3_3, _, op0, t3, t4) ->
         Coq_peval_bvapp_graph_equation_52 (m, n, _UU03c3_1, op, t0,
           _UU03c3_2, _UU03c3_3, op0, t3, t4)
       | Coq_term_unop (_UU03c3_2, _, op0, t3) ->
         Coq_peval_bvapp_graph_equation_53 (m, n, _UU03c3_1, op, t0,
           _UU03c3_2, op0, t3)
       | _ -> assert false (* absurd case *))
    | _ -> assert false (* absurd case *)

  (** val peval_bvapp_elim :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_LVar
      -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
      -> coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
      (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat
      -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
      Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
      -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
      nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
      nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat
      -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
      coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term
      -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
      nat -> nat -> __ -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat ->
      nat -> nat -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Val ->
      'a1) -> (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> nat -> nat -> nat -> __ -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) ->
      (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat
      -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> nat ->
      coq_Term -> coq_Term -> 'a1 **)

  let peval_bvapp_elim _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 m n t1 t2 =
    match peval_bvapp_graph_correct _UU03a3_ m n t1 t2 with
    | Coq_peval_bvapp_graph_equation_1 (m0, n0, l, lIn, l0, lIn0) ->
      f m0 n0 l lIn l0 lIn0
    | Coq_peval_bvapp_graph_equation_2 (m0, n0, l, lIn, v2) ->
      f0 m0 n0 l lIn v2
    | Coq_peval_bvapp_graph_equation_3 (m0, n0, l, lIn, _UU03c3_1, _UU03c3_2,
                                        op, t3, t4) ->
      f1 m0 n0 l lIn _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_bvapp_graph_equation_4 (m0, n0, l, lIn, _UU03c3_4, op0, t0) ->
      f2 m0 n0 l lIn _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_5 (m0, n0, v, l, lIn) -> f3 m0 n0 v l lIn
    | Coq_peval_bvapp_graph_equation_6 (m0, n0, v1, v2) -> f4 m0 n0 v1 v2
    | Coq_peval_bvapp_graph_equation_7 (m0, n0, v, _UU03c3_1, _UU03c3_2, op,
                                        t3, t4) ->
      f5 m0 n0 v _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_bvapp_graph_equation_8 (m0, n0, v, _UU03c3_4, op0, t0) ->
      f6 m0 n0 v _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_9 (m0, n0, n1, t3, t4, l, lIn) ->
      f7 m0 n0 n1 t3 t4 l lIn
    | Coq_peval_bvapp_graph_equation_10 (m0, n0, n1, t3, t4, v2) ->
      f8 m0 n0 n1 t3 t4 v2
    | Coq_peval_bvapp_graph_equation_11 (m0, n0, n1, t3, t4, _UU03c3_1,
                                         _UU03c3_2, op, t5, t6) ->
      f9 m0 n0 n1 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvapp_graph_equation_12 (m0, n0, n1, t3, t4, _UU03c3_4, op0,
                                         t0) ->
      f10 m0 n0 n1 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_13 (m0, n0, n1, t3, t4, l, lIn) ->
      f11 m0 n0 n1 t3 t4 l lIn
    | Coq_peval_bvapp_graph_equation_14 (m0, n0, n1, t3, t4, v2) ->
      f12 m0 n0 n1 t3 t4 v2
    | Coq_peval_bvapp_graph_equation_15 (m0, n0, n1, t3, t4, _UU03c3_1,
                                         _UU03c3_2, op, t5, t6) ->
      f13 m0 n0 n1 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvapp_graph_equation_16 (m0, n0, n1, t3, t4, _UU03c3_4, op0,
                                         t0) ->
      f14 m0 n0 n1 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_17 (m0, n0, t3, t4, l, lIn) ->
      f15 m0 n0 t3 t4 l lIn
    | Coq_peval_bvapp_graph_equation_18 (m0, n0, t3, t4, v2) ->
      f16 m0 n0 t3 t4 v2
    | Coq_peval_bvapp_graph_equation_19 (m0, n0, t3, t4, _UU03c3_1,
                                         _UU03c3_2, op, t5, t6) ->
      f17 m0 n0 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvapp_graph_equation_20 (m0, n0, t3, t4, _UU03c3_4, op0, t0) ->
      f18 m0 n0 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_21 (m0, n0, t3, t4, l, lIn) ->
      f19 m0 n0 t3 t4 l lIn
    | Coq_peval_bvapp_graph_equation_22 (m0, n0, t3, t4, v2) ->
      f20 m0 n0 t3 t4 v2
    | Coq_peval_bvapp_graph_equation_23 (m0, n0, t3, t4, _UU03c3_1,
                                         _UU03c3_2, op, t5, t6) ->
      f21 m0 n0 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvapp_graph_equation_24 (m0, n0, t3, t4, _UU03c3_4, op0, t0) ->
      f22 m0 n0 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_25 (m0, n0, t3, t4, l, lIn) ->
      f23 m0 n0 t3 t4 l lIn
    | Coq_peval_bvapp_graph_equation_26 (m0, n0, t3, t4, v2) ->
      f24 m0 n0 t3 t4 v2
    | Coq_peval_bvapp_graph_equation_27 (m0, n0, t3, t4, _UU03c3_1,
                                         _UU03c3_2, op, t5, t6) ->
      f25 m0 n0 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvapp_graph_equation_28 (m0, n0, t3, t4, _UU03c3_4, op0, t0) ->
      f26 m0 n0 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_29 (m0, n0, t3, t4, l, lIn) ->
      f27 m0 n0 t3 t4 l lIn
    | Coq_peval_bvapp_graph_equation_30 (m0, n0, t3, t4, v2) ->
      f28 m0 n0 t3 t4 v2
    | Coq_peval_bvapp_graph_equation_31 (m0, n0, t3, t4, _UU03c3_1,
                                         _UU03c3_2, op, t5, t6) ->
      f29 m0 n0 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvapp_graph_equation_32 (m0, n0, t3, t4, _UU03c3_4, op0, t0) ->
      f30 m0 n0 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_33 (m0, n0, t3, t4, l, lIn) ->
      f31 m0 n0 t3 t4 l lIn
    | Coq_peval_bvapp_graph_equation_34 (m0, n0, t3, t4, v2) ->
      f32 m0 n0 t3 t4 v2
    | Coq_peval_bvapp_graph_equation_35 (m0, n0, t3, t4, _UU03c3_1,
                                         _UU03c3_2, op, t5, t6) ->
      f33 m0 n0 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvapp_graph_equation_36 (m0, n0, t3, t4, _UU03c3_4, op0, t0) ->
      f34 m0 n0 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_37 (m0, n0, t3, t4, l, lIn) ->
      f35 m0 n0 t3 t4 l lIn
    | Coq_peval_bvapp_graph_equation_38 (m0, n0, t3, t4, v2) ->
      f36 m0 n0 t3 t4 v2
    | Coq_peval_bvapp_graph_equation_39 (m0, n0, t3, t4, _UU03c3_1,
                                         _UU03c3_2, op, t5, t6) ->
      f37 m0 n0 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvapp_graph_equation_40 (m0, n0, t3, t4, _UU03c3_4, op0, t0) ->
      f38 m0 n0 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_41 (m2, n8, n0, t11, t12, t3) ->
      f39 m2 n8 n0 t11 t12 t3
    | Coq_peval_bvapp_graph_equation_42 (m3, n0, t3, t4, l, lIn) ->
      f40 m3 n0 t3 t4 l lIn
    | Coq_peval_bvapp_graph_equation_43 (m3, n0, t3, t4, v2) ->
      f41 m3 n0 t3 t4 v2
    | Coq_peval_bvapp_graph_equation_44 (m3, n0, t3, t4, _UU03c3_1,
                                         _UU03c3_2, op, t5, t6) ->
      f42 m3 n0 t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvapp_graph_equation_45 (m3, n0, t3, t4, _UU03c3_4, op0, t0) ->
      f43 m3 n0 t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_46 (m0, n0, l, s, t3, t4, l0, lIn) ->
      f44 m0 n0 l s __ t3 t4 l0 lIn
    | Coq_peval_bvapp_graph_equation_47 (m0, n0, l, s, t3, t4, v2) ->
      f45 m0 n0 l s __ t3 t4 v2
    | Coq_peval_bvapp_graph_equation_48 (m0, n0, l, s, t3, t4, _UU03c3_1,
                                         _UU03c3_2, op, t5, t6) ->
      f46 m0 n0 l s __ t3 t4 _UU03c3_1 _UU03c3_2 op t5 t6
    | Coq_peval_bvapp_graph_equation_49 (m0, n0, l, s, t3, t4, _UU03c3_4,
                                         op0, t0) ->
      f47 m0 n0 l s __ t3 t4 _UU03c3_4 op0 t0
    | Coq_peval_bvapp_graph_equation_50 (m0, n0, _UU03c3_4, op0, t0, l, lIn) ->
      f48 m0 n0 _UU03c3_4 op0 t0 l lIn
    | Coq_peval_bvapp_graph_equation_51 (m0, n0, _UU03c3_4, op0, t0, v2) ->
      f49 m0 n0 _UU03c3_4 op0 t0 v2
    | Coq_peval_bvapp_graph_equation_52 (m0, n0, _UU03c3_4, op0, t0,
                                         _UU03c3_1, _UU03c3_2, op, t3, t4) ->
      f50 m0 n0 _UU03c3_4 op0 t0 _UU03c3_1 _UU03c3_2 op t3 t4
    | Coq_peval_bvapp_graph_equation_53 (m0, n0, _UU03c3_4, op0, t0,
                                         _UU03c3_5, op1, t3) ->
      f51 m0 n0 _UU03c3_4 op0 t0 _UU03c3_5 op1 t3

  (** val coq_FunctionalElimination_peval_bvapp :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
      Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
      (nat -> nat -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
      -> coq_Term -> __) -> (nat -> nat -> Coq_ty.coq_Val -> coq_LVar ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
      (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) -> (nat -> nat
      -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
      Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __)
      -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
      -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat
      -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat -> nat
      -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
      coq_Term -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Val -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
      nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
      coq_Term -> coq_Term -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
      nat -> nat -> __ -> coq_Term -> coq_Term -> coq_LVar -> (coq_LVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
      -> nat -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) ->
      (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
      coq_Term -> __) -> (nat -> nat -> nat -> nat -> __ -> coq_Term ->
      coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) ->
      (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> __) -> (nat -> nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
      (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> nat -> nat ->
      coq_Term -> coq_Term -> __ **)

  let coq_FunctionalElimination_peval_bvapp =
    peval_bvapp_elim

  (** val coq_FunctionalInduction_peval_bvapp :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> nat -> coq_Term -> coq_Term -> coq_Term) coq_FunctionalInduction **)

  let coq_FunctionalInduction_peval_bvapp _UU03a3_ =
    Obj.magic peval_bvapp_graph_correct _UU03a3_

  (** val peval_bvdrop_bvapp :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat ->
      nat -> coq_Term -> coq_Term -> coq_Term **)

  let peval_bvdrop_bvapp _ peval_bvdrop_eq0 m n k l x x0 =
    match nat_compare m k with
    | EQ _ -> x0
    | LT (m', d) ->
      Coq_term_binop ((Coq_ty.Coq_bvec (S d)), (Coq_ty.Coq_bvec l),
        (Coq_ty.Coq_bvec (add (S d) l)), (Coq_bop.Coq_bvapp ((S d), l)),
        (peval_bvdrop_eq0 m' (S d) (add m' (S d)) x __), x0)
    | GT (_, d) -> peval_bvdrop_eq0 (S d) n (add (S d) n) x0 __

  (** val peval_bvdrop_bvcons :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat ->
      coq_Term -> coq_Term -> coq_Term **)

  let peval_bvdrop_bvcons _ peval_bvdrop_eq0 m n k t1 t2 =
    match m with
    | O ->
      Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec k), (Coq_ty.Coq_bvec
        (S k)), (Coq_bop.Coq_bvcons k), t1, t2)
    | S m0 -> peval_bvdrop_eq0 m0 n k t2 __

  (** val peval_bvdrop_bvdrop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat ->
      nat -> coq_Term -> coq_Term **)

  let peval_bvdrop_bvdrop _ peval_bvdrop_eq0 m n k l t1 =
    peval_bvdrop_eq0 (add k m) n (add k l) t1 __

  (** val peval_bvdrop_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> Coq_ty.coq_Val -> coq_Term **)

  let peval_bvdrop_val _ m n _ v =
    Coq_term_val ((Coq_ty.Coq_bvec n), (Obj.magic Coq_bv.drop m n v))

  (** val peval_bvdrop_default :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> coq_Term -> coq_Term **)

  let peval_bvdrop_default _ m n _ t0 =
    match eq_dec nat_EqDec O m with
    | Coq_left -> t0
    | Coq_right ->
      (match eq_dec nat_EqDec n O with
       | Coq_left ->
         Coq_term_val ((Coq_ty.Coq_bvec n), (Obj.magic Coq_bv.nil))
       | Coq_right ->
         Coq_term_unop ((Coq_ty.Coq_bvec (add m n)), (Coq_ty.Coq_bvec n),
           (Coq_uop.Coq_bvdrop (m, n)), t0))

  (** val peval_bvdrop_eq :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> coq_Term -> coq_Term **)

  let rec peval_bvdrop_eq _UU03a3_ m n mn t0 =
    coq_Term_bvec_case _UU03a3_ (fun _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun k v _ ->
      peval_bvdrop_val _UU03a3_ m n k v) (fun _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun k l t1 t2 _ ->
      peval_bvdrop_bvapp _UU03a3_ (fun m0 n0 mn0 t3 _ ->
        peval_bvdrop_eq _UU03a3_ m0 n0 mn0 t3) m n k l t1 t2)
      (fun k t1 t2 _ ->
      peval_bvdrop_bvcons _UU03a3_ (fun m0 n0 mn0 t3 _ ->
        peval_bvdrop_eq _UU03a3_ m0 n0 mn0 t3) m n k t1 t2)
      (fun _ _ _ _ _ _ _ -> peval_bvdrop_default _UU03a3_ m n mn t0)
      (fun _ _ _ -> peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ _ ->
      peval_bvdrop_default _UU03a3_ m n mn t0) (fun k l t1 _ ->
      peval_bvdrop_bvdrop _UU03a3_ (fun m0 n0 mn0 t2 _ ->
        peval_bvdrop_eq _UU03a3_ m0 n0 mn0 t2) m n k l t1)
      (fun _ _ _ _ -> peval_bvdrop_default _UU03a3_ m n mn t0) mn t0 __

  (** val peval_bvdrop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> coq_Term -> coq_Term **)

  let peval_bvdrop _UU03a3_ m n t0 =
    peval_bvdrop_eq _UU03a3_ m n (add m n) t0

  (** val peval_bvtake_bvapp :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat ->
      nat -> coq_Term -> coq_Term -> coq_Term **)

  let peval_bvtake_bvapp _ peval_bvtake_eq0 m n k l x x0 =
    match nat_compare m k with
    | EQ _ -> x
    | LT (m', d) -> peval_bvtake_eq0 m' (S d) (add m' (S d)) x __
    | GT (k', d) ->
      Coq_term_binop ((Coq_ty.Coq_bvec k'), (Coq_ty.Coq_bvec (S d)),
        (Coq_ty.Coq_bvec (add k' (S d))), (Coq_bop.Coq_bvapp (k', (S d))), x,
        (peval_bvtake_eq0 (S d) n l x0 __))

  (** val peval_bvtake_bvcons :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat ->
      coq_Term -> coq_Term -> coq_Term **)

  let peval_bvtake_bvcons _ peval_bvtake_eq0 m n k t1 t2 =
    match m with
    | O -> Coq_term_val ((Coq_ty.Coq_bvec O), (Obj.magic Coq_bv.nil))
    | S m0 ->
      Coq_term_binop (Coq_ty.Coq_bool, (Coq_ty.Coq_bvec m0), (Coq_ty.Coq_bvec
        (S m0)), (Coq_bop.Coq_bvcons m0), t1, (peval_bvtake_eq0 m0 n k t2 __))

  (** val peval_bvtake_bvtake :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> nat -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat ->
      nat -> coq_Term -> coq_Term **)

  let peval_bvtake_bvtake _ peval_bvtake_eq0 m n k l t1 =
    peval_bvtake_eq0 m (add n l) (add k l) t1 __

  (** val peval_bvtake_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> Coq_ty.coq_Val -> coq_Term **)

  let peval_bvtake_val _ m n _ v =
    Coq_term_val ((Coq_ty.Coq_bvec m), (Obj.magic Coq_bv.take m n v))

  (** val peval_bvtake_default :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> coq_Term -> coq_Term **)

  let peval_bvtake_default _ m n _ t0 =
    match eq_dec nat_EqDec m O with
    | Coq_left -> Coq_term_val ((Coq_ty.Coq_bvec O), (Obj.magic Coq_bv.nil))
    | Coq_right ->
      (match eq_dec nat_EqDec O n with
       | Coq_left -> t0
       | Coq_right ->
         Coq_term_unop ((Coq_ty.Coq_bvec (add m n)), (Coq_ty.Coq_bvec m),
           (Coq_uop.Coq_bvtake (m, n)), t0))

  (** val peval_bvtake_eq :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> coq_Term -> coq_Term **)

  let rec peval_bvtake_eq _UU03a3_ m n mn t0 =
    coq_Term_bvec_case _UU03a3_ (fun _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun k v _ ->
      peval_bvtake_val _UU03a3_ m n k v) (fun _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun k l t1 t2 _ ->
      peval_bvtake_bvapp _UU03a3_ (fun m0 n0 mn0 t3 _ ->
        peval_bvtake_eq _UU03a3_ m0 n0 mn0 t3) m n k l t1 t2)
      (fun k t1 t2 _ ->
      peval_bvtake_bvcons _UU03a3_ (fun m0 n0 mn0 t3 _ ->
        peval_bvtake_eq _UU03a3_ m0 n0 mn0 t3) m n k t1 t2)
      (fun _ _ _ _ _ _ _ -> peval_bvtake_default _UU03a3_ m n mn t0)
      (fun _ _ _ -> peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun _ _ _ _ ->
      peval_bvtake_default _UU03a3_ m n mn t0) (fun k l t1 _ ->
      peval_bvtake_bvtake _UU03a3_ (fun m0 n0 mn0 t2 _ ->
        peval_bvtake_eq _UU03a3_ m0 n0 mn0 t2) m n k l t1)
      mn t0 __

  (** val peval_bvtake :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> coq_Term -> coq_Term **)

  let peval_bvtake _UU03a3_ m n t0 =
    peval_bvtake_eq _UU03a3_ m n (add m n) t0

  (** val peval_update_vector_subrange :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> coq_Term -> coq_Term -> coq_Term **)

  let peval_update_vector_subrange _UU03a3_ n s l =
    let k = Coq_bv.leview (add s l) n in
    (fun tslk tl ->
    peval_bvapp _UU03a3_ (add s l) k
      (peval_bvapp _UU03a3_ s l
        (peval_bvtake _UU03a3_ s l (peval_bvtake _UU03a3_ (add s l) k tslk))
        tl)
      (peval_bvdrop _UU03a3_ (add s l) k tslk))

  (** val peval_binop' :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> coq_Term **)

  let peval_binop' _ _ _UU03c3_2 _UU03c3_ op t1 t2 =
    match t1 with
    | Coq_term_var (l, _UU03c3_0, lIn) ->
      Coq_term_binop (_UU03c3_0, _UU03c3_2, _UU03c3_, op, (Coq_term_var (l,
        _UU03c3_0, lIn)), t2)
    | Coq_term_val (_UU03c3_0, v) ->
      (match t2 with
       | Coq_term_var (l, _UU03c3_1, lIn) ->
         Coq_term_binop (_UU03c3_0, _UU03c3_1, _UU03c3_, op, (Coq_term_val
           (_UU03c3_0, v)), (Coq_term_var (l, _UU03c3_1, lIn)))
       | Coq_term_val (_UU03c3_1, v0) ->
         Coq_term_val (_UU03c3_,
           (Coq_bop.eval typedeclkit typedenotekit typedefkit _UU03c3_0
             _UU03c3_1 _UU03c3_ op v v0))
       | Coq_term_binop (_UU03c3_1, _UU03c3_3, _UU03c3_4, op0, t3, t4) ->
         Coq_term_binop (_UU03c3_0, _UU03c3_4, _UU03c3_, op, (Coq_term_val
           (_UU03c3_0, v)), (Coq_term_binop (_UU03c3_1, _UU03c3_3, _UU03c3_4,
           op0, t3, t4)))
       | Coq_term_unop (_UU03c3_1, _UU03c3_3, op0, t0) ->
         Coq_term_binop (_UU03c3_0, _UU03c3_3, _UU03c3_, op, (Coq_term_val
           (_UU03c3_0, v)), (Coq_term_unop (_UU03c3_1, _UU03c3_3, op0, t0)))
       | Coq_term_tuple (_UU03c3_s, ts) ->
         Coq_term_binop (_UU03c3_0, (Coq_ty.Coq_tuple _UU03c3_s), _UU03c3_,
           op, (Coq_term_val (_UU03c3_0, v)), (Coq_term_tuple (_UU03c3_s,
           ts)))
       | Coq_term_union (u, k, t0) ->
         Coq_term_binop (_UU03c3_0, (Coq_ty.Coq_union u), _UU03c3_, op,
           (Coq_term_val (_UU03c3_0, v)), (Coq_term_union (u, k, t0)))
       | Coq_term_record (r, ts) ->
         Coq_term_binop (_UU03c3_0, (Coq_ty.Coq_record r), _UU03c3_, op,
           (Coq_term_val (_UU03c3_0, v)), (Coq_term_record (r, ts))))
    | Coq_term_binop (_UU03c3_1, _UU03c3_3, _UU03c3_4, op0, t3, t4) ->
      Coq_term_binop (_UU03c3_4, _UU03c3_2, _UU03c3_, op, (Coq_term_binop
        (_UU03c3_1, _UU03c3_3, _UU03c3_4, op0, t3, t4)), t2)
    | Coq_term_unop (_UU03c3_1, _UU03c3_3, op0, t0) ->
      Coq_term_binop (_UU03c3_3, _UU03c3_2, _UU03c3_, op, (Coq_term_unop
        (_UU03c3_1, _UU03c3_3, op0, t0)), t2)
    | Coq_term_tuple (_UU03c3_s, ts) ->
      Coq_term_binop ((Coq_ty.Coq_tuple _UU03c3_s), _UU03c3_2, _UU03c3_, op,
        (Coq_term_tuple (_UU03c3_s, ts)), t2)
    | Coq_term_union (u, k, t0) ->
      Coq_term_binop ((Coq_ty.Coq_union u), _UU03c3_2, _UU03c3_, op,
        (Coq_term_union (u, k, t0)), t2)
    | Coq_term_record (r, ts) ->
      Coq_term_binop ((Coq_ty.Coq_record r), _UU03c3_2, _UU03c3_, op,
        (Coq_term_record (r, ts)), t2)

  (** val peval_binop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_Term -> coq_Term -> coq_Term **)

  let peval_binop _UU03a3_ _ _ _ = function
  | Coq_bop.Coq_plus -> peval_plus _UU03a3_
  | Coq_bop.Coq_and -> peval_and _UU03a3_
  | Coq_bop.Coq_or -> peval_or _UU03a3_
  | Coq_bop.Coq_pair (_UU03c3_0, _UU03c3_3) ->
    peval_binop' _UU03a3_ _UU03c3_0 _UU03c3_3 (Coq_ty.Coq_prod (_UU03c3_0,
      _UU03c3_3)) (Coq_bop.Coq_pair (_UU03c3_0, _UU03c3_3))
  | Coq_bop.Coq_cons _UU03c3_0 ->
    peval_binop' _UU03a3_ _UU03c3_0 (Coq_ty.Coq_list _UU03c3_0)
      (Coq_ty.Coq_list _UU03c3_0) (Coq_bop.Coq_cons _UU03c3_0)
  | Coq_bop.Coq_append _UU03c3_0 -> peval_append _UU03a3_ _UU03c3_0
  | Coq_bop.Coq_shiftr (m, n) ->
    peval_binop' _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec n)
      (Coq_ty.Coq_bvec m) (Coq_bop.Coq_shiftr (m, n))
  | Coq_bop.Coq_shiftl (m, n) ->
    peval_binop' _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec n)
      (Coq_ty.Coq_bvec m) (Coq_bop.Coq_shiftl (m, n))
  | Coq_bop.Coq_bvadd n -> peval_bvadd _UU03a3_ n
  | Coq_bop.Coq_bvsub n ->
    peval_binop' _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n)
      (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvsub n)
  | Coq_bop.Coq_bvmul n ->
    peval_binop' _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n)
      (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvmul n)
  | Coq_bop.Coq_bvand n -> peval_bvand _UU03a3_ n
  | Coq_bop.Coq_bvor n -> peval_bvor _UU03a3_ n
  | Coq_bop.Coq_bvxor n ->
    peval_binop' _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n)
      (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvxor n)
  | Coq_bop.Coq_bvapp (m, n) -> peval_bvapp _UU03a3_ m n
  | Coq_bop.Coq_bvcons m ->
    peval_binop' _UU03a3_ Coq_ty.Coq_bool (Coq_ty.Coq_bvec m)
      (Coq_ty.Coq_bvec (S m)) (Coq_bop.Coq_bvcons m)
  | Coq_bop.Coq_update_vector_subrange (n, s, l) ->
    peval_update_vector_subrange _UU03a3_ n s l
  | Coq_bop.Coq_relop (_UU03c3_0, r) ->
    peval_binop' _UU03a3_ _UU03c3_0 _UU03c3_0 Coq_ty.Coq_bool
      (Coq_bop.Coq_relop (_UU03c3_0, r))
  | x -> peval_binop' _UU03a3_ Coq_ty.Coq_int Coq_ty.Coq_int Coq_ty.Coq_int x

  (** val peval_not :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Term -> coq_Term **)

  let rec peval_not _UU03a3_ = function
  | Coq_term_var (l, _, lIn) ->
    Coq_term_unop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_uop.Coq_not,
      (Coq_term_var (l, Coq_ty.Coq_bool, lIn)))
  | Coq_term_val (_, v) -> Coq_term_val (Coq_ty.Coq_bool, (Obj.magic negb v))
  | Coq_term_binop (_, _, _, op, t1, t2) ->
    (match op with
     | Coq_bop.Coq_and ->
       Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
         Coq_bop.Coq_or, (peval_not _UU03a3_ t1), (peval_not _UU03a3_ t2))
     | Coq_bop.Coq_or ->
       Coq_term_binop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_ty.Coq_bool,
         Coq_bop.Coq_and, (peval_not _UU03a3_ t1), (peval_not _UU03a3_ t2))
     | Coq_bop.Coq_relop (_UU03c3_, r) ->
       term_relop_neg _UU03a3_ _UU03c3_ r t1 t2
     | _ -> assert false (* absurd case *))
  | Coq_term_unop (_UU03c3_1, _, op, t1) ->
    Coq_term_unop (Coq_ty.Coq_bool, Coq_ty.Coq_bool, Coq_uop.Coq_not,
      (Coq_term_unop (_UU03c3_1, Coq_ty.Coq_bool, op, t1)))
  | _ -> assert false (* absurd case *)

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

  (** val peval_not_graph_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
      coq_Term -> peval_not_graph -> 'a1 -> peval_not_graph -> 'a1 -> 'a1) ->
      (coq_Term -> coq_Term -> peval_not_graph -> 'a1 -> peval_not_graph ->
      'a1 -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term ->
      coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      'a1) -> coq_Term -> coq_Term -> peval_not_graph -> 'a1 **)

  let rec peval_not_graph_rect _UU03a3_ f f0 f1 f2 f3 f4 _ _ = function
  | Coq_peval_not_graph_equation_1 (l, lIn) -> f l lIn
  | Coq_peval_not_graph_equation_2 v -> f0 v
  | Coq_peval_not_graph_equation_3 (t1, t2, hind, hind0) ->
    f1 t1 t2 hind
      (peval_not_graph_rect _UU03a3_ f f0 f1 f2 f3 f4 t1
        (peval_not _UU03a3_ t1) hind)
      hind0
      (peval_not_graph_rect _UU03a3_ f f0 f1 f2 f3 f4 t2
        (peval_not _UU03a3_ t2) hind0)
  | Coq_peval_not_graph_equation_4 (t1, t2, hind, hind0) ->
    f2 t1 t2 hind
      (peval_not_graph_rect _UU03a3_ f f0 f1 f2 f3 f4 t1
        (peval_not _UU03a3_ t1) hind)
      hind0
      (peval_not_graph_rect _UU03a3_ f f0 f1 f2 f3 f4 t2
        (peval_not _UU03a3_ t2) hind0)
  | Coq_peval_not_graph_equation_5 (_UU03c3_5, op, t1, t2) ->
    f3 _UU03c3_5 op t1 t2
  | Coq_peval_not_graph_equation_6 (_UU03c3_4, op0, t0) -> f4 _UU03c3_4 op0 t0

  (** val peval_not_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Term -> peval_not_graph **)

  let rec peval_not_graph_correct _UU03a3_ = function
  | Coq_term_var (l, _, lIn) -> Coq_peval_not_graph_equation_1 (l, lIn)
  | Coq_term_val (_, v) -> Coq_peval_not_graph_equation_2 v
  | Coq_term_binop (_, _, _, op, t1, t2) ->
    (match op with
     | Coq_bop.Coq_and ->
       Coq_peval_not_graph_equation_3 (t1, t2,
         (peval_not_graph_correct _UU03a3_ t1),
         (peval_not_graph_correct _UU03a3_ t2))
     | Coq_bop.Coq_or ->
       Coq_peval_not_graph_equation_4 (t1, t2,
         (peval_not_graph_correct _UU03a3_ t1),
         (peval_not_graph_correct _UU03a3_ t2))
     | Coq_bop.Coq_relop (_UU03c3_, r) ->
       Coq_peval_not_graph_equation_5 (_UU03c3_, r, t1, t2)
     | _ -> assert false (* absurd case *))
  | Coq_term_unop (_UU03c3_1, _, op, t1) ->
    Coq_peval_not_graph_equation_6 (_UU03c3_1, op, t1)
  | _ -> assert false (* absurd case *)

  (** val peval_not_elim :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
      coq_Term -> 'a1 -> 'a1 -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1
      -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term
      -> 'a1) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) ->
      coq_Term -> 'a1 **)

  let peval_not_elim _UU03a3_ f f0 f1 f2 f3 f4 t0 =
    let rec f5 _ _ = function
    | Coq_peval_not_graph_equation_1 (l, lIn) -> f l lIn
    | Coq_peval_not_graph_equation_2 v -> f0 v
    | Coq_peval_not_graph_equation_3 (t1, t2, hind, hind0) ->
      f1 t1 t2 (f5 t1 (peval_not _UU03a3_ t1) hind)
        (f5 t2 (peval_not _UU03a3_ t2) hind0)
    | Coq_peval_not_graph_equation_4 (t1, t2, hind, hind0) ->
      f2 t1 t2 (f5 t1 (peval_not _UU03a3_ t1) hind)
        (f5 t2 (peval_not _UU03a3_ t2) hind0)
    | Coq_peval_not_graph_equation_5 (_UU03c3_5, op, t1, t2) ->
      f3 _UU03c3_5 op t1 t2
    | Coq_peval_not_graph_equation_6 (_UU03c3_4, op0, t1) ->
      f4 _UU03c3_4 op0 t1
    in f5 t0 (peval_not _UU03a3_ t0) (peval_not_graph_correct _UU03a3_ t0)

  (** val coq_FunctionalElimination_peval_not :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> __) -> (Coq_ty.coq_Val -> __) -> (coq_Term ->
      coq_Term -> __ -> __ -> __) -> (coq_Term -> coq_Term -> __ -> __ -> __)
      -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> __)
      -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> coq_Term ->
      __ **)

  let coq_FunctionalElimination_peval_not =
    peval_not_elim

  (** val coq_FunctionalInduction_peval_not :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_Term -> coq_Term) coq_FunctionalInduction **)

  let coq_FunctionalInduction_peval_not _UU03a3_ =
    Obj.magic peval_not_graph_correct _UU03a3_

  (** val peval_unsigned_bvapp :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> coq_Term -> coq_Term -> coq_Term **)

  let peval_unsigned_bvapp _ m1 m2 t1 t2 =
    Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_ty.Coq_int,
      Coq_bop.Coq_plus, (Coq_term_unop ((Coq_ty.Coq_bvec m1), Coq_ty.Coq_int,
      (Coq_uop.Coq_unsigned m1), t1)), (Coq_term_binop (Coq_ty.Coq_int,
      Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_bop.Coq_times, (Coq_term_unop
      ((Coq_ty.Coq_bvec m2), Coq_ty.Coq_int, (Coq_uop.Coq_unsigned m2), t2)),
      (Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic BinInt.Z.pow (Zpos (Coq_xO Coq_xH)) (BinInt.Z.of_nat m1)))))))

  (** val peval_unsigned :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> coq_Term **)

  let peval_unsigned _UU03a3_ m = function
  | Coq_term_var (l, _, lIn) ->
    Coq_term_unop ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int, (Coq_uop.Coq_unsigned
      m), (Coq_term_var (l, (Coq_ty.Coq_bvec m), lIn)))
  | Coq_term_val (_, v) ->
    Coq_term_val (Coq_ty.Coq_int, (Obj.magic Coq_bv.unsigned m v))
  | Coq_term_binop (_, _, _, op, t1, t2) ->
    (match op with
     | Coq_bop.Coq_shiftr (_, n) ->
       Coq_term_unop ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned m), (Coq_term_binop ((Coq_ty.Coq_bvec m),
         (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftr (m,
         n)), t1, t2)))
     | Coq_bop.Coq_shiftl (_, n) ->
       Coq_term_unop ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned m), (Coq_term_binop ((Coq_ty.Coq_bvec m),
         (Coq_ty.Coq_bvec n), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_shiftl (m,
         n)), t1, t2)))
     | Coq_bop.Coq_bvadd _ ->
       Coq_term_unop ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned m), (Coq_term_binop ((Coq_ty.Coq_bvec m),
         (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvadd m), t1,
         t2)))
     | Coq_bop.Coq_bvsub _ ->
       Coq_term_unop ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned m), (Coq_term_binop ((Coq_ty.Coq_bvec m),
         (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvsub m), t1,
         t2)))
     | Coq_bop.Coq_bvmul _ ->
       Coq_term_unop ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned m), (Coq_term_binop ((Coq_ty.Coq_bvec m),
         (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvmul m), t1,
         t2)))
     | Coq_bop.Coq_bvand _ ->
       Coq_term_unop ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned m), (Coq_term_binop ((Coq_ty.Coq_bvec m),
         (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvand m), t1,
         t2)))
     | Coq_bop.Coq_bvor _ ->
       Coq_term_unop ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned m), (Coq_term_binop ((Coq_ty.Coq_bvec m),
         (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvor m), t1,
         t2)))
     | Coq_bop.Coq_bvxor _ ->
       Coq_term_unop ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned m), (Coq_term_binop ((Coq_ty.Coq_bvec m),
         (Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec m), (Coq_bop.Coq_bvxor m), t1,
         t2)))
     | Coq_bop.Coq_bvapp (m0, n) -> peval_unsigned_bvapp _UU03a3_ m0 n t1 t2
     | Coq_bop.Coq_bvcons m0 ->
       Coq_term_unop ((Coq_ty.Coq_bvec (S m0)), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned (S m0)), (Coq_term_binop (Coq_ty.Coq_bool,
         (Coq_ty.Coq_bvec m0), (Coq_ty.Coq_bvec (S m0)), (Coq_bop.Coq_bvcons
         m0), t1, t2)))
     | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
       Coq_term_unop ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned m), (Coq_term_binop ((Coq_ty.Coq_bvec m),
         (Coq_ty.Coq_bvec l), (Coq_ty.Coq_bvec m),
         (Coq_bop.Coq_update_vector_subrange (m, s, l)), t1, t2)))
     | _ -> assert false (* absurd case *))
  | Coq_term_unop (_UU03c3_1, _, op, t1) ->
    Coq_term_unop ((Coq_ty.Coq_bvec m), Coq_ty.Coq_int, (Coq_uop.Coq_unsigned
      m), (Coq_term_unop (_UU03c3_1, (Coq_ty.Coq_bvec m), op, t1)))
  | _ -> assert false (* absurd case *)

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

  (** val peval_unsigned_graph_rect :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat
      -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term
      -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat
      -> nat -> __ -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty
      -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> coq_Term -> coq_Term
      -> peval_unsigned_graph -> 'a1 **)

  let peval_unsigned_graph_rect _ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 _ _ _ = function
  | Coq_peval_unsigned_graph_equation_1 (m, l, lIn) -> f m l lIn
  | Coq_peval_unsigned_graph_equation_2 (m, v) -> f0 m v
  | Coq_peval_unsigned_graph_equation_3 (m, n, t1, t2) -> f1 m n t1 t2
  | Coq_peval_unsigned_graph_equation_4 (m, n0, t1, t2) -> f2 m n0 t1 t2
  | Coq_peval_unsigned_graph_equation_5 (m, t1, t2) -> f3 m t1 t2
  | Coq_peval_unsigned_graph_equation_6 (m, t1, t2) -> f4 m t1 t2
  | Coq_peval_unsigned_graph_equation_7 (m, t1, t2) -> f5 m t1 t2
  | Coq_peval_unsigned_graph_equation_8 (m, t1, t2) -> f6 m t1 t2
  | Coq_peval_unsigned_graph_equation_9 (m, t1, t2) -> f7 m t1 t2
  | Coq_peval_unsigned_graph_equation_10 (m, t1, t2) -> f8 m t1 t2
  | Coq_peval_unsigned_graph_equation_11 (m2, n7, t1, t2) -> f9 m2 n7 t1 t2
  | Coq_peval_unsigned_graph_equation_12 (m3, t1, t2) -> f10 m3 t1 t2
  | Coq_peval_unsigned_graph_equation_13 (m, l, s, t1, t2) ->
    f11 m l s __ t1 t2
  | Coq_peval_unsigned_graph_equation_14 (m, _UU03c3_4, op0, t0) ->
    f12 m _UU03c3_4 op0 t0

  (** val peval_unsigned_graph_correct :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      coq_Term -> peval_unsigned_graph **)

  let peval_unsigned_graph_correct _ m = function
  | Coq_term_var (l, _, lIn) ->
    Coq_peval_unsigned_graph_equation_1 (m, l, lIn)
  | Coq_term_val (_, v) -> Coq_peval_unsigned_graph_equation_2 (m, v)
  | Coq_term_binop (_, _, _, op, t1, t2) ->
    (match op with
     | Coq_bop.Coq_shiftr (_, n) ->
       Coq_peval_unsigned_graph_equation_3 (m, n, t1, t2)
     | Coq_bop.Coq_shiftl (_, n) ->
       Coq_peval_unsigned_graph_equation_4 (m, n, t1, t2)
     | Coq_bop.Coq_bvadd _ -> Coq_peval_unsigned_graph_equation_5 (m, t1, t2)
     | Coq_bop.Coq_bvsub _ -> Coq_peval_unsigned_graph_equation_6 (m, t1, t2)
     | Coq_bop.Coq_bvmul _ -> Coq_peval_unsigned_graph_equation_7 (m, t1, t2)
     | Coq_bop.Coq_bvand _ -> Coq_peval_unsigned_graph_equation_8 (m, t1, t2)
     | Coq_bop.Coq_bvor _ -> Coq_peval_unsigned_graph_equation_9 (m, t1, t2)
     | Coq_bop.Coq_bvxor _ -> Coq_peval_unsigned_graph_equation_10 (m, t1, t2)
     | Coq_bop.Coq_bvapp (m0, n) ->
       Coq_peval_unsigned_graph_equation_11 (m0, n, t1, t2)
     | Coq_bop.Coq_bvcons m0 ->
       Coq_peval_unsigned_graph_equation_12 (m0, t1, t2)
     | Coq_bop.Coq_update_vector_subrange (_, s, l) ->
       Coq_peval_unsigned_graph_equation_13 (m, l, s, t1, t2)
     | _ -> assert false (* absurd case *))
  | Coq_term_unop (_UU03c3_1, _, op, t1) ->
    Coq_peval_unsigned_graph_equation_14 (m, _UU03c3_1, op, t1)
  | _ -> assert false (* absurd case *)

  (** val peval_unsigned_elim :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat
      -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term
      -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat ->
      coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) ->
      (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term ->
      coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat
      -> nat -> __ -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty
      -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> coq_Term -> 'a1 **)

  let peval_unsigned_elim _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 m t0 =
    match peval_unsigned_graph_correct _UU03a3_ m t0 with
    | Coq_peval_unsigned_graph_equation_1 (m0, l, lIn) -> f m0 l lIn
    | Coq_peval_unsigned_graph_equation_2 (m0, v) -> f0 m0 v
    | Coq_peval_unsigned_graph_equation_3 (m0, n, t1, t2) -> f1 m0 n t1 t2
    | Coq_peval_unsigned_graph_equation_4 (m0, n0, t1, t2) -> f2 m0 n0 t1 t2
    | Coq_peval_unsigned_graph_equation_5 (m0, t1, t2) -> f3 m0 t1 t2
    | Coq_peval_unsigned_graph_equation_6 (m0, t1, t2) -> f4 m0 t1 t2
    | Coq_peval_unsigned_graph_equation_7 (m0, t1, t2) -> f5 m0 t1 t2
    | Coq_peval_unsigned_graph_equation_8 (m0, t1, t2) -> f6 m0 t1 t2
    | Coq_peval_unsigned_graph_equation_9 (m0, t1, t2) -> f7 m0 t1 t2
    | Coq_peval_unsigned_graph_equation_10 (m0, t1, t2) -> f8 m0 t1 t2
    | Coq_peval_unsigned_graph_equation_11 (m2, n7, t1, t2) -> f9 m2 n7 t1 t2
    | Coq_peval_unsigned_graph_equation_12 (m3, t1, t2) -> f10 m3 t1 t2
    | Coq_peval_unsigned_graph_equation_13 (m0, l, s, t1, t2) ->
      f11 m0 l s __ t1 t2
    | Coq_peval_unsigned_graph_equation_14 (m0, _UU03c3_4, op0, t1) ->
      f12 m0 _UU03c3_4 op0 t1

  (** val coq_FunctionalElimination_peval_unsigned :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_LVar -> (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Val -> __) -> (nat -> nat
      -> coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term
      -> __) -> (nat -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
      coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> __) -> (nat ->
      coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> __) ->
      (nat -> coq_Term -> coq_Term -> __) -> (nat -> nat -> coq_Term ->
      coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> __) -> (nat -> nat
      -> nat -> __ -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty ->
      Coq_uop.coq_UnOp -> coq_Term -> __) -> nat -> coq_Term -> __ **)

  let coq_FunctionalElimination_peval_unsigned =
    peval_unsigned_elim

  (** val coq_FunctionalInduction_peval_unsigned :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat
      -> coq_Term -> coq_Term) coq_FunctionalInduction **)

  let coq_FunctionalInduction_peval_unsigned _UU03a3_ =
    Obj.magic peval_unsigned_graph_correct _UU03a3_

  (** val peval_vector_subrange :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> nat -> coq_Term -> coq_Term **)

  let peval_vector_subrange _UU03a3_ n start len t0 =
    peval_bvdrop _UU03a3_ start len
      (peval_bvtake _UU03a3_ (add start len)
        (Coq_bv.leview (add start len) n) t0)

  (** val peval_unop' :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      coq_Term **)

  let peval_unop' _UU03a3_ _UU03c3_1 _UU03c3_2 op t0 =
    match term_get_val _UU03a3_ _UU03c3_1 t0 with
    | Some v ->
      Coq_term_val (_UU03c3_2,
        (Coq_uop.eval typedeclkit typedenotekit _UU03c3_1 _UU03c3_2 op v))
    | None -> Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t0)

  (** val peval_zext :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      nat -> coq_Term -> coq_Term **)

  let peval_zext _ m n t0 =
    match eq_dec nat_EqDec n m with
    | Coq_left -> t0
    | Coq_right ->
      Coq_term_unop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
        (Coq_uop.Coq_zext (m, n)), t0)

  (** val peval_unop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
      coq_Term **)

  let peval_unop _UU03a3_ _ _ = function
  | Coq_uop.Coq_inl (_UU03c3_0, _UU03c3_3) ->
    peval_unop' _UU03a3_ _UU03c3_0 (Coq_ty.Coq_sum (_UU03c3_0, _UU03c3_3))
      (Coq_uop.Coq_inl (_UU03c3_0, _UU03c3_3))
  | Coq_uop.Coq_inr (_UU03c3_0, _UU03c3_3) ->
    peval_unop' _UU03a3_ _UU03c3_3 (Coq_ty.Coq_sum (_UU03c3_0, _UU03c3_3))
      (Coq_uop.Coq_inr (_UU03c3_0, _UU03c3_3))
  | Coq_uop.Coq_neg ->
    peval_unop' _UU03a3_ Coq_ty.Coq_int Coq_ty.Coq_int Coq_uop.Coq_neg
  | Coq_uop.Coq_not -> peval_not _UU03a3_
  | Coq_uop.Coq_rev _UU03c3_ ->
    peval_unop' _UU03a3_ (Coq_ty.Coq_list _UU03c3_) (Coq_ty.Coq_list
      _UU03c3_) (Coq_uop.Coq_rev _UU03c3_)
  | Coq_uop.Coq_sext (m, n) ->
    peval_unop' _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec n)
      (Coq_uop.Coq_sext (m, n))
  | Coq_uop.Coq_zext (m, n) -> peval_zext _UU03a3_ m n
  | Coq_uop.Coq_get_slice_int n ->
    peval_unop' _UU03a3_ Coq_ty.Coq_int (Coq_ty.Coq_bvec n)
      (Coq_uop.Coq_get_slice_int n)
  | Coq_uop.Coq_signed n ->
    peval_unop' _UU03a3_ (Coq_ty.Coq_bvec n) Coq_ty.Coq_int
      (Coq_uop.Coq_signed n)
  | Coq_uop.Coq_unsigned n -> peval_unsigned _UU03a3_ n
  | Coq_uop.Coq_truncate (n, m) ->
    peval_unop' _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec m)
      (Coq_uop.Coq_truncate (n, m))
  | Coq_uop.Coq_vector_subrange (n, start, len) ->
    peval_vector_subrange _UU03a3_ n start len
  | Coq_uop.Coq_bvnot n ->
    peval_unop' _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n)
      (Coq_uop.Coq_bvnot n)
  | Coq_uop.Coq_bvdrop (m, n) -> peval_bvdrop _UU03a3_ m n
  | Coq_uop.Coq_bvtake (m, n) -> peval_bvtake _UU03a3_ m n
  | Coq_uop.Coq_negate n ->
    peval_unop' _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n)
      (Coq_uop.Coq_negate n)

  (** val evalPolTm :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_TermRing -> coq_Term list -> coq_Z coq_Pol ->
      coq_Term **)

  let evalPolTm _UU03a3_ _UU03c3_ h =
    coq_Pphi_dev (Coq_term_val (_UU03c3_, h.tmr_zero)) (Coq_term_val
      (_UU03c3_, h.tmr_one))
      (peval_binop' _UU03a3_ _UU03c3_ _UU03c3_ _UU03c3_ h.tmr_plus)
      (peval_binop' _UU03a3_ _UU03c3_ _UU03c3_ _UU03c3_ h.tmr_times)
      (peval_binop' _UU03a3_ _UU03c3_ _UU03c3_ _UU03c3_ h.tmr_minus)
      (peval_unop' _UU03a3_ _UU03c3_ _UU03c3_ h.tmr_negate) Z0 (Zpos Coq_xH)
      BinInt.Z.eqb (fun c -> Coq_term_val (_UU03c3_, (h.tmr_of_Z c)))
      get_signZ

  (** val coq_CanonTerm_to_Term :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_CanonTerm -> coq_Term **)

  let coq_CanonTerm_to_Term _UU03a3_ _UU03c3_ ct =
    match _UU03c3_ with
    | Coq_ty.Coq_int ->
      let Coq_pair (pexpr, env) = Obj.magic ct Datatypes.Coq_nil Coq_xH in
      evalPolTm _UU03a3_ Coq_ty.Coq_int (coq_TermRing_int _UU03a3_) env
        (norm_aux Z0 (Zpos Coq_xH) BinInt.Z.add BinInt.Z.mul BinInt.Z.sub
          BinInt.Z.opp BinInt.Z.eqb pexpr)
    | Coq_ty.Coq_bvec n ->
      let Coq_pair (pexpr, env) = Obj.magic ct Datatypes.Coq_nil Coq_xH in
      evalPolTm _UU03a3_ (Coq_ty.Coq_bvec n) (coq_TermRing_bv _UU03a3_ n) env
        (norm_aux Z0 (Zpos Coq_xH) BinInt.Z.add BinInt.Z.mul BinInt.Z.sub
          BinInt.Z.opp BinInt.Z.eqb pexpr)
    | _ -> Obj.magic ct

  (** val peval_union :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.unioni -> Coq_ty.unionk -> coq_Term -> coq_Term **)

  let peval_union _UU03a3_ u k t0 =
    match term_get_val _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k) t0 with
    | Some v ->
      Coq_term_val ((Coq_ty.Coq_union u),
        (typedefkit.Coq_ty.unionv_fold u (Coq_existT (k, v))))
    | None -> Coq_term_union (u, k, t0)

  (** val peval_record' :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) coq_NamedEnv ->
      (Coq_ty.recordf, Coq_ty.coq_Ty, Coq_ty.coq_Val) coq_NamedEnv option **)

  let rec peval_record' _UU03a3_ _ = function
  | Coq_env.Coq_nil -> Some Coq_env.Coq_nil
  | Coq_env.Coq_snoc (_UU0393_, ts0, b, t0) ->
    Coq_option.bind (peval_record' _UU03a3_ _UU0393_ ts0) (fun vs ->
      Coq_option.bind (term_get_val _UU03a3_ b.Binding.coq_type t0) (fun v ->
        Some (Coq_env.Coq_snoc (_UU0393_, vs, b, v))))

  (** val peval_record :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term)
      coq_NamedEnv -> coq_Term **)

  let peval_record _UU03a3_ r ts =
    match peval_record' _UU03a3_ (typedefkit.Coq_ty.recordf_ty r) ts with
    | Some a ->
      Coq_term_val ((Coq_ty.Coq_record r),
        (typedefkit.Coq_ty.recordv_fold r a))
    | None -> Coq_term_record (r, ts)

  (** val coq_CanonTerm_def :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> coq_CanonTerm **)

  let coq_CanonTerm_def _UU03a3_ = function
  | Coq_ty.Coq_int -> Obj.magic coq_Term_Quote_def _UU03a3_ Coq_ty.Coq_int
  | Coq_ty.Coq_bvec n ->
    Obj.magic coq_Term_Quote_def _UU03a3_ (Coq_ty.Coq_bvec n)
  | _ -> (fun t0 -> Obj.magic t0)

  (** val peval2_val :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Val -> coq_CanonTerm **)

  let peval2_val _ = function
  | Coq_ty.Coq_int ->
    (fun v -> Obj.magic (fun _ _ -> Coq_pair ((PEc v), Datatypes.Coq_nil)))
  | Coq_ty.Coq_bvec n ->
    (fun v ->
      Obj.magic (fun _ _ -> Coq_pair ((PEc
        (Coq_bv.unsigned n (Obj.magic v))), Datatypes.Coq_nil)))
  | x -> Obj.magic (fun x0 -> Coq_term_val (x, x0))

  (** val peval2_binop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      coq_CanonTerm -> coq_CanonTerm -> coq_CanonTerm **)

  let peval2_binop _UU03a3_ _ _ _ = function
  | Coq_bop.Coq_plus ->
    Obj.magic coq_Term_Quote_bin _UU03a3_ Coq_ty.Coq_int
      (coq_TermRing_int _UU03a3_) (fun x x0 -> PEadd (x, x0))
  | Coq_bop.Coq_minus ->
    Obj.magic coq_Term_Quote_bin _UU03a3_ Coq_ty.Coq_int
      (coq_TermRing_int _UU03a3_) (fun x x0 -> PEsub (x, x0))
  | Coq_bop.Coq_times ->
    Obj.magic coq_Term_Quote_bin _UU03a3_ Coq_ty.Coq_int
      (coq_TermRing_int _UU03a3_) (fun x x0 -> PEmul (x, x0))
  | Coq_bop.Coq_land ->
    (fun t1 t2 ->
      coq_CanonTerm_def _UU03a3_ Coq_ty.Coq_int
        (peval_binop _UU03a3_ Coq_ty.Coq_int Coq_ty.Coq_int Coq_ty.Coq_int
          Coq_bop.Coq_land (coq_CanonTerm_to_Term _UU03a3_ Coq_ty.Coq_int t1)
          (coq_CanonTerm_to_Term _UU03a3_ Coq_ty.Coq_int t2)))
  | Coq_bop.Coq_pair (_UU03c3_0, _UU03c3_4) ->
    (fun t1 t2 ->
      Obj.magic peval_binop _UU03a3_ _UU03c3_0 _UU03c3_4 (Coq_ty.Coq_prod
        (_UU03c3_0, _UU03c3_4)) (Coq_bop.Coq_pair (_UU03c3_0, _UU03c3_4))
        (coq_CanonTerm_to_Term _UU03a3_ _UU03c3_0 t1)
        (coq_CanonTerm_to_Term _UU03a3_ _UU03c3_4 t2))
  | Coq_bop.Coq_cons _UU03c3_ ->
    (fun t1 t2 ->
      Obj.magic peval_binop _UU03a3_ _UU03c3_ (Coq_ty.Coq_list _UU03c3_)
        (Coq_ty.Coq_list _UU03c3_) (Coq_bop.Coq_cons _UU03c3_)
        (coq_CanonTerm_to_Term _UU03a3_ _UU03c3_ t1) t2)
  | Coq_bop.Coq_append _UU03c3_ ->
    (fun t1 t2 ->
      Obj.magic peval_binop _UU03a3_ (Coq_ty.Coq_list _UU03c3_)
        (Coq_ty.Coq_list _UU03c3_) (Coq_ty.Coq_list _UU03c3_)
        (Coq_bop.Coq_append _UU03c3_) t1 t2)
  | Coq_bop.Coq_shiftr (m, n) ->
    (fun t1 t2 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec m)
        (peval_binop _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec n)
          (Coq_ty.Coq_bvec m) (Coq_bop.Coq_shiftr (m, n))
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec m) t1)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t2)))
  | Coq_bop.Coq_shiftl (m, n) ->
    (fun t1 t2 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec m)
        (peval_binop _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec n)
          (Coq_ty.Coq_bvec m) (Coq_bop.Coq_shiftl (m, n))
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec m) t1)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t2)))
  | Coq_bop.Coq_bvadd n ->
    Obj.magic coq_Term_Quote_bin _UU03a3_ (Coq_ty.Coq_bvec n)
      (coq_TermRing_bv _UU03a3_ n) (fun x x0 -> PEadd (x, x0))
  | Coq_bop.Coq_bvsub n ->
    Obj.magic coq_Term_Quote_bin _UU03a3_ (Coq_ty.Coq_bvec n)
      (coq_TermRing_bv _UU03a3_ n) (fun x x0 -> PEsub (x, x0))
  | Coq_bop.Coq_bvmul n ->
    Obj.magic coq_Term_Quote_bin _UU03a3_ (Coq_ty.Coq_bvec n)
      (coq_TermRing_bv _UU03a3_ n) (fun x x0 -> PEmul (x, x0))
  | Coq_bop.Coq_bvand n ->
    (fun t1 t2 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec n)
        (peval_binop _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n)
          (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvand n)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t1)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t2)))
  | Coq_bop.Coq_bvor n ->
    (fun t1 t2 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec n)
        (peval_binop _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n)
          (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvor n)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t1)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t2)))
  | Coq_bop.Coq_bvxor n ->
    (fun t1 t2 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec n)
        (peval_binop _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n)
          (Coq_ty.Coq_bvec n) (Coq_bop.Coq_bvxor n)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t1)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t2)))
  | Coq_bop.Coq_bvapp (m, n) ->
    (fun t1 t2 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec (add m n))
        (peval_binop _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec n)
          (Coq_ty.Coq_bvec (add m n)) (Coq_bop.Coq_bvapp (m, n))
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec m) t1)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t2)))
  | Coq_bop.Coq_bvcons m ->
    (fun t1 t2 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec (S m))
        (peval_binop _UU03a3_ Coq_ty.Coq_bool (Coq_ty.Coq_bvec m)
          (Coq_ty.Coq_bvec (S m)) (Coq_bop.Coq_bvcons m) (Obj.magic t1)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec m) t2)))
  | Coq_bop.Coq_update_vector_subrange (n, s, l) ->
    (fun t1 t2 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec n)
        (peval_binop _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec l)
          (Coq_ty.Coq_bvec n) (Coq_bop.Coq_update_vector_subrange (n, s, l))
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t1)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec l) t2)))
  | Coq_bop.Coq_relop (_UU03c3_, rop) ->
    (fun t1 t2 ->
      Obj.magic peval_binop _UU03a3_ _UU03c3_ _UU03c3_ Coq_ty.Coq_bool
        (Coq_bop.Coq_relop (_UU03c3_, rop))
        (coq_CanonTerm_to_Term _UU03a3_ _UU03c3_ t1)
        (coq_CanonTerm_to_Term _UU03a3_ _UU03c3_ t2))
  | x ->
    Obj.magic peval_binop _UU03a3_ Coq_ty.Coq_bool Coq_ty.Coq_bool
      Coq_ty.Coq_bool x

  (** val peval2_unop :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_CanonTerm ->
      coq_CanonTerm **)

  let peval2_unop _UU03a3_ _ _ = function
  | Coq_uop.Coq_inl (_UU03c3_0, _UU03c3_3) ->
    (fun t1 ->
      Obj.magic peval_unop _UU03a3_ _UU03c3_0 (Coq_ty.Coq_sum (_UU03c3_0,
        _UU03c3_3)) (Coq_uop.Coq_inl (_UU03c3_0, _UU03c3_3))
        (coq_CanonTerm_to_Term _UU03a3_ _UU03c3_0 t1))
  | Coq_uop.Coq_inr (_UU03c3_0, _UU03c3_3) ->
    (fun t1 ->
      Obj.magic peval_unop _UU03a3_ _UU03c3_3 (Coq_ty.Coq_sum (_UU03c3_0,
        _UU03c3_3)) (Coq_uop.Coq_inr (_UU03c3_0, _UU03c3_3))
        (coq_CanonTerm_to_Term _UU03a3_ _UU03c3_3 t1))
  | Coq_uop.Coq_neg ->
    Obj.magic coq_Term_Quote_unop _UU03a3_ Coq_ty.Coq_int (fun x -> PEopp x)
  | Coq_uop.Coq_not ->
    Obj.magic peval_unop _UU03a3_ Coq_ty.Coq_bool Coq_ty.Coq_bool
      Coq_uop.Coq_not
  | Coq_uop.Coq_rev _UU03c3_ ->
    (fun t1 ->
      Obj.magic peval_unop _UU03a3_ (Coq_ty.Coq_list _UU03c3_)
        (Coq_ty.Coq_list _UU03c3_) (Coq_uop.Coq_rev _UU03c3_)
        (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_list _UU03c3_) t1))
  | Coq_uop.Coq_sext (m, n) ->
    (fun t1 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec n)
        (peval_unop _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec n)
          (Coq_uop.Coq_sext (m, n))
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec m) t1)))
  | Coq_uop.Coq_zext (m, n) ->
    (fun t1 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec n)
        (peval_unop _UU03a3_ (Coq_ty.Coq_bvec m) (Coq_ty.Coq_bvec n)
          (Coq_uop.Coq_zext (m, n))
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec m) t1)))
  | Coq_uop.Coq_get_slice_int n ->
    (fun t1 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec n)
        (peval_unop _UU03a3_ Coq_ty.Coq_int (Coq_ty.Coq_bvec n)
          (Coq_uop.Coq_get_slice_int n)
          (coq_CanonTerm_to_Term _UU03a3_ Coq_ty.Coq_int t1)))
  | Coq_uop.Coq_signed n ->
    (fun t1 ->
      coq_CanonTerm_def _UU03a3_ Coq_ty.Coq_int
        (peval_unop _UU03a3_ (Coq_ty.Coq_bvec n) Coq_ty.Coq_int
          (Coq_uop.Coq_signed n)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t1)))
  | Coq_uop.Coq_unsigned n ->
    (fun t1 ->
      coq_CanonTerm_def _UU03a3_ Coq_ty.Coq_int
        (peval_unop _UU03a3_ (Coq_ty.Coq_bvec n) Coq_ty.Coq_int
          (Coq_uop.Coq_unsigned n)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t1)))
  | Coq_uop.Coq_truncate (n, m) ->
    (fun t1 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec m)
        (peval_unop _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec m)
          (Coq_uop.Coq_truncate (n, m))
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t1)))
  | Coq_uop.Coq_vector_subrange (n, s, l) ->
    (fun t1 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec l)
        (peval_unop _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec l)
          (Coq_uop.Coq_vector_subrange (n, s, l))
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t1)))
  | Coq_uop.Coq_bvnot n ->
    (fun t1 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec n)
        (peval_unop _UU03a3_ (Coq_ty.Coq_bvec n) (Coq_ty.Coq_bvec n)
          (Coq_uop.Coq_bvnot n)
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec n) t1)))
  | Coq_uop.Coq_bvdrop (m, n) ->
    (fun t1 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec n)
        (peval_unop _UU03a3_ (Coq_ty.Coq_bvec (add m n)) (Coq_ty.Coq_bvec n)
          (Coq_uop.Coq_bvdrop (m, n))
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec (add m n)) t1)))
  | Coq_uop.Coq_bvtake (m, n) ->
    (fun t1 ->
      coq_CanonTerm_def _UU03a3_ (Coq_ty.Coq_bvec m)
        (peval_unop _UU03a3_ (Coq_ty.Coq_bvec (add m n)) (Coq_ty.Coq_bvec m)
          (Coq_uop.Coq_bvtake (m, n))
          (coq_CanonTerm_to_Term _UU03a3_ (Coq_ty.Coq_bvec (add m n)) t1)))
  | Coq_uop.Coq_negate n ->
    Obj.magic coq_Term_Quote_unop _UU03a3_ (Coq_ty.Coq_bvec n) (fun x ->
      PEopp x)

  (** val peval2 :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> coq_CanonTerm **)

  let rec peval2 _UU03a3_ _ = function
  | Coq_term_var (_UU03c2_, _UU03c3_0, lIn) ->
    coq_CanonTerm_def _UU03a3_ _UU03c3_0 (Coq_term_var (_UU03c2_, _UU03c3_0,
      lIn))
  | Coq_term_val (_UU03c3_0, v) -> peval2_val _UU03a3_ _UU03c3_0 v
  | Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, t1, t2) ->
    peval2_binop _UU03a3_ _UU03c3_1 _UU03c3_2 _UU03c3_3 op
      (peval2 _UU03a3_ _UU03c3_1 t1) (peval2 _UU03a3_ _UU03c3_2 t2)
  | Coq_term_unop (_UU03c3_1, _UU03c3_2, op, t1) ->
    peval2_unop _UU03a3_ _UU03c3_1 _UU03c3_2 op (peval2 _UU03a3_ _UU03c3_1 t1)
  | Coq_term_tuple (_UU03c3_s, ts) ->
    Obj.magic (Coq_term_tuple (_UU03c3_s,
      (Coq_env.map (fun b t1 ->
        coq_CanonTerm_to_Term _UU03a3_ b (peval2 _UU03a3_ b t1)) _UU03c3_s ts)))
  | Coq_term_union (u, k, t1) ->
    Obj.magic peval_union _UU03a3_ u k
      (coq_CanonTerm_to_Term _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k)
        (peval2 _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k) t1))
  | Coq_term_record (r, ts) ->
    Obj.magic peval_record _UU03a3_ r
      (Coq_env.map (fun b t1 ->
        coq_CanonTerm_to_Term _UU03a3_ b.Binding.coq_type
          (peval2 _UU03a3_ b.Binding.coq_type t1))
        (typedefkit.Coq_ty.recordf_ty r) ts)

  (** val peval :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Term -> coq_Term **)

  let rec peval _UU03a3_ _UU03c3_ t0 =
    let res_poly =
      match t0 with
      | Coq_term_var (x, _UU03c3_0, lIn) ->
        Some (Coq_term_var (x, _UU03c3_0, lIn))
      | Coq_term_val (_UU03c3_0, v) -> Some (Coq_term_val (_UU03c3_0, v))
      | Coq_term_binop (_, _, _, op, t1, t2) ->
        (match op with
         | Coq_bop.Coq_cons _UU03c3_0 ->
           Some
             (peval_binop' _UU03a3_ _UU03c3_0 (Coq_ty.Coq_list _UU03c3_0)
               (Coq_ty.Coq_list _UU03c3_0) (Coq_bop.Coq_cons _UU03c3_0)
               (peval _UU03a3_ _UU03c3_0 t1)
               (peval _UU03a3_ (Coq_ty.Coq_list _UU03c3_0) t2))
         | _ -> None)
      | _ -> None
    in
    (match res_poly with
     | Some t1 -> t1
     | None ->
       coq_CanonTerm_to_Term _UU03a3_ _UU03c3_ (peval2 _UU03a3_ _UU03c3_ t0))

  (** val pevals :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Term)
      Coq_env.coq_Env -> (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env **)

  let pevals _UU03a3_ _UU0394_ =
    Coq_env.map (fun _UU03c3_ t0 -> peval _UU03a3_ _UU03c3_ t0) _UU0394_

  type 'n coq_SMatchResult =
    ('n coq_PatternCase, ('n, Coq_ty.coq_Ty, coq_Term) coq_NamedEnv) sigT

  (** val pattern_match_term_reverse :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
      Coq_ty.coq_Ty, coq_Term) coq_NamedEnv -> coq_Term **)

  let rec pattern_match_term_reverse _UU03a3_ _ pat pc ts =
    match pat with
    | Coq_pat_var (x, _UU03c3_0) ->
      Coq_env.head Coq_ctx.Coq_nil { Binding.name = x; Binding.coq_type =
        _UU03c3_0 } ts
    | Coq_pat_bool -> Coq_term_val (Coq_ty.Coq_bool, pc)
    | Coq_pat_list (_UU03c3_, x, y) ->
      (match Obj.magic pc with
       | Coq_true ->
         Coq_term_val ((Coq_ty.Coq_list _UU03c3_),
           (Obj.magic Datatypes.Coq_nil))
       | Coq_false ->
         let Coq_env.Coq_isSnoc (eh, t0) =
           Obj.magic Coq_env.view
             (coq_PatternCaseCtx (Coq_ty.Coq_list _UU03c3_) (Coq_pat_list
               (_UU03c3_, x, y)) (Obj.magic Coq_false))
             ts
         in
         let Coq_env.Coq_isSnoc (_, h) =
           Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
             { Binding.name = x; Binding.coq_type = _UU03c3_ })) eh
         in
         Coq_term_binop (_UU03c3_, (Coq_ty.Coq_list _UU03c3_),
         (Coq_ty.Coq_list _UU03c3_), (Coq_bop.Coq_cons _UU03c3_), h, t0))
    | Coq_pat_pair (x, y, _UU03c3_0, _UU03c4_) ->
      let Coq_env.Coq_isSnoc (ex, v_UU03c4_) =
        Obj.magic Coq_env.view
          (coq_PatternCaseCtx (Coq_ty.Coq_prod (_UU03c3_0, _UU03c4_))
            (Coq_pat_pair (x, y, _UU03c3_0, _UU03c4_)) pc)
          ts
      in
      let Coq_env.Coq_isSnoc (_, v_UU03c3_) =
        Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          { Binding.name = x; Binding.coq_type = _UU03c3_0 })) ex
      in
      Coq_term_binop (_UU03c3_0, _UU03c4_, (Coq_ty.Coq_prod (_UU03c3_0,
      _UU03c4_)), (Coq_bop.Coq_pair (_UU03c3_0, _UU03c4_)), v_UU03c3_,
      v_UU03c4_)
    | Coq_pat_sum (_UU03c3_0, _UU03c4_, x, y) ->
      (match Obj.magic pc with
       | Coq_true ->
         Coq_term_unop (_UU03c3_0, (Coq_ty.Coq_sum (_UU03c3_0, _UU03c4_)),
           (Coq_uop.Coq_inl (_UU03c3_0, _UU03c4_)),
           (Coq_env.head Coq_ctx.Coq_nil { Binding.name = x;
             Binding.coq_type = _UU03c3_0 } ts))
       | Coq_false ->
         Coq_term_unop (_UU03c4_, (Coq_ty.Coq_sum (_UU03c3_0, _UU03c4_)),
           (Coq_uop.Coq_inr (_UU03c3_0, _UU03c4_)),
           (Coq_env.head Coq_ctx.Coq_nil { Binding.name = y;
             Binding.coq_type = _UU03c4_ } ts)))
    | Coq_pat_unit -> Coq_term_val (Coq_ty.Coq_unit, pc)
    | Coq_pat_enum e -> Coq_term_val ((Coq_ty.Coq_enum e), pc)
    | Coq_pat_bvec_split (m, n, x, y) ->
      let Coq_env.Coq_isSnoc (ex, vr) =
        Obj.magic Coq_env.view
          (coq_PatternCaseCtx (Coq_ty.Coq_bvec (add m n)) (Coq_pat_bvec_split
            (m, n, x, y)) pc)
          ts
      in
      let Coq_env.Coq_isSnoc (_, vl) =
        Obj.magic Coq_env.view (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          { Binding.name = x; Binding.coq_type = (Coq_ty.Coq_bvec m) })) ex
      in
      Coq_term_binop ((Coq_ty.Coq_bvec m), (Coq_ty.Coq_bvec n),
      (Coq_ty.Coq_bvec (add m n)), (Coq_bop.Coq_bvapp (m, n)), vl, vr)
    | Coq_pat_bvec_exhaustive m -> Coq_term_val ((Coq_ty.Coq_bvec m), pc)
    | Coq_pat_tuple (_UU03c3_s, _UU0394_, p) ->
      Coq_term_tuple (_UU03c3_s,
        (tuple_pattern_match_env_reverse _UU03c3_s _UU0394_ p ts))
    | Coq_pat_record (r, _UU0394_, p) ->
      Coq_term_record (r,
        (record_pattern_match_env_reverse (typedefkit.Coq_ty.recordf_ty r)
          _UU0394_ p ts))
    | Coq_pat_union (u, x) ->
      let Coq_existT (k, pc0) = Obj.magic pc in
      Coq_term_union (u, k,
      (pattern_match_term_reverse _UU03a3_ (typedefkit.Coq_ty.unionk_ty u k)
        (x k) pc0 ts))

  (** val seval_exp :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SStore -> Coq_ty.coq_Ty -> coq_Exp -> coq_Term **)

  let rec seval_exp _UU0393_ _UU03a3_ _UU03b4_ _ = function
  | Coq_exp_var (_UU03c2_, _UU03c3_0, xIn_UU0393_) ->
    Coq_env.lookup _UU0393_ _UU03b4_ { Binding.name = _UU03c2_;
      Binding.coq_type = _UU03c3_0 } xIn_UU0393_
  | Coq_exp_val (_UU03c3_, v) -> Coq_term_val (_UU03c3_, v)
  | Coq_exp_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op, e1, e2) ->
    Coq_term_binop (_UU03c3_1, _UU03c3_2, _UU03c3_3, op,
      (seval_exp _UU0393_ _UU03a3_ _UU03b4_ _UU03c3_1 e1),
      (seval_exp _UU0393_ _UU03a3_ _UU03b4_ _UU03c3_2 e2))
  | Coq_exp_unop (_UU03c3_1, _UU03c3_2, op, e0) ->
    Coq_term_unop (_UU03c3_1, _UU03c3_2, op,
      (seval_exp _UU0393_ _UU03a3_ _UU03b4_ _UU03c3_1 e0))
  | Coq_exp_list (_UU03c3_0, es) ->
    term_list _UU03a3_ _UU03c3_0
      (ListDef.map (seval_exp _UU0393_ _UU03a3_ _UU03b4_ _UU03c3_0) es)
  | Coq_exp_bvec (n, es) ->
    term_bvec _UU03a3_ n
      (map (seval_exp _UU0393_ _UU03a3_ _UU03b4_ Coq_ty.Coq_bool) n es)
  | Coq_exp_tuple (_UU03c3_s, es) ->
    Coq_term_tuple (_UU03c3_s,
      (Coq_env.map (seval_exp _UU0393_ _UU03a3_ _UU03b4_) _UU03c3_s es))
  | Coq_exp_union (e0, k, e1) ->
    Coq_term_union (e0, k,
      (seval_exp _UU0393_ _UU03a3_ _UU03b4_
        (typedefkit.Coq_ty.unionk_ty e0 k) e1))
  | Coq_exp_record (r, es) ->
    Coq_term_record (r,
      (Coq_env.map (fun b ->
        seval_exp _UU0393_ _UU03a3_ _UU03b4_ b.Binding.coq_type)
        (typedefkit.Coq_ty.recordf_ty r) es))

  (** val seval_exps :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SStore -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> ('a1, Coq_ty.coq_Ty, coq_Exp) coq_NamedEnv -> ('a1, Coq_ty.coq_Ty,
      coq_Term) coq_NamedEnv **)

  let seval_exps _UU0393_ _UU03a3_ _UU03b4_ _UU0394_ =
    Coq_env.map (fun b e ->
      peval _UU03a3_ b.Binding.coq_type
        (seval_exp _UU0393_ _UU03a3_ _UU03b4_ b.Binding.coq_type e))
      _UU0394_

  type 'p coq_Precise = { prec_input : Coq_ty.coq_Ty Coq_ctx.coq_Ctx;
                          prec_output : Coq_ty.coq_Ty Coq_ctx.coq_Ctx }

  (** val prec_input :
      ('a1 -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx) -> 'a1 -> 'a1 coq_Precise ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx **)

  let prec_input _ _ p =
    p.prec_input

  (** val prec_output :
      ('a1 -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx) -> 'a1 -> 'a1 coq_Precise ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx **)

  let prec_output _ _ p =
    p.prec_output
 end
