(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Coq Require Import
     Strings.String
     Bool
     Lia
     Lists.List
     ZArith.ZArith.
From Equations Require Import
     Equations.
From stdpp Require Import
     base.
From stdpp Require
     finite strings.
From Katamaran Require Import
     Base
     Bitvector
     Syntax.TypeDecl.

Import ListNotations.
Local Unset Equations Derive Equations.
Local Set Implicit Arguments.


(* Taken from Coq >= 8.15 SigTNotations *)
Local Notation "( x ; y )" := (existT x y) (only parsing).

Definition xlen            := 32.
Definition byte            := 8.
Definition bytes_per_word  := 4.
Definition bytes_per_instr := 4.
Definition word            := bytes_per_word * byte.
Definition xlenbytes       := 4.
Definition xlenbits        := xlenbytes * byte.

Definition bv_instrsize {n} : bv n := bv.of_nat bytes_per_instr.

#[export] Instance IsTrue_bytes_xlenbytes (x y: nat) (H : IsTrue (x <=? y)): IsTrue (x * byte <=? y * byte).
Proof.
  revert y H.
  induction x; cbn.
  - constructor. constructor.
  - intros [|y]; cbn; auto.
Defined.

Definition Xlenbits : Set := bv xlenbits.
Definition Addr : Set     := bv xlenbits.
Definition Word : Set     := bv word.
Definition Byte : Set     := bv byte.

(* 1. Definition of RAM memory *)
Definition minAddr : N := 0.
Definition lenAddr : N := 2^10.
Definition maxAddr : N := minAddr + lenAddr.
Lemma minAddr_rep : (minAddr < bv.exp2 xlenbits)%N.
Proof. now compute. Qed.
Lemma maxAddr_rep : (maxAddr < bv.exp2 xlenbits)%N.
Proof. now compute. Qed.
Lemma lenAddr_rep : (lenAddr < bv.exp2 xlenbits)%N.
Proof. now compute. Qed.
(* xlenbits is made opaque further on and it really must be non-zero. *)
Lemma xlenbits_pos : (xlenbits > 0).
Proof. cbv. lia. Qed.
(* All addresses present in RAM memory *)
Definition liveAddrs := bv.seqBv (@bv.of_N xlenbits minAddr) lenAddr.

(* 2. Definition of MMIO memory *)
(* For now, we only consider the one femtokernel address to be part of the MMIO-mapped memory. *)
(* We place the MMIO memory after the RAM memory, and have the PMP entry for the adversary in the FemtoKernel provide access up to but not including the MMIO memory. The lack of an entry for the MMIO memory will ensure that this memory is addressable by the kernel. *)
Definition mmioStartAddr := maxAddr.
Definition mmioLenAddr := (maxAddr + lenAddr)%N.
Definition mmioAddrs : list Addr := bv.seqBv (@bv.of_N xlenbits mmioStartAddr) mmioLenAddr.
Definition isMMIO a : Prop := a ∈ mmioAddrs.
Fixpoint withinMMIO (a : Addr) (size : nat) : Prop :=
  match size with
  | O => False (* Avoid allowing and hence recording zero-width MMIO events *)
  | 1 => a ∈ mmioAddrs
  | S size' => a ∈ mmioAddrs /\ withinMMIO (bv.add (bv.one) a) size' end.
#[export] Instance withinMMIODec a size: Decision (withinMMIO a size).
Proof. generalize a. induction size.
       - apply _.
       - intro a'. cbn. destruct size; first apply _.
         apply decidable.and_dec; [apply _|auto].
Qed.

(* 3. Definition of machinery required to do MMIO *)
Class MMIOEnv : Type := {
  State : Type;
  (* The combination of these two allows us to simulate a finitely non-deterministic I/O device, by quantifying over these transition functions at the top-level and adding restrictions *)
  state_tra_read : State -> Addr -> forall (bytes : nat) , State * bv (bytes * 8);
  state_tra_write : State -> Addr -> forall (bytes : nat) , bv (bytes * 8) -> State;
  state_init : State; (* Useful mostly when reasoning about concrete devices *)
}.
Parameter mmioenv : MMIOEnv.
#[export] Existing Instance mmioenv.
#[export] Instance state_inhabited : Inhabited Base.State := populate (state_init).

Require Import stdpp.finite.
(* Addresses cannot both be MMIO and RAM. We need to know this when trying to inject pointsto-chunks for RAM back into maps of pointsto chunks. *)

Lemma mmio_ram_False a : a ∈ liveAddrs → a ∈ mmioAddrs -> False.
Proof. unfold liveAddrs, mmioAddrs, mmioStartAddr, mmioLenAddr, maxAddr, minAddr, lenAddr.
       apply bv.seqBv_no_overlap; cbn; lia.
Qed.

Inductive Privilege : Set :=
| User
| Machine
.

(* Enum for available CRSs' *)
Inductive CSRIdx : Set :=
| MStatus
| MTvec
| MCause
| MEpc
| MPMP0CFG
| MPMPADDR0
| MPMPADDR1
.

Definition NumPmpEntries := 2.
(* NOTE: PMP CSRs limited to 1 for now *)
Inductive PmpCfgIdx : Set :=
| PMP0CFG
| PMP1CFG
.

Inductive PmpCfgPerm : Set :=
| PmpO
| PmpR
| PmpW
| PmpX
| PmpRW
| PmpRX
| PmpWX
| PmpRWX.

Inductive PmpAddrIdx : Set :=
| PMPADDR0
| PMPADDR1
.

(* NOTE: PMP Addr Match Type limited to OFF and TOR for now *)
Inductive PmpAddrMatchType : Set :=
| OFF
| TOR
.

Inductive PmpMatch : Set :=
| PMP_Success
| PMP_Continue
| PMP_Fail
.

Inductive PmpAddrMatch : Set :=
| PMP_NoMatch
| PMP_PartialMatch
| PMP_Match
.

Inductive ROP : Set :=
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
.

Inductive IOP : Set :=
| RISCV_ADDI
| RISCV_SLTI
| RISCV_SLTIU
| RISCV_ANDI
| RISCV_ORI
| RISCV_XORI
.

Inductive SOP : Set :=
| RISCV_SLLI
| RISCV_SRLI
| RISCV_SRAI
.

Inductive UOP : Set :=
| RISCV_LUI
| RISCV_AUIPC
.

Inductive BOP : Set :=
| RISCV_BEQ
| RISCV_BNE
| RISCV_BLT
| RISCV_BGE
| RISCV_BLTU
| RISCV_BGEU
.

(* Zicsr extension, only support for Read-Write (no set or clear) *)
Inductive CSROP : Set :=
| CSRRW
| CSRRS
| CSRRC
.

Inductive MOP : Set :=
| RISCV_MUL
| RISCV_MULH
| RISCV_MULHSU
| RISCV_MULHU
.

Inductive Retired : Set :=
| RETIRE_SUCCESS
| RETIRE_FAIL
.

Inductive WordWidth :=
| BYTE
| HALF
| WORD
.

Inductive Enums : Set :=
| privilege
| csridx
| pmpcfgidx
| pmpcfgperm
| pmpaddridx
| pmpaddrmatchtype
| pmpmatch
| pmpaddrmatch
| rop
| iop
| sop
| uop
| bop
| csrop
| retired
| wordwidth
| mop
.

Definition RegIdx := bv 5.
Bind Scope bv_scope with RegIdx.

Inductive AST : Set :=
| RTYPE (rs2 rs1 rd : RegIdx) (op : ROP)
| ITYPE (imm : bv 12) (rs1 rd : RegIdx) (op : IOP)
| SHIFTIOP (shamt : bv 6) (rs1 rd : RegIdx) (op : SOP)
| UTYPE (imm : bv 20) (rd : RegIdx) (op : UOP)
| BTYPE (imm : bv 13) (rs2 rs1 : RegIdx) (op : BOP)
| RISCV_JAL (imm : bv 21) (rd : RegIdx)
| RISCV_JALR (imm : bv 12) (rs1 rd : RegIdx)
| LOAD (imm : bv 12) (rs1 rd : RegIdx) (is_unsigned : bool) (width : WordWidth)
| STORE (imm : bv 12) (rs2 rs1 : RegIdx) (width : WordWidth)
| ECALL
| EBREAK
| MRET
| CSR (csr : CSRIdx) (rs1 rd : RegIdx) (is_imm : bool) (csrop : CSROP)
| MUL (rs2 rs1 rd : RegIdx) (high signed1 signed2 : bool)
.

Inductive AccessType : Set :=
| Read
| Write
| ReadWrite
| Execute
.

Inductive ExceptionType : Set :=
| E_Fetch_Access_Fault
| E_Load_Access_Fault
| E_SAMO_Access_Fault
| E_U_EnvCall
| E_M_EnvCall
| E_Illegal_Instr
.

Inductive FetchResult : Set :=
| F_Base (v : Word)
| F_Error (e : ExceptionType) (v : Xlenbits)
.

(* NOTE: simplified to only take the ctl_trap constructor into account
         (other constructors are for mret, sret and uret, not considered atm) *)
Inductive CtlResult : Set :=
| CTL_TRAP (e : ExceptionType)
| CTL_MRET
.

Inductive MemoryOpResult (bytes : nat): Set :=
| MemValue (bs : bv (bytes * 8))
| MemException (e : ExceptionType)
.

Inductive ASTConstructor : Set :=
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
.

Inductive AccessTypeConstructor : Set :=
| KRead
| KWrite
| KReadWrite
| KExecute
.

Inductive ExceptionTypeConstructor : Set :=
| KE_Fetch_Access_Fault
| KE_Load_Access_Fault
| KE_SAMO_Access_Fault
| KE_U_EnvCall
| KE_M_EnvCall
| KE_Illegal_Instr
.

Inductive MemoryOpResultConstructor : Set :=
| KMemValue
| KMemException
.

Inductive FetchResultConstructor : Set :=
| KF_Base
| KF_Error
.

Inductive CtlResultConstructor : Set :=
| KCTL_TRAP
| KCTL_MRET
.

Inductive Unions : Set :=
| ast
| access_type
| exception_type
| memory_op_result (bytes : nat)
| fetch_result
| ctl_result
(* | pmp_entries *)
.

Record Pmpcfg_ent : Set :=
  MkPmpcfg_ent
    { L : bool;
      A : PmpAddrMatchType;
      X : bool;
      W : bool;
      R : bool;
    }.

Record Mstatus : Set :=
  MkMstatus
    { MPP : Privilege
    }.

Inductive Records : Set :=
| rpmpcfg_ent
| rmstatus
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Enums.
  Derive NoConfusion for Privilege.
  Derive NoConfusion for CSRIdx.
  Derive NoConfusion for PmpCfgIdx.
  Derive NoConfusion for PmpCfgPerm.
  Derive NoConfusion for PmpAddrIdx.
  Derive NoConfusion for PmpAddrMatchType.
  Derive NoConfusion for PmpMatch.
  Derive NoConfusion for PmpAddrMatch.
  Derive NoConfusion for ROP.
  Derive NoConfusion for IOP.
  Derive NoConfusion for SOP.
  Derive NoConfusion for UOP.
  Derive NoConfusion for BOP.
  Derive NoConfusion for CSROP.
  Derive NoConfusion for MOP.
  Derive NoConfusion for Retired.
  Derive NoConfusion for WordWidth.
  Derive NoConfusion for Unions.
  Derive NoConfusion for AST.
  Derive NoConfusion for ASTConstructor.
  Derive NoConfusion for AccessType.
  Derive NoConfusion for AccessTypeConstructor.
  Derive NoConfusion for ExceptionType.
  Derive NoConfusion for ExceptionTypeConstructor.
  Derive NoConfusion for FetchResult.
  Derive NoConfusion for FetchResultConstructor.
  Derive NoConfusion for CtlResult.
  Derive NoConfusion for CtlResultConstructor.
  Derive NoConfusion for MemoryOpResult.
  Derive NoConfusion for MemoryOpResultConstructor.
  Derive NoConfusion for Records.
  Derive NoConfusion for Pmpcfg_ent.
  Derive NoConfusion for Mstatus.
End TransparentObligations.

Derive EqDec for Enums.
Derive EqDec for Privilege.
Derive EqDec for CSRIdx.
Derive EqDec for PmpCfgIdx.
Derive EqDec for PmpCfgPerm.
Derive EqDec for PmpAddrIdx.
Derive EqDec for PmpAddrMatchType.
Derive EqDec for PmpMatch.
Derive EqDec for PmpAddrMatch.
Derive EqDec for ROP.
Derive EqDec for IOP.
Derive EqDec for SOP.
Derive EqDec for UOP.
Derive EqDec for BOP.
Derive EqDec for CSROP.
Derive EqDec for MOP.
Derive EqDec for Retired.
Derive EqDec for WordWidth.
Derive EqDec for Unions.
Derive EqDec for AST.
Derive EqDec for ASTConstructor.
Derive EqDec for AccessType.
Derive EqDec for AccessTypeConstructor.
Derive EqDec for ExceptionType.
Derive EqDec for ExceptionTypeConstructor.
Derive EqDec for FetchResult.
Derive EqDec for FetchResultConstructor.
Derive EqDec for CtlResult.
Derive EqDec for CtlResultConstructor.
Derive EqDec for MemoryOpResult.
Derive EqDec for MemoryOpResultConstructor.
Derive EqDec for Records.
Derive EqDec for Pmpcfg_ent.
Derive EqDec for Mstatus.

Section Finite.
  Import stdpp.finite.

  Local Obligation Tactic :=
    try finite_from_eqdec.

  #[export,program] Instance Privilege_finite : Finite Privilege :=
    {| enum := [User;Machine] |}.

  #[export,program] Instance CSRIdx_finite : Finite CSRIdx :=
    {| enum := [MStatus;MTvec;MCause;MEpc;MPMP0CFG;MPMPADDR0;MPMPADDR1] |}.

  #[export,program] Instance PmpCfgIdx_finite : Finite PmpCfgIdx :=
    {| enum := [PMP0CFG;PMP1CFG] |}.

  #[export,program] Instance PmpCfgPerm_finite : Finite PmpCfgPerm :=
    {| enum := [PmpO; PmpR; PmpW; PmpX; PmpRW; PmpRX; PmpWX; PmpRWX] |}.

  #[export,program] Instance PmpAddrIdx_finite : Finite PmpAddrIdx :=
    {| enum := [PMPADDR0;PMPADDR1] |}.

  #[export,program] Instance PmpAddrMatchType_finite : Finite PmpAddrMatchType :=
    {| enum := [OFF;TOR] |}.

  #[export,program] Instance PmpMatch_finite : Finite PmpMatch :=
    {| enum := [PMP_Success;PMP_Continue;PMP_Fail] |}.

  #[export,program] Instance PmpAddrMatch_finite : Finite PmpAddrMatch :=
    {| enum := [PMP_NoMatch;PMP_PartialMatch;PMP_Match] |}.

  #[export,program] Instance ROP_finite :
    Finite ROP :=
    {| enum := [RISCV_ADD;RISCV_SUB;RISCV_SLT;RISCV_SLTU;RISCV_SLL;RISCV_SRL;RISCV_SRA;RISCV_AND;RISCV_OR;RISCV_XOR] |}.

  #[export,program] Instance IOP_finite :
    Finite IOP :=
    {| enum := [RISCV_ADDI;RISCV_SLTI;RISCV_SLTIU;RISCV_ANDI;RISCV_ORI;RISCV_XORI] |}.

  #[export,program] Instance SOP_finite :
    Finite SOP :=
    {| enum := [RISCV_SLLI;RISCV_SRLI;RISCV_SRAI] |}.

  #[export,program] Instance UOP_finite :
    Finite UOP :=
    {| enum := [RISCV_LUI;RISCV_AUIPC] |}.

  #[export,program] Instance BOP_finite :
    Finite BOP :=
    {| enum := [RISCV_BEQ;RISCV_BNE;RISCV_BLT;RISCV_BGE;RISCV_BLTU;RISCV_BGEU] |}.

  #[export,program] Instance CSROP_finite :
    Finite CSROP :=
    {| enum := [CSRRW;CSRRS;CSRRC] |}.

  #[export,program] Instance MOP_finite :
    Finite MOP :=
    {| enum := [RISCV_MUL; RISCV_MULH; RISCV_MULHU; RISCV_MULHSU] |}.

  #[export,program] Instance Retired_finite :
    Finite Retired :=
    {| enum := [RETIRE_SUCCESS; RETIRE_FAIL] |}.

  #[export,program] Instance WordWidth_finite :
    Finite WordWidth :=
    {| enum := [BYTE; HALF; WORD] |}.

  #[export,program] Instance ASTConstructor_finite :
    Finite ASTConstructor :=
    {| enum := [KRTYPE;KITYPE;KSHIFTIOP;KUTYPE;KBTYPE;KRISCV_JAL;KRISCV_JALR;KLOAD;KSTORE;KECALL;KEBREAK;KMRET;KCSR;KMUL] |}.

  #[export,program] Instance AccessType_finite :
    Finite AccessType :=
    {| enum := [Read; Write; ReadWrite; Execute] |}.

  #[export,program] Instance AccessTypeConstructor_finite :
    Finite AccessTypeConstructor :=
    {| enum := [KRead;KWrite;KReadWrite;KExecute] |}.

  #[export,program] Instance ExceptionTypeConstructor_finite :
    Finite ExceptionTypeConstructor :=
    {| enum := [KE_Fetch_Access_Fault;KE_Load_Access_Fault;KE_SAMO_Access_Fault;
                KE_U_EnvCall;KE_M_EnvCall;KE_Illegal_Instr] |}.

  #[export,program] Instance FetchResultConstructor_finite :
    Finite FetchResultConstructor :=
    {| enum := [KF_Base;KF_Error] |}.

  #[export,program] Instance CtlResultConstructor_finite :
    Finite CtlResultConstructor :=
    {| enum := [KCTL_TRAP;KCTL_MRET] |}.

  #[export,program] Instance MemoryOpResultConstructor_finite :
    Finite MemoryOpResultConstructor :=
    {| enum := [KMemValue;KMemException] |}.
End Finite.

Module Export RiscvPmpBase <: Base.

  Import ctx.notations.
  Import ctx.resolution.
  Import env.notations.
  Import stdpp.finite.

  #[export] Instance typedeclkit : TypeDeclKit :=
    {| enumi := Enums;
       unioni := Unions;
       recordi := Records;
    |}.

  (* Override notations of bindigns to put the variable x into string_scope. *)
  Notation "x ∷ t" := (MkB x%string t) : ctx_scope.

  Definition ty_xlenbits                       := (ty.bvec xlenbits).
  Definition ty_word                           := (ty.bvec word).
  Definition ty_byte                           := (ty.bvec byte).
  Definition ty_bytes (bytes : nat)            := (ty.bvec (bytes * byte)).
  Definition ty_regno                          := (ty.bvec 5).
  Definition ty_privilege                      := (ty.enum privilege).
  Definition ty_priv_level                     := (ty.bvec 2).
  Definition ty_csridx                         := (ty.enum csridx).
  Definition ty_pmpcfgidx                      := (ty.enum pmpcfgidx).
  Definition ty_pmpcfgperm                     := (ty.enum pmpcfgperm).
  Definition ty_pmpaddridx                     := (ty.enum pmpaddridx).
  Definition ty_pmpaddrmatchtype               := (ty.enum pmpaddrmatchtype).
  Definition ty_pmpmatch                       := (ty.enum pmpmatch).
  Definition ty_pmpaddrmatch                   := (ty.enum pmpaddrmatch).
  Definition ty_pmp_addr_range                 := (ty.option (ty.prod ty_xlenbits ty_xlenbits)).
  Definition ty_rop                            := (ty.enum rop).
  Definition ty_iop                            := (ty.enum iop).
  Definition ty_sop                            := (ty.enum sop).
  Definition ty_uop                            := (ty.enum uop).
  Definition ty_bop                            := (ty.enum bop).
  Definition ty_csrop                          := (ty.enum csrop).
  Definition ty_mop                            := (ty.enum mop).
  Definition ty_retired                        := (ty.enum retired).
  Definition ty_word_width                     := (ty.enum wordwidth).
  Definition ty_mcause                         := (ty_xlenbits).
  Definition ty_exc_code                       := (ty.bvec 8).
  Definition ty_ast                            := (ty.union ast).
  Definition ty_access_type                    := (ty.union access_type).
  Definition ty_exception_type                 := (ty.union exception_type).
  Definition ty_memory_op_result (bytes : nat) := (ty.union (memory_op_result bytes)).
  Definition ty_fetch_result                   := (ty.union fetch_result).
  Definition ty_ctl_result                     := (ty.union ctl_result).
  Definition ty_pmpcfg_ent                     := (ty.record rpmpcfg_ent).
  Definition ty_mstatus                        := (ty.record rmstatus).
  Definition ty_pmpentry                       := (ty.prod ty_pmpcfg_ent ty_xlenbits).
  Definition ty_pmpentries                     := (ty.list (ty.prod ty_pmpcfg_ent ty_xlenbits)).

  Definition enum_denote (e : Enums) : Set :=
    match e with
    | privilege        => Privilege
    | csridx           => CSRIdx
    | pmpcfgidx        => PmpCfgIdx
    | pmpcfgperm       => PmpCfgPerm
    | pmpaddridx       => PmpAddrIdx
    | pmpaddrmatchtype => PmpAddrMatchType
    | pmpmatch         => PmpMatch
    | pmpaddrmatch     => PmpAddrMatch
    | rop              => ROP
    | iop              => IOP
    | sop              => SOP
    | uop              => UOP
    | bop              => BOP
    | csrop            => CSROP
    | mop              => MOP
    | retired          => Retired
    | wordwidth        => WordWidth
    end.

  Definition union_denote (U : Unions) : Set :=
    match U with
    | ast                    => AST
    | access_type            => AccessType
    | exception_type         => ExceptionType
    | memory_op_result bytes => MemoryOpResult bytes
    | fetch_result           => FetchResult
    | ctl_result             => CtlResult
    (* | pmp_entries      => Coq type in the model for pmp_entries  *)
    end.

  Definition record_denote (R : Records) : Set :=
    match R with
    | rpmpcfg_ent => Pmpcfg_ent
    | rmstatus    => Mstatus
    end.

  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit :=
    {| enumt := enum_denote;
       uniont := union_denote;
       recordt := record_denote;
    |}.

  Definition union_constructor (U : Unions) : Set :=
    match U with
    | ast                    => ASTConstructor
    | access_type            => AccessTypeConstructor
    | exception_type         => ExceptionTypeConstructor
    | memory_op_result bytes => MemoryOpResultConstructor
    | fetch_result           => FetchResultConstructor
    | ctl_result             => CtlResultConstructor
    (* | pmp_entries   => PmpEntriesConstructor *)
    end.

  Definition union_constructor_type (U : Unions) : union_constructor U -> Ty :=
    match U with
    | ast              => fun K =>
                            match K with
                            | KRTYPE      => ty.tuple [ty_regno; ty_regno; ty_regno; ty_rop]
                            | KITYPE      => ty.tuple [ty.bvec 12; ty_regno; ty_regno; ty_iop]
                            | KSHIFTIOP   => ty.tuple [ty.bvec 6;  ty_regno; ty_regno; ty_sop]
                            | KUTYPE      => ty.tuple [ty.bvec 20; ty_regno; ty_uop]
                            | KBTYPE      => ty.tuple [ty.bvec 13; ty_regno; ty_regno; ty_bop]
                            | KRISCV_JAL  => ty.tuple [ty.bvec 21; ty_regno]
                            | KRISCV_JALR => ty.tuple [ty.bvec 12; ty_regno; ty_regno]
                            | KLOAD       => ty.tuple [ty.bvec 12; ty_regno; ty_regno; ty.bool; ty_word_width]
                            | KSTORE      => ty.tuple [ty.bvec 12; ty_regno; ty_regno; ty_word_width]
                            | KECALL      => ty.unit
                            | KEBREAK     => ty.unit
                            | KMRET       => ty.unit
                            | KCSR        => ty.tuple [ty_csridx; ty_regno; ty_regno; ty.bool; ty_csrop]
                            | KMUL        => ty.tuple [ty_regno; ty_regno; ty_regno; ty.bool; ty.bool; ty.bool]
                            end
    | access_type      => fun _ => ty.unit
    | exception_type   => fun _ => ty.unit
    | memory_op_result bytes => fun K =>
                                  match K with
                                  | KMemValue     => ty.bvec (bytes * 8)
                                  | KMemException => ty_exception_type
                                  end
    | fetch_result     => fun K =>
                            match K with
                            | KF_Base  => ty_word
                            | KF_Error => ty.prod ty_exception_type ty_word
                            end
    | ctl_result       => fun K =>
                            match K with
                            | KCTL_TRAP => ty_exception_type
                            | KCTL_MRET => ty.unit
                            end
    end.

  #[export] Instance eqdec_enum_denote E : EqDec (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance finite_enum_denote E : finite.Finite (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance eqdec_union_denote U : EqDec (union_denote U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_union_constructor U : EqDec (union_constructor U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance finite_union_constructor U : finite.Finite (union_constructor U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_record_denote R : EqDec (record_denote R) :=
    ltac:(destruct R; auto with typeclass_instances).

  Definition union_unfold (U : unioni) : uniont U -> { K & Val (union_constructor_type U K) } :=
    match U with
    | ast              => fun Kv =>
                            match Kv with
                            | RTYPE rs2 rs1 rd op           => existT KRTYPE (tt , rs2 , rs1 , rd , op)
                            | ITYPE imm rs1 rd op           => existT KITYPE (tt , imm , rs1 , rd , op)
                            | SHIFTIOP shamt rs1 rd op      => existT KSHIFTIOP (tt , shamt , rs1 , rd , op)
                            | UTYPE imm rd op               => existT KUTYPE (tt , imm , rd , op)
                            | BTYPE imm rs2 rs1 op          => existT KBTYPE (tt , imm , rs2 , rs1 , op)
                            | RISCV_JAL imm rd              => existT KRISCV_JAL (tt , imm , rd)
                            | RISCV_JALR imm rs1 rd         => existT KRISCV_JALR (tt , imm , rs1 , rd)
                            | LOAD imm rs1 rd is_unsigned w => existT KLOAD (tt , imm , rs1 , rd , is_unsigned , w)
                            | STORE imm rs2 rs1 w           => existT KSTORE (tt , imm , rs2 , rs1 , w)
                            | ECALL                         => existT KECALL tt
                            | EBREAK                        => existT KEBREAK tt
                            | MRET                          => existT KMRET tt
                            | CSR csr rs1 rd is_imm op      => existT KCSR (tt , csr , rs1 , rd , is_imm , op)
                            | MUL rs2 rs1 rd h s1 s2        => existT KMUL (tt, rs2 , rs1 , rd , h, s1, s2 )
                            end
    | access_type      => fun Kv =>
                            match Kv with
                            | Read      => existT KRead tt
                            | Write     => existT KWrite tt
                            | ReadWrite => existT KReadWrite tt
                            | Execute   => existT KExecute tt
                            end
    | exception_type   => fun Kv =>
                            match Kv with
                            | E_Fetch_Access_Fault => existT KE_Fetch_Access_Fault tt
                            | E_Load_Access_Fault  => existT KE_Load_Access_Fault tt
                            | E_SAMO_Access_Fault  => existT KE_SAMO_Access_Fault tt
                            | E_U_EnvCall          => existT KE_U_EnvCall tt
                            | E_M_EnvCall          => existT KE_M_EnvCall tt
                            | E_Illegal_Instr      => existT KE_Illegal_Instr tt
                            end
    | memory_op_result bytes => fun Kv =>
                            match Kv with
                            | MemValue _ v     => existT KMemValue v
                            | MemException _ e => existT KMemException e
                            end
    | fetch_result     => fun Kv =>
                            match Kv with
                            | F_Base v    => existT KF_Base v
                            | F_Error e v => existT KF_Error (e , v)
                            end
    | ctl_result       => fun Kv =>
                            match Kv with
                            | CTL_TRAP e => existT KCTL_TRAP e
                            | CTL_MRET   => existT KCTL_MRET tt
                            end
    end.

  Definition union_fold (U : unioni) : { K & Val (union_constructor_type U K) } -> uniont U :=
      match U with
      | ast              => fun Kv =>
                              match Kv with
                              | existT KRTYPE (tt , rs2 , rs1 , rd , op)             => RTYPE rs2 rs1 rd op
                              | existT KITYPE (tt , imm , rs1 , rd , op)             => ITYPE imm rs1 rd op
                              | existT KSHIFTIOP (tt , shamt , rs1 , rd , op)        => SHIFTIOP shamt rs1 rd op
                              | existT KUTYPE (tt , imm , rd , op)                   => UTYPE imm rd op
                              | existT KBTYPE (tt , imm , rs2 , rs1 , op)            => BTYPE imm rs2 rs1 op
                              | existT KRISCV_JAL (tt , imm , rd)                    => RISCV_JAL imm rd
                              | existT KRISCV_JALR (tt , imm , rs1 , rd)             => RISCV_JALR imm rs1 rd
                              | existT KLOAD (tt , imm , rs1 , rd , is_unsigned , w) => LOAD imm rs1 rd is_unsigned w
                              | existT KSTORE (tt , imm , rs2 , rs1 , w)             => STORE imm rs2 rs1 w
                              | existT KECALL tt                                     => ECALL
                              | existT KEBREAK tt                                    => EBREAK
                              | existT KMRET tt                                      => MRET
                              | existT KCSR (tt , csr , rs1 , rd , is_imm , op)      => CSR csr rs1 rd is_imm op
                              | existT KMUL (tt, rs2 , rs1 , rd , h, s1, s2 )        => MUL rs2 rs1 rd h s1 s2
                              end
      | access_type      => fun Kv =>
                              match Kv with
                              | existT KRead tt      => Read
                              | existT KWrite tt     => Write
                              | existT KReadWrite tt => ReadWrite
                              | existT KExecute tt   => Execute
                              end
      | exception_type   => fun Kv =>
                              match Kv with
                              | existT KE_Fetch_Access_Fault tt => E_Fetch_Access_Fault
                              | existT KE_Load_Access_Fault tt  => E_Load_Access_Fault
                              | existT KE_SAMO_Access_Fault tt  => E_SAMO_Access_Fault
                              | existT KE_U_EnvCall tt          => E_U_EnvCall
                              | existT KE_M_EnvCall tt          => E_M_EnvCall
                              | existT KE_Illegal_Instr tt      => E_Illegal_Instr
                              end
      | memory_op_result bytes => fun Kv =>
                              match Kv with
                              | existT KMemValue v     => MemValue bytes v
                              | existT KMemException e => MemException bytes e
                              end
      | fetch_result     => fun Kv =>
                              match Kv with
                              | existT KF_Base v        => F_Base v
                              | existT KF_Error (e , v) => F_Error e v
                              end
      | ctl_result       => fun Kv =>
                              match Kv with
                              | existT KCTL_TRAP e  => CTL_TRAP e
                              | existT KCTL_MRET tt => CTL_MRET
                              end
      end.

  Definition record_field_type (R : recordi) : NCtx string Ty :=
    match R with
    | rpmpcfg_ent => [ "L" ∷ ty.bool;
                       "A" ∷ ty_pmpaddrmatchtype;
                       "X" ∷ ty.bool;
                       "W" ∷ ty.bool;
                       "R" ∷ ty.bool
      ]
    | rmstatus    => ["MPP" ∷ ty_privilege
      ]
    end.

  Equations record_fold (R : recordi) : NamedEnv Val (record_field_type R) -> recordt R :=
  | rpmpcfg_ent | [l;a;x;w;r]%env := MkPmpcfg_ent l a x w r
  | rmstatus    | [mpp]%env       := MkMstatus mpp.

  Equations record_unfold (R : recordi) : recordt R -> NamedEnv Val (record_field_type R) :=
  | rpmpcfg_ent | p => [kv (_ ∷ ty.bool             ; L p);
                           (_ ∷ ty_pmpaddrmatchtype ; A p);
                           (_ ∷ ty.bool             ; X p);
                           (_ ∷ ty.bool             ; W p);
                           (_ ∷ ty.bool             ; R p) ];
  | rmstatus    | m => [kv ("MPP" ∷ ty_privilege; MPP m) ].

  #[export,refine] Instance typedefkit : TypeDefKit typedenotekit :=
    {| unionk           := union_constructor;
       unionk_ty        := union_constructor_type;
       recordf          := string;
       recordf_ty       := record_field_type;
       unionv_fold      := union_fold;
       unionv_unfold    := union_unfold;
       recordv_fold     := record_fold;
       recordv_unfold   := record_unfold;
    |}.
  Proof.
    - abstract (intros [] []; now cbn).
    - abstract (intros [] [[] x]; cbn in x;
        repeat match goal with
               | x: unit |- _ => destruct x
               | x: prod _ _ |- _ => destruct x
               end; auto).
    - abstract (now intros [] []).
    - abstract (intros []; now apply env.Forall_forall).
  Defined.

  Canonical typedeclkit.
  Canonical typedenotekit.
  Canonical typedefkit.

  #[export] Instance varkit : VarKit := DefaultVarKit.

  Section RegDeclKit.

    Inductive Reg : Ty -> Set :=
    | pc            : Reg ty_xlenbits
    | nextpc        : Reg ty_xlenbits
    | mstatus       : Reg ty_mstatus
    | mtvec         : Reg ty_xlenbits
    | mcause        : Reg ty_mcause
    | mepc          : Reg ty_xlenbits
    | cur_privilege : Reg ty_privilege
    | x1            : Reg ty_xlenbits
    | x2            : Reg ty_xlenbits
    | x3            : Reg ty_xlenbits
    | x4            : Reg ty_xlenbits
    | x5            : Reg ty_xlenbits
    | x6            : Reg ty_xlenbits
    | x7            : Reg ty_xlenbits
    | x8            : Reg ty_xlenbits
    | x9            : Reg ty_xlenbits
    | x10           : Reg ty_xlenbits
    | x11           : Reg ty_xlenbits
    | x12           : Reg ty_xlenbits
    | x13           : Reg ty_xlenbits
    | x14           : Reg ty_xlenbits
    | x15           : Reg ty_xlenbits
    | x16           : Reg ty_xlenbits
    | x17           : Reg ty_xlenbits
    | x18           : Reg ty_xlenbits
    | x19           : Reg ty_xlenbits
    | x20           : Reg ty_xlenbits
    | x21           : Reg ty_xlenbits
    | x22           : Reg ty_xlenbits
    | x23           : Reg ty_xlenbits
    | x24           : Reg ty_xlenbits
    | x25           : Reg ty_xlenbits
    | x26           : Reg ty_xlenbits
    | x27           : Reg ty_xlenbits
    | x28           : Reg ty_xlenbits
    | x29           : Reg ty_xlenbits
    | x30           : Reg ty_xlenbits
    | x31           : Reg ty_xlenbits
    | pmp0cfg       : Reg ty_pmpcfg_ent
    | pmp1cfg       : Reg ty_pmpcfg_ent
    | pmpaddr0      : Reg ty_xlenbits
    | pmpaddr1      : Reg ty_xlenbits
    .

    Import bv.notations.
    Definition reg_convert (idx : RegIdx) : option (Reg ty_xlenbits) :=
      match bv.to_bitstring idx with
      | 00000 => None
      | 00001 => Some x1
      | 00010 => Some x2
      | 00011 => Some x3
      | 00100 => Some x4
      | 00101 => Some x5
      | 00110 => Some x6
      | 00111 => Some x7
      | 01000 => Some x8
      | 01001 => Some x9
      | 01010 => Some x10
      | 01011 => Some x11
      | 01100 => Some x12
      | 01101 => Some x13
      | 01110 => Some x14
      | 01111 => Some x15
      | 10000 => Some x16
      | 10001 => Some x17
      | 10010 => Some x18
      | 10011 => Some x19
      | 10100 => Some x20
      | 10101 => Some x21
      | 10110 => Some x22
      | 10111 => Some x23
      | 11000 => Some x24
      | 11001 => Some x25
      | 11010 => Some x26
      | 11011 => Some x27
      | 11100 => Some x28
      | 11101 => Some x29
      | 11110 => Some x30
      | 11111 => Some x31
      end.

    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive Signature NoConfusion (* NoConfusionHom *) for Reg.
    End TransparentObligations.

    Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.

    (* With definitions like ty_xlenbits the equations library cannot
       derive this instance automatically. *)
    #[export,refine] Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg) :=
      fun '(existT σ x) '(existT τ y) =>
        match x , y with
        | pc            , pc            => left eq_refl
        | nextpc        , nextpc        => left eq_refl
        | mstatus       , mstatus       => left eq_refl
        | mtvec         , mtvec         => left eq_refl
        | mcause        , mcause        => left eq_refl
        | mepc          , mepc          => left eq_refl
        | cur_privilege , cur_privilege => left eq_refl
        | x1            , x1            => left eq_refl
        | x2            , x2            => left eq_refl
        | x3            , x3            => left eq_refl
        | x4            , x4            => left eq_refl
        | x5            , x5            => left eq_refl
        | x6            , x6            => left eq_refl
        | x7            , x7            => left eq_refl
        | x8            , x8            => left eq_refl
        | x9            , x9            => left eq_refl
        | x10           , x10           => left eq_refl
        | x11           , x11           => left eq_refl
        | x12           , x12           => left eq_refl
        | x13           , x13           => left eq_refl
        | x14           , x14           => left eq_refl
        | x15           , x15           => left eq_refl
        | x16           , x16           => left eq_refl
        | x17           , x17           => left eq_refl
        | x18           , x18           => left eq_refl
        | x19           , x19           => left eq_refl
        | x20           , x20           => left eq_refl
        | x21           , x21           => left eq_refl
        | x22           , x22           => left eq_refl
        | x23           , x23           => left eq_refl
        | x24           , x24           => left eq_refl
        | x25           , x25           => left eq_refl
        | x26           , x26           => left eq_refl
        | x27           , x27           => left eq_refl
        | x28           , x28           => left eq_refl
        | x29           , x29           => left eq_refl
        | x30           , x30           => left eq_refl
        | x31           , x31           => left eq_refl
        | pmp0cfg       , pmp0cfg       => left eq_refl
        | pmp1cfg       , pmp1cfg       => left eq_refl
        | pmpaddr0      , pmpaddr0      => left eq_refl
        | pmpaddr1      , pmpaddr1      => left eq_refl
        | _             , _             => right _
        end.
    Proof. all: transparent_abstract (intros H; depelim H). Defined.

    Local Obligation Tactic :=
      finite_from_eqdec.

    Program Instance 𝑹𝑬𝑮_finite : Finite (sigT Reg) :=
      {| enum :=
        [ existT _ pc;
          existT _ nextpc;
          existT _ mstatus;
          existT _ mtvec;
          existT _ mcause;
          existT _ mepc;
          existT _ cur_privilege;
          existT _ x1;
          existT _ x2;
          existT _ x3;
          existT _ x4;
          existT _ x5;
          existT _ x6;
          existT _ x7;
          existT _ x8;
          existT _ x9;
          existT _ x10;
          existT _ x11;
          existT _ x12;
          existT _ x13;
          existT _ x14;
          existT _ x15;
          existT _ x16;
          existT _ x17;
          existT _ x18;
          existT _ x19;
          existT _ x20;
          existT _ x21;
          existT _ x22;
          existT _ x23;
          existT _ x24;
          existT _ x25;
          existT _ x26;
          existT _ x27;
          existT _ x28;
          existT _ x29;
          existT _ x30;
          existT _ x31;
          existT _ pmp0cfg;
          existT _ pmp1cfg;
          existT _ pmpaddr0;
          existT _ pmpaddr1
        ]%list
      |}.

  End RegDeclKit.

  Section Inhabited.
      #[export] Instance val_inhabited σ: Inhabited (Val σ).
      Proof. generalize dependent σ.
            induction σ as [| | | | | | | E | | | U | R]; try apply _; cbn.
            - destruct E; repeat constructor.
            - induction σs; first apply _.
              cbn. inversion IH. apply prod_inhabited; [apply IHσs |]; auto.
            - destruct U;  repeat constructor. all: try apply bv.bv_inhabited.
            - destruct R;  repeat constructor.
      Qed.

  End Inhabited.

  Section MemoryModel.
    Import Bitvector.bv.notations.

    Definition RAM : Type := Addr -> Byte.

    (* Trace of Events *)
    Inductive EventTy : Set :=
    | IOWrite
    | IORead .
    Record Event : Set :=
      mkEvent {
        event_type : EventTy;
        event_addr : Addr;
        event_nbbytes : nat;
        event_contents : bv (event_nbbytes * 8);
      }.

    Definition Trace : Set := list Event.

    (* Memory *)
    Record MemoryType : Type :=
      mkMem {
        memory_ram : RAM;
        memory_trace : Trace;
        memory_state : State;
      } .
    Definition Memory := MemoryType.

    Definition memory_update_ram (μ : Memory) (r : RAM) := mkMem r (memory_trace μ) (memory_state μ).
    Definition memory_update_trace (μ : Memory) (t : Trace) := mkMem (memory_ram μ) t (memory_state μ).
    Definition memory_append_trace (μ : Memory) (e : Event) := memory_update_trace μ (cons e (memory_trace μ)).
    Definition memory_update_state (μ : Memory) (s : State) := mkMem (memory_ram μ) (memory_trace μ) s .

    Fixpoint fun_read_ram (μ : Memory) (data_size : nat) (addr : Val ty_xlenbits) : 
      Val (ty_bytes data_size) :=
      match data_size with
      | O   => bv.zero
      | S n => bv.app ((memory_ram μ) addr) (fun_read_ram μ n (bv.one + addr))
      end.

    (* Small test to show that read_ram reads bitvectors in little
       endian order. *)
    Goal ∀ μ : Memory,
      let μ': Memory := memory_update_ram μ (fun a =>
        if eq_dec a [bv 0x0] then [bv 0xEF] else
        if eq_dec a [bv 0x1] then [bv 0xBE] else
        if eq_dec a [bv 0x2] then [bv 0xAD] else
        if eq_dec a [bv 0x3] then [bv 0xDE] else
        [bv 0])
      in fun_read_ram μ' 4 [bv 0] = [bv 0xDEADBEEF].
    Proof. reflexivity. Qed.

    Definition write_byte (r : RAM) (addr : Val ty_xlenbits) (data : Byte) : RAM :=
      (fun a => if eq_dec addr a then data else r a).

    Fixpoint fun_write_ram (μ : Memory) (data_size : nat) (addr : Val ty_xlenbits) :
      Val (ty_bytes data_size) -> Memory :=
      match data_size as n return (Val (ty_bytes n) → Memory) with
      | O   => fun _data => μ
      | S n => fun data : Val (ty_bytes (S n)) =>
                 let (byte , bytes) := bv.appView 8 (n * 8) data in
                 let μ' := (memory_update_ram μ (write_byte (memory_ram μ) addr byte)) in
                 fun_write_ram μ' (bv.one + addr) bytes
      end.
    #[global] Arguments fun_write_ram : clear implicits.

    (* Separated into a read and a write function in the sail model *)
    (* NOTE: we have to check overflow here, because the PMP model does not...*)
    Definition fun_within_mmio (data_size : nat) (addr : Val ty_xlenbits) : bool :=
      bool_decide (withinMMIO addr data_size ∧
      bv.bin addr + N.of_nat data_size < (bv.exp2 xlenbits))%N.

    (* TODO: in principle, restricted bytes don't need a zero-case *)
    Definition fun_read_mmio (μ : Memory) (data_size : nat) (addr : Val ty_xlenbits) :
      Memory * Val (ty_bytes data_size) :=
      match data_size with
      | O   => (μ , bv.zero)
      | S n => let (s' , readv) := state_tra_read (memory_state μ) addr data_size in
               let mmioev := mkEvent IORead addr data_size readv in
               let μ' := memory_append_trace (memory_update_state μ s') mmioev in
                (μ' , readv)%type
      end.

    Definition fun_write_mmio (μ : Memory) (data_size : nat) (addr : Val ty_xlenbits) :
      Val (ty_bytes data_size) -> Memory :=
      match data_size as n return (Val (ty_bytes n) → Memory) with
      | O   => fun _data => μ
      | S n => fun data : Val (ty_bytes (S n)) =>
                let s' := state_tra_write (memory_state μ) addr (S n) data in
                let mmioev := mkEvent IOWrite addr (S n) data in
                memory_append_trace (memory_update_state μ s') mmioev
      end.

  End MemoryModel.

  Include BaseMixin.

End RiscvPmpBase.
