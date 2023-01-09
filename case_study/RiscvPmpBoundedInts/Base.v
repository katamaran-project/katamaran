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
     ZArith.ZArith.
From Equations Require Import
     Equations.
From stdpp Require
     finite.
From Katamaran Require Import
     Base
     Syntax.TypeDecl.

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

(* Parameter minAddr : Addr. *)
(* Parameter maxAddr : Addr. *)
Definition minAddr : nat := 0.
Definition lenAddr : nat := 100.
Definition maxAddr : nat := minAddr + lenAddr.
Lemma minAddr_rep : (N.of_nat minAddr < bv.exp2 xlenbits)%N.
Proof. now compute. Qed.
Lemma maxAddr_rep : (N.of_nat maxAddr < bv.exp2 xlenbits)%N.
Proof. now compute. Qed.
Lemma lenAddr_rep : (N.of_nat lenAddr < bv.exp2 xlenbits)%N.
Proof. now compute. Qed.
(* xlenbits is made opaque further on and it really must be non-zero. *)
Lemma xlenbits_pos : (xlenbits > 0).
Proof. cbv. lia. Qed.

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
| MPMP1CFG
| MPMPADDR0
| MPMPADDR1
.

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
| RISCV_SUB
.

Inductive IOP : Set :=
| RISCV_ADDI
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
.

Inductive Retired : Set :=
| RETIRE_SUCCESS
| RETIRE_FAIL.

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
| uop
| bop
| csrop
| retired
.

Definition RegIdx := bv 3.
Bind Scope bv_scope with RegIdx.

Inductive AST : Set :=
| RTYPE (rs2 rs1 rd : RegIdx) (op : ROP)
| ITYPE (imm : bv 12) (rs1 rd : RegIdx) (op : IOP)
| UTYPE (imm : bv 20) (rd : RegIdx) (op : UOP)
| BTYPE (imm : bv 13) (rs2 rs1 : RegIdx) (op : BOP)
| RISCV_JAL (imm : bv 21) (rd : RegIdx)
| RISCV_JALR (imm : bv 12) (rs1 rd : RegIdx)
| LOAD (imm : bv 12) (rs1 rd : RegIdx)
| STORE (imm : bv 12) (rs2 rs1 : RegIdx)
| ECALL
| MRET
(* Ziscr extension, excluding immediate variants *)
| CSR (csr : CSRIdx) (rs1 rd : RegIdx) (csrop : CSROP)
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
| KUTYPE
| KBTYPE
| KRISCV_JAL
| KRISCV_JALR
| KLOAD
| KSTORE
| KECALL
| KMRET
| KCSR
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
  Derive NoConfusion for UOP.
  Derive NoConfusion for BOP.
  Derive NoConfusion for CSROP.
  Derive NoConfusion for Retired.
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
Derive EqDec for UOP.
Derive EqDec for BOP.
Derive EqDec for CSROP.
Derive EqDec for Retired.
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
    {| enum := [MStatus;MTvec;MCause;MEpc;MPMP0CFG;MPMP1CFG;MPMPADDR0;MPMPADDR1] |}.

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
    {| enum := [RISCV_ADD;RISCV_SUB] |}.

  #[export,program] Instance IOP_finite :
    Finite IOP :=
    {| enum := [RISCV_ADDI] |}.

  #[export,program] Instance UOP_finite :
    Finite UOP :=
    {| enum := [RISCV_LUI;RISCV_AUIPC] |}.

  #[export,program] Instance BOP_finite :
    Finite BOP :=
    {| enum := [RISCV_BEQ;RISCV_BNE;RISCV_BLT;RISCV_BGE;RISCV_BLTU;RISCV_BGEU] |}.

  #[export,program] Instance CSROP_finite :
    Finite CSROP :=
    {| enum := [CSRRW] |}.

  #[export,program] Instance Retired_finite :
    Finite Retired :=
    {| enum := [RETIRE_SUCCESS; RETIRE_FAIL] |}.

  #[export,program] Instance ASTConstructor_finite :
    Finite ASTConstructor :=
    {| enum := [KRTYPE;KITYPE;KUTYPE;KBTYPE;KRISCV_JAL;KRISCV_JALR;KLOAD;KSTORE;KECALL;KMRET;KCSR] |}.

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
  Definition ty_regno                          := (ty.bvec 3).
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
  Definition ty_uop                            := (ty.enum uop).
  Definition ty_bop                            := (ty.enum bop).
  Definition ty_csrop                          := (ty.enum csrop).
  Definition ty_retired                        := (ty.enum retired).
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
    | uop              => UOP
    | bop              => BOP
    | csrop            => CSROP
    | retired          => Retired
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
                            | KUTYPE      => ty.tuple [ty.bvec 20; ty_regno; ty_uop]
                            | KBTYPE      => ty.tuple [ty.bvec 13; ty_regno; ty_regno; ty_bop]
                            | KRISCV_JAL  => ty.tuple [ty.bvec 21; ty_regno]
                            | KRISCV_JALR => ty.tuple [ty.bvec 12; ty_regno; ty_regno]
                            | KLOAD       => ty.tuple [ty.bvec 12; ty_regno; ty_regno]
                            | KSTORE      => ty.tuple [ty.bvec 12; ty_regno; ty_regno]
                            | KECALL      => ty.unit
                            | KMRET       => ty.unit
                            | KCSR        => ty.tuple [ty_csridx; ty_regno; ty_regno; ty_csrop]
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

  Definition union_unfold (U : unioni) : uniont U -> { K & Val (union_constructor_type U K) } :=
    match U with
    | ast              => fun Kv =>
                            match Kv with
                            | RTYPE rs2 rs1 rd op   => existT KRTYPE (tt , rs2 , rs1 , rd , op)
                            | ITYPE imm rs1 rd op   => existT KITYPE (tt , imm , rs1 , rd , op)
                            | UTYPE imm rd op       => existT KUTYPE (tt , imm , rd , op)
                            | BTYPE imm rs2 rs1 op  => existT KBTYPE (tt , imm , rs2 , rs1 , op)
                            | RISCV_JAL imm rd      => existT KRISCV_JAL (tt , imm , rd)
                            | RISCV_JALR imm rs1 rd => existT KRISCV_JALR (tt , imm , rs1 , rd)
                            | LOAD imm rs1 rd       => existT KLOAD (tt , imm , rs1 , rd)
                            | STORE imm rs2 rs1     => existT KSTORE (tt , imm , rs2 , rs1)
                            | ECALL                 => existT KECALL tt
                            | MRET                  => existT KMRET tt
                            | CSR csr rs1 rd op     => existT KCSR (tt , csr , rs1 , rd , op)
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
                              | existT KRTYPE (tt , rs2 , rs1 , rd , op)  => RTYPE rs2 rs1 rd op
                              | existT KITYPE (tt , imm , rs1 , rd , op)  => ITYPE imm rs1 rd op
                              | existT KUTYPE (tt , imm , rd , op)        => UTYPE imm rd op
                              | existT KBTYPE (tt , imm , rs2 , rs1 , op) => BTYPE imm rs2 rs1 op
                              | existT KRISCV_JAL (tt , imm , rd)         => RISCV_JAL imm rd
                              | existT KRISCV_JALR (tt , imm , rs1 , rd)  => RISCV_JALR imm rs1 rd
                              | existT KLOAD (tt , imm , rs1 , rd)        => LOAD imm rs1 rd
                              | existT KSTORE (tt , imm , rs2 , rs1)      => STORE imm rs2 rs1
                              | existT KECALL tt                          => ECALL
                              | existT KMRET tt                           => MRET
                              | existT KCSR (tt , csr , rs1 , rd , op)    => CSR csr rs1 rd op
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
    - transparent_abstract (now intros []; apply _).
    - transparent_abstract (intros [] []; now cbn).
    - transparent_abstract (intros [] [[] x]; cbn in x;
        repeat match goal with
               | x: unit |- _ => destruct x
               | x: prod _ _ |- _ => destruct x
               end; auto).
    - transparent_abstract (now intros [] []).
    - transparent_abstract (intros []; now apply env.Forall_forall).
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
    | pmp0cfg       : Reg ty_pmpcfg_ent
    | pmp1cfg       : Reg ty_pmpcfg_ent
    | pmpaddr0      : Reg ty_xlenbits
    | pmpaddr1      : Reg ty_xlenbits
    .

    Import bv.notations.
    Definition reg_convert (idx : RegIdx) : option (Reg ty_xlenbits) :=
      match bv.to_bitstring idx with
      | 000 => None
      | 001 => Some x1
      | 010 => Some x2
      | 011 => Some x3
      | 100 => Some x4
      | 101 => Some x5
      | 110 => Some x6
      | 111 => Some x7
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
          existT _ pmp0cfg;
          existT _ pmp1cfg;
          existT _ pmpaddr0;
          existT _ pmpaddr1
        ]%list
      |}.

  End RegDeclKit.

  Include BaseMixin.

End RiscvPmpBase.
