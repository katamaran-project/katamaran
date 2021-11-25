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
     ZArith.ZArith.
From Equations Require Import
     Equations.
From stdpp Require
     finite.
From Katamaran Require Import
     Syntax.Types.

Definition Xlenbits : Set := Z.
Definition Addr : Set := Z.
Definition Word : Set := Z.

(** Enums **)
Inductive RegIdx : Set :=
| X0
| X1
| X2
.

Inductive Privilege : Set :=
| User
| Machine
.

(* NOTE: PMP CSRs limited to 1 for now *)
Inductive PmpCfgIdx : Set :=
| PMP0CFG
.

Inductive PmpAddrIdx : Set :=
| PMPADDR0
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

Inductive Retired : Set :=
| RETIRE_SUCCESS
| RETIRE_FAIL.

Inductive Enums : Set :=
| regidx
| privilege
| pmpcfgidx
| pmpaddridx
| pmpaddrmatchtype
| pmpmatch
| pmpaddrmatch
| rop
| iop
| uop
| bop
| retired
.

(** Unions **)
Inductive AST : Set :=
| RTYPE (rs2 rs1 rd : RegIdx) (op : ROP)
| ITYPE (imm : Z) (rs1 rd : RegIdx) (op : IOP)
| UTYPE (imm : Z) (rd : RegIdx) (op : UOP)
| BTYPE (imm : Z) (rs2 rs1 : RegIdx) (op : BOP)
| RISCV_JAL (imm : Z) (rd : RegIdx)
| RISCV_JALR (imm : Z) (rs1 rd : RegIdx)
| LOAD (imm : Z) (rs1 rd : RegIdx)
| STORE (imm : Z) (rs2 rs1 : RegIdx)
| ECALL
| MRET
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

Inductive MemoryOpResult : Set :=
| MemValue (v : Word)
| MemException (e : ExceptionType)
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
| memory_op_result
| fetch_result
| ctl_result
.

(* Records *)
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
  Derive NoConfusion for RegIdx.
  Derive NoConfusion for Privilege.
  Derive NoConfusion for PmpCfgIdx.
  Derive NoConfusion for PmpAddrIdx.
  Derive NoConfusion for PmpAddrMatchType.
  Derive NoConfusion for PmpMatch.
  Derive NoConfusion for PmpAddrMatch.
  Derive NoConfusion for ROP.
  Derive NoConfusion for IOP.
  Derive NoConfusion for UOP.
  Derive NoConfusion for BOP.
  Derive NoConfusion for Retired.
  Derive NoConfusion for Unions.
  Derive NoConfusion for AST.
  Derive NoConfusion for ASTConstructor.
  Derive NoConfusion for AccessType.
  Derive NoConfusion for AccessTypeConstructor.
  Derive NoConfusion for ExceptionType.
  Derive NoConfusion for ExceptionTypeConstructor.
  Derive NoConfusion for MemoryOpResult.
  Derive NoConfusion for MemoryOpResultConstructor.
  Derive NoConfusion for FetchResult.
  Derive NoConfusion for FetchResultConstructor.
  Derive NoConfusion for CtlResult.
  Derive NoConfusion for CtlResultConstructor.
  Derive NoConfusion for Records.
  Derive NoConfusion for Pmpcfg_ent.
  Derive NoConfusion for Mstatus.
End TransparentObligations.

Derive EqDec for Enums.
Derive EqDec for RegIdx.
Derive EqDec for Privilege.
Derive EqDec for PmpCfgIdx.
Derive EqDec for PmpAddrIdx.
Derive EqDec for PmpAddrMatchType.
Derive EqDec for PmpMatch.
Derive EqDec for PmpAddrMatch.
Derive EqDec for ROP.
Derive EqDec for IOP.
Derive EqDec for UOP.
Derive EqDec for BOP.
Derive EqDec for Retired.
Derive EqDec for Unions.
Derive EqDec for AST.
Derive EqDec for ASTConstructor.
Derive EqDec for AccessType.
Derive EqDec for AccessTypeConstructor.
Derive EqDec for ExceptionType.
Derive EqDec for ExceptionTypeConstructor.
Derive EqDec for MemoryOpResult.
Derive EqDec for MemoryOpResultConstructor.
Derive EqDec for FetchResult.
Derive EqDec for FetchResultConstructor.
Derive EqDec for CtlResult.
Derive EqDec for CtlResultConstructor.
Derive EqDec for Records.
Derive EqDec for Pmpcfg_ent.
Derive EqDec for Mstatus.

Section Finite.
  Import stdpp.finite.

  Global Program Instance RegIdx_finite : Finite RegIdx :=
    {| enum := [X0;X1;X2] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance Privilege_finite : Finite Privilege :=
    {| enum := [User;Machine] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance PmpCfgIdx_finite : Finite PmpCfgIdx :=
    {| enum := [PMP0CFG] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance PmpAddrIdx_finite : Finite PmpAddrIdx :=
    {| enum := [PMPADDR0] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance PmpAddrMatchType_finite : Finite PmpAddrMatchType :=
    {| enum := [OFF;TOR] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance PmpMatch_finite : Finite PmpMatch :=
    {| enum := [PMP_Success;PMP_Continue;PMP_Fail] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance PmpAddrMatch_finite : Finite PmpAddrMatch :=
    {| enum := [PMP_NoMatch;PMP_PartialMatch;PMP_Match] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance ROP_finite :
    Finite ROP :=
    {| enum := [RISCV_ADD;RISCV_SUB] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance IOP_finite :
    Finite IOP :=
    {| enum := [RISCV_ADDI] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance UOP_finite :
    Finite UOP :=
    {| enum := [RISCV_LUI;RISCV_AUIPC] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance BOP_finite :
    Finite BOP :=
    {| enum := [RISCV_BEQ;RISCV_BNE;RISCV_BLT;RISCV_BGE;RISCV_BLTU;RISCV_BGEU] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance Retired_finite :
    Finite Retired :=
    {| enum := [RETIRE_SUCCESS; RETIRE_FAIL] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance ASTConstructor_finite :
    Finite ASTConstructor :=
    {| enum := [KRTYPE;KITYPE;KUTYPE;KBTYPE;KRISCV_JAL;KRISCV_JALR;KLOAD;KSTORE;KECALL;KMRET] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance AccessTypeConstructor_finite :
    Finite AccessTypeConstructor :=
    {| enum := [KRead;KWrite;KReadWrite;KExecute] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance ExceptionTypeConstructor_finite :
    Finite ExceptionTypeConstructor :=
    {| enum := [KE_Fetch_Access_Fault;KE_Load_Access_Fault;KE_SAMO_Access_Fault;KE_U_EnvCall;KE_M_EnvCall;KE_Illegal_Instr] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance MemoryOpResultConstructor_finite :
    Finite MemoryOpResultConstructor :=
    {| enum := [KMemValue;KMemException] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance FetchResultConstructor_finite :
    Finite FetchResultConstructor :=
    {| enum := [KF_Base;KF_Error] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

  Global Program Instance CtlResultConstructor_finite :
    Finite CtlResultConstructor :=
    {| enum := [KCTL_TRAP;KCTL_MRET] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply (@bool_decide_unpack _ (elem_of_list_dec _ _)); auto.
  Qed.

End Finite.

Module RiscvPmpTypeKit <: TypeKit.
  Import stdpp.finite.

  (** Enums **)
  Definition 𝑬        := Enums.
  Definition 𝑬_eq_dec := Enums_eqdec.
  Definition 𝑬𝑲 (e : 𝑬) : Set :=
    match e with
    | regidx           => RegIdx
    | privilege        => Privilege
    | pmpcfgidx        => PmpCfgIdx
    | pmpaddridx       => PmpAddrIdx
    | pmpaddrmatchtype => PmpAddrMatchType
    | pmpmatch         => PmpMatch
    | pmpaddrmatch     => PmpAddrMatch
    | rop              => ROP
    | iop              => IOP
    | uop              => UOP
    | bop              => BOP
    | retired          => Retired
    end.
  Instance 𝑬𝑲_eq_dec (E : 𝑬) : EqDec (𝑬𝑲 E) :=
    ltac:(destruct E; auto with typeclass_instances).
  Instance 𝑬𝑲_finite (E : 𝑬) : Finite (𝑬𝑲 E) :=
    ltac:(destruct E; auto with typeclass_instances).

  (** Unions **)
  Definition 𝑼        := Unions.
  Definition 𝑼_eq_dec := Unions_eqdec.
  Definition 𝑼𝑻 (U : 𝑼) : Set :=
    match U with
    | ast              => AST
    | access_type      => AccessType
    | exception_type   => ExceptionType
    | memory_op_result => MemoryOpResult
    | fetch_result     => FetchResult
    | ctl_result       => CtlResult
    end.
  Instance 𝑼𝑻_eq_dec U : EqDec (𝑼𝑻 U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).

  Definition 𝑼𝑲 (U : 𝑼) : Set :=
    match U with
    | ast              => ASTConstructor
    | access_type      => AccessTypeConstructor
    | exception_type   => ExceptionTypeConstructor
    | memory_op_result => MemoryOpResultConstructor
    | fetch_result     => FetchResultConstructor
    | ctl_result       => CtlResultConstructor
    end.
  Instance 𝑼𝑲_eq_dec U : EqDec (𝑼𝑲 U) :=
    ltac:(destruct U; auto with typeclass_instances).
  Instance 𝑼𝑲_finite U : Finite (𝑼𝑲 U) :=
    ltac:(destruct U; auto with typeclass_instances).

  (** Records **)
  Definition 𝑹        := Records.
  Definition 𝑹_eq_dec := Records_eqdec.
  Definition 𝑹𝑻 (R : 𝑹) : Set :=
    match R with
    | rpmpcfg_ent => Pmpcfg_ent
    | rmstatus    => Mstatus
    end.
  Instance 𝑹𝑻_eq_dec R : EqDec (𝑹𝑻 R) :=
    ltac:(destruct R; auto with typeclass_instances).
End RiscvPmpTypeKit.

