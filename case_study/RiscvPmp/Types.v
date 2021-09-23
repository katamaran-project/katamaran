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
From MicroSail Require Import
     Syntax.Types.

Definition Addr : Set := Z.
Definition Word : Set := Z.

(** Enums **)
Inductive RegIdx : Set :=
| X0
| X1
| X2
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
| BTYPE (imm : Z) (rs1 rs2 : RegIdx) (op : BOP)
| RISCV_JAL (imm : Z) (rd : RegIdx)
| RISCV_JALR (imm : Z) (rs1 rd : RegIdx)
| LOAD (imm : Z) (rs1 rd : RegIdx)
.

Inductive AccessType : Set :=
| Read
| Write
| ReadWrite
| Execute
.

Inductive ExceptionType : Set :=
| E_FETCH_ACCESS_FAULT
| E_LOAD_ACCESS_FAULT
| E_SAMO_ACCESS_FAULT
.

Inductive MemoryOpResult : Set :=
| MemValue (v : Word)
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
.

Inductive AccessTypeConstructor : Set :=
| KRead
| KWrite
| KReadWrite
| KExecute
.

Inductive ExceptionTypeConstructor : Set :=
| KE_FETCH_ACCESS_FAULT
| KE_LOAD_ACCESS_FAULT
| KE_SAMO_ACCESS_FAULT
.

Inductive MemoryOpResultConstructor : Set :=
| KMemValue
| KMemException
.

Inductive Unions : Set :=
| ast
| access_type
| exception_type
| memory_op_result
.

Inductive Records : Set :=. 

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Enums.
  Derive NoConfusion for RegIdx.
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
  Derive NoConfusion for Records.
End TransparentObligations.

Derive EqDec for Enums.
Derive EqDec for RegIdx.
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
Derive EqDec for Records.

Section Finite.
  Import stdpp.finite.

  Global Program Instance RegIdx_finite : Finite RegIdx :=
    {| enum := [X0;X1;X2] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance ROP_finite :
    Finite ROP :=
    {| enum := [RISCV_ADD;RISCV_SUB] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance IOP_finite :
    Finite IOP :=
    {| enum := [RISCV_ADDI] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance UOP_finite :
    Finite UOP :=
    {| enum := [RISCV_LUI;RISCV_AUIPC] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance BOP_finite :
    Finite BOP :=
    {| enum := [RISCV_BEQ;RISCV_BNE;RISCV_BLT;RISCV_BGE;RISCV_BLTU;RISCV_BGEU] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance Retired_finite :
    Finite Retired :=
    {| enum := [RETIRE_SUCCESS; RETIRE_FAIL] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance ASTConstructor_finite :
    Finite ASTConstructor :=
    {| enum := [KRTYPE;KITYPE;KUTYPE;KBTYPE;KRISCV_JAL;KRISCV_JALR;KLOAD] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance AccessTypeConstructor_finite :
    Finite AccessTypeConstructor :=
    {| enum := [KRead;KWrite;KReadWrite;KExecute] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance ExceptionTypeConstructor_finite :
    Finite ExceptionTypeConstructor :=
    {| enum := [KE_FETCH_ACCESS_FAULT;KE_LOAD_ACCESS_FAULT;KE_SAMO_ACCESS_FAULT] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance MemoryOpResultConstructor_finite :
    Finite MemoryOpResultConstructor :=
    {| enum := [KMemValue;KMemException] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.
End Finite.

Module RiscvPmpTypeKit <: TypeKit.
  Import stdpp.finite.

  (** Enums **)
  Definition 𝑬        := Enums.
  Definition 𝑬_eq_dec := Enums_eqdec.
  Definition 𝑬𝑲 (e : 𝑬) : Set :=
    match e with
    | regidx  => RegIdx
    | rop     => ROP
    | iop     => IOP
    | uop     => UOP
    | bop     => BOP
    | retired => Retired
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
    end.
  Instance 𝑼𝑻_eq_dec U : EqDec (𝑼𝑻 U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).

  Definition 𝑼𝑲 (U : 𝑼) : Set :=
    match U with
    | ast              => ASTConstructor
    | access_type      => AccessTypeConstructor
    | exception_type   => ExceptionTypeConstructor
    | memory_op_result => MemoryOpResultConstructor
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
    end.
  Instance 𝑹𝑻_eq_dec R : EqDec (𝑹𝑻 R) :=
    ltac:(destruct R; auto with typeclass_instances).
End RiscvPmpTypeKit.
