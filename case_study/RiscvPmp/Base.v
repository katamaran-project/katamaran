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
     Strings.String.
From Equations Require Import
     Equations.
From stdpp Require
     finite.
From Katamaran Require Import
     Base.

Local Unset Equations Derive Equations.
Local Set Implicit Arguments.

(* Taken from Coq >= 8.15 SigTNotations *)
Local Notation "( x ; y )" := (existT x y) (only parsing).

Definition Xlenbits : Set := Z.
Definition Addr : Set := Z.
Definition Word : Set := Z.

(** Enums **)
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
.

(* NOTE: PMP CSRs limited to 1 for now *)
Inductive PmpCfgIdx : Set :=
| PMP0CFG
| PMP1CFG
.

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

(** Unions **)
Definition RegIdx := bv 3.
Bind Scope bv_scope with RegIdx.

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
| memory_op_result
| fetch_result
| ctl_result
(* | pmp_entries *)
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
  Derive NoConfusion for Privilege.
  Derive NoConfusion for CSRIdx.
  Derive NoConfusion for PmpCfgIdx.
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
Derive EqDec for Privilege.
Derive EqDec for CSRIdx.
Derive EqDec for PmpCfgIdx.
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

  Local Obligation Tactic :=
    finite_from_eqdec.

  Global Program Instance Privilege_finite : Finite Privilege :=
    {| enum := [User;Machine] |}.

  Global Program Instance CSRIdx_finite : Finite CSRIdx :=
    {| enum := [MStatus;MTvec;MCause;MEpc] |}.

  Global Program Instance PmpCfgIdx_finite : Finite PmpCfgIdx :=
    {| enum := [PMP0CFG;PMP1CFG] |}.

  Global Program Instance PmpAddrIdx_finite : Finite PmpAddrIdx :=
    {| enum := [PMPADDR0;PMPADDR1] |}.

  Global Program Instance PmpAddrMatchType_finite : Finite PmpAddrMatchType :=
    {| enum := [OFF;TOR] |}.

  Global Program Instance PmpMatch_finite : Finite PmpMatch :=
    {| enum := [PMP_Success;PMP_Continue;PMP_Fail] |}.

  Global Program Instance PmpAddrMatch_finite : Finite PmpAddrMatch :=
    {| enum := [PMP_NoMatch;PMP_PartialMatch;PMP_Match] |}.

  Global Program Instance ROP_finite :
    Finite ROP :=
    {| enum := [RISCV_ADD;RISCV_SUB] |}.

  Global Program Instance IOP_finite :
    Finite IOP :=
    {| enum := [RISCV_ADDI] |}.

  Global Program Instance UOP_finite :
    Finite UOP :=
    {| enum := [RISCV_LUI;RISCV_AUIPC] |}.

  Global Program Instance BOP_finite :
    Finite BOP :=
    {| enum := [RISCV_BEQ;RISCV_BNE;RISCV_BLT;RISCV_BGE;RISCV_BLTU;RISCV_BGEU] |}.

  Global Program Instance CSROP_finite :
    Finite CSROP :=
    {| enum := [CSRRW] |}.

  Global Program Instance Retired_finite :
    Finite Retired :=
    {| enum := [RETIRE_SUCCESS; RETIRE_FAIL] |}.

  Global Program Instance ASTConstructor_finite :
    Finite ASTConstructor :=
    {| enum := [KRTYPE;KITYPE;KUTYPE;KBTYPE;KRISCV_JAL;KRISCV_JALR;KLOAD;KSTORE;KECALL;KMRET;KCSR] |}.

  Global Program Instance AccessTypeConstructor_finite :
    Finite AccessTypeConstructor :=
    {| enum := [KRead;KWrite;KReadWrite;KExecute] |}.

  Global Program Instance ExceptionTypeConstructor_finite :
    Finite ExceptionTypeConstructor :=
    {| enum := [KE_Fetch_Access_Fault;KE_Load_Access_Fault;KE_SAMO_Access_Fault;
                KE_U_EnvCall;KE_M_EnvCall;KE_Illegal_Instr] |}.

  Global Program Instance MemoryOpResultConstructor_finite :
    Finite MemoryOpResultConstructor :=
    {| enum := [KMemValue;KMemException] |}.

  Global Program Instance FetchResultConstructor_finite :
    Finite FetchResultConstructor :=
    {| enum := [KF_Base;KF_Error] |}.

  Global Program Instance CtlResultConstructor_finite :
    Finite CtlResultConstructor :=
    {| enum := [KCTL_TRAP;KCTL_MRET] |}.

End Finite.

Module Export RiscvPmpBase <: Base.

Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Import stdpp.finite.

Include DefaultVarKit.

Section TypeDeclKit.

  (** Enums **)
  Definition 𝑬        := Enums.
  Definition 𝑬_eq_dec := Enums_eqdec.
  Definition 𝑬𝑲 (e : 𝑬) : Set :=
    match e with
    | privilege        => Privilege
    | csridx           => CSRIdx
    | pmpcfgidx        => PmpCfgIdx
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
    (* | pmp_entries      => Coq type in the model for pmp_entries  *)
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
    (* | pmp_entries   => PmpEntriesConstructor *)
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

End TypeDeclKit.

Include TypeDeclMixin.

(* Override notations of bindigns to put the variable x into string_scope. *)
Notation "x ∷ t" := (MkB x%string t) : ctx_scope.

Notation ty_xlenbits         := (ty_int).
Notation ty_word             := (ty_int).
Notation ty_regno            := (ty_bvec 3).
Notation ty_privilege        := (ty_enum privilege).
Notation ty_csridx           := (ty_enum csridx).
Notation ty_pmpcfgidx        := (ty_enum pmpcfgidx).
Notation ty_pmpaddridx       := (ty_enum pmpaddridx).
Notation ty_pmpaddrmatchtype := (ty_enum pmpaddrmatchtype).
Notation ty_pmpmatch         := (ty_enum pmpmatch).
Notation ty_pmpaddrmatch     := (ty_enum pmpaddrmatch).
Notation ty_pmp_addr_range   := (ty_option (ty_prod ty_xlenbits ty_xlenbits)).
Notation ty_rop              := (ty_enum rop).
Notation ty_iop              := (ty_enum iop).
Notation ty_uop              := (ty_enum uop).
Notation ty_bop              := (ty_enum bop).
Notation ty_csrop            := (ty_enum csrop).
Notation ty_retired          := (ty_enum retired).
Notation ty_mcause           := (ty_xlenbits).
Notation ty_exc_code         := (ty_int).
Notation ty_ast              := (ty_union ast).
Notation ty_access_type      := (ty_union access_type).
Notation ty_exception_type   := (ty_union exception_type).
Notation ty_memory_op_result := (ty_union memory_op_result).
Notation ty_fetch_result     := (ty_union fetch_result).
Notation ty_ctl_result       := (ty_union ctl_result).
Notation ty_pmpcfg_ent       := (ty_record rpmpcfg_ent).
Notation ty_mstatus          := (ty_record rmstatus).
Notation ty_pmpentry         := (ty_prod ty_pmpcfg_ent ty_xlenbits).

Section TypeDefKit.

  Open Scope string_scope.

  (** Unions **)
  Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty :=
    match U with
    | ast              => fun K =>
                            match K with
                            | KRTYPE      => ty_tuple [ty_regno; ty_regno; ty_regno; ty_rop]
                            | KITYPE      => ty_tuple [ty_int; ty_regno; ty_regno; ty_iop]
                            | KUTYPE      => ty_tuple [ty_int; ty_regno; ty_uop]
                            | KBTYPE      => ty_tuple [ty_int; ty_regno; ty_regno; ty_bop]
                            | KRISCV_JAL  => ty_tuple [ty_int; ty_regno]
                            | KRISCV_JALR => ty_tuple [ty_int; ty_regno; ty_regno]
                            | KLOAD       => ty_tuple [ty_int; ty_regno; ty_regno]
                            | KSTORE      => ty_tuple [ty_int; ty_regno; ty_regno]
                            | KECALL      => ty_unit
                            | KMRET       => ty_unit
                            | KCSR        => ty_tuple [ty_csridx; ty_regno; ty_regno; ty_csrop]
                            end
    | access_type      => fun _ => ty_unit
    | exception_type   => fun _ => ty_unit
    | memory_op_result => fun K =>
                            match K with
                            | KMemValue     => ty_word
                            | KMemException => ty_exception_type
                            end
    | fetch_result     => fun K =>
                            match K with
                            | KF_Base  => ty_word
                            | KF_Error => ty_prod ty_exception_type ty_word
                            end
    | ctl_result       => fun K =>
                            match K with
                            | KCTL_TRAP => ty_exception_type
                            | KCTL_MRET => ty_unit
                            end
    end.

  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty U K) } :=
    match U as u return (𝑼𝑻 u -> {K : 𝑼𝑲 u & Val (𝑼𝑲_Ty u K)}) with
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
    | memory_op_result => fun Kv =>
                            match Kv with
                            | MemValue v     => existT KMemValue v
                            | MemException e => existT KMemException e
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

  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
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
    | memory_op_result => fun Kv =>
                            match Kv with
                            | existT KMemValue v     => MemValue v
                            | existT KMemException e => MemException e
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

  Lemma 𝑼_fold_unfold : forall (U : 𝑼) (Kv: 𝑼𝑻 U),
      𝑼_fold U (𝑼_unfold U Kv) = Kv.
  Proof. now intros [] []. Qed.
  Lemma 𝑼_unfold_fold : forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty U K) }),
      𝑼_unfold U (𝑼_fold U Kv) = Kv.
  Proof.
    intros [] [[] x]; cbn in x;
      repeat match goal with
             | x: unit     |- _ => destruct x
             | x: prod _ _ |- _ => destruct x
             end; auto.
  Qed.

  (** Records **)
  Definition 𝑹𝑭  : Set := string.

  Definition 𝑹𝑭_Ty (R : 𝑹) : NCtx 𝑹𝑭 Ty :=
    match R with
    | rpmpcfg_ent => [ "L" ∷ ty_bool;
                       "A" ∷ ty_pmpaddrmatchtype;
                       "X" ∷ ty_bool;
                       "W" ∷ ty_bool;
                       "R" ∷ ty_bool
                     ]
    | rmstatus    => ["MPP" ∷ ty_privilege
                    ]
    end.

  Equations 𝑹_fold (R : 𝑹) : NamedEnv Val (𝑹𝑭_Ty R) -> 𝑹𝑻 R :=
  | rpmpcfg_ent | [l;a;x;w;r]%env := MkPmpcfg_ent l a x w r
  | rmstatus    | [mpp]%env       := MkMstatus mpp.

  Equations 𝑹_unfold (R : 𝑹) : 𝑹𝑻 R -> NamedEnv Val (𝑹𝑭_Ty R) :=
  | rpmpcfg_ent | p => [kv (_ ∷ ty_bool             ; L p);
                           (_ ∷ ty_pmpaddrmatchtype ; A p);
                           (_ ∷ ty_bool             ; X p);
                           (_ ∷ ty_bool             ; W p);
                           (_ ∷ ty_bool             ; R p) ];
  | rmstatus    | m => [kv ("MPP" ∷ ty_privilege; MPP m) ].

  Lemma 𝑹_fold_unfold : forall (R : 𝑹) (Kv: 𝑹𝑻 R),
      𝑹_fold R (𝑹_unfold R Kv) = Kv.
  Proof. now intros [] []. Qed.
  Lemma 𝑹_unfold_fold : forall (R : 𝑹) (Kv: NamedEnv Val (𝑹𝑭_Ty R)),
      𝑹_unfold R (𝑹_fold R Kv) = Kv.
  Proof. intros []; now apply env.Forall_forall. Qed.

End TypeDefKit.

Section RegDeclKit.

  Inductive Reg : Ty -> Set :=
  | pc            : Reg ty_xlenbits
  | nextpc        : Reg ty_xlenbits
  | mstatus       : Reg ty_mstatus
  | mtvec         : Reg ty_xlenbits
  | mcause        : Reg ty_exc_code
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
    Derive Signature NoConfusion NoConfusionHom EqDec for Reg.
  End TransparentObligations.

  Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
  Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg) :=
    sigma_eqdec _ _.

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
