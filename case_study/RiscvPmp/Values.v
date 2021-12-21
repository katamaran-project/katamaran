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
     ZArith.ZArith.

From Katamaran Require Import
     Notation
     Syntax.Values.

From RiscvPmp Require Export
     Types.

Set Implicit Arguments.
Import ctx.notations.
Import EnvNotations.
Local Open Scope string_scope.

Module RiscvPmpValueKit <: ValueKit.
  Module typekit := RiscvPmpTypeKit.
  Module Export TY := Syntax.Types.Types typekit.
  Import ctx.resolution.

  Notation ty_xlenbits         := (ty_int).
  Notation ty_word             := (ty_int).
  Notation ty_regidx           := (ty_enum regidx).
  Notation ty_privilege        := (ty_enum privilege).
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

  (** Unions **)
  Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty :=
    match U with
    | ast              => fun K =>
                            match K with
                            | KRTYPE      => ty_tuple [ty_regidx, ty_regidx, ty_regidx, ty_rop]
                            | KITYPE      => ty_tuple [ty_int, ty_regidx, ty_regidx, ty_iop]
                            | KUTYPE      => ty_tuple [ty_int, ty_regidx, ty_uop]
                            | KBTYPE      => ty_tuple [ty_int, ty_regidx, ty_regidx, ty_bop]
                            | KRISCV_JAL  => ty_tuple [ty_int, ty_regidx]
                            | KRISCV_JALR => ty_tuple [ty_int, ty_regidx, ty_regidx]
                            | KLOAD       => ty_tuple [ty_int, ty_regidx, ty_regidx]
                            | KSTORE      => ty_tuple [ty_int, ty_regidx, ty_regidx]
                            | KECALL      => ty_unit
                            | KMRET       => ty_unit
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

  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } :=
    match U as u return (𝑼𝑻 u -> {K : 𝑼𝑲 u & Lit (𝑼𝑲_Ty u K)}) with
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

  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
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
  Lemma 𝑼_unfold_fold : forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) }),
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
    | rpmpcfg_ent => [ "L" :: ty_bool,
                      "A" :: ty_pmpaddrmatchtype,
                      "X" :: ty_bool,
                      "W" :: ty_bool,
                      "R" :: ty_bool
                    ]
    | rmstatus    => ["MPP" :: ty_privilege
                    ]
    end.

  Definition 𝑹_fold (R : 𝑹) : NamedEnv Lit (𝑹𝑭_Ty R) -> 𝑹𝑻 R :=
    match R with
    | rpmpcfg_ent =>
      fun fields =>
        MkPmpcfg_ent
          (fields ‼ "L")
          (fields ‼ "A")
          (fields ‼ "X")
          (fields ‼ "W")
          (fields ‼ "R")
    | rmstatus =>
      fun fields =>
        MkMstatus
          (fields ‼ "MPP")
    end%exp.

  Definition 𝑹_unfold (Rec : 𝑹) : 𝑹𝑻 Rec -> NamedEnv Lit (𝑹𝑭_Ty Rec) :=
    match Rec with
    | rpmpcfg_ent =>
      fun p =>
        env_nil
          ► ("L" :: ty_bool             ↦ L p)
          ► ("A" :: ty_pmpaddrmatchtype ↦ A p)
          ► ("X" :: ty_bool             ↦ X p)
          ► ("W" :: ty_bool             ↦ W p)
          ► ("R" :: ty_bool             ↦ R p)
    | rmstatus    =>
      fun m =>
        env_nil
          ► ("MPP" :: ty_privilege ↦ MPP m)
    end%env.

  Lemma 𝑹_fold_unfold : forall (R : 𝑹) (Kv: 𝑹𝑻 R),
      𝑹_fold R (𝑹_unfold R Kv) = Kv.
  Proof. now intros [] []. Qed.
  Lemma 𝑹_unfold_fold : forall (R : 𝑹) (Kv: NamedEnv Lit (𝑹𝑭_Ty R)),
      𝑹_unfold R (𝑹_fold R Kv) = Kv.
  Proof. intros []; now apply Forall_forall. Qed.
End RiscvPmpValueKit.
