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
From MicroSail Require Import
     Syntax.
From RiscvPmp Require Export
     Values.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.

Module RiscvPmpTermKit <: TermKit.
  Module valuekit := RiscvPmpValueKit.
  Module Export VAL := Syntax.Values.Values valuekit.

  (** Variables **)
  Definition 𝑿        := string.
  Definition 𝑿_eq_dec := string_dec.
  Definition 𝑺        := string.
  Definition 𝑺_eq_dec := string_dec.

  Notation PCtx := (NCtx 𝑿 Ty).
  Notation LCtx := (NCtx 𝑺 Ty).

  Definition 𝑿to𝑺 (x : 𝑿) : 𝑺 := x.
  Definition fresh := Context.fresh (T := Ty).

  Module RiscvPmpVariableNotation.
    Notation "'rs'"      := "rs" : string_scope.
    Notation "'rs1'"     := "rs1" : string_scope.
    Notation "'rs1_val'" := "rs1_val" : string_scope.
    Notation "'rs2'"     := "rs2" : string_scope.
    Notation "'rs2_val'" := "rs2_val" : string_scope.
    Notation "'rd'"      := "rd" : string_scope.
    Notation "'op'"      := "op" : string_scope.
    Notation "'result'"  := "result" : string_scope.
    Notation "'v'"       := "v" : string_scope.
    Notation "'imm'"     := "imm" : string_scope.
    Notation "'off'"     := "off" : string_scope.
    Notation "'ret'"     := "ret" : string_scope.
    Notation "'tmp'"     := "tmp" : string_scope.
    Notation "'t'"       := "t" : string_scope.
    Notation "'addr'"    := "addr" : string_scope.
  End RiscvPmpVariableNotation.
  Import RiscvPmpVariableNotation.

  (** Functions **)
  Inductive Fun : PCtx -> Ty -> Set :=
  | rX                 : Fun [rs ∶ ty_regidx] ty_word
  | wX                 : Fun [rd ∶ ty_regidx, v ∶ ty_word] ty_unit
  | get_arch_pc        : Fun ctx_nil ty_word
  | get_next_pc        : Fun ctx_nil ty_word
  | set_next_pc        : Fun [addr ∶ ty_word] ty_unit
  | address_aligned    : Fun [addr ∶ ty_word] ty_bool
  | execute_RTYPE      : Fun [rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_rop] ty_retired
  | execute_UTYPE      : Fun [imm ∶ ty_int, rd ∶ ty_regidx, op ∶ ty_uop] ty_retired
  | execute_RISCV_JAL  : Fun [imm ∶ ty_int, rd ∶ ty_regidx] ty_retired
  | execute_RISCV_JALR : Fun [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx] ty_retired
  .

  Inductive FunX : PCtx -> Ty -> Set :=.

  Inductive Lem : PCtx -> Set :=. 

  Definition 𝑭  : PCtx -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : PCtx -> Ty -> Set := FunX.
  Definition 𝑳  : PCtx -> Set := Lem.

  Inductive Reg : Ty -> Set :=
  | pc     : Reg ty_word
  | nextpc : Reg ty_word
  | x1     : Reg ty_word
  | x2     : Reg ty_word.

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive Signature NoConfusion for Reg.
  End TransparentObligations.

  Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
  Definition 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg).
  Proof.
    intros [? []] [? []]; cbn;
      first
        [ left; now apply eq_refl
        | right; intros e; dependent elimination e
        ].
  Defined.
End RiscvPmpTermKit.

Module RiscvPmpProgramKit <: (ProgramKit RiscvPmpTermKit).
  Module Export TM := Terms RiscvPmpTermKit.

  Module RiscvPmpVariableExpVarNotation.
    Notation "'rs'"      := (@exp_var _ "rs" _ _) : exp_scope.
    Notation "'rs1'"     := (@exp_var _ "rs1" _ _) : exp_scope.
    Notation "'rs1_val'" := (@exp_var _ "rs1_val" _ _) : exp_scope.
    Notation "'rs2'"     := (@exp_var _ "rs2" _ _) : exp_scope.
    Notation "'rs2_val'" := (@exp_var _ "rs2_val" _ _) : exp_scope.
    Notation "'rd'"      := (@exp_var _ "rd" _ _) : exp_scope.
    Notation "'op'"      := (@exp_var _ "op" _ _) : exp_scope.
    Notation "'result'"  := (@exp_var _ "result" _ _) : exp_scope.
    Notation "'v'"       := (@exp_var _ "v" _ _) : exp_scope.
    Notation "'imm'"     := (@exp_var _ "imm" _ _) : exp_scope.
    Notation "'off'"     := (@exp_var _ "off" _ _) : exp_scope.
    Notation "'ret'"     := (@exp_var _ "ret" _ _) : exp_scope.
    Notation "'tmp'"     := (@exp_var _ "tmp" _ _) : exp_scope.
    Notation "'t'"       := (@exp_var _ "t" _ _) : exp_scope.
    Notation "'addr'"    := (@exp_var _ "addr" _ _) : exp_scope.
  End RiscvPmpVariableExpVarNotation.

  Import RiscvPmpVariableExpVarNotation.
  Import RiscvPmpVariableNotation.

  (** Functions **)
  Definition fun_rX : Stm [rs ∶ ty_regidx] ty_word :=
    match: rs in regidx with
    | X1 => stm_read_register x1
    | X2 => stm_read_register x2
    end.

  Definition fun_wX : Stm [rd ∶ ty_regidx, v ∶ ty_word] ty_unit :=
    match: rd in regidx with
    | X1 => stm_write_register x1 v
    | X2 => stm_write_register x2 v
    end ;;
    stm_lit ty_unit tt.

  Definition fun_get_arch_pc : Stm ctx_nil ty_word :=
    stm_read_register pc.

  Definition fun_get_next_pc : Stm ctx_nil ty_word :=
    stm_read_register nextpc.

  Definition fun_set_next_pc : Stm [addr ∶ ty_word] ty_unit :=
    stm_write_register pc addr ;;
    stm_lit ty_unit tt.

  Definition fun_address_aligned : Stm [addr ∶ ty_word] ty_bool :=
    stm_lit ty_bool true.

  Definition fun_execute_RTYPE : Stm [rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_rop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: (rs2_val)%string := call rX rs2 in (* TODO: why is the string scope annotation required here and on next line but not on previous one? *)
    let: (result)%string :=
       match: op in rop with
       | RISCV_ADD => stm_exp (rs1_val + rs2_val)
       end in
     call wX rd result ;;
     stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_UTYPE : Stm [imm ∶ ty_int, rd ∶ ty_regidx, op ∶ ty_uop] ty_retired :=
    let: off := stm_exp imm in
    let: (ret)%string :=
       match: op in uop with
       | RISCV_LUI   => stm_exp off
       | RISCV_AUIPC =>
         let: tmp%string := call get_arch_pc in
         stm_exp (tmp + off)
       end in
    call wX rd ret ;;
    stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_RISCV_JAL : Stm [imm ∶ ty_int, rd ∶ ty_regidx] ty_retired :=
    let: tmp := stm_read_register pc in
    let: t%string := stm_exp (tmp + imm) in
    let: tmp%string := call address_aligned t in
    if: exp_not tmp
    then
      (* TODO: handle_mem_exception? *)
      stm_lit ty_retired RETIRE_FAIL
    else
      let: tmp%string := call get_next_pc in
      call wX rd tmp ;;
      stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_RISCV_JALR : Stm [imm ∶ ty_int , rs1 ∶ ty_regidx, rd ∶ ty_regidx] ty_retired :=
    let: tmp := call rX rs1 in
    let: t%string := stm_exp (tmp + imm) in
    let: tmp%string := call address_aligned t in
    if: exp_not tmp
    then
      (* TODO: handle_mem_exception? *)
      stm_lit ty_retired RETIRE_FAIL
    else
      let: tmp%string := call get_next_pc in
      call wX rd tmp ;;
      call set_next_pc t ;;
      stm_lit ty_retired RETIRE_SUCCESS.

  Definition RegStore := GenericRegStore.
  Definition read_register := generic_read_register.
  Definition write_register := generic_write_register.
  Definition read_write := generic_read_write.
  Definition read_write_distinct := generic_read_write_distinct.
  Definition write_read := generic_write_read.
  Definition write_write := generic_write_write.

  (* Memory *)
  Definition Memory := Addr -> Word.

  Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) :
    forall (args : NamedEnv Lit σs) (res : string + Lit σ) (γ γ' : RegStore) (μ μ' : Memory), Prop :=
    match f with
    end.

  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Proof.
    destruct f.
  Qed.

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f with
    | rX                 => fun_rX
    | wX                 => fun_wX
    | get_arch_pc        => fun_get_arch_pc
    | get_next_pc        => fun_get_next_pc
    | set_next_pc        => fun_set_next_pc
    | address_aligned    => fun_address_aligned
    | execute_RTYPE      => fun_execute_RTYPE
    | execute_UTYPE      => fun_execute_UTYPE
    | execute_RISCV_JAL  => fun_execute_RISCV_JAL
    | execute_RISCV_JALR => fun_execute_RISCV_JALR
    end.

End RiscvPmpProgramKit.
