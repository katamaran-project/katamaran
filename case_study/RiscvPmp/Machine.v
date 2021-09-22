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
From Equations Require Import
     Equations.
Require Import Equations.Prop.EqDec.
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
    Notation "'immext'"  := "immext" : string_scope.
    Notation "'off'"     := "off" : string_scope.
    Notation "'offset'"  := "offset" : string_scope.
    Notation "'ret'"     := "ret" : string_scope.
    Notation "'tmp'"     := "tmp" : string_scope.
    Notation "'tmp1'"    := "tmp1" : string_scope.
    Notation "'tmp2'"    := "tmp2" : string_scope.
    Notation "'t'"       := "t" : string_scope.
    Notation "'addr'"    := "addr" : string_scope.
    Notation "'paddr'"   := "paddr" : string_scope.
    Notation "'taken'"   := "taken" : string_scope.
    Notation "'typ'"     := "typ" : string_scope.
    Notation "'value'"   := "value" : string_scope.
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
  | abs                : Fun [v ∶ ty_int] ty_int
  | mem_read           : Fun [typ ∶ ty_access_type, paddr ∶ ty_int] ty_word
  | process_load       : Fun [rd ∶ ty_regidx, value ∶ ty_word] ty_retired
  | execute_RTYPE      : Fun [rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_rop] ty_retired
  | execute_ITYPE      : Fun [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_iop] ty_retired
  | execute_UTYPE      : Fun [imm ∶ ty_int, rd ∶ ty_regidx, op ∶ ty_uop] ty_retired
  | execute_BTYPE      : Fun [imm ∶ ty_int, rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, op ∶ ty_bop] ty_retired
  | execute_RISCV_JAL  : Fun [imm ∶ ty_int, rd ∶ ty_regidx] ty_retired
  | execute_RISCV_JALR : Fun [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx] ty_retired
  | execute_LOAD       : Fun [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx] ty_retired
  .

  Inductive FunX : PCtx -> Ty -> Set :=.

  Inductive Lem : PCtx -> Set :=. 

  Definition 𝑭  : PCtx -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : PCtx -> Ty -> Set := FunX.
  Definition 𝑳  : PCtx -> Set := Lem.

  Inductive Reg : Ty -> Set :=
  | pc     : Reg ty_word
  | nextpc : Reg ty_word
  | x0     : Reg ty_word
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

  Local Coercion stm_exp : Exp >-> Stm.

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
    Notation "'immext'"  := (@exp_var _ "immext" _ _) : exp_scope.
    Notation "'off'"     := (@exp_var _ "off" _ _) : exp_scope.
    Notation "'offset'"  := (@exp_var _ "offset" _ _) : exp_scope.
    Notation "'ret'"     := (@exp_var _ "ret" _ _) : exp_scope.
    Notation "'tmp'"     := (@exp_var _ "tmp" _ _) : exp_scope.
    Notation "'tmp1'"    := (@exp_var _ "tmp1" _ _) : exp_scope.
    Notation "'tmp2'"    := (@exp_var _ "tmp2" _ _) : exp_scope.
    Notation "'t'"       := (@exp_var _ "t" _ _) : exp_scope.
    Notation "'addr'"    := (@exp_var _ "addr" _ _) : exp_scope.
    Notation "'paddr'"   := (@exp_var _ "paddr" _ _) : exp_scope.
    Notation "'taken'"   := (@exp_var _ "taken" _ _) : exp_scope.
    Notation "'typ'"     := (@exp_var _ "typ" _ _) : exp_scope.
    Notation "'value'"   := (@exp_var _ "value" _ _) : exp_scope.
  End RiscvPmpVariableExpVarNotation.

  Import RiscvPmpVariableExpVarNotation.
  Import RiscvPmpVariableNotation.

  Local Notation "'Read'" := (exp_union access_type KRead (exp_lit ty_unit tt)) : exp_scope.
  Local Notation "'Write'" := (exp_union access_type KWrite (exp_lit ty_unit tt)) : exp_scope.
  Local Notation "'ReadWrite'" := (exp_union access_type KReadWrite (exp_lit ty_unit tt)) : exp_scope.
  Local Notation "'Execute'" := (exp_union access_type KExecute (exp_lit ty_unit tt)) : exp_scope.

  (** Functions **)
  Definition fun_rX : Stm [rs ∶ ty_regidx] ty_word :=
    match: rs in regidx with
    | X0 => exp_lit ty_word 0%Z
    | X1 => stm_read_register x1
    | X2 => stm_read_register x2
    end.

  Definition fun_wX : Stm [rd ∶ ty_regidx, v ∶ ty_word] ty_unit :=
    match: rd in regidx with
    | X0 => stm_lit ty_unit tt
    | X1 => stm_write_register x1 v ;; stm_lit ty_unit tt
    | X2 => stm_write_register x2 v ;; stm_lit ty_unit tt
    end.

  Definition fun_get_arch_pc : Stm ctx_nil ty_word :=
    stm_read_register pc.

  Definition fun_get_next_pc : Stm ctx_nil ty_word :=
    stm_read_register nextpc.

  Definition fun_set_next_pc : Stm [addr ∶ ty_word] ty_unit :=
    stm_write_register pc addr ;;
    stm_lit ty_unit tt.

  Definition fun_address_aligned : Stm [addr ∶ ty_word] ty_bool :=
    stm_lit ty_bool true.

  Definition fun_abs : Stm [v ∶ ty_int] ty_int :=
    if: v < (exp_lit ty_int 0%Z)
    then v * (exp_lit ty_int (-1)%Z)
    else v.

  Definition fun_mem_read : Stm [typ ∶ ty_access_type, paddr ∶ ty_int] ty_word :=
    (* TODO *)
    stm_lit ty_word 0%Z.

  Definition fun_process_load : Stm [rd ∶ ty_regidx, value ∶ ty_word] ty_retired :=
    call wX rd value ;;
    stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_RTYPE : Stm [rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_rop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: rs2_val%string := call rX rs2 in (* TODO: why is the string scope annotation required here and on next line but not on previous one? *)
    let: result%string :=
       match: op in rop with
       | RISCV_ADD => rs1_val + rs2_val
       | RISCV_SUB => rs1_val - rs2_val
       end in
     call wX rd result ;;
     stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_ITYPE : Stm [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_iop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: immext%string := imm in
    let: result%string :=
       match: op in iop with
       | RISCV_ADDI => rs1_val + immext
       end in
     call wX rd result ;;
     stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_UTYPE : Stm [imm ∶ ty_int, rd ∶ ty_regidx, op ∶ ty_uop] ty_retired :=
    let: off := imm in
    let: (ret)%string :=
       match: op in uop with
       | RISCV_LUI   => off
       | RISCV_AUIPC =>
         let: tmp%string := call get_arch_pc in
         tmp + off
       end in
    call wX rd ret ;;
    stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_RISCV_JAL : Stm [imm ∶ ty_int, rd ∶ ty_regidx] ty_retired :=
    let: tmp := stm_read_register pc in
    let: t%string := tmp + imm in
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
    let: t%string := tmp + imm in
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

  Definition fun_execute_BTYPE : Stm [imm ∶ ty_int, rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, op ∶ ty_bop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: rs2_val%string := call rX rs2 in
    let: taken%string :=
       match: op in bop with
       | RISCV_BEQ  => rs1_val = rs2_val
       | RISCV_BNE  => exp_not (rs1_val = rs2_val)
       | RISCV_BLT  => rs1_val < rs2_val
       | RISCV_BGE  => rs2_val <= rs1_val
       | RISCV_BLTU =>
         let: tmp1%string := call abs rs1_val in
         let: tmp2%string := call abs rs2_val in
         tmp1 < tmp2
       | RISCV_BGEU =>
         let: tmp1%string := call abs rs1_val in
         let: tmp2%string := call abs rs2_val in
         tmp2 <= tmp1
       end in
    let: tmp%string := stm_read_register pc in
    let: t%string := tmp + imm in
    if: taken
    then
      let: tmp%string := call address_aligned t in
      if: exp_not tmp
      then
        (* TODO: handle_mem_exception? *)
        stm_lit ty_retired RETIRE_FAIL
      else
        (call set_next_pc t ;;
         stm_lit ty_retired RETIRE_SUCCESS)
    else
      stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_LOAD : Stm [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx] ty_retired :=
    let: offset := imm in
    let: tmp%string := call rX rs1 in
    let: paddr%string := tmp + offset in
    let: tmp%string := call mem_read Read paddr in
    call process_load rd tmp ;;
    stm_lit ty_retired RETIRE_SUCCESS.

  Definition RegStore := GenericRegStore.

  (* Definition riscv_read_register (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) : Lit σ := 
    match r with
    | x0 => 0%Z
    | r => generic_read_register γ r
    end.

  Definition riscv_write_register (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) (val : Lit σ) : RegStore :=
    match r with
    | x0 => γ
    | r => generic_write_register γ r val
    end.

  Lemma riscv_read_write (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) (val : Lit σ) :
    match r with
    | x0 => riscv_read_register (riscv_write_register γ r val) x0 = 0%Z
    | r => riscv_read_register (riscv_write_register γ r val) r = val
    end.
  Proof.
    destruct r; cbn; reflexivity.
  Qed.

  Lemma riscv_read_write_distinct γ {σ τ} (r : 𝑹𝑬𝑮 σ) (k : 𝑹𝑬𝑮 τ) (val : Lit σ):
    existT _ r <> existT _ k ->
    riscv_read_register (riscv_write_register γ r val) k = riscv_read_register γ k.
  Proof.
    intros ?; unfold riscv_read_register, riscv_write_register.
    destruct k, r;
      try reflexivity;
      apply generic_read_write_distinct; assumption.
  Qed.

  Lemma riscv_write_read γ {σ} (r : 𝑹𝑬𝑮 σ) :
    forall τ (r' : 𝑹𝑬𝑮 τ),
      riscv_write_register γ r (riscv_read_register γ r) r' = γ τ r'.
  Proof.
    intros ? ?.
    unfold riscv_write_register, riscv_read_register.
    destruct r;
      try reflexivity;
      apply generic_write_read.
  Qed.

  Lemma riscv_write_write γ {σ} (r : 𝑹𝑬𝑮 σ) (v1 v2 : Lit σ) :
    forall τ (r' : 𝑹𝑬𝑮 τ),
      riscv_write_register (riscv_write_register γ r v1) r v2 r' =
      riscv_write_register γ r v2 r'.
  Proof.
    intros ? ?.
    unfold riscv_write_register, riscv_read_register.
    destruct r;
      try reflexivity;
      apply generic_write_write.
  Qed.

  Definition read_register := riscv_read_register.
  Definition write_register := riscv_write_register.
  Definition read_write := riscv_read_write.
  Definition read_write_distinct := riscv_read_write_distinct.
  Definition write_read := riscv_write_read.
  Definition write_write := riscv_write_write.
  *)

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
    | abs                => fun_abs
    | mem_read           => fun_mem_read
    | process_load       => fun_process_load
    | execute_RTYPE      => fun_execute_RTYPE
    | execute_ITYPE      => fun_execute_ITYPE
    | execute_UTYPE      => fun_execute_UTYPE
    | execute_BTYPE      => fun_execute_BTYPE
    | execute_RISCV_JAL  => fun_execute_RISCV_JAL
    | execute_RISCV_JALR => fun_execute_RISCV_JALR
    | execute_LOAD       => fun_execute_LOAD
    end.

End RiscvPmpProgramKit.
