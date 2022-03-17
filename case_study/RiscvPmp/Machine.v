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
From Katamaran Require Import
     Semantics.Registers
     Program.
From RiscvPmp Require Export
     Base.
Import Enums.
Import Unions.
Import Records.

From stdpp Require Import decidable finite.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope string_scope.

Module RiscvNotations.
  Notation "'rs'"           := "rs" : string_scope.
  Notation "'rs1'"          := "rs1" : string_scope.
  Notation "'rs2'"          := "rs2" : string_scope.
  Notation "'rd'"           := "rd" : string_scope.
  Notation "'op'"           := "op" : string_scope.
  Notation "'v'"            := "v" : string_scope.
  Notation "'imm'"          := "imm" : string_scope.
  Notation "'t'"            := "t" : string_scope.
  Notation "'addr'"         := "addr" : string_scope.
  Notation "'paddr'"        := "paddr" : string_scope.
  Notation "'vaddr'"        := "vaddr" : string_scope.
  Notation "'typ'"          := "typ" : string_scope.
  Notation "'acc'"          := "acc" : string_scope.
  Notation "'value'"        := "value" : string_scope.
  Notation "'data'"         := "data" : string_scope.
  Notation "'ent'"          := "ent" : string_scope.
  Notation "'pmpaddr'"      := "pmpaddr" : string_scope.
  Notation "'prev_pmpaddr'" := "prev_pmpaddr" : string_scope.
  Notation "'cfg'"          := "cfg" : string_scope.
  Notation "'rng'"          := "rng" : string_scope.
  Notation "'bv'"           := "bv" : string_scope.
  Notation "'e'"            := "e" : string_scope.
  Notation "'ctl'"          := "ctl" : string_scope.
  Notation "'c'"            := "c" : string_scope.
  Notation "'cause'"        := "cause" : string_scope.
  Notation "'m'"            := "m" : string_scope.
  Notation "'priv'"         := "priv" : string_scope.
  Notation "'cur_priv'"     := "cur_priv" : string_scope.
  Notation "'del_priv'"     := "del_priv" : string_scope.
  Notation "'p'"            := "p" : string_scope.
  Notation "'rs1_val'"      := "rs1_val" : string_scope.
  Notation "'rs2_val'"      := "rs2_val" : string_scope.
  Notation "'csr_val'"      := "csr_val" : string_scope.
  Notation "'op'"           := "op" : string_scope.
  Notation "'result'"       := "result" : string_scope.
  Notation "'res'"          := "res" : string_scope.
  Notation "'immext'"       := "immext" : string_scope.
  Notation "'off'"          := "off" : string_scope.
  Notation "'offset'"       := "offset" : string_scope.
  Notation "'ret'"          := "ret" : string_scope.
  Notation "'tmp'"          := "tmp" : string_scope.
  Notation "'tmp1'"         := "tmp1" : string_scope.
  Notation "'tmp2'"         := "tmp2" : string_scope.
  Notation "'tmp3'"         := "tmp3" : string_scope.
  Notation "'taken'"        := "taken" : string_scope.
  Notation "'check'"        := "check" : string_scope.
  Notation "'L'"            := "L" : string_scope.
  Notation "'A'"            := "A" : string_scope.
  Notation "'X'"            := "X" : string_scope.
  Notation "'W'"            := "W" : string_scope.
  Notation "'R'"            := "R" : string_scope.
  Notation "'lo'"           := "lo" : string_scope.
  Notation "'hi'"           := "hi" : string_scope.
  Notation "'f'"            := "f" : string_scope.
  Notation "'w'"            := "w" : string_scope.
  Notation "'tvec'"         := "tvec" : string_scope.
  Notation "'epc'"          := "epc" : string_scope.
  Notation "'prev_priv'"    := "prev_priv" : string_scope.
  Notation "'MPP'"          := "MPP" : string_scope.
  Notation "'csr'"          := "csr" : string_scope.
  Notation "'csrrw'"        := "csrrw" : string_scope.
  Notation "'csrpr'"        := "csrpr" : string_scope.
End RiscvNotations.

(* We postulate a pure decode function and assume that that's what the decode primitive implements. *)
Axiom pure_decode : Z -> string + AST.

Module Import RiscvPmpProgram <: Program RiscvPmpBase.

  Section FunDeclKit.
  Import RiscvNotations.

  (** Functions **)
  Inductive Fun : PCtx -> Ty -> Set :=
  | rX                    : Fun [rs ∶ ty_regno] ty_xlenbits
  | wX                    : Fun [rd ∶ ty_regno; v ∶ ty_xlenbits] ty_unit
  | get_arch_pc           : Fun ctx.nil ty_xlenbits
  | get_next_pc           : Fun ctx.nil ty_xlenbits
  | set_next_pc           : Fun [addr ∶ ty_xlenbits] ty_unit
  | tick_pc               : Fun ctx.nil ty_unit
  | abs                   : Fun [v ∶ ty_int] ty_int
  | mem_read              : Fun [typ ∶ ty_access_type; paddr ∶ ty_xlenbits] ty_memory_op_result
  | checked_mem_read      : Fun [t ∶ ty_access_type; paddr ∶ ty_xlenbits] ty_memory_op_result
  | checked_mem_write     : Fun [paddr ∶ ty_xlenbits; data ∶ ty_int] ty_memory_op_result
  | pmp_mem_read          : Fun [t∶ ty_access_type; p ∶ ty_privilege; paddr ∶ ty_xlenbits] ty_memory_op_result
  | pmp_mem_write         : Fun [paddr ∶ ty_xlenbits; data ∶ ty_int; typ ∶ ty_access_type; priv ∶ ty_privilege] ty_memory_op_result
  | pmpLocked             : Fun [cfg ∶ ty_pmpcfg_ent] ty_bool
  | pmpCheck              : Fun [addr ∶ ty_xlenbits; acc ∶ ty_access_type; priv ∶ ty_privilege] (ty_option ty_exception_type)
  | pmpCheckPerms         : Fun [ent ∶ ty_pmpcfg_ent; acc ∶ ty_access_type; priv ∶ ty_privilege] ty_bool
  | pmpCheckRWX           : Fun [ent ∶ ty_pmpcfg_ent; acc ∶ ty_access_type] ty_bool
  | pmpMatchEntry         : Fun [addr ∶ ty_xlenbits; acc ∶ ty_access_type; priv ∶ ty_privilege; ent ∶ ty_pmpcfg_ent; pmpaddr ∶ ty_xlenbits; prev_pmpaddr ∶ ty_xlenbits] ty_pmpmatch
  | pmpAddrRange          : Fun [cfg ∶ ty_pmpcfg_ent; pmpaddr ∶ ty_xlenbits; prev_pmpaddr ∶ ty_xlenbits] ty_pmp_addr_range
  | pmpMatchAddr          : Fun [addr ∶ ty_xlenbits; rng ∶ ty_pmp_addr_range] ty_pmpaddrmatch
  | process_load          : Fun [rd ∶ ty_regno; vaddr ∶ ty_xlenbits; value ∶ ty_memory_op_result] ty_retired
  | mem_write_value       : Fun [paddr ∶ ty_xlenbits; value ∶ ty_int] ty_memory_op_result
  | main                  : Fun ctx.nil ty_unit
  | init_model            : Fun ctx.nil ty_unit
  | loop                  : Fun ctx.nil ty_unit
  | step                  : Fun ctx.nil ty_unit
  | fetch                 : Fun ctx.nil ty_fetch_result
  | init_sys              : Fun ctx.nil ty_unit
  | init_pmp              : Fun ctx.nil ty_unit
  | exceptionType_to_bits : Fun [e ∶ ty_exception_type] ty_exc_code
  | privLevel_to_bits     : Fun [p ∶ ty_privilege] ty_xlenbits
  | mstatus_to_bits       : Fun [value ∶ ty_mstatus] ty_xlenbits
  | mstatus_from_bits     : Fun [value ∶ ty_xlenbits] ty_mstatus
  | handle_mem_exception  : Fun [addr ∶ ty_xlenbits; e ∶ ty_exception_type] ty_unit
  | exception_handler     : Fun [cur_priv ∶ ty_privilege; ctl ∶ ty_ctl_result; "pc" ∶ ty_xlenbits] ty_int
  | exception_delegatee   : Fun [p ∶ ty_privilege] ty_privilege
  | trap_handler          : Fun [del_priv ∶ ty_privilege; c ∶ ty_exc_code; "pc" ∶ ty_xlenbits] ty_xlenbits
  | prepare_trap_vector   : Fun [p ∶ ty_privilege; cause ∶ ty_mcause] ty_xlenbits
  | tvec_addr             : Fun [m ∶ ty_int; c ∶ ty_mcause] (ty_option ty_xlenbits)
  | handle_illegal        : Fun ctx.nil ty_unit
  | check_CSR             : Fun [csr ∶ ty_csridx; p ∶ ty_privilege] ty_bool
  | is_CSR_defined        : Fun [csr ∶ ty_csridx; p ∶ ty_privilege] ty_bool
  | csrAccess             : Fun [csr ∶ ty_csridx] ty_access_type
  | csrPriv               : Fun [csr ∶ ty_csridx] ty_privilege
  | check_CSR_access      : Fun [csrrw ∶ ty_access_type; csrpr ∶ ty_privilege; p ∶ ty_privilege] ty_bool
  | readCSR               : Fun [csr ∶ ty_csridx] ty_xlenbits
  | writeCSR              : Fun [csr ∶ ty_csridx; value ∶ ty_xlenbits] ty_unit
  | execute               : Fun ["ast" ∶ ty_ast] ty_retired
  | execute_RTYPE         : Fun [rs2 ∶ ty_regno; rs1 ∶ ty_regno; rd ∶ ty_regno; op ∶ ty_rop] ty_retired
  | execute_ITYPE         : Fun [imm ∶ ty_int; rs1 ∶ ty_regno; rd ∶ ty_regno; op ∶ ty_iop] ty_retired
  | execute_UTYPE         : Fun [imm ∶ ty_int; rd ∶ ty_regno; op ∶ ty_uop] ty_retired
  | execute_BTYPE         : Fun [imm ∶ ty_int; rs2 ∶ ty_regno; rs1 ∶ ty_regno; op ∶ ty_bop] ty_retired
  | execute_RISCV_JAL     : Fun [imm ∶ ty_int; rd ∶ ty_regno] ty_retired
  | execute_RISCV_JALR    : Fun [imm ∶ ty_int; rs1 ∶ ty_regno; rd ∶ ty_regno] ty_retired
  | execute_LOAD          : Fun [imm ∶ ty_int; rs1 ∶ ty_regno; rd ∶ ty_regno] ty_retired
  | execute_STORE         : Fun [imm ∶ ty_int; rs2 ∶ ty_regno; rs1 ∶ ty_regno] ty_retired
  | execute_ECALL         : Fun ctx.nil ty_retired
  | execute_MRET          : Fun ctx.nil ty_retired
  | execute_CSR           : Fun [csr ∶ ty_csridx; rs1 ∶ ty_regno; rd ∶ ty_regno; op ∶ ty_csrop] ty_retired
  .

  Inductive FunX : PCtx -> Ty -> Set :=
  | read_ram  : FunX [paddr ∶ ty_int] ty_word
  | write_ram : FunX [paddr ∶ ty_int; data ∶ ty_word] ty_word
  | decode    : FunX [bv ∶ ty_int] ty_ast
  .

  Inductive Lem : PCtx -> Set :=
  | open_gprs             : Lem ctx.nil
  | close_gprs            : Lem ctx.nil
  | open_pmp_entries      : Lem ctx.nil
  | close_pmp_entries     : Lem ctx.nil
  | extract_pmp_ptsto     : Lem [paddr ∶ ty_xlenbits]
  | gen_addr_matching_cfg : Lem [paddr :: ty_xlenbits; "cfgidx" :: ty_pmpcfgidx; cfg :: ty_pmpcfg_ent; "prev_addr" :: ty_xlenbits; addr :: ty_xlenbits]
  .

  Definition 𝑭  : PCtx -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : PCtx -> Ty -> Set := FunX.
  Definition 𝑳  : PCtx -> Set := Lem.
  End FunDeclKit.

  Include FunDeclMixin RiscvPmpBase.

  Module RiscvμSailNotations.
    Notation "'rs'"           := (@exp_var _ "rs" _ _) : exp_scope.
    Notation "'rs1'"          := (@exp_var _ "rs1" _ _) : exp_scope.
    Notation "'rs1_val'"      := (@exp_var _ "rs1_val" _ _) : exp_scope.
    Notation "'rs2'"          := (@exp_var _ "rs2" _ _) : exp_scope.
    Notation "'rs2_val'"      := (@exp_var _ "rs2_val" _ _) : exp_scope.
    Notation "'csr_val'"      := (@exp_var _ "csr_val" _ _) : exp_scope.
    Notation "'rd'"           := (@exp_var _ "rd" _ _) : exp_scope.
    Notation "'op'"           := (@exp_var _ "op" _ _) : exp_scope.
    Notation "'result'"       := (@exp_var _ "result" _ _) : exp_scope.
    Notation "'res'"          := (@exp_var _ "res" _ _) : exp_scope.
    Notation "'v'"            := (@exp_var _ "v" _ _) : exp_scope.
    Notation "'imm'"          := (@exp_var _ "imm" _ _) : exp_scope.
    Notation "'immext'"       := (@exp_var _ "immext" _ _) : exp_scope.
    Notation "'off'"          := (@exp_var _ "off" _ _) : exp_scope.
    Notation "'offset'"       := (@exp_var _ "offset" _ _) : exp_scope.
    Notation "'ret'"          := (@exp_var _ "ret" _ _) : exp_scope.
    Notation "'tmp'"          := (@exp_var _ "tmp" _ _) : exp_scope.
    Notation "'tmp1'"         := (@exp_var _ "tmp1" _ _) : exp_scope.
    Notation "'tmp2'"         := (@exp_var _ "tmp2" _ _) : exp_scope.
    Notation "'tmp3'"         := (@exp_var _ "tmp3" _ _) : exp_scope.
    Notation "'t'"            := (@exp_var _ "t" _ _) : exp_scope.
    Notation "'e'"            := (@exp_var _ "e" _ _) : exp_scope.
    Notation "'addr'"         := (@exp_var _ "addr" _ _) : exp_scope.
    Notation "'paddr'"        := (@exp_var _ "paddr" _ _) : exp_scope.
    Notation "'vaddr'"        := (@exp_var _ "vaddr" _ _) : exp_scope.
    Notation "'taken'"        := (@exp_var _ "taken" _ _) : exp_scope.
    Notation "'typ'"          := (@exp_var _ "typ" _ _) : exp_scope.
    Notation "'acc'"          := (@exp_var _ "acc" _ _) : exp_scope.
    Notation "'value'"        := (@exp_var _ "value" _ _) : exp_scope.
    Notation "'data'"         := (@exp_var _ "data" _ _) : exp_scope.
    Notation "'check'"        := (@exp_var _ "check" _ _) : exp_scope.
    Notation "'ent'"          := (@exp_var _ "ent" _ _) : exp_scope.
    Notation "'pmpaddr'"      := (@exp_var _ "pmpaddr" _ _) : exp_scope.
    Notation "'prev_pmpaddr'" := (@exp_var _ "prev_pmpaddr" _ _) : exp_scope.
    Notation "'rng'"          := (@exp_var _ "rng" _ _) : exp_scope.
    Notation "'cfg'"          := (@exp_var _ "cfg" _ _) : exp_scope.
    Notation "'L'"            := (@exp_var _ "L" _ _) : exp_scope.
    Notation "'A'"            := (@exp_var _ "A" _ _) : exp_scope.
    Notation "'X'"            := (@exp_var _ "X" _ _) : exp_scope.
    Notation "'W'"            := (@exp_var _ "W" _ _) : exp_scope.
    Notation "'R'"            := (@exp_var _ "R" _ _) : exp_scope.
    Notation "'lo'"           := (@exp_var _ "lo" _ _) : exp_scope.
    Notation "'hi'"           := (@exp_var _ "hi" _ _) : exp_scope.
    Notation "'f'"            := (@exp_var _ "f" _ _) : exp_scope.
    Notation "'w'"            := (@exp_var _ "w" _ _) : exp_scope.
    Notation "'ctl'"          := (@exp_var _ "ctl" _ _) : exp_scope.
    Notation "'c'"            := (@exp_var _ "c" _ _) : exp_scope.
    Notation "'cause'"        := (@exp_var _ "cause" _ _) : exp_scope.
    Notation "'tvec'"         := (@exp_var _ "tvec" _ _) : exp_scope.
    Notation "'m'"            := (@exp_var _ "m" _ _) : exp_scope.
    Notation "'epc'"          := (@exp_var _ "epc" _ _) : exp_scope.
    Notation "'priv'"         := (@exp_var _ "priv" _ _) : exp_scope.
    Notation "'cur_priv'"     := (@exp_var _ "cur_priv" _ _) : exp_scope.
    Notation "'del_priv'"     := (@exp_var _ "del_priv" _ _) : exp_scope.
    Notation "'prev_priv'"    := (@exp_var _ "prev_priv" _ _) : exp_scope.
    Notation "'p'"            := (@exp_var _ "p" _ _) : exp_scope.
    Notation "'MPP'"          := (@exp_var _ "MPP" _ _) : exp_scope.
    Notation "'csr'"          := (@exp_var _ "csr" _ _) : exp_scope.
    Notation "'csrrw'"        := (@exp_var _ "csrrw" _ _) : exp_scope.
    Notation "'csrpr'"        := (@exp_var _ "csrpr" _ _) : exp_scope.

    Notation "'Read'" := (exp_union access_type KRead (exp_val ty_unit tt)) : exp_scope.
    Notation "'Write'" := (exp_union access_type KWrite (exp_val ty_unit tt)) : exp_scope.
    Notation "'ReadWrite'" := (exp_union access_type KReadWrite (exp_val ty_unit tt)) : exp_scope.
    Notation "'Execute'" := (exp_union access_type KExecute (exp_val ty_unit tt)) : exp_scope.

    Notation "'E_Fetch_Access_Fault'" := (exp_union exception_type KE_Fetch_Access_Fault (exp_val ty_unit tt)) : exp_scope.
    Notation "'E_Load_Access_Fault'" := (exp_union exception_type KE_Load_Access_Fault (exp_val ty_unit tt)) : exp_scope.
    Notation "'E_SAMO_Access_Fault'" := (exp_union exception_type KE_SAMO_Access_Fault (exp_val ty_unit tt)) : exp_scope.
    Notation "'E_U_EnvCall'" := (exp_union exception_type KE_U_EnvCall (exp_val ty_unit tt)) : exp_scope.
    Notation "'E_M_EnvCall'" := (exp_union exception_type KE_M_EnvCall (exp_val ty_unit tt)) : exp_scope.
    Notation "'E_Illegal_Instr'" := (exp_union exception_type KE_Illegal_Instr (exp_val ty_unit tt)) : exp_scope.

    Notation "'None'" := (exp_inr (exp_val ty_unit tt)) : exp_scope.
    Notation "'Some' va" := (exp_inl va) (at level 10, va at next level) : exp_scope.

    Notation "'MemValue' memv" := (exp_union memory_op_result KMemValue memv) (at level 10, memv at next level) : exp_scope.
    Notation "'MemException' meme" := (exp_union memory_op_result KMemException meme) (at level 10, meme at next level) : exp_scope.

    Notation "'F_Base' memv" := (exp_union fetch_result KF_Base memv) (at level 10, memv at next level) : exp_scope.
    Notation "'F_Error' meme memv" := (exp_union fetch_result KF_Error (exp_binop binop_pair meme memv)) (at level 10, meme at next level, memv at next level) : exp_scope.

    Notation "'CTL_TRAP' exc" := (exp_union ctl_result KCTL_TRAP exc) (at level 10, exc at next level) : exp_scope.
    Notation "'CTL_MRET'" := (exp_union ctl_result KCTL_MRET (exp_val ty_unit tt)) : exp_scope.
  End RiscvμSailNotations.

  Section FunDefKit.
  Import RiscvNotations.
  Import RiscvμSailNotations.
  Local Coercion stm_exp : Exp >-> Stm.

  Notation "'use' 'lemma' lem args" := (stm_lemma lem args%env) (at level 10, lem at next level) : exp_scope.
  Notation "'use' 'lemma' lem" := (stm_lemma lem env.nil) (at level 10, lem at next level) : exp_scope.

  Definition z_exp {Γ} : Z -> Exp Γ ty_int := exp_val ty_int.

  Definition zero_reg {Γ} : Stm Γ ty_xlenbits := exp_val ty_int 0%Z.

  (** Functions **)
  Import Bitvector.bv.notations.
  Definition fun_rX : Stm [rs ∶ ty_regno] ty_xlenbits :=
    use lemma open_gprs ;;
    let: v := match: rs in bvec 3 with
              | 000 => z_exp 0
              | 001 => stm_read_register x1
              | 010 => stm_read_register x2
              | 011 => stm_read_register x3
              | 100 => stm_read_register x4
              | 101 => stm_read_register x5
              | 110 => stm_read_register x6
              | 111 => stm_read_register x7
              end in
    use lemma close_gprs ;;
    v.

  Definition fun_wX : Stm [rd ∶ ty_regno; v ∶ ty_xlenbits] ty_unit :=
    use lemma open_gprs ;;
    match: rd in bvec 3 with
    | 000 => z_exp 0
    | 001 => stm_write_register x1 v
    | 010 => stm_write_register x2 v
    | 011 => stm_write_register x3 v
    | 100 => stm_write_register x4 v
    | 101 => stm_write_register x5 v
    | 110 => stm_write_register x6 v
    | 111 => stm_write_register x7 v
    end ;;
    use lemma close_gprs.

  Definition fun_get_arch_pc : Stm ctx.nil ty_xlenbits :=
    stm_read_register pc.

  Definition fun_get_next_pc : Stm ctx.nil ty_xlenbits :=
    stm_read_register nextpc.

  Definition fun_set_next_pc : Stm [addr ∶ ty_xlenbits] ty_unit :=
    stm_write_register nextpc addr ;;
    stm_val ty_unit tt.

  Definition fun_tick_pc : Stm ctx.nil ty_unit :=
    let: tmp := stm_read_register nextpc in
    stm_write_register pc tmp ;;
    stm_val ty_unit tt.

  Definition fun_abs : Stm [v ∶ ty_int] ty_int :=
    if: v < z_exp 0
    then v * z_exp (-1)
    else v.

  Definition fun_mem_read : Stm [typ ∶ ty_access_type; paddr ∶ ty_xlenbits] ty_memory_op_result :=
    let: tmp := stm_read_register cur_privilege in
    call pmp_mem_read typ tmp paddr.

  Definition fun_checked_mem_read : Stm [t ∶ ty_access_type; paddr ∶ ty_xlenbits] ty_memory_op_result :=
    let: tmp := foreign read_ram paddr in
    MemValue tmp.

  Definition fun_checked_mem_write : Stm [paddr ∶ ty_xlenbits; data ∶ ty_int] ty_memory_op_result :=
    let: tmp := foreign write_ram paddr data in
    MemValue tmp.

  (* TODO *)
  (* pre: pmp_entries(?entries) ∗ pmp_addr_access(?entries, ?mode) *)
  Definition fun_pmp_mem_read : Stm [t∶ ty_access_type; p ∶ ty_privilege; paddr ∶ ty_xlenbits] ty_memory_op_result :=
    let: tmp := call pmpCheck paddr t p in
    match: tmp with
    | inl e => MemException e
    | inr v => call checked_mem_read t paddr
    end.
  (* post: result .
     match tmp with
     | Some e => result = MemException e
     | None   => ∃ w . result = MemValue w (* can probably just drop the MemValue here *)
     end *)

  Definition fun_pmp_mem_write : Stm [paddr ∶ ty_xlenbits; data ∶ ty_int; typ ∶ ty_access_type; priv ∶ ty_privilege] ty_memory_op_result :=
    let: tmp := call pmpCheck paddr typ priv in
    match: tmp with
    | inl e => MemException e
    | inr v => call checked_mem_write paddr data
    end.

  Definition fun_pmpLocked : Stm [cfg ∶ ty_pmpcfg_ent] ty_bool :=
    match: cfg in rpmpcfg_ent with [L; A; X; W; R] => L end.

  (* TODO *)
  (* pre: pmp_entries(?entries) ∗ pmp_addr_access(?entries, ?mode) *)
  Definition fun_pmpCheck : Stm [addr ∶ ty_xlenbits; acc ∶ ty_access_type; priv ∶ ty_privilege] (ty_option ty_exception_type) :=
    use lemma open_pmp_entries ;;
    let: check%string :=
      let: tmp1 := stm_read_register pmp0cfg in
      let: tmp2 := stm_read_register pmpaddr0 in
      let: tmp3 := z_exp 0 in
      let: tmp := call pmpMatchEntry addr acc priv tmp1 tmp2 tmp3 in
      match: tmp in pmpmatch with
      | PMP_Success  => stm_val ty_bool true
      | PMP_Fail     => stm_val ty_bool false
      | PMP_Continue =>
      let: tmp1 := stm_read_register pmp1cfg in
      let: tmp2 := stm_read_register pmpaddr1 in
      let: tmp3 := stm_read_register pmpaddr0 in
      let: tmp := call pmpMatchEntry addr acc priv tmp1 tmp2 tmp3 in
      match: tmp in pmpmatch with
      | PMP_Success  => stm_val ty_bool true
      | PMP_Fail     => stm_val ty_bool false
      | PMP_Continue =>
          match: priv in privilege with
          | Machine => stm_val ty_bool true
          | User    => stm_val ty_bool false
          end
      end
      end in
      use lemma close_pmp_entries ;;
      if: check
      then None
      else
        match: acc in union access_type with
        |> KRead pat_unit      => Some E_Load_Access_Fault
        |> KWrite pat_unit     => Some E_SAMO_Access_Fault
        |> KReadWrite pat_unit => Some E_SAMO_Access_Fault
        |> KExecute pat_unit   => Some E_Fetch_Access_Fault
        end.
  (* post: result .
     if check then result = None ∗ ∃ w . addr ↦ w ∗ ((∃ w' . addr ↦ w') -∗ pmp_addr_access(?entries, ?mode)) (* magic wand: with predicate or add support to Katamaran *)
     else    ∃ e . result = Some e *)

  Definition fun_pmpCheckPerms : Stm [ent ∶ ty_pmpcfg_ent; acc ∶ ty_access_type; priv ∶ ty_privilege] ty_bool :=
    match: priv in privilege with
    | Machine =>
      let: tmp := call pmpLocked ent in
      if: tmp
      then call pmpCheckRWX ent acc
      else stm_val ty_bool true
    | User =>
      call pmpCheckRWX ent acc
    end.

  Definition fun_pmpCheckRWX : Stm [ent ∶ ty_pmpcfg_ent; acc ∶ ty_access_type] ty_bool :=
    match: ent in rpmpcfg_ent with
      [L; A; X; W; R] =>
        match: acc in union access_type with
        |> KRead pat_unit      => R
        |> KWrite pat_unit     => W
        |> KReadWrite pat_unit => R && W
        |> KExecute pat_unit   => X
        end
    end.

  (* TODO *)
  (* pre: ⊤ *)
  Definition fun_pmpMatchEntry : Stm [addr ∶ ty_xlenbits; acc ∶ ty_access_type; priv ∶ ty_privilege; ent ∶ ty_pmpcfg_ent; pmpaddr ∶ ty_xlenbits; prev_pmpaddr ∶ ty_xlenbits] ty_pmpmatch :=
    let: rng := call pmpAddrRange ent pmpaddr prev_pmpaddr in
    let: tmp := call pmpMatchAddr addr rng in
    match: tmp in pmpaddrmatch with
    | PMP_NoMatch      => exp_val ty_pmpmatch PMP_Continue
    | PMP_PartialMatch => exp_val ty_pmpmatch PMP_Fail
    | PMP_Match        =>
      let: tmp := call pmpCheckPerms ent acc priv in
      if: tmp
      then exp_val ty_pmpmatch PMP_Success
      else exp_val ty_pmpmatch PMP_Fail
    end.
  (* post: result .
     match tmp with
     | PMP_NoMatch      => result = PMP_Continue
     | PMP_PartialMatch => result = PMP_Fail
     | PMP_Match        => if tmp1 then result = PMP_Success ∗ prev_pmpaddr <= addr ∗ addr <= pmpaddr
                           else         result = PMP_Fail
     end *)

  Definition fun_pmpAddrRange : Stm [cfg ∶ ty_pmpcfg_ent; pmpaddr ∶ ty_xlenbits; prev_pmpaddr ∶ ty_xlenbits] ty_pmp_addr_range :=
    match: cfg in rpmpcfg_ent with
      [L; A; X; W; R] =>
        match: A in pmpaddrmatchtype with
        | OFF => None
        | TOR => Some (exp_binop binop_pair prev_pmpaddr pmpaddr)
        end
    end.

  Definition fun_pmpMatchAddr : Stm [addr ∶ ty_int; rng ∶ ty_pmp_addr_range] ty_pmpaddrmatch :=
    match: rng with
    | inl v =>
      match: v in (ty_int , ty_int) with
      | (lo , hi) =>
        if: hi < lo
        then exp_val ty_pmpaddrmatch PMP_NoMatch
        else
          if: (addr < lo) || (hi <= addr) (* NOTE: this only makes sense when using a "width" (see Sail impl), having this without the width means the PartialMatch case will never occur *)
          then exp_val ty_pmpaddrmatch PMP_NoMatch
          else if: (lo <= addr) && (addr < hi) (* NOTE: small difference with actual model due to lack of width, but more correct with respect to the manual (y matches TOR if pmpaddrᵢ₋₁ <= y < pmpaddrᵢ) *)
               then exp_val ty_pmpaddrmatch PMP_Match
               else exp_val ty_pmpaddrmatch PMP_PartialMatch
      end
    | inr v => exp_val ty_pmpaddrmatch PMP_NoMatch
    end.

  Definition fun_process_load : Stm [rd ∶ ty_regno; vaddr ∶ ty_xlenbits; value ∶ ty_memory_op_result] ty_retired :=
    match: value in union memory_op_result with
    |> KMemValue (pat_var "result") => call wX rd result;;
                                       stm_val ty_retired RETIRE_SUCCESS
    |> KMemException (pat_var "e")  => call handle_mem_exception vaddr e;;
                                       stm_val ty_retired RETIRE_FAIL
    end.

  Definition fun_mem_write_value : Stm [paddr ∶ ty_xlenbits; value ∶ ty_int] ty_memory_op_result :=
    let: tmp := stm_read_register cur_privilege in
    call pmp_mem_write paddr value Write tmp.

  Definition fun_main : Stm ctx.nil ty_unit :=
    call init_model ;;
    call loop.

  (* NOTE: simplified init_model function, just calls init_sys which just calls
           init_pmp *)
  Definition fun_init_model : Stm ctx.nil ty_unit :=
    call init_sys.

  Definition fun_loop : Stm ctx.nil ty_unit :=
    call step ;; call loop.

  Definition fun_fetch : Stm ctx.nil ty_fetch_result :=
    let: tmp1 := stm_read_register pc in
    let: tmp2 := call mem_read Execute tmp1 in
    match: tmp2 in union memory_op_result with
    |> KMemValue (pat_var "result") => F_Base result
    |> KMemException (pat_var "e")  => F_Error e tmp1
    end.

  Definition fun_step : Stm ctx.nil ty_unit :=
    let: f := call fetch in
    match: f in union fetch_result with
    |> KF_Base (pat_var "w") =>  let: "ast" := foreign decode w in
                                 let: tmp := stm_read_register pc in
                                 stm_write_register nextpc (tmp + (z_exp 4)) ;;
                                 call execute (exp_var "ast")
    |> KF_Error (pat_pair "e" "addr") => call handle_mem_exception addr e ;;
                                         stm_val ty_retired RETIRE_FAIL
    end ;;
    call tick_pc.

  Definition fun_init_sys : Stm ctx.nil ty_unit :=
    call init_pmp.

  Definition fun_init_pmp : Stm ctx.nil ty_unit :=
    let: tmp := stm_read_register pmp0cfg in
    match: tmp in rpmpcfg_ent with
      ["L"; "A"; "X"; "W"; "R"] =>
        stm_write_register
          pmp0cfg (exp_record rpmpcfg_ent
                              [nenv L;
                               exp_val ty_pmpaddrmatchtype OFF;
                               X;
                               W;
                               R ]) ;;
        stm_val ty_unit tt
    end ;;
    let: tmp := stm_read_register pmp1cfg in
    match: tmp in rpmpcfg_ent with
      ["L"; "A"; "X"; "W"; "R"] =>
        stm_write_register
          pmp1cfg (exp_record rpmpcfg_ent
                              [nenv L;
                               exp_val ty_pmpaddrmatchtype OFF;
                               X;
                               W;
                               R ]) ;;
        stm_val ty_unit tt
    end.

  Definition fun_exceptionType_to_bits : Stm [e ∶ ty_exception_type] ty_exc_code :=
    match: e in union exception_type with
      |> KE_Fetch_Access_Fault pat_unit => stm_val ty_exc_code 1%Z
      |> KE_Illegal_Instr      pat_unit => stm_val ty_exc_code 2%Z
      |> KE_Load_Access_Fault  pat_unit => stm_val ty_exc_code 5%Z
      |> KE_SAMO_Access_Fault  pat_unit => stm_val ty_exc_code 7%Z
      |> KE_U_EnvCall          pat_unit => stm_val ty_exc_code 8%Z
      |> KE_M_EnvCall          pat_unit => stm_val ty_exc_code 11%Z
    end.

  Definition fun_handle_mem_exception : Stm [addr ∶ ty_xlenbits; e ∶ ty_exception_type] ty_unit :=
    let: tmp1 := stm_read_register pc in
    let: tmp2 := stm_read_register cur_privilege in
    let: tmp3 := call exception_handler tmp2 (CTL_TRAP e) tmp1 in
    call set_next_pc tmp3.

  Definition fun_exception_handler : Stm [cur_priv ∶ ty_privilege; ctl ∶ ty_ctl_result; "pc" ∶ ty_xlenbits] ty_xlenbits :=
    match: ctl in union ctl_result with
    |> KCTL_TRAP (pat_var "e") => let: del_priv := call exception_delegatee cur_priv in
                                  let: tmp := call exceptionType_to_bits e in
                                  call trap_handler del_priv tmp (exp_var "pc")
    |> KCTL_MRET pat_unit      =>
      (* NOTE: normally the return address is computed with:
               prepare_xret_target(Machine) & pc_alignment_mask()
               we drop the alignment mask and inline prepare_xret_target,
               which just calls get_xret_target, which returns (for M-mode)
               the value of mepc *)
      let: tmp1 := stm_read_register mstatus in
      (stm_match_record rmstatus tmp1
                        (recordpat_snoc recordpat_nil "MPP" MPP%string)
                        (stm_write_register cur_privilege MPP ;;
                         stm_write_register mstatus (exp_record rmstatus [ exp_val ty_privilege User ]) ;;
                         stm_read_register mepc))
    end.

  Definition fun_exception_delegatee : Stm [p ∶ ty_privilege] ty_privilege :=
    stm_val ty_privilege Machine.

  Definition fun_trap_handler : Stm [del_priv ∶ ty_privilege; c ∶ ty_exc_code; "pc" ∶ ty_xlenbits] ty_xlenbits :=
    stm_write_register mcause c ;;
    let: tmp := stm_read_register cur_privilege in
    stm_write_register mstatus (exp_record rmstatus [ tmp ]) ;;
    stm_write_register mepc (exp_var "pc") ;;
    stm_write_register cur_privilege del_priv ;;
    (* NOTE: the following let can be dropped by just reusing c (the value we are
             writing into mcause, but this (manual) translation is more faithful to
             what I expect an automatic translation would produce, i.e. do an 
             stm_read_register when a register is used as param to a function call,
             to get the value in the register
     
             Also keep into account that the risc-v model trap handler function handles
             more cases than represented here, i.e. we only have support for M-mode and
             do not explicitly check for this here. So we could simplify
             prepare_trap_vector to not take a cause parameter (which it won't use
             anyway because we only support direct mode for the trap vector, meaning
             that the trap handler function installed at the memory address denoted
             by mtvec will need to read the mcause register to dispatch to the
             corresponding trap handler for the cause). *)
    let: tmp := stm_read_register mcause in
    call prepare_trap_vector del_priv tmp.

  Definition fun_prepare_trap_vector : Stm [p ∶ ty_privilege; cause ∶ ty_mcause] ty_xlenbits :=
    let: tvec := match: p in privilege with
    | Machine => stm_read_register mtvec
    | User => fail "N extension (user-level interrupts) not supported"
    end in
    let: tmp := call tvec_addr tvec cause in
    (* NOTE: tvec_addr will only ever return Some(epc), because we don't support
             the 2 mode bits and only have direct mode. The None case only arises
             for the Reserved mode of trap vectors.

             The given privilege level (p) is ignored, this only makes sense when
             supervisor mode is supported. *)
    match: tmp with
    | inl epc => epc
    | inr e   => fail "Invalid tvec mode"
    end.

  Definition fun_tvec_addr : Stm [m ∶ ty_xlenbits; c ∶ ty_mcause] (ty_option ty_xlenbits) :=
    Some m.

  Definition fun_handle_illegal : Stm ctx.nil ty_unit :=
    let: t := E_Illegal_Instr in
    let: tmp1 := stm_read_register cur_privilege in
    let: tmp2 := stm_read_register pc in
    let: tmp3 := call exception_handler tmp1 (CTL_TRAP t) tmp2 in
    call set_next_pc tmp3.

  Definition fun_check_CSR : Stm [csr ∶ ty_csridx; p ∶ ty_privilege] ty_bool :=
    let: tmp1 := call is_CSR_defined csr p in
    let: tmp2 := call csrAccess csr in
    let: tmp3 := call csrPriv csr in
    let: tmp := call check_CSR_access tmp2 tmp3 p in
    tmp1 && tmp.

  Definition fun_is_CSR_defined : Stm [csr ∶ ty_csridx; p ∶ ty_privilege] ty_bool :=
    match: csr in csridx with
    | MStatus => match: p in privilege with
                 | Machine => stm_val ty_bool true
                 | _ => stm_val ty_bool false
                 end
    | MTvec => match: p in privilege with
                 | Machine => stm_val ty_bool true
                 | _ => stm_val ty_bool false
                 end
    | MCause => match: p in privilege with
                 | Machine => stm_val ty_bool true
                 | _ => stm_val ty_bool false
                 end
    | MEpc => match: p in privilege with
                 | Machine => stm_val ty_bool true
                 | _ => stm_val ty_bool false
                 end
    end.

  (* NOTE: - normally this information is part of the CSR bitpattern,
             we are reusing our existing access_type
           - all CSRs we currently support are MRW (= Machine, ReadWrite) *)
  Definition fun_csrAccess : Stm [csr ∶ ty_csridx] ty_access_type :=
    ReadWrite.
  Definition fun_csrPriv : Stm [csr ∶ ty_csridx] ty_privilege :=
    stm_val ty_privilege Machine.

  Definition fun_check_CSR_access : Stm [csrrw ∶ ty_access_type; csrpr ∶ ty_privilege; p ∶ ty_privilege] ty_bool :=
    let: tmp1 := call privLevel_to_bits csrpr in
    let: tmp2 := call privLevel_to_bits p in
    tmp1 <= tmp2.

  Definition fun_privLevel_to_bits : Stm [p ∶ ty_privilege] ty_xlenbits :=
    match: p in privilege with
    | Machine => stm_val ty_int 3%Z
    | User => stm_val ty_int 0%Z
    end.

  (* NOTE: not part of Sail model, added these to make readCSR/writeCSR easier to implement *)
  Definition fun_mstatus_to_bits : Stm [value ∶ ty_mstatus] ty_xlenbits :=
    match: value in rmstatus with [MPP] => call privLevel_to_bits MPP end.

  Definition fun_mstatus_from_bits : Stm [value ∶ ty_xlenbits] ty_mstatus :=
    let: p := if: value = z_exp 0
              then stm_val ty_privilege User
              else if: value = z_exp 3
                   then stm_val ty_privilege Machine
                   else stm_val ty_privilege User in
    exp_record rmstatus [ p ].

  Definition fun_readCSR : Stm [csr ∶ ty_csridx] ty_xlenbits :=
    match: csr in csridx with
    | MStatus => let: tmp := stm_read_register mstatus in
                 call mstatus_to_bits tmp
    | MTvec =>   stm_read_register mtvec
    | MCause =>  stm_read_register mcause
    | MEpc =>    stm_read_register mepc
    end.

  Definition fun_writeCSR : Stm [csr ∶ ty_csridx; value ∶ ty_xlenbits] ty_unit :=
    match: csr in csridx with
    | MStatus => let: tmp := call mstatus_from_bits value in
                 stm_write_register mstatus tmp ;;
                 stm_val ty_unit tt
    | MTvec =>   stm_write_register mtvec value ;;
                 stm_val ty_unit tt
    | MCause =>  stm_write_register mcause value ;;
                 stm_val ty_unit tt
    | MEpc =>    stm_write_register mepc value ;;
                 stm_val ty_unit tt
    end.

  (* NOTE: normally the definitions of execute_X are inlined and defined as
           function clauses of execute (a scattered definition) *)
  Definition fun_execute : Stm ["ast" ∶ ty_ast] ty_retired :=
    match: exp_var "ast" in union ast with
    |> KRTYPE (pat_tuple (rs2 , rs1 , rd , op)) => call execute_RTYPE rs2 rs1 rd op
    |> KITYPE (pat_tuple (imm , rs1 , rd , op)) => call execute_ITYPE imm rs1 rd op
    |> KUTYPE (pat_tuple (imm , rd , op))       => call execute_UTYPE imm rd op
    |> KBTYPE (pat_tuple (imm , rs2, rs1 , op)) => call execute_BTYPE imm rs2 rs1 op
    |> KRISCV_JAL (pat_tuple (imm , rd))        => call execute_RISCV_JAL imm rd
    |> KRISCV_JALR (pat_tuple (imm , rs1 , rd)) => call execute_RISCV_JALR imm rs1 rd
    |> KLOAD (pat_tuple (imm , rs1, rd))        => call execute_LOAD imm rs1 rd
    |> KSTORE (pat_tuple (imm , rs2 , rs1))     => call execute_STORE imm rs2 rs1
    |> KECALL pat_unit                          => call execute_ECALL
    |> KMRET pat_unit                           => call execute_MRET
    |> KCSR (pat_tuple (csr , rs1 , rd , op))   => call execute_CSR csr rs1 rd op
    end.

  Definition fun_execute_RTYPE : Stm [rs2 ∶ ty_regno; rs1 ∶ ty_regno; rd ∶ ty_regno; op ∶ ty_rop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: rs2_val := call rX rs2 in
    let: result :=
       match: op in rop with
       | RISCV_ADD => rs1_val + rs2_val
       | RISCV_SUB => rs1_val - rs2_val
       end in
     call wX rd result ;;
     stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_ITYPE : Stm [imm ∶ ty_int; rs1 ∶ ty_regno; rd ∶ ty_regno; op ∶ ty_iop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: immext := imm in
    let: result :=
       match: op in iop with
       | RISCV_ADDI => rs1_val + immext
       end in
     call wX rd result ;;
     stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_UTYPE : Stm [imm ∶ ty_int; rd ∶ ty_regno; op ∶ ty_uop] ty_retired :=
    let: off := imm in
    let: ret :=
       match: op in uop with
       | RISCV_LUI   => off
       | RISCV_AUIPC =>
         let: tmp := call get_arch_pc in
         tmp + off
       end in
    call wX rd ret ;;
    stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_RISCV_JAL : Stm [imm ∶ ty_int; rd ∶ ty_regno] ty_retired :=
    let: tmp := stm_read_register pc in
    let: t := tmp + imm in
    let: tmp := call get_next_pc in
    call wX rd tmp ;;
    call set_next_pc t ;;
    stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_RISCV_JALR : Stm [imm ∶ ty_int ; rs1 ∶ ty_regno; rd ∶ ty_regno] ty_retired :=
    let: tmp := call rX rs1 in
    let: t := tmp + imm in
    let: tmp := call get_next_pc in
    call wX rd tmp ;;
    call set_next_pc t ;;
    stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_BTYPE : Stm [imm ∶ ty_int; rs2 ∶ ty_regno; rs1 ∶ ty_regno; op ∶ ty_bop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: rs2_val := call rX rs2 in
    let: taken :=
       match: op in bop with
       | RISCV_BEQ  => rs1_val = rs2_val
       | RISCV_BNE  => exp_not (rs1_val = rs2_val)
       | RISCV_BLT  => rs1_val < rs2_val
       | RISCV_BGE  => rs2_val <= rs1_val
       | RISCV_BLTU =>
         let: tmp1 := call abs rs1_val in
         let: tmp2 := call abs rs2_val in
         tmp1 < tmp2
       | RISCV_BGEU =>
         let: tmp1 := call abs rs1_val in
         let: tmp2 := call abs rs2_val in
         tmp2 <= tmp1
       end in
    let: tmp := stm_read_register pc in
    let: t := tmp + imm in
    if: taken
    then
      call set_next_pc t ;;
      stm_val ty_retired RETIRE_SUCCESS
    else
      stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_LOAD : Stm [imm ∶ ty_int; rs1 ∶ ty_regno; rd ∶ ty_regno] ty_retired :=
    let: offset := imm in
    let: tmp := call rX rs1 in
    let: paddr := tmp + offset in
    let: tmp := call mem_read Read paddr in
    call process_load rd paddr tmp ;;
    stm_val ty_retired RETIRE_SUCCESS.

  Definition fun_execute_STORE : Stm [imm ∶ ty_int; rs2 ∶ ty_regno; rs1 ∶ ty_regno] ty_retired :=
    let: offset := imm in
    let: tmp := call rX rs1 in
    let: paddr := tmp + offset in
    let: rs2_val := call rX rs2 in
    let: res := call mem_write_value paddr rs2_val in
    match: res in union memory_op_result with
    |> KMemValue (pat_var "v") => if: v = z_exp 1
                                  then stm_val ty_retired RETIRE_SUCCESS
                                  else fail "store got false from write_mem_value"
    |> KMemException (pat_var "e") => call handle_mem_exception paddr e ;;
                                      stm_val ty_retired RETIRE_FAIL
    end.

  Definition fun_execute_ECALL : Stm ctx.nil ty_retired :=
    let: tmp1 := stm_read_register cur_privilege in
    let: t := match: tmp1 in privilege with
              | Machine => E_M_EnvCall
              | User    => E_U_EnvCall
              end in
    let: tmp2 := stm_read_register pc in
    let: tmp3 := call exception_handler tmp1 (CTL_TRAP t) tmp2 in
    call set_next_pc tmp3 ;;
    stm_val ty_retired RETIRE_FAIL.

  Definition fun_execute_MRET : Stm ctx.nil ty_retired :=
    let: tmp1 := stm_read_register cur_privilege in
    match: tmp1 in privilege with
    | Machine =>
      let: tmp2 := stm_read_register pc in
      let: tmp3 := call exception_handler tmp1 CTL_MRET tmp2 in
      call set_next_pc tmp3 ;;
      stm_val ty_retired RETIRE_SUCCESS
    | User    =>
      call handle_illegal ;;
      stm_val ty_retired RETIRE_FAIL
    end.

  Definition fun_execute_CSR : Stm [csr ∶ ty_csridx; rs1 ∶ ty_regno; rd ∶ ty_regno; op ∶ ty_csrop] ty_retired :=
    let: rs1_val := call rX rs1 in
    let: tmp1 := stm_read_register cur_privilege in
    let: tmp2 := call check_CSR csr tmp1 in
    if: tmp2 (* then and else branch switched, Sail model uses a not here *)
    then
      (let: csr_val := call readCSR csr in
       call writeCSR csr rs1_val ;;
       call wX rd csr_val ;;
       stm_val ty_retired RETIRE_SUCCESS)
    else (call handle_illegal ;;
          stm_val ty_retired RETIRE_FAIL).

  End FunDefKit.

  Include DefaultRegStoreKit RiscvPmpBase.

  Section ForeignKit.
  (* Memory *)
  Definition Memory := Addr -> Word.

  Definition fun_read_ram (μ : Memory) (addr : Val ty_int) : Val ty_word :=
    μ addr.

  Definition fun_write_ram (μ : Memory) (addr : Val ty_int) (data : Val ty_word) : Memory :=
    fun addr' => if Z.eqb addr addr' then data else μ addr'.

  #[derive(equations=no)]
  Equations ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop :=
    ForeignCall read_ram (env.snoc env.nil _ addr) res γ γ' μ μ' :=
      (γ' , μ' , res) = (γ , μ , inr (fun_read_ram μ addr));
    ForeignCall write_ram (env.snoc (env.snoc env.nil _ addr) _ data) res γ γ' μ μ' :=
      (γ' , μ' , res) = (γ , fun_write_ram μ addr data , inr 1%Z);
    ForeignCall decode (env.snoc env.nil _ code) res γ γ' μ μ' :=
        (γ' , μ' , res) = (γ , μ , pure_decode code).

  Import bv.notations.
  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Proof.
    destruct f; cbn.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args.
      exists γ, μ. eexists. reflexivity.
  Qed.
  End ForeignKit.

  Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f with
    | rX                    => fun_rX
    | wX                    => fun_wX
    | get_arch_pc           => fun_get_arch_pc
    | get_next_pc           => fun_get_next_pc
    | set_next_pc           => fun_set_next_pc
    | tick_pc               => fun_tick_pc
    | abs                   => fun_abs
    | mem_read              => fun_mem_read
    | mem_write_value       => fun_mem_write_value
    | checked_mem_read      => fun_checked_mem_read
    | checked_mem_write     => fun_checked_mem_write
    | pmp_mem_read          => fun_pmp_mem_read
    | pmp_mem_write         => fun_pmp_mem_write
    | pmpLocked             => fun_pmpLocked
    | pmpCheck              => fun_pmpCheck
    | pmpCheckPerms         => fun_pmpCheckPerms
    | pmpCheckRWX           => fun_pmpCheckRWX
    | pmpMatchEntry         => fun_pmpMatchEntry
    | pmpAddrRange          => fun_pmpAddrRange
    | pmpMatchAddr          => fun_pmpMatchAddr
    | process_load          => fun_process_load
    | exceptionType_to_bits => fun_exceptionType_to_bits
    | privLevel_to_bits     => fun_privLevel_to_bits
    | mstatus_to_bits       => fun_mstatus_to_bits
    | mstatus_from_bits     => fun_mstatus_from_bits
    | main                  => fun_main
    | init_model            => fun_init_model
    | init_sys              => fun_init_sys
    | init_pmp              => fun_init_pmp
    | loop                  => fun_loop
    | step                  => fun_step
    | fetch                 => fun_fetch
    | handle_mem_exception  => fun_handle_mem_exception
    | exception_handler     => fun_exception_handler
    | exception_delegatee   => fun_exception_delegatee
    | trap_handler          => fun_trap_handler
    | prepare_trap_vector   => fun_prepare_trap_vector
    | tvec_addr             => fun_tvec_addr
    | handle_illegal        => fun_handle_illegal
    | check_CSR             => fun_check_CSR
    | is_CSR_defined        => fun_is_CSR_defined
    | csrAccess             => fun_csrAccess
    | csrPriv               => fun_csrPriv
    | check_CSR_access      => fun_check_CSR_access
    | readCSR               => fun_readCSR
    | writeCSR              => fun_writeCSR
    | execute               => fun_execute
    | execute_RTYPE         => fun_execute_RTYPE
    | execute_ITYPE         => fun_execute_ITYPE
    | execute_UTYPE         => fun_execute_UTYPE
    | execute_BTYPE         => fun_execute_BTYPE
    | execute_RISCV_JAL     => fun_execute_RISCV_JAL
    | execute_RISCV_JALR    => fun_execute_RISCV_JALR
    | execute_LOAD          => fun_execute_LOAD
    | execute_STORE         => fun_execute_STORE
    | execute_ECALL         => fun_execute_ECALL
    | execute_MRET          => fun_execute_MRET
    | execute_CSR           => fun_execute_CSR
    end.

  Include ProgramMixin RiscvPmpBase.

End RiscvPmpProgram.
