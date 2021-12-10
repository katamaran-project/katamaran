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
     Syntax.
From RiscvPmp Require Export
     Values.

From stdpp Require Import decidable finite.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
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
End RiscvNotations.

Module RiscvPmpTermKit <: TermKit.
  Module valuekit := RiscvPmpValueKit.
  Module Export VAL := Syntax.Values.Values valuekit.

  Import RiscvNotations.

  (** Variables **)
  Definition 𝑿        := string.
  Definition 𝑿_eq_dec := string_dec.
  Definition 𝑺        := string.
  Definition 𝑺_eq_dec := string_dec.

  Notation PCtx := (NCtx 𝑿 Ty).
  Notation LCtx := (NCtx 𝑺 Ty).

  Definition 𝑿to𝑺 (x : 𝑿) : 𝑺 := x.
  Definition fresh := Context.fresh (T := Ty).

  (** Functions **)
  Inductive Fun : PCtx -> Ty -> Set :=
  | rX                    : Fun [rs ∶ ty_regidx] ty_xlenbits
  | wX                    : Fun [rd ∶ ty_regidx, v ∶ ty_xlenbits] ty_unit
  | get_arch_pc           : Fun ctx_nil ty_xlenbits
  | get_next_pc           : Fun ctx_nil ty_xlenbits
  | set_next_pc           : Fun [addr ∶ ty_xlenbits] ty_unit
  | tick_pc               : Fun ctx_nil ty_unit
  | abs                   : Fun [v ∶ ty_int] ty_int
  | mem_read              : Fun [typ ∶ ty_access_type, paddr ∶ ty_xlenbits] ty_memory_op_result
  | checked_mem_read      : Fun [t ∶ ty_access_type, paddr ∶ ty_xlenbits] ty_memory_op_result
  | checked_mem_write     : Fun [paddr ∶ ty_xlenbits, data ∶ ty_int] ty_memory_op_result
  | pmp_mem_read          : Fun [t∶ ty_access_type, p ∶ ty_privilege, paddr ∶ ty_xlenbits] ty_memory_op_result
  | pmp_mem_write         : Fun [paddr ∶ ty_xlenbits, data ∶ ty_int, typ ∶ ty_access_type, priv ∶ ty_privilege] ty_memory_op_result
  | pmpLocked             : Fun [cfg ∶ ty_pmpcfg_ent] ty_bool
  | pmpCheck              : Fun [addr ∶ ty_xlenbits, acc ∶ ty_access_type, priv ∶ ty_privilege] (ty_option ty_exception_type)
  | pmpCheckPerms         : Fun [ent ∶ ty_pmpcfg_ent, acc ∶ ty_access_type, priv ∶ ty_privilege] ty_bool
  | pmpCheckRWX           : Fun [ent ∶ ty_pmpcfg_ent, acc ∶ ty_access_type] ty_bool
  | pmpMatchEntry         : Fun [addr ∶ ty_xlenbits, acc ∶ ty_access_type, priv ∶ ty_privilege, ent ∶ ty_pmpcfg_ent, pmpaddr ∶ ty_xlenbits, prev_pmpaddr ∶ ty_xlenbits] ty_pmpmatch
  | pmpAddrRange          : Fun [cfg ∶ ty_pmpcfg_ent, pmpaddr ∶ ty_xlenbits, prev_pmpaddr ∶ ty_xlenbits] ty_pmp_addr_range
  | pmpMatchAddr          : Fun [addr ∶ ty_xlenbits, rng ∶ ty_pmp_addr_range] ty_pmpaddrmatch
  | process_load          : Fun [rd ∶ ty_regidx, vaddr ∶ ty_xlenbits, value ∶ ty_memory_op_result] ty_retired
  | mem_write_value       : Fun [paddr ∶ ty_xlenbits, value ∶ ty_int] ty_memory_op_result
  | main                  : Fun ctx_nil ty_unit
  | init_model            : Fun ctx_nil ty_unit
  | loop                  : Fun ctx_nil ty_unit
  | step                  : Fun ctx_nil ty_unit
  | fetch                 : Fun ctx_nil ty_fetch_result
  | init_sys              : Fun ctx_nil ty_unit
  | init_pmp              : Fun ctx_nil ty_unit
  | exceptionType_to_bits : Fun [e ∶ ty_exception_type] ty_exc_code
  | handle_mem_exception  : Fun [addr ∶ ty_xlenbits, e ∶ ty_exception_type] ty_unit
  | exception_handler     : Fun [cur_priv ∶ ty_privilege, ctl ∶ ty_ctl_result, "pc" ∶ ty_xlenbits] ty_int
  | exception_delegatee   : Fun [p ∶ ty_privilege] ty_privilege
  | trap_handler          : Fun [del_priv ∶ ty_privilege, c ∶ ty_exc_code, "pc" ∶ ty_xlenbits] ty_xlenbits
  | prepare_trap_vector   : Fun [p ∶ ty_privilege, cause ∶ ty_mcause] ty_xlenbits
  | tvec_addr             : Fun [m ∶ ty_int, c ∶ ty_mcause] (ty_option ty_xlenbits)
  | handle_illegal        : Fun ctx_nil ty_unit
  | execute               : Fun ["ast" ∶ ty_ast] ty_retired
  | execute_RTYPE         : Fun [rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_rop] ty_retired
  | execute_ITYPE         : Fun [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_iop] ty_retired
  | execute_UTYPE         : Fun [imm ∶ ty_int, rd ∶ ty_regidx, op ∶ ty_uop] ty_retired
  | execute_BTYPE         : Fun [imm ∶ ty_int, rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, op ∶ ty_bop] ty_retired
  | execute_RISCV_JAL     : Fun [imm ∶ ty_int, rd ∶ ty_regidx] ty_retired
  | execute_RISCV_JALR    : Fun [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx] ty_retired
  | execute_LOAD          : Fun [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx] ty_retired
  | execute_STORE         : Fun [imm ∶ ty_int, rs2 ∶ ty_regidx, rs1 ∶ ty_regidx] ty_retired
  | execute_ECALL         : Fun ctx_nil ty_retired
  | execute_MRET          : Fun ctx_nil ty_retired
  .

  Inductive FunX : PCtx -> Ty -> Set :=
  | read_ram  : FunX [paddr ∶ ty_int] ty_word
  | write_ram : FunX [paddr ∶ ty_int, data ∶ ty_word] ty_word
  | decode    : FunX [bv ∶ ty_int] ty_ast
  .

  Inductive Lem : PCtx -> Set :=
  | open_ptsreg               : Lem [rs ∶ ty_regidx]
  | close_ptsreg (r : RegIdx) : Lem ctx_nil
  .

  Definition 𝑭  : PCtx -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : PCtx -> Ty -> Set := FunX.
  Definition 𝑳  : PCtx -> Set := Lem.

  Inductive Reg : Ty -> Set :=
  | pc            : Reg ty_xlenbits
  | nextpc        : Reg ty_xlenbits
  | mstatus       : Reg ty_mstatus
  | mtvec         : Reg ty_xlenbits
  | mcause        : Reg ty_exc_code
  | mepc          : Reg ty_xlenbits
  | cur_privilege : Reg ty_privilege
  | x0            : Reg ty_xlenbits
  | x1            : Reg ty_xlenbits
  | x2            : Reg ty_xlenbits
  | pmp0cfg       : Reg ty_pmpcfg_ent
  | pmpaddr0      : Reg ty_xlenbits
  .

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
        | right; intros e1; dependent elimination e1
        ].
  Defined.

  Instance 𝑹𝑬𝑮_eq_decision : EqDecision (sigT Reg).
  Proof.
    intros xy; eapply 𝑹𝑬𝑮_eq_dec.
  Defined.

  Program Instance 𝑹𝑬𝑮_finite : Finite (sigT Reg) := {| enum := [ existT _ pc; existT _ nextpc; existT _ mstatus; existT _ mtvec; existT _ mcause; existT _ mepc; existT _ cur_privilege; existT _ x0; existT _ x1; existT _ x2; existT _ pmp0cfg; existT _ pmpaddr0 ]%list |}.
  Next Obligation.
    now eapply (nodup_fixed (H := 𝑹𝑬𝑮_eq_dec)).
  Defined.
  Next Obligation.
    intros x.
    refine (@bool_decide_unpack _ (elem_of_list_dec _ _) _).
    destruct x; now destruct r.
  Qed.

End RiscvPmpTermKit.

Module RiscvPmpProgramKit <: (ProgramKit RiscvPmpTermKit).
  Module Export TM := Terms RiscvPmpTermKit.
  Import NameResolution.

  Module RiscvμSailNotations.
    Notation "'rs'"           := (@exp_var _ "rs" _ _) : exp_scope.
    Notation "'rs1'"          := (@exp_var _ "rs1" _ _) : exp_scope.
    Notation "'rs1_val'"      := (@exp_var _ "rs1_val" _ _) : exp_scope.
    Notation "'rs2'"          := (@exp_var _ "rs2" _ _) : exp_scope.
    Notation "'rs2_val'"      := (@exp_var _ "rs2_val" _ _) : exp_scope.
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

    Notation "'Read'" := (exp_union access_type KRead (exp_lit ty_unit tt)) : exp_scope.
    Notation "'Write'" := (exp_union access_type KWrite (exp_lit ty_unit tt)) : exp_scope.
    Notation "'ReadWrite'" := (exp_union access_type KReadWrite (exp_lit ty_unit tt)) : exp_scope.
    Notation "'Execute'" := (exp_union access_type KExecute (exp_lit ty_unit tt)) : exp_scope.

    Notation "'E_Fetch_Access_Fault'" := (exp_union exception_type KE_Fetch_Access_Fault (exp_lit ty_unit tt)) : exp_scope.
    Notation "'E_Load_Access_Fault'" := (exp_union exception_type KE_Load_Access_Fault (exp_lit ty_unit tt)) : exp_scope.
    Notation "'E_SAMO_Access_Fault'" := (exp_union exception_type KE_SAMO_Access_Fault (exp_lit ty_unit tt)) : exp_scope.
    Notation "'E_U_EnvCall'" := (exp_union exception_type KE_U_EnvCall (exp_lit ty_unit tt)) : exp_scope.
    Notation "'E_M_EnvCall'" := (exp_union exception_type KE_M_EnvCall (exp_lit ty_unit tt)) : exp_scope.
    Notation "'E_Illegal_Instr'" := (exp_union exception_type KE_Illegal_Instr (exp_lit ty_unit tt)) : exp_scope.

    Notation "'None'" := (exp_inr (exp_lit ty_unit tt)) : exp_scope.
    Notation "'Some' va" := (exp_inl va) (at level 10, va at next level) : exp_scope.

    Notation "'MemValue' memv" := (exp_union memory_op_result KMemValue memv) (at level 10, memv at next level) : exp_scope.
    Notation "'MemException' meme" := (exp_union memory_op_result KMemException meme) (at level 10, meme at next level) : exp_scope.

    Notation "'F_Base' memv" := (exp_union fetch_result KF_Base memv) (at level 10, memv at next level) : exp_scope.
    Notation "'F_Error' meme memv" := (exp_union fetch_result KF_Error (exp_binop binop_pair meme memv)) (at level 10, meme at next level, memv at next level) : exp_scope.

    Notation "'CTL_TRAP' exc" := (exp_union ctl_result KCTL_TRAP exc) (at level 10, exc at next level) : exp_scope.
    Notation "'CTL_MRET'" := (exp_union ctl_result KCTL_MRET (exp_lit ty_unit tt)) : exp_scope.
  End RiscvμSailNotations.

  Section Functions.
  Import RiscvNotations.
  Import RiscvμSailNotations.
  Local Coercion stm_exp : Exp >-> Stm.


  Notation "'use' 'lemma' lem args" := (stm_lemma lem args%arg) (at level 10, lem at next level) : exp_scope.
  Notation "'use' 'lemma' lem" := (stm_lemma lem env_nil) (at level 10, lem at next level) : exp_scope.

  (** Functions **)
  Definition fun_rX : Stm [rs ∶ ty_regidx] ty_xlenbits :=
    match: rs in regidx with
    | X0 => exp_lit ty_xlenbits 0%Z
    | X1 => use lemma open_ptsreg [exp_var rs]%arg ;;
            let: v := stm_read_register x1 in
            use lemma (close_ptsreg X1) ;;
            stm_exp v
    | X2 => use lemma open_ptsreg [exp_var rs]%arg ;;
            let: v := stm_read_register x2 in
            use lemma (close_ptsreg X2) ;;
            stm_exp v
    end.

  Definition fun_wX : Stm [rd ∶ ty_regidx, v ∶ ty_xlenbits] ty_unit :=
    match: rd in regidx with
    | X0 => stm_lit ty_unit tt
    | X1 => use lemma open_ptsreg [exp_var rd] ;;
            stm_write_register x1 v ;;
            use lemma (close_ptsreg X1) ;;
            stm_lit ty_unit tt
    | X2 => use lemma open_ptsreg [exp_var rd] ;;
            stm_write_register x2 v ;;
            use lemma (close_ptsreg X2) ;;
            stm_lit ty_unit tt
    end.

  Definition fun_get_arch_pc : Stm ctx_nil ty_xlenbits :=
    stm_read_register pc.

  Definition fun_get_next_pc : Stm ctx_nil ty_xlenbits :=
    stm_read_register nextpc.

  Definition fun_set_next_pc : Stm [addr ∶ ty_xlenbits] ty_unit :=
    stm_write_register nextpc addr ;;
    stm_lit ty_unit tt.

  Definition fun_tick_pc : Stm ctx_nil ty_unit :=
    let: tmp := stm_read_register nextpc in
    stm_write_register pc tmp ;;
    stm_lit ty_unit tt.

  Definition fun_abs : Stm [v ∶ ty_int] ty_int :=
    if: v < (exp_lit ty_int 0%Z)
    then v * (exp_lit ty_int (-1)%Z)
    else v.

  Definition fun_mem_read : Stm [typ ∶ ty_access_type, paddr ∶ ty_xlenbits] ty_memory_op_result :=
    let: tmp := stm_read_register cur_privilege in
    call pmp_mem_read typ tmp paddr.

  Definition fun_checked_mem_read : Stm [t ∶ ty_access_type, paddr ∶ ty_xlenbits] ty_memory_op_result :=
    let: tmp := foreign read_ram paddr in
    MemValue tmp.

  Definition fun_checked_mem_write : Stm [paddr ∶ ty_xlenbits, data ∶ ty_int] ty_memory_op_result :=
    let: tmp := foreign write_ram paddr data in
    MemValue tmp.

  Definition fun_pmp_mem_read : Stm [t∶ ty_access_type, p ∶ ty_privilege, paddr ∶ ty_xlenbits] ty_memory_op_result :=
    let: tmp := call pmpCheck paddr t p in
    match: tmp with
    | inl e => MemException e
    | inr v => call checked_mem_read t paddr
    end.

  Definition fun_pmp_mem_write : Stm [paddr ∶ ty_xlenbits, data ∶ ty_int, typ ∶ ty_access_type, priv ∶ ty_privilege] ty_memory_op_result :=
    let: tmp := call pmpCheck paddr typ priv in
    match: tmp with
    | inl e => MemException e
    | inr v => call checked_mem_write paddr data
    end.

  Definition fun_pmpLocked : Stm [cfg ∶ ty_pmpcfg_ent] ty_bool :=
    (stm_match_record rpmpcfg_ent cfg
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
       "L" L)
       "A" A)
       "X" X)
       "W" W)
       "R" R)
      L).

  Definition fun_pmpCheck : Stm [addr ∶ ty_xlenbits, acc ∶ ty_access_type, priv ∶ ty_privilege] (ty_option ty_exception_type) :=
    let: tmp1 := stm_read_register pmp0cfg in
    let: tmp2 := stm_read_register pmpaddr0 in
    let: tmp3 := call pmpMatchEntry addr acc priv tmp1 tmp2 (exp_lit ty_int 0%Z) in
    let: check%string := match: tmp3 in pmpmatch with
                  | PMP_Success  => stm_lit ty_bool true
                  | PMP_Fail     => stm_lit ty_bool false
                  | PMP_Continue => match: priv in privilege with
                                    | Machine => stm_lit ty_bool true
                                    | User    => stm_lit ty_bool false
                                    end
                  end in
           if: check
           then None
           else
             stm_match_union_alt access_type acc
                                 (fun K =>
                                    match K with
                                    | KRead      => MkAlt pat_unit
                                                     (Some E_Load_Access_Fault)
                                    | KWrite     => MkAlt pat_unit
                                                     (Some E_SAMO_Access_Fault)
                                    | KReadWrite => MkAlt pat_unit
                                                     (Some E_SAMO_Access_Fault)
                                    | KExecute   => MkAlt pat_unit
                                                     (Some E_Fetch_Access_Fault)
                                    end).

  Definition fun_pmpCheckPerms : Stm [ent ∶ ty_pmpcfg_ent, acc ∶ ty_access_type, priv ∶ ty_privilege] ty_bool :=
    match: priv in privilege with
    | Machine =>
      let: tmp := call pmpLocked ent in
      if: tmp
      then call pmpCheckRWX ent acc
      else stm_lit ty_bool true
    | User =>
      call pmpCheckRWX ent acc
    end.

  Definition fun_pmpCheckRWX : Stm [ent ∶ ty_pmpcfg_ent, acc ∶ ty_access_type] ty_bool :=
    (stm_match_record rpmpcfg_ent ent
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
       "L" L)
       "A" A)
       "X" X)
       "W" W)
       "R" R)
      (stm_match_union_alt access_type acc
                           (fun K =>
                              match K with
                              | KRead      => MkAlt pat_unit
                                                    R
                              | KWrite     => MkAlt pat_unit
                                                    W
                              | KReadWrite => MkAlt pat_unit
                                                    (R && W)
                              | KExecute   => MkAlt pat_unit
                                                    X
                              end))).

  Definition fun_pmpMatchEntry : Stm [addr ∶ ty_xlenbits, acc ∶ ty_access_type, priv ∶ ty_privilege, ent ∶ ty_pmpcfg_ent, pmpaddr ∶ ty_xlenbits, prev_pmpaddr ∶ ty_xlenbits] ty_pmpmatch :=
    let: rng := call pmpAddrRange ent pmpaddr prev_pmpaddr in
    let: tmp := call pmpMatchAddr addr rng in
    match: tmp in pmpaddrmatch with
    | PMP_NoMatch      => exp_lit ty_pmpmatch PMP_Continue
    | PMP_PartialMatch => exp_lit ty_pmpmatch PMP_Fail
    | PMP_Match        =>
      let: tmp := call pmpCheckPerms ent acc priv in
      if: tmp
      then exp_lit ty_pmpmatch PMP_Success
      else exp_lit ty_pmpmatch PMP_Fail
    end.

  Definition fun_pmpAddrRange : Stm [cfg ∶ ty_pmpcfg_ent, pmpaddr ∶ ty_xlenbits, prev_pmpaddr ∶ ty_xlenbits] ty_pmp_addr_range :=
    (stm_match_record rpmpcfg_ent cfg
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
       "L" L)
       "A" A)
       "X" X)
       "W" W)
       "R" R)
      (match: A in pmpaddrmatchtype with
       | OFF => None
       | TOR => Some (exp_binop binop_pair prev_pmpaddr pmpaddr)
       end)).

  Definition fun_pmpMatchAddr : Stm [addr ∶ ty_int, rng ∶ ty_pmp_addr_range] ty_pmpaddrmatch :=
    match: rng with
    | inl v =>
      match: v in (ty_int , ty_int) with
      | (lo , hi) =>
        if: hi < lo
        then exp_lit ty_pmpaddrmatch PMP_NoMatch
        else
          if: (addr < lo) || (hi < addr)
          then exp_lit ty_pmpaddrmatch PMP_NoMatch
          else if: (lo <= addr) && (addr <= hi)
               then exp_lit ty_pmpaddrmatch PMP_Match
               else exp_lit ty_pmpaddrmatch PMP_PartialMatch
      end
    | inr v => exp_lit ty_pmpaddrmatch PMP_NoMatch
    end.

  Definition fun_process_load : Stm [rd ∶ ty_regidx, vaddr ∶ ty_xlenbits, value ∶ ty_memory_op_result] ty_retired :=
    stm_match_union_alt memory_op_result value
                        (fun K =>
                           match K with
                           | KMemValue     => MkAlt (pat_var result)
                                                    (call wX rd result ;;
                                                     stm_lit ty_retired RETIRE_SUCCESS)
                           | KMemException => MkAlt (pat_var e)
                                                    (call handle_mem_exception vaddr e ;;
                                                     stm_lit ty_retired RETIRE_FAIL)
                           end).

  Definition fun_mem_write_value : Stm [paddr ∶ ty_xlenbits, value ∶ ty_int] ty_memory_op_result :=
    let: tmp := stm_read_register cur_privilege in
    call pmp_mem_write paddr value Write tmp.

  Definition fun_main : Stm ctx_nil ty_unit :=
    call init_model ;;
    call loop.

  (* NOTE: simplified init_model function, just calls init_sys which just calls
           init_pmp *)
  Definition fun_init_model : Stm ctx_nil ty_unit :=
    call init_sys.

  Definition fun_loop : Stm ctx_nil ty_unit :=
    call step.

  Definition fun_fetch : Stm ctx_nil ty_fetch_result :=
    let: tmp1 := stm_read_register pc in
    let: tmp2 := call mem_read Execute tmp1 in
    stm_match_union_alt memory_op_result tmp2
                        (fun K =>
                           match K with
                           | KMemValue     => MkAlt (pat_var result%string)
                                                    (F_Base result)
                           | KMemException => MkAlt (pat_var e%string)
                                                    (F_Error e tmp1)
                           end).

  Definition fun_step : Stm ctx_nil ty_unit :=
    let: f := call fetch in
    stm_match_union_alt fetch_result f
                        (fun K =>
                           match K with
                           | KF_Base  => MkAlt (pat_var w%string)
                                               (let: "ast" := foreign decode w in
                                                let: tmp := stm_read_register pc in
                                                stm_write_register nextpc (tmp + (exp_lit ty_int 4%Z)) ;;
                                                call execute (exp_var "ast"))
                           | KF_Error => MkAlt (pat_pair e%string addr%string)
                                               (call handle_mem_exception addr e ;;
                                                stm_lit ty_retired RETIRE_FAIL)
                           end) ;;
    call tick_pc.

  Definition fun_init_sys : Stm ctx_nil ty_unit :=
    call init_pmp.

  Definition fun_init_pmp : Stm ctx_nil ty_unit :=
    let: tmp := stm_read_register pmp0cfg in
    (stm_match_record rpmpcfg_ent tmp
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
       "L" L%string)
       "A" A%string)
       "X" X%string)
       "W" W%string)
       "R" R%string)
      (stm_write_register pmp0cfg (exp_record rpmpcfg_ent
                                             [ L,
                                               exp_lit ty_pmpaddrmatchtype OFF,
                                               X,
                                               W,
                                               R ]) ;;
       stm_lit ty_unit tt)).

  Definition fun_exceptionType_to_bits : Stm [e ∶ ty_exception_type] ty_exc_code :=
    stm_match_union_alt exception_type e
                        (fun K =>
                           match K with
                           | KE_Fetch_Access_Fault => MkAlt pat_unit
                                                            (stm_lit ty_exc_code 1%Z)
                           | KE_Illegal_Instr      => MkAlt pat_unit
                                                            (stm_lit ty_exc_code 2%Z)
                           | KE_Load_Access_Fault  => MkAlt pat_unit
                                                            (stm_lit ty_exc_code 5%Z)
                           | KE_SAMO_Access_Fault  => MkAlt pat_unit
                                                            (stm_lit ty_exc_code 7%Z)
                           | KE_U_EnvCall          => MkAlt pat_unit
                                                            (stm_lit ty_exc_code 8%Z)
                           | KE_M_EnvCall          => MkAlt pat_unit
                                                            (stm_lit ty_exc_code 11%Z)
                           end).

  Definition fun_handle_mem_exception : Stm [addr ∶ ty_xlenbits, e ∶ ty_exception_type] ty_unit :=
    let: tmp1 := stm_read_register pc in
    let: tmp2 := stm_read_register cur_privilege in
    let: tmp3 := call exception_handler tmp2 (CTL_TRAP e) tmp1 in
    call set_next_pc tmp3.

  Definition fun_exception_handler : Stm [cur_priv ∶ ty_privilege, ctl ∶ ty_ctl_result, "pc" ∶ ty_xlenbits] ty_xlenbits :=
    stm_match_union_alt ctl_result ctl
                        (fun K =>
                           match K with
                           | KCTL_TRAP => MkAlt (pat_var e%string)
                                                (let: del_priv := call exception_delegatee cur_priv in
                                                 let: tmp := call exceptionType_to_bits e in
                                                 call trap_handler del_priv tmp (exp_var "pc"))
                           | KCTL_MRET => MkAlt pat_unit
                                                (* NOTE: normally the return address is computed with:
                                                         prepare_xret_target(Machine) & pc_alignment_mask()
                                                         
                                                         we drop the alignment mask and inline prepare_xret_target,
                                                         which just calls get_xret_target, which returns (for M-mode)
                                                         the value of mepc *)
                                                (let: prev_priv := stm_read_register cur_privilege in
                                                 let: tmp1 := stm_read_register mstatus in
                                                 (stm_match_record rmstatus tmp1
                                                                   (recordpat_snoc recordpat_nil "MPP" MPP%string)
                                                                   (stm_write_register cur_privilege MPP ;;
                                                                    stm_write_register mstatus (exp_record rmstatus [ exp_lit ty_privilege User ]) ;;
                                                                    stm_read_register mepc)))
                           end).

  Definition fun_exception_delegatee : Stm [p ∶ ty_privilege] ty_privilege :=
    stm_lit ty_privilege Machine.

  Definition fun_trap_handler : Stm [del_priv ∶ ty_privilege, c ∶ ty_exc_code, "pc" ∶ ty_xlenbits] ty_xlenbits :=
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

  Definition fun_prepare_trap_vector : Stm [p ∶ ty_privilege, cause ∶ ty_mcause] ty_xlenbits :=
    let: tvec := stm_read_register mtvec in
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

  Definition fun_tvec_addr : Stm [m ∶ ty_xlenbits, c ∶ ty_mcause] (ty_option ty_xlenbits) :=
    Some m.

  Definition fun_handle_illegal : Stm ctx_nil ty_unit :=
    let: t := E_Illegal_Instr in
    let: tmp1 := stm_read_register cur_privilege in
    let: tmp2 := stm_read_register pc in
    let: tmp3 := call exception_handler tmp1 (CTL_TRAP t) tmp2 in
    call set_next_pc tmp3.

  (* NOTE: normally the definitions of execute_X are inlined and defined as
           function clauses of execute (a scattered definition) *)
  Definition fun_execute : Stm ["ast" ∶ ty_ast] ty_retired :=
    stm_match_union_alt ast (exp_var "ast")
                        (fun K =>
                           match K with
                           | KRTYPE      => MkAlt (pat_tuple [rs2 , rs1 , rd , op])
                                                  (call execute_RTYPE rs2 rs1 rd op)
                           | KITYPE      => MkAlt (pat_tuple [imm , rs1 , rd , op])
                                                  (call execute_ITYPE imm rs1 rd op)
                           | KUTYPE      => MkAlt (pat_tuple [imm , rd , op])
                                                  (call execute_UTYPE imm rd op)
                           | KBTYPE      => MkAlt (pat_tuple [imm , rs2, rs1 , op])
                                                  (call execute_BTYPE imm rs2 rs1 op)
                           | KRISCV_JAL  => MkAlt (pat_tuple [imm , rd])
                                                  (call execute_RISCV_JAL imm rd)
                           | KRISCV_JALR => MkAlt (pat_tuple [imm , rs1 , rd])
                                                  (call execute_RISCV_JALR imm rs1 rd)
                           | KLOAD       => MkAlt (pat_tuple [imm , rs1, rd])
                                                  (call execute_LOAD imm rs1 rd)
                           | KSTORE      => MkAlt (pat_tuple [imm , rs2 , rs1])
                                                  (call execute_STORE imm rs2 rs1)
                           | KECALL      => MkAlt pat_unit
                                                  (call execute_ECALL)
                           | KMRET       => MkAlt pat_unit
                                                  (call execute_MRET)
                           end).

  Definition fun_execute_RTYPE : Stm [rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_rop] ty_retired :=
    stm_match_enum regidx rs1 (fun _ => stm_lit ty_unit tt) ;;
    stm_match_enum regidx rs2 (fun _ => stm_lit ty_unit tt) ;;
    let: rs1_val := call rX rs1 in
    let: rs2_val := call rX rs2 in
    let: result :=
       match: op in rop with
       | RISCV_ADD => rs1_val + rs2_val
       | RISCV_SUB => rs1_val - rs2_val
       end in
     stm_match_enum regidx rd (fun _ => stm_lit ty_unit tt) ;;
     call wX rd result ;;
     stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_ITYPE : Stm [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_iop] ty_retired :=
    stm_match_enum regidx rs1 (fun _ => stm_lit ty_unit tt) ;;
    let: rs1_val := call rX rs1 in
    let: immext := imm in
    let: result :=
       match: op in iop with
       | RISCV_ADDI => rs1_val + immext
       end in
     stm_match_enum regidx rd (fun _ => stm_lit ty_unit tt) ;;
     call wX rd result ;;
     stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_UTYPE : Stm [imm ∶ ty_int, rd ∶ ty_regidx, op ∶ ty_uop] ty_retired :=
    let: off := imm in
    let: ret :=
       match: op in uop with
       | RISCV_LUI   => off
       | RISCV_AUIPC =>
         let: tmp := call get_arch_pc in
         tmp + off
       end in
    stm_match_enum regidx rd (fun _ => stm_lit ty_unit tt) ;;
    call wX rd ret ;;
    stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_RISCV_JAL : Stm [imm ∶ ty_int, rd ∶ ty_regidx] ty_retired :=
    let: tmp := stm_read_register pc in
    let: t := tmp + imm in
    let: tmp := call get_next_pc in
    stm_match_enum regidx rd (fun _ => stm_lit ty_unit tt) ;;
    call wX rd tmp ;;
    call set_next_pc t ;;
    stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_RISCV_JALR : Stm [imm ∶ ty_int , rs1 ∶ ty_regidx, rd ∶ ty_regidx] ty_retired :=
    stm_match_enum regidx rs1 (fun _ => stm_lit ty_unit tt) ;;
    let: tmp := call rX rs1 in
    let: t := tmp + imm in
    let: tmp := call get_next_pc in
    stm_match_enum regidx rd (fun _ => stm_lit ty_unit tt) ;;
    call wX rd tmp ;;
    call set_next_pc t ;;
    stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_BTYPE : Stm [imm ∶ ty_int, rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, op ∶ ty_bop] ty_retired :=
    stm_match_enum regidx rs1 (fun _ => stm_lit ty_unit tt) ;;
    stm_match_enum regidx rs2 (fun _ => stm_lit ty_unit tt) ;;
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
      stm_lit ty_retired RETIRE_SUCCESS
    else
      stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_LOAD : Stm [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx] ty_retired :=
    let: offset := imm in
    let: tmp := call rX rs1 in
    let: paddr := tmp + offset in
    let: tmp := call mem_read Read paddr in
    call process_load rd paddr tmp ;;
    stm_lit ty_retired RETIRE_SUCCESS.

  Definition fun_execute_STORE : Stm [imm ∶ ty_int, rs2 ∶ ty_regidx, rs1 ∶ ty_regidx] ty_retired :=
    let: offset := imm in
    let: tmp := call rX rs1 in
    let: paddr := tmp + offset in
    let: rs2_val := call rX rs2 in
    let: res := call mem_write_value paddr rs2_val in
    stm_match_union_alt memory_op_result res
                        (fun K =>
                           match K with
                           | KMemValue => MkAlt (pat_var v%string)
                                                (if: v = (exp_lit ty_int 1%Z)
                                                 then stm_lit ty_retired RETIRE_SUCCESS
                                                 else fail "store got false from write_mem_value")
                           | KMemException => MkAlt (pat_var e%string)
                                                    (call handle_mem_exception paddr e ;;
                                                     stm_lit ty_retired RETIRE_FAIL)
                           end).

  Definition fun_execute_ECALL : Stm ctx_nil ty_retired :=
    let: tmp1 := stm_read_register cur_privilege in
    let: t := match: tmp1 in privilege with
              | Machine => E_M_EnvCall
              | User    => E_U_EnvCall
              end in
    let: tmp2 := stm_read_register pc in
    let: tmp3 := call exception_handler tmp1 (CTL_TRAP t) tmp2 in
    call set_next_pc tmp3 ;;
    stm_lit ty_retired RETIRE_FAIL.

  Definition fun_execute_MRET : Stm ctx_nil ty_retired :=
    let: tmp1 := stm_read_register cur_privilege in
    match: tmp1 in privilege with
    | Machine =>
      let: tmp2 := stm_read_register pc in
      let: tmp3 := call exception_handler tmp1 CTL_MRET tmp2 in
      call set_next_pc tmp3 ;;
      stm_lit ty_retired RETIRE_SUCCESS
    | User    =>
      call handle_illegal ;;
      stm_lit ty_retired RETIRE_FAIL
    end.

  End Functions.

  Definition RegStore := GenericRegStore.
  Definition read_register := generic_read_register.
  Definition write_register := generic_write_register.
  Definition read_write := generic_read_write.
  Definition read_write_distinct := generic_read_write_distinct.
  Definition write_read := generic_write_read.
  Definition write_write := generic_write_write.

  (* Memory *)
  Definition Memory := Addr -> Word.

  Definition fun_read_ram (μ : Memory) (addr : Lit ty_int) : Lit ty_word :=
    μ addr.

  Definition fun_write_ram (μ : Memory) (addr : Lit ty_int) (data : Lit ty_word) : Memory :=
    fun addr' => if Z.eqb addr addr' then data else μ addr'.

  Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) :
    forall (args : NamedEnv Lit σs) (res : string + Lit σ) (γ γ' : RegStore) (μ μ' : Memory), Prop :=
    match f with
    | read_ram  => fun args res γ γ' μ μ' =>
                     let addr := (args ‼ "paddr")%exp in
                     (γ' , μ' , res) = (γ , μ , inr (fun_read_ram μ addr))
    | write_ram => fun args res γ γ' μ μ' =>
                     let addr := (args ‼ "paddr")%exp in
                     let data := (args ‼ "data")%exp in
                     (γ' , μ' , res) = (γ , fun_write_ram μ addr data , inr 1%Z)
    | decode    => fun args res γ γ' μ μ' =>
                     let bv := (args ‼ "bv")%exp in
                     (exists res' : Lit (ty_sum ty_string ty_ast),
                         (γ' , μ' , res) = (γ , μ , res'))
    end.

  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Proof.
    destruct f; cbn.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args.
      exists γ, μ, (inr (RTYPE X0 X0 X0 RISCV_ADD)), (inr (RTYPE X0 X0 X0 RISCV_ADD)).
      reflexivity.
  Qed.

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
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
    end.

End RiscvPmpProgramKit.
