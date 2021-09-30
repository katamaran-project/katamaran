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

  Local Notation "'rs'"           := "rs" : string_scope.
  Local Notation "'rs1'"          := "rs1" : string_scope.
  Local Notation "'rs2'"          := "rs2" : string_scope.
  Local Notation "'rd'"           := "rd" : string_scope.
  Local Notation "'op'"           := "op" : string_scope.
  Local Notation "'v'"            := "v" : string_scope.
  Local Notation "'imm'"          := "imm" : string_scope.
  Local Notation "'t'"            := "t" : string_scope.
  Local Notation "'addr'"         := "addr" : string_scope.
  Local Notation "'paddr'"        := "paddr" : string_scope.
  Local Notation "'typ'"          := "typ" : string_scope.
  Local Notation "'acc'"          := "acc" : string_scope.
  Local Notation "'value'"        := "value" : string_scope.
  Local Notation "'data'"         := "data" : string_scope.
  Local Notation "'ent'"          := "ent" : string_scope.
  Local Notation "'pmpaddr'"      := "pmpaddr" : string_scope.
  Local Notation "'prev_pmpaddr'" := "prev_pmpaddr" : string_scope.
  Local Notation "'cfg'"          := "cfg" : string_scope.
  Local Notation "'rng'"          := "rng" : string_scope.

  (** Functions **)
  Inductive Fun : PCtx -> Ty -> Set :=
  | rX                 : Fun [rs ∶ ty_regidx] ty_word
  | wX                 : Fun [rd ∶ ty_regidx, v ∶ ty_word] ty_unit
  | get_arch_pc        : Fun ctx_nil ty_word
  | get_next_pc        : Fun ctx_nil ty_word
  | set_next_pc        : Fun [addr ∶ ty_word] ty_unit
  | address_aligned    : Fun [addr ∶ ty_word] ty_bool
  | abs                : Fun [v ∶ ty_int] ty_int
  | mem_read           : Fun [typ ∶ ty_access_type, paddr ∶ ty_int] ty_memory_op_result
  | checked_mem_read   : Fun [t ∶ ty_access_type, paddr ∶ ty_int] ty_memory_op_result
  | checked_mem_write  : Fun [paddr ∶ ty_int, data ∶ ty_word] ty_memory_op_result
  | pmp_mem_read       : Fun [t∶ ty_access_type, paddr ∶ ty_int] ty_memory_op_result
  | pmp_mem_write      : Fun [paddr ∶ ty_int, data ∶ ty_word, typ ∶ ty_access_type] ty_memory_op_result
  | pmpLocked          : Fun [cfg ∶ ty_pmpcfg_ent] ty_bool
  | pmpCheck           : Fun [addr ∶ ty_int, acc ∶ ty_access_type] (ty_option ty_exception_type)
  | pmpCheckPerms      : Fun [ent ∶ ty_pmpcfg_ent, acc ∶ ty_access_type] ty_bool
  | pmpCheckRWX        : Fun [ent ∶ ty_pmpcfg_ent, acc ∶ ty_access_type] ty_bool
  | pmpMatchEntry      : Fun [addr ∶ ty_int, acc ∶ ty_access_type, ent ∶ ty_pmpcfg_ent, pmpaddr ∶ ty_int, prev_pmpaddr ∶ ty_int] ty_pmpmatch
  | pmpAddrRange       : Fun [cfg ∶ ty_pmpcfg_ent, pmpaddr ∶ ty_int, prev_pmpaddr ∶ ty_int] ty_pmp_addr_range
  | pmpMatchAddr       : Fun [addr ∶ ty_int, rng ∶ ty_pmp_addr_range] ty_pmpaddrmatch
  | process_load       : Fun [rd ∶ ty_regidx, value ∶ ty_memory_op_result] ty_retired
  | write_mem_value    : Fun [paddr ∶ ty_int, value ∶ ty_word] ty_memory_op_result
  | execute_RTYPE      : Fun [rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_rop] ty_retired
  | execute_ITYPE      : Fun [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_iop] ty_retired
  | execute_UTYPE      : Fun [imm ∶ ty_int, rd ∶ ty_regidx, op ∶ ty_uop] ty_retired
  | execute_BTYPE      : Fun [imm ∶ ty_int, rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, op ∶ ty_bop] ty_retired
  | execute_RISCV_JAL  : Fun [imm ∶ ty_int, rd ∶ ty_regidx] ty_retired
  | execute_RISCV_JALR : Fun [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx] ty_retired
  | execute_LOAD       : Fun [imm ∶ ty_int, rs1 ∶ ty_regidx, rd ∶ ty_regidx] ty_retired
  | execute_STORE      : Fun [imm ∶ ty_int, rs2 ∶ ty_regidx, rs1 ∶ ty_regidx] ty_retired
  .

  Inductive FunX : PCtx -> Ty -> Set :=
  | read_ram  : FunX [paddr ∶ ty_int] ty_word
  | write_ram : FunX [paddr ∶ ty_int, data ∶ ty_word] ty_word
  .

  Inductive Lem : PCtx -> Set :=. 

  Definition 𝑭  : PCtx -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : PCtx -> Ty -> Set := FunX.
  Definition 𝑳  : PCtx -> Set := Lem.

  Inductive Reg : Ty -> Set :=
  | pc       : Reg ty_word
  | nextpc   : Reg ty_word
  | x0       : Reg ty_word
  | x1       : Reg ty_word
  | x2       : Reg ty_word
  | pmp0cfg  : Reg ty_pmpcfg_ent
  | pmpaddr0 : Reg ty_int
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
        | right; intros e; dependent elimination e
        ].
  Defined.
End RiscvPmpTermKit.

Module RiscvPmpProgramKit <: (ProgramKit RiscvPmpTermKit).
  Module Export TM := Terms RiscvPmpTermKit.

  Section Functions.
  Local Coercion stm_exp : Exp >-> Stm.

  Local Notation "'rs'"           := "rs" : string_scope.
  Local Notation "'rs1'"          := "rs1" : string_scope.
  Local Notation "'rs1_val'"      := "rs1_val" : string_scope.
  Local Notation "'rs2'"          := "rs2" : string_scope.
  Local Notation "'rs2_val'"      := "rs2_val" : string_scope.
  Local Notation "'rd'"           := "rd" : string_scope.
  Local Notation "'op'"           := "op" : string_scope.
  Local Notation "'result'"       := "result" : string_scope.
  Local Notation "'res'"          := "res" : string_scope.
  Local Notation "'v'"            := "v" : string_scope.
  Local Notation "'imm'"          := "imm" : string_scope.
  Local Notation "'immext'"       := "immext" : string_scope.
  Local Notation "'off'"          := "off" : string_scope.
  Local Notation "'offset'"       := "offset" : string_scope.
  Local Notation "'ret'"          := "ret" : string_scope.
  Local Notation "'tmp'"          := "tmp" : string_scope.
  Local Notation "'tmp1'"         := "tmp1" : string_scope.
  Local Notation "'tmp2'"         := "tmp2" : string_scope.
  Local Notation "'tmp3'"         := "tmp3" : string_scope.
  Local Notation "'t'"            := "t" : string_scope.
  Local Notation "'e'"            := "e" : string_scope.
  Local Notation "'addr'"         := "addr" : string_scope.
  Local Notation "'paddr'"        := "paddr" : string_scope.
  Local Notation "'taken'"        := "taken" : string_scope.
  Local Notation "'typ'"          := "typ" : string_scope.
  Local Notation "'acc'"          := "acc" : string_scope.
  Local Notation "'value'"        := "value" : string_scope.
  Local Notation "'data'"         := "data" : string_scope.
  Local Notation "'check'"        := "check" : string_scope.
  Local Notation "'ent'"          := "ent" : string_scope.
  Local Notation "'pmpaddr'"      := "pmpaddr" : string_scope.
  Local Notation "'prev_pmpaddr'" := "prev_pmpaddr" : string_scope.
  Local Notation "'rng'"          := "rng" : string_scope.
  Local Notation "'cfg'"          := "cfg" : string_scope.
  Local Notation "'L'"            := "L" : string_scope.
  Local Notation "'A'"            := "A" : string_scope.
  Local Notation "'X'"            := "X" : string_scope.
  Local Notation "'W'"            := "W" : string_scope.
  Local Notation "'R'"            := "R" : string_scope.
  Local Notation "'lo'"           := "lo" : string_scope.
  Local Notation "'hi'"           := "hi" : string_scope.

  Local Notation "'rs'"           := (@exp_var _ "rs" _ _) : exp_scope.
  Local Notation "'rs1'"          := (@exp_var _ "rs1" _ _) : exp_scope.
  Local Notation "'rs1_val'"      := (@exp_var _ "rs1_val" _ _) : exp_scope.
  Local Notation "'rs2'"          := (@exp_var _ "rs2" _ _) : exp_scope.
  Local Notation "'rs2_val'"      := (@exp_var _ "rs2_val" _ _) : exp_scope.
  Local Notation "'rd'"           := (@exp_var _ "rd" _ _) : exp_scope.
  Local Notation "'op'"           := (@exp_var _ "op" _ _) : exp_scope.
  Local Notation "'result'"       := (@exp_var _ "result" _ _) : exp_scope.
  Local Notation "'res'"          := (@exp_var _ "res" _ _) : exp_scope.
  Local Notation "'v'"            := (@exp_var _ "v" _ _) : exp_scope.
  Local Notation "'imm'"          := (@exp_var _ "imm" _ _) : exp_scope.
  Local Notation "'immext'"       := (@exp_var _ "immext" _ _) : exp_scope.
  Local Notation "'off'"          := (@exp_var _ "off" _ _) : exp_scope.
  Local Notation "'offset'"       := (@exp_var _ "offset" _ _) : exp_scope.
  Local Notation "'ret'"          := (@exp_var _ "ret" _ _) : exp_scope.
  Local Notation "'tmp'"          := (@exp_var _ "tmp" _ _) : exp_scope.
  Local Notation "'tmp1'"         := (@exp_var _ "tmp1" _ _) : exp_scope.
  Local Notation "'tmp2'"         := (@exp_var _ "tmp2" _ _) : exp_scope.
  Local Notation "'tmp3'"         := (@exp_var _ "tmp3" _ _) : exp_scope.
  Local Notation "'t'"            := (@exp_var _ "t" _ _) : exp_scope.
  Local Notation "'e'"            := (@exp_var _ "e" _ _) : exp_scope.
  Local Notation "'addr'"         := (@exp_var _ "addr" _ _) : exp_scope.
  Local Notation "'paddr'"        := (@exp_var _ "paddr" _ _) : exp_scope.
  Local Notation "'taken'"        := (@exp_var _ "taken" _ _) : exp_scope.
  Local Notation "'typ'"          := (@exp_var _ "typ" _ _) : exp_scope.
  Local Notation "'acc'"          := (@exp_var _ "acc" _ _) : exp_scope.
  Local Notation "'value'"        := (@exp_var _ "value" _ _) : exp_scope.
  Local Notation "'data'"         := (@exp_var _ "data" _ _) : exp_scope.
  Local Notation "'check'"        := (@exp_var _ "check" _ _) : exp_scope.
  Local Notation "'ent'"          := (@exp_var _ "ent" _ _) : exp_scope.
  Local Notation "'pmpaddr'"      := (@exp_var _ "pmpaddr" _ _) : exp_scope.
  Local Notation "'prev_pmpaddr'" := (@exp_var _ "prev_pmpaddr" _ _) : exp_scope.
  Local Notation "'rng'"          := (@exp_var _ "rng" _ _) : exp_scope.
  Local Notation "'cfg'"          := (@exp_var _ "cfg" _ _) : exp_scope.
  Local Notation "'L'"            := (@exp_var _ "L" _ _) : exp_scope.
  Local Notation "'A'"            := (@exp_var _ "A" _ _) : exp_scope.
  Local Notation "'X'"            := (@exp_var _ "X" _ _) : exp_scope.
  Local Notation "'W'"            := (@exp_var _ "W" _ _) : exp_scope.
  Local Notation "'R'"            := (@exp_var _ "R" _ _) : exp_scope.
  Local Notation "'lo'"           := (@exp_var _ "lo" _ _) : exp_scope.
  Local Notation "'hi'"           := (@exp_var _ "hi" _ _) : exp_scope.

  Local Notation "'Read'" := (exp_union access_type KRead (exp_lit ty_unit tt)) : exp_scope.
  Local Notation "'Write'" := (exp_union access_type KWrite (exp_lit ty_unit tt)) : exp_scope.
  Local Notation "'ReadWrite'" := (exp_union access_type KReadWrite (exp_lit ty_unit tt)) : exp_scope.
  Local Notation "'Execute'" := (exp_union access_type KExecute (exp_lit ty_unit tt)) : exp_scope.

  Local Notation "'E_Fetch_Access_Fault'" := (exp_union exception_type KE_Fetch_Access_Fault (exp_lit ty_unit tt)) : exp_scope.
  Local Notation "'E_Load_Access_Fault'" := (exp_union exception_type KE_Load_Access_Fault (exp_lit ty_unit tt)) : exp_scope.
  Local Notation "'E_SAMO_Access_Fault'" := (exp_union exception_type KE_SAMO_Access_Fault (exp_lit ty_unit tt)) : exp_scope.

  Local Notation "'None'" := (exp_inr (exp_lit ty_unit tt)) : exp_scope.
  Local Notation "'Some' va" := (exp_inl va) (at level 10, va at next level) : exp_scope.

  Local Notation "'MemValue' memv" := (exp_union memory_op_result KMemValue memv) (at level 10, memv at next level) : exp_scope.
  Local Notation "'MemException' meme" := (exp_union memory_op_result KMemException meme) (at level 10, meme at next level) : exp_scope.

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

  Definition fun_mem_read : Stm [typ ∶ ty_access_type, paddr ∶ ty_int] ty_memory_op_result :=
    call pmp_mem_read typ paddr.

  Definition fun_checked_mem_read : Stm [t ∶ ty_access_type, paddr ∶ ty_int] ty_memory_op_result :=
    let: tmp := foreign read_ram paddr in
    MemValue tmp.

  Definition fun_checked_mem_write : Stm [paddr ∶ ty_int, data ∶ ty_word] ty_memory_op_result :=
    let: tmp := foreign write_ram paddr data in
    MemValue tmp.

  Definition fun_pmp_mem_read : Stm [t∶ ty_access_type, paddr ∶ ty_int] ty_memory_op_result :=
    let: tmp := call pmpCheck paddr t in
    match: tmp with
    | inl e => MemException e
    | inr v => call checked_mem_read t paddr
    end.

  Definition fun_pmp_mem_write : Stm [paddr ∶ ty_int, data ∶ ty_word, typ ∶ ty_access_type] ty_memory_op_result :=
    let: tmp := call pmpCheck paddr typ in
    match: tmp with
    | inl e => MemException e
    | inr v => call checked_mem_write paddr data
    end.

  Definition fun_pmpLocked : Stm [cfg ∶ ty_pmpcfg_ent] ty_bool :=
    (stm_match_record pmpcfg_ent cfg
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
       "L" L)
       "A" A)
       "X" X)
       "W" W)
       "R" R)
      L).

  Definition fun_pmpCheck : Stm [addr ∶ ty_int, acc ∶ ty_access_type] (ty_option ty_exception_type) :=
    let: tmp1 := stm_read_register pmp0cfg in
    let: tmp2%string := stm_read_register pmpaddr0 in
    let: tmp3%string := call pmpMatchEntry addr acc tmp1 tmp2 (exp_lit ty_int 0%Z) in
    let: check%string := match: tmp3 in pmpmatch with
                  | PMP_Success  => stm_lit ty_bool true
                  | PMP_Fail     => stm_lit ty_bool false
                  | PMP_Continue => stm_lit ty_bool true
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

  Definition fun_pmpCheckPerms : Stm [ent ∶ ty_pmpcfg_ent, acc ∶ ty_access_type] ty_bool :=
    let: tmp := call pmpLocked ent in
    if: tmp
    then let: tmp%string := call pmpCheckRWX ent acc in
         tmp
    else stm_lit ty_bool true.

  Definition fun_pmpCheckRWX : Stm [ent ∶ ty_pmpcfg_ent, acc ∶ ty_access_type] ty_bool :=
    (stm_match_record pmpcfg_ent ent
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

  Definition fun_pmpMatchEntry : Stm [addr ∶ ty_int, acc ∶ ty_access_type, ent ∶ ty_pmpcfg_ent, pmpaddr ∶ ty_int, prev_pmpaddr ∶ ty_int] ty_pmpmatch :=
    let: rng := call pmpAddrRange ent pmpaddr prev_pmpaddr in
    let: tmp%string := call pmpMatchAddr addr rng in
    match: tmp in pmpaddrmatch with
    | PMP_NoMatch      => exp_lit ty_pmpmatch PMP_Continue
    | PMP_PartialMatch => exp_lit ty_pmpmatch PMP_Fail
    | PMP_Match        =>
      let: tmp%string := call pmpCheckPerms ent acc in
      if: tmp
      then exp_lit ty_pmpmatch PMP_Success
      else exp_lit ty_pmpmatch PMP_Fail
    end.

  Definition fun_pmpAddrRange : Stm [cfg ∶ ty_pmpcfg_ent, pmpaddr ∶ ty_int, prev_pmpaddr ∶ ty_int] ty_pmp_addr_range :=
    (stm_match_record pmpcfg_ent cfg
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

  Definition fun_process_load : Stm [rd ∶ ty_regidx, value ∶ ty_memory_op_result] ty_retired :=
    stm_match_union_alt memory_op_result value
                        (fun K =>
                           match K with
                           | KMemValue     => MkAlt (pat_var result)
                                                    (call wX rd result ;;
                                                     stm_lit ty_retired RETIRE_SUCCESS)
                           | KMemException => MkAlt (pat_var e)
                                                    (* TODO: handle_mem_exception? *)
                                                    (stm_lit ty_retired RETIRE_FAIL)
                           end).

  Definition fun_write_mem_value : Stm [paddr ∶ ty_int, value ∶ ty_word] ty_memory_op_result :=
    call pmp_mem_write paddr value Write.

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

  Definition fun_execute_STORE : Stm [imm ∶ ty_int, rs2 ∶ ty_regidx, rs1 ∶ ty_regidx] ty_retired :=
    let: offset := imm in
    let: tmp%string := call rX rs1 in
    let: paddr%string := tmp + offset in
    let: rs2_val%string := call rX rs2 in
    let: res%string := call write_mem_value paddr rs2_val in
    stm_match_union_alt memory_op_result res
                        (fun K =>
                           match K with
                           | KMemValue => MkAlt (pat_var v%string)
                                                (if: v = (exp_lit ty_int 1%Z)
                                                 then stm_lit ty_retired RETIRE_SUCCESS
                                                 else fail "store got false from write_mem_value")
                           | KMemException => MkAlt (pat_var e%string)
                                                    (* TODO: handle_mem_exception? *)
                                                    (stm_lit ty_retired RETIRE_FAIL)
                           end).

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
    end.

  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Proof.
    destruct f; cbn;
      repeat depelim args; repeat eexists; constructor.
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
    | write_mem_value    => fun_write_mem_value
    | checked_mem_read   => fun_checked_mem_read
    | checked_mem_write  => fun_checked_mem_write
    | pmp_mem_read       => fun_pmp_mem_read
    | pmp_mem_write      => fun_pmp_mem_write
    | pmpLocked          => fun_pmpLocked
    | pmpCheck           => fun_pmpCheck
    | pmpCheckPerms      => fun_pmpCheckPerms
    | pmpCheckRWX        => fun_pmpCheckRWX
    | pmpMatchEntry      => fun_pmpMatchEntry
    | pmpAddrRange       => fun_pmpAddrRange
    | pmpMatchAddr       => fun_pmpMatchAddr
    | process_load       => fun_process_load
    | execute_RTYPE      => fun_execute_RTYPE
    | execute_ITYPE      => fun_execute_ITYPE
    | execute_UTYPE      => fun_execute_UTYPE
    | execute_BTYPE      => fun_execute_BTYPE
    | execute_RISCV_JAL  => fun_execute_RISCV_JAL
    | execute_RISCV_JALR => fun_execute_RISCV_JALR
    | execute_LOAD       => fun_execute_LOAD
    | execute_STORE      => fun_execute_STORE
    end.

End RiscvPmpProgramKit.
