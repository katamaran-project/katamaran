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
     ZArith.ZArith
     Strings.String
     Lists.List.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Iris.Instance
     Iris.Model
     Notations
     Sep.Hoare
     Shallow.Executor
     Shallow.Soundness
     Specification
     Symbolic.Executor
     Symbolic.Soundness
     RiscvPmp.PmpCheck
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.Sig
     RiscvPmp.Contracts.
From Katamaran Require RiscvPmp.Model.

Import RiscvPmpProgram.
Import ListNotations.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.

Module Assembly.
  (* Instruction synonyms. *)
  Definition ADD (rd rs1 rs2 : RegIdx) : AST :=
    RTYPE rs2 rs1 rd RISCV_ADD.
  Definition SUB (rd rs1 rs2 : RegIdx) : AST :=
    RTYPE rs2 rs1 rd RISCV_SUB.
  Definition BEQ (rs1 rs2 : RegIdx) (imm : bv 13) : AST :=
    BTYPE imm rs2 rs1 RISCV_BEQ.
  Definition BNE (rs1 rs2 : RegIdx) (imm : bv 13) : AST :=
    BTYPE imm rs2 rs1 RISCV_BNE.
  Definition ADDI (rd rs1 : RegIdx) (imm : bv 12) : AST :=
    ITYPE imm rs1 rd RISCV_ADDI.
  Definition JALR (rd rs1 : RegIdx) (imm : bv 12) : AST :=
    RISCV_JALR imm rs1 rd.
  Definition RET : AST :=
    JALR (bv.of_N 0) (bv.of_N 1) bv.zero.
  Definition MV (rd rs1 : RegIdx) : AST :=
    ADDI rd rs1 bv.zero.
End Assembly.

Module RiscvPmpBlockVerifSpec <: Specification RiscvPmpBase RiscvPmpProgram RiscvPmpSignature.
  Include SpecificationMixin RiscvPmpBase RiscvPmpProgram RiscvPmpSignature.
  Section ContractDefKit.

  Import asn.notations.
  Notation asn_bool t := (asn.formula (formula_bool t)).
  Notation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
  Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70).
  Notation "a '↦ᵣ' t" := (asn.chunk (chunk_user (@ptstomem_readonly bytes_per_word) [a; t])) (at level 70).
  Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user ptstoinstr [a; t])) (at level 70).
  Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
  Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
  Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
  Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
  Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).
  Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
  Notation asn_pmp_access addr width es m p := (asn.formula (formula_user pmp_access [addr;width;es;m;p])).

  Definition term_eqb {Σ} (e1 e2 : Term Σ ty_regno) : Term Σ ty.bool :=
    term_binop (bop.relop bop.eq) e1 e2.

  Local Notation "e1 '=?' e2" := (term_eqb e1 e2).

  Definition z_term {Σ} : Z -> Term Σ ty.int := term_val ty.int.

  Definition sep_contract_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
    ctx.map (fun '(x::σ) => x::σ) Δ ▻▻ Σ.

  Definition create_localstore (Δ : PCtx) (Σ : LCtx) : SStore Δ (sep_contract_logvars Δ Σ) :=
    (env.tabulate (fun '(x::σ) xIn =>
                     @term_var
                       (sep_contract_logvars Δ Σ)
                       x
                       σ
                       (ctx.in_cat_left Σ (ctx.in_map (fun '(y::τ) => y::τ) xIn)))).

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepLemma {Δ} (f : Lem Δ) : Type :=
    Lemma Δ.

  Fixpoint asn_exists {Σ} (Γ : NCtx string Ty) : Assertion (Σ ▻▻ Γ) -> Assertion Σ :=
    match Γ return Assertion (Σ ▻▻ Γ) -> Assertion Σ with
    | ctx.nil => fun asn => asn
    | ctx.snoc Γ (x :: τ) =>
      fun asn =>
        @asn_exists Σ Γ (asn.exist x τ asn)
    end.

  Definition asn_with_reg {Σ} (r : Term Σ ty_regno) (asn : Reg ty_xlenbits -> Assertion Σ) (asn_default : Assertion Σ) : Assertion Σ :=
     asn.match_bool (r =? term_val ty_regno (bv.of_N 0)) (asn_default)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 1)) (asn x1)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 2)) (asn x2)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 3)) (asn x3)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 4)) (asn x4)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 5)) (asn x5)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 6)) (asn x6)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 7)) (asn x7)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 8)) (asn x8)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 9)) (asn x9)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 10)) (asn x10)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 11)) (asn x11)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 12)) (asn x12)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 13)) (asn x13)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 14)) (asn x14)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 15)) (asn x15)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 16)) (asn x16)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 17)) (asn x17)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 18)) (asn x18)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 19)) (asn x19)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 20)) (asn x20)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 21)) (asn x21)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 22)) (asn x22)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 23)) (asn x23)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 24)) (asn x24)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 25)) (asn x25)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 26)) (asn x26)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 27)) (asn x27)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 28)) (asn x28)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 29)) (asn x29)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 30)) (asn x30)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 31)) (asn x31)
     ⊥))))))))))))))))))))))))))))))).

  Definition asn_reg_ptsto {Σ} (r : Term Σ ty_regno) (w : Term Σ ty_word) : Assertion Σ :=
    asn_with_reg r (fun r => asn.chunk (chunk_ptsreg r w)) (w = term_val ty_word bv.zero).

  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

  (* TODO: abstract away the concrete type, look into unions for that *)
  (* TODO: length of list should be 16, no duplicates *)
  (* Definition pmp_entries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfgidx ty_pmpaddridx)) :=
    term_list
      (cons (term_val ty_pmpcfgidx PMP0CFG ,ₜ term_val ty_pmpaddridx PMPADDR0)
            (cons (term_val ty_pmpcfgidx PMP1CFG ,ₜ term_val ty_pmpaddridx PMPADDR1) nil)). *)

  End ContractDefKit.

  Import RiscvPmpSpecification.

  Import asn.notations.
  (* TODO: This notation is already defined with a different meaning in
     asn.notations. Resolve this.
   *)
  (* Notation "a '*↦ₘ[' n ']' xs" := (asn.chunk (chunk_user (@ptstomem n) [a; xs])) (at level 79). *)
  Local Notation "a '↦ₘ[' bytes ']' t" := (asn.chunk (chunk_user (@ptstomem bytes) [a; t])) (at level 70).
  Local Notation "a '↦ᵣ[' bytes ']' t" := (asn.chunk (chunk_user (@ptstomem_readonly bytes) [a; t])) (at level 70).
  Local Notation "r '↦' val" := (asn_reg_ptsto r val) : asn_scope.
  Local Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70).
  Local Notation "a '↦ᵣ' t" := (asn.chunk (chunk_user (@ptstomem_readonly bytes_per_word) [a; t])) (at level 70).
  Local Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user ptstoinstr [a; t])) (at level 70).
  Local Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
  Local Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
  Local Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
  Local Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
  Local Notation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
  Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).
  Local Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
  Local Notation asn_pmp_access addr width es m p := (asn.formula (formula_user pmp_access [addr;width;es;m;p])).
  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
  (* TODO: clean up above notations to get rid of the following one *)
  Local Notation asn_cur_privilege val := (asn.chunk (chunk_ptsreg cur_privilege val)).
  Local Notation asn_bool t := (asn.formula (formula_bool t)).
  Import bv.notations.


  Definition sep_contract_rX : SepContractFun rX :=
    {| sep_contract_logic_variables := ["rs" :: ty_regno; "w" :: ty_word];
       sep_contract_localstore      := [term_var "rs"];
       sep_contract_precondition    := term_var "rs" ↦ term_var "w";
       sep_contract_result          := "result_rX";
       sep_contract_postcondition   := term_var "result_rX" = term_var "w" ∗
                                       term_var "rs" ↦ term_var "w";
    |}.

  Definition sep_contract_wX : SepContractFun wX :=
    {| sep_contract_logic_variables := ["rs" :: ty_regno; "v" :: ty_xlenbits; "w" :: ty_xlenbits];
       sep_contract_localstore      := [term_var "rs"; term_var "v"];
       sep_contract_precondition    := term_var "rs" ↦ term_var "w";
       sep_contract_result          := "result_wX";
       sep_contract_postcondition   := term_var "result_wX" = term_val ty.unit tt ∗
                                       if: term_eqb (term_var "rs") (term_val ty_regno [bv 0])
                                       then term_var "rs" ↦ term_val ty_word bv.zero
                                       else term_var "rs" ↦ term_var "v"
    |}.

  Definition sep_contract_fetch : SepContractFun fetch :=
    {| sep_contract_logic_variables := ["a" :: ty_xlenbits; "w" :: ty_word];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn.chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ₘ term_var "w";
       sep_contract_result          := "result_fetch";
       sep_contract_postcondition   := asn.chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ₘ term_var "w" ∗
                                                 term_var "result_fetch" = term_union fetch_result KF_Base (term_var "w");
    |}.

  Definition sep_contract_fetch_instr : SepContractFun fetch :=
    {| sep_contract_logic_variables := ["a" :: ty_xlenbits; "i" :: ty_ast; "entries" :: ty.list ty_pmpentry];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn.chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ᵢ term_var "i" ∗
                                                 (term_val ty.int (Z.of_nat minAddr) <= term_unsigned (term_var "a"))%asn ∗
                                                 (term_binop bop.plus (term_unsigned (term_var "a")) (term_val ty.int (Z.of_nat bytes_per_instr))) <= term_val ty.int (Z.of_nat maxAddr) ∗
                                                 asn_cur_privilege (term_val ty_privilege Machine) ∗
                                                 asn_pmp_entries (term_var "entries") ∗
                                                 asn_pmp_access (term_var "a") (term_val ty_word bv_instrsize) (term_var "entries") (term_val ty_privilege Machine) (term_val ty_access_type Execute);
       sep_contract_result          := "result_fetch";
       sep_contract_postcondition   :=
         asn.chunk (chunk_ptsreg pc (term_var "a")) ∗ term_var "a" ↦ᵢ term_var "i" ∗
         asn.exist "w" _
           (term_var "result_fetch" = term_union fetch_result KF_Base (term_var "w") ∗
                                        asn.chunk (chunk_user encodes_instr [term_var "w"; term_var "i"])) ∗
           asn_cur_privilege (term_val ty_privilege Machine) ∗
           asn_pmp_entries (term_var "entries");
    |}.

  Definition sep_contract_checked_mem_read {bytes} {H: restrict_bytes bytes} : SepContractFun (@checked_mem_read bytes H) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; "w" :: ty_bytes bytes];
      sep_contract_localstore      := [term_var "typ"; term_var "paddr"];
      sep_contract_precondition    :=
        asn.match_bool (term_var "inv")
          (term_var "paddr" ↦ᵣ[ bytes ] term_var "w")
          (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
          (term_val ty.int (Z.of_nat minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_nat maxAddr);
      sep_contract_result          := "result_mem_read";
      sep_contract_postcondition   :=
        term_var "result_mem_read" = term_union (memory_op_result bytes) KMemValue (term_var "w") ∗
                                       asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w");
    |}.

  Definition sep_contract_pmpCheck {bytes : nat} {H : restrict_bytes bytes} : SepContractFun (@pmpCheck bytes H) :=
    {| sep_contract_logic_variables := ["addr" :: ty_xlenbits; "acc" :: ty_access_type; "priv" :: ty_privilege; "entries" :: ty.list ty_pmpentry];
       sep_contract_localstore      := [term_var "addr"; term_var "acc"; term_var "priv"];
       sep_contract_precondition    :=
        asn_pmp_entries (term_var "entries")
          ∗ term_var "priv" = term_val ty_privilege Machine
                                ∗ asn_pmp_access (term_var "addr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var "priv") (term_var "acc");
       sep_contract_result          := "result_pmpCheck";
       sep_contract_postcondition   :=
         term_var "result_pmpCheck" = term_inr (term_val ty.unit tt)
         ∗ asn_pmp_entries (term_var "entries");
    |}.

  Definition sep_contract_pmp_mem_read {bytes} {H : restrict_bytes bytes} : SepContractFun (@pmp_mem_read bytes H) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; "entries" :: ty.list ty_pmpentry; "w" :: ty_bytes bytes; "m" :: ty_privilege];
      sep_contract_localstore      := [term_var "typ"; term_var "m"; term_var "paddr"];
      sep_contract_precondition    :=
        asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
          term_var "m" = term_val ty_privilege Machine ∗
          (term_val ty.int (Z.of_nat minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_nat maxAddr) ∗
          asn_cur_privilege (term_var "m") ∗
          asn_pmp_entries (term_var "entries") ∗
          asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var "m") (term_var "typ");
      sep_contract_result          := "result_mem_read";
      sep_contract_postcondition   :=
        term_var "result_mem_read" = term_union (memory_op_result bytes) KMemValue (term_var "w") ∗
                                       asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
          asn_cur_privilege (term_val ty_privilege Machine) ∗
          asn_pmp_entries (term_var "entries");
    |}.

  Definition sep_contract_mem_read {bytes} {H : restrict_bytes bytes} : SepContractFun (@mem_read bytes H) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; "entries" :: ty.list ty_pmpentry; "w" :: ty_bytes bytes];
      sep_contract_localstore      := [term_var "typ"; term_var "paddr"];
      sep_contract_precondition    :=
        asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
          (term_val ty.int (Z.of_nat minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_nat maxAddr) ∗
          asn_cur_privilege (term_val ty_privilege Machine) ∗
          asn_pmp_entries (term_var "entries") ∗
          asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_val ty_privilege Machine) (term_var "typ");
      sep_contract_result          := "result_mem_read";
      sep_contract_postcondition   :=
        term_var "result_mem_read" = term_union (memory_op_result bytes) KMemValue (term_var "w") ∗
                                       asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
          asn_cur_privilege (term_val ty_privilege Machine) ∗
          asn_pmp_entries (term_var "entries");
    |}.

  Definition sep_contract_tick_pc : SepContractFun tick_pc :=
    {| sep_contract_logic_variables := ["ao" :: ty_xlenbits; "an" :: ty_xlenbits];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn.chunk (chunk_ptsreg pc (term_var "ao")) ∗
                                                 asn.chunk (chunk_ptsreg nextpc (term_var "an"));
       sep_contract_result          := "result_tick_pc";
       sep_contract_postcondition   := asn.chunk (chunk_ptsreg pc (term_var "an")) ∗
                                                 asn.chunk (chunk_ptsreg nextpc (term_var "an")) ∗
                                                 term_var "result_tick_pc" = term_val ty.unit tt;
    |}.

  Definition sep_contract_within_phys_mem : SepContractFun within_phys_mem :=
    {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "width" :: ty.int];
       sep_contract_localstore      := [term_var "paddr"; term_var "width"];
       sep_contract_precondition    :=
        let paddr_int : Term _ ty.int := term_unsigned (term_var "paddr") in
        (term_val ty.int (Z.of_nat minAddr) <= paddr_int) ∗
          (term_binop bop.plus paddr_int (term_var "width")) <= term_val ty.int (Z.of_nat maxAddr);
       sep_contract_result          := "result_within_phys_mem";
       sep_contract_postcondition   :=
         term_var "result_within_phys_mem" = term_val ty.bool true;
    |}.

  Definition sep_contract_execute_EBREAK : SepContractFun execute_EBREAK :=
    RiscvPmpExecutor.Symbolic.Statistics.extend_postcond_with_debug sep_contract_execute_EBREAK.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | rX                        => Some sep_contract_rX
      | wX                        => Some sep_contract_wX
      | fetch                     => Some sep_contract_fetch_instr
      | @mem_read bytes H         => Some (@sep_contract_mem_read bytes H)
      | tick_pc                   => Some sep_contract_tick_pc
      | @pmpCheck bytes H         => Some (@sep_contract_pmpCheck bytes H)
      | within_phys_mem           => Some sep_contract_within_phys_mem
      | pmpMatchAddr              => Some sep_contract_pmpMatchAddr
      | @pmp_mem_read bytes H     => Some (@sep_contract_pmp_mem_read bytes H)
      | @checked_mem_read bytes H => Some (@sep_contract_checked_mem_read bytes H)
      | execute_EBREAK            => Some sep_contract_execute_EBREAK
      | _                         => None
      end.

  Lemma linted_cenv :
    forall Δ τ (f : Fun Δ τ),
      match CEnv f with
      | Some c => Linted c
      | None   => True
      end.
  Proof. intros ? ? []; try constructor. Qed.

  Definition sep_contract_read_ram {bytes} : SepContractFunX (read_ram bytes) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits; "w" :: ty_bytes bytes];
       sep_contract_localstore      := [term_var "paddr"];
       sep_contract_precondition    := asn.match_bool (term_var "inv")  (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w");
       sep_contract_result          := "result_read_ram";
       sep_contract_postcondition   := asn.match_bool (term_var "inv")
                                         (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗
                                            term_var "result_read_ram" = term_var "w";
    |}.

  Definition sep_contract_write_ram {bytes} : SepContractFunX (write_ram bytes) :=
    {| sep_contract_logic_variables := ["paddr" :: ty_word; "data" :: ty_bytes bytes];
       sep_contract_localstore      := [term_var "paddr"; term_var "data"];
       sep_contract_precondition    := ∃ "w", (asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]));
       sep_contract_result          := "result_write_ram";
       sep_contract_postcondition   :=  term_var "paddr" ↦ₘ[ bytes ] term_var "data" ∗
                                       term_var "result_write_ram" = term_val ty.bool true;
    |}.

  (* Only deal with case where the call fails *)
  (* Note; we define the contract like this, because it matches the PRE of `checked_mem_read` quite well*)
  Definition sep_contract_within_mmio (bytes : nat) : SepContractFunX (within_mmio bytes) :=
    {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits];
        sep_contract_localstore      := [term_var "paddr"];
        sep_contract_precondition    :=
            (term_val ty.int (Z.of_nat minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
              (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_nat maxAddr);
        sep_contract_result          := "result_is_within";
        sep_contract_postcondition   := term_var "result_is_within" = term_val ty.bool false
    |}.


  Definition sep_contract_decode    : SepContractFunX decode :=
    {| sep_contract_logic_variables := ["code" :: ty_word; "instr" :: ty_ast];
       sep_contract_localstore      := [term_var "code"];
       sep_contract_precondition    := asn.chunk (chunk_user encodes_instr [term_var "code"; term_var "instr"]);
       sep_contract_result          := "result_decode";
       sep_contract_postcondition   := term_var "result_decode" = term_var "instr";
    |}.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | read_ram bytes  => sep_contract_read_ram
      | write_ram bytes => sep_contract_write_ram
      | within_mmio bytes => sep_contract_within_mmio bytes
      | mmio_read bytes  => sep_contract_mmio_read bytes
      | mmio_write bytes => sep_contract_mmio_write bytes
      | decode    => sep_contract_decode
      end.

  Lemma linted_cenvex :
    forall Δ τ (f : FunX Δ τ),
      Linted (CEnvEx f).
  Proof.
    intros ? ? []; try constructor.
  Qed.

  Definition lemma_open_gprs : SepLemma open_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_close_gprs : SepLemma close_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_open_ptsto_instr : SepLemma open_ptsto_instr :=
    {| lemma_logic_variables := ["paddr" :: ty_word; "i" :: ty_ast];
       lemma_patterns        := [term_var "paddr"];
       lemma_precondition    := asn.chunk (chunk_user ptstoinstr [term_var "paddr"; term_var "i"]);
      lemma_postcondition   := ∃ "w", (asn.chunk (chunk_user (ptstomem bytes_per_word) [term_var "paddr"; term_var "w"]) ∗
                                      asn.chunk (chunk_user encodes_instr [term_var "w"; term_var "i"]))
    |}.

  Definition lemma_close_ptsto_instr : SepLemma close_ptsto_instr :=
    {| lemma_logic_variables := ["paddr" :: ty_word; "w" :: ty_word; "i" :: ty_ast];
       lemma_patterns        := [term_var "paddr"; term_var "w"];
       lemma_precondition    := asn.chunk (chunk_user (ptstomem bytes_per_word) [term_var "paddr"; term_var "w"]) ∗
                                  asn.chunk (chunk_user encodes_instr [term_var "w"; term_var "i"]);
       lemma_postcondition   := asn.chunk (chunk_user ptstoinstr [term_var "paddr"; term_var "i"]);
    |}.

  Definition lemma_extract_pmp_ptsto bytes : SepLemma (extract_pmp_ptsto bytes) :=
    {| lemma_logic_variables := ["paddr" :: ty_xlenbits];
       lemma_patterns        := [term_var "paddr"];
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_return_pmp_ptsto bytes : SepLemma (return_pmp_ptsto bytes) :=
    {| lemma_logic_variables := ["paddr" :: ty_xlenbits];
       lemma_patterns        := [term_var "paddr"];
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

   Definition LEnv : LemmaEnv :=
     fun Δ l =>
       match l with
       | open_gprs      => lemma_open_gprs
       | close_gprs     => lemma_close_gprs
       | open_ptsto_instr      => lemma_open_ptsto_instr
       | close_ptsto_instr     => lemma_close_ptsto_instr
       | open_pmp_entries                   => lemma_open_pmp_entries
       | close_pmp_entries                  => lemma_close_pmp_entries
       | extract_pmp_ptsto bytes => lemma_extract_pmp_ptsto bytes
       | return_pmp_ptsto bytes => lemma_return_pmp_ptsto bytes
      end.
End RiscvPmpBlockVerifSpec.

Module RiscvPmpBlockVerifShalExecutor :=
  MakeShallowExecutor RiscvPmpBase RiscvPmpProgram RiscvPmpSignature RiscvPmpBlockVerifSpec.
Module RiscvPmpBlockVerifExecutor :=
  MakeExecutor RiscvPmpBase RiscvPmpProgram RiscvPmpSignature RiscvPmpBlockVerifSpec RiscvPmpSolver.

Module RiscvPmpSpecVerif.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifExecutor.Symbolic.

  Notation "r '↦' val" := (chunk_ptsreg r val) (at level 79).

  Import ModalNotations.

  Definition ValidContractDebug {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContract c (FunDef f)
    | None => False
    end.

  Definition ValidContractWithFuelDebug {Δ τ} (fuel : nat) (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContractWithFuel fuel c (FunDef f)
    | None => False
    end.


  Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContractReflect c (FunDef f)
    | None => False
    end.

  Definition ValidContractWithFuel {Δ τ} (fuel : nat) (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContractReflectWithFuel fuel c (FunDef f)
    | None => False
    end.

  Lemma valid_execute_rX : ValidContract rX.
  Proof. reflexivity. Qed.

  Lemma valid_execute_wX : ValidContract wX.
  Proof. reflexivity. Qed.

  (* Import SymProp.notations. *)
  (* Set Printing Depth 200. *)
  (* Eval vm_compute in (postprocess (RiscvPmpBlockVerifExecutor.SHeapSpecM.vcgen RiscvPmpBlockVerifExecutor.default_config 1 *)
  (*            sep_contract_fetch_instr (FunDef fetch))). *)
  Lemma valid_execute_fetch : ValidContract fetch.
  Proof. reflexivity. Qed.

  (* Lemma valid_execute_fetch_instr : SMut.ValidContract sep_contract_fetch_instr (FunDef fetch). *)
  (* Proof. compute. Admitted. *)

  Lemma valid_execute_tick_pc : ValidContract tick_pc.
  Proof. reflexivity. Qed.

  Ltac symbolic_simpl :=
    apply validcontract_with_erasure_sound;
    compute;
    constructor;
    cbn.

  Import RiscvPmpBlockVerifExecutor.

  Lemma valid_checked_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@checked_mem_read bytes H).
  Proof.
    destruct H as [->|[->| ->]];
    now vm_compute.
  Qed.

  Lemma valid_pmp_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@pmp_mem_read bytes H).
  Proof.
    destruct H as [->|[->| ->]]; now vm_compute.
  Qed.

  Import Bitvector.bv.notations.

  Lemma valid_pmpMatchAddr : ValidContractDebug pmpMatchAddr.
  Proof.
    symbolic_simpl.
    intros; split; intros; bv_comp; auto.
    destruct (v + v0 <=ᵘ? v1)%bv eqn:?; bv_comp; auto.
  Qed.

  Lemma valid_pmpCheck {bytes : nat} {H : restrict_bytes bytes} : ValidContractWithFuelDebug 4 (@pmpCheck bytes H).
  Proof.
  (*   destruct H as [-> |[-> | ->]]; *)
  (*     hnf; apply verification_condition_with_erasure_sound; vm_compute; *)
  (*     constructor; cbn; *)
  (*     repeat (intros; split; intros); *)
  (*     repeat match goal with *)
  (*       | H: (?b1 || ?b2)%bool = true |- _ => *)
  (*           apply Bool.orb_true_iff in H *)
  (*       | H: ?P /\ ?Q |- _ => *)
  (*           destruct H *)
  (*       | H: ?P \/ ?Q |- _ => *)
  (*           destruct H as [H|H] *)
  (*       | H: negb ?b = true |- _ => *)
  (*           apply Bool.negb_true_iff in H; *)
  (*           subst *)
  (*       | H1: ?a <=ᵘ ?b, H2: ?b <ᵘ ?a |- False => *)
  (*           unfold bv.ult, bv.ule in *; apply N.le_ngt in H1; apply (H1 H2) *)
  (*       end; *)
  (*     subst; *)
  (*     unfold Pmp_check_perms, decide_pmp_check_perms, pmp_check_RWX in *; *)
  (*     simpl in *; *)
  (*     try discriminate; *)
  (*     try Lia.lia. *)
  (* Qed. *)
  Admitted.

  Lemma valid_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@mem_read bytes H).
  Proof.
    destruct H as [->|[->| ->]]; reflexivity.
  Qed.

  Lemma valid_contract_within_phys_mem : ValidContractDebug within_phys_mem.
  Proof. symbolic_simpl. intros. Lia.lia. Qed.

  Lemma valid_contract_execute_EBREAK : ValidContractDebug execute_EBREAK.
  Proof. now symbolic_simpl. Qed.

  Lemma valid_contract : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      RiscvPmpBlockVerifSpec.CEnv f = Some c ->
      ValidContract f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContract in Hvc.
    rewrite Hcenv in Hvc.
    apply Symbolic.validcontract_reflect_sound.
    apply Hvc.
  Qed.

  Lemma valid_contract_with_fuel_debug : forall {Δ τ} (fuel : nat) (f : Fun Δ τ) (c : SepContract Δ τ),
      RiscvPmpBlockVerifSpec.CEnv f = Some c ->
      ValidContractWithFuelDebug fuel f ->
      Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros ? ? fuel f c Hcenv Hvc.
    unfold ValidContractWithFuelDebug in Hvc.
    rewrite Hcenv in Hvc.
    apply Hvc.
  Qed.

  Lemma valid_contract_debug : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContractDebug f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContractDebug in Hvc.
    rewrite Hcenv in Hvc.
    apply Hvc.
  Qed.

  Lemma ValidContracts : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros.
    destruct f; try discriminate H; eexists.
    - apply (valid_contract _ H valid_execute_rX).
    - apply (valid_contract _ H valid_execute_wX).
    - apply (valid_contract _ H valid_execute_tick_pc).
    - apply (valid_contract_debug _ H valid_contract_within_phys_mem).
    - apply (valid_contract _ H valid_mem_read).
    - apply (valid_contract _ H valid_checked_mem_read).
    - apply (valid_contract _ H valid_pmp_mem_read).
    - apply (valid_contract_with_fuel_debug _ _ H valid_pmpCheck).
    - apply (valid_contract_debug _ H valid_pmpMatchAddr).
    - apply (valid_contract _ H valid_execute_fetch).
    - apply (valid_contract_debug _ H valid_contract_execute_EBREAK).
  Qed.
End RiscvPmpSpecVerif.

Module RiscvPmpIrisInstanceWithContracts.
  Include ProgramLogicOn RiscvPmpBase RiscvPmpProgram RiscvPmpSignature RiscvPmpBlockVerifSpec.
  Include IrisInstanceWithContracts RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
    RiscvPmpSignature RiscvPmpBlockVerifSpec RiscvPmpIrisBase RiscvPmpIrisInstance.
  Include Shallow.Soundness.Soundness RiscvPmpBase RiscvPmpProgram RiscvPmpSignature
    RiscvPmpBlockVerifSpec RiscvPmpBlockVerifShalExecutor.
  Include Symbolic.Soundness.Soundness RiscvPmpBase RiscvPmpProgram RiscvPmpSignature
    RiscvPmpBlockVerifSpec RiscvPmpSolver RiscvPmpBlockVerifShalExecutor RiscvPmpBlockVerifExecutor.

  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstance.
  Import RiscvPmp.Model.
  Import RiscvPmp.BitvectorSolve.

  Import iris.bi.interface.
  Import iris.bi.big_op.
  Import iris.base_logic.lib.iprop.
  Import iris.program_logic.weakestpre.
  Import iris.base_logic.lib.gen_heap.
  Import iris.proofmode.string_ident.
  Import iris.proofmode.tactics.

  Lemma read_ram_sound `{sailGS Σ} {bytes} :
    ValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_read_ram (read_ram bytes).
  Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι. cbn.
      iIntros "H". cbn in *.
      iApply (RiscvPmpModel2.wp_lift_atomic_step_no_fork); [auto | ].
      iIntros (? ? ? ? ?) "(Hregs & % & Hmem & %Hmap & Htr)".
      iSplitR; first auto.
      destruct inv; cbn -[prim_step].
      - (* readonly case *)
        unfold interp_ptstomem_readonly.
        iDestruct "H" as "#H".
        iInv "H" as "Hptsto" "Hclose_ptsto".
        iDestruct (bi.later_mono _ _ (RiscvPmpModel2.fun_read_ram_works Hmap) with "[$Hptsto $Hmem]") as "#>%eq_fun_read_ram".
        iMod ("Hclose_ptsto" with "Hptsto") as "_".
        repeat iModIntro.
        iIntros. iModIntro.
        eliminate_prim_step Heq.
        iPoseProof (RiscvPmpModel2.mem_inv_not_modified $! Hmap with "Hmem Htr") as "Hmem".
        now iFrame "% # ∗".
      - (* old case *)
        repeat iModIntro.
        iIntros. iModIntro.
        eliminate_prim_step Heq.
        iPoseProof (RiscvPmpModel2.fun_read_ram_works Hmap with "[$H $Hmem]") as "%eq_fun_read_ram".
        iPoseProof (RiscvPmpModel2.mem_inv_not_modified $! Hmap with "Hmem Htr") as "Hmem".
        now iFrame.
  Qed.

  Lemma write_ram_sound `{sailGS Σ} {bytes} :
    ValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_write_ram (write_ram bytes).
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
      iIntros "[%w H]".
      iApply (RiscvPmpModel2.wp_lift_atomic_step_no_fork); [auto | ].
      iIntros (? ? ? ? ?) "[Hregs [% (Hmem & %Hmap & Htr)]]".
      iSplitR; first auto.
      repeat iModIntro.
      iIntros.
      eliminate_prim_step Heq.
      iMod (RiscvPmpModel2.fun_write_ram_works with "[$H $Hmem $Htr]") as "[$ H]"; [auto | now iFrame].
 Qed.

  Lemma decode_sound `{sailGS Σ} :
    ValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_decode RiscvPmpProgram.decode.
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "%Hdecode".
    iApply (RiscvPmpModel2.wp_lift_atomic_step_no_fork); [auto | ].
    iIntros (? ? ? ? ?) "[Hregs [% (Hmem & %Hmap & Htr)]]".
    iSplitR; first auto.
    repeat iModIntro.
    iIntros.
    eliminate_prim_step Heq.
    destruct (pure_decode _); inversion Hdecode.
    subst; cbn.
    iPoseProof (RiscvPmpModel2.mem_inv_not_modified $! Hmap with "Hmem Htr") as "Hmem".
    now iFrame.
  Qed.

  Lemma within_mmio_sound `{sailGS Σ} {bytes}:
    ValidContractForeign (RiscvPmpBlockVerifSpec.sep_contract_within_mmio bytes) (RiscvPmpProgram.within_mmio bytes).
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "([%Hlow _] & [%Hhi _])".
    iApply (lifting.wp_lift_pure_step_no_fork _ _ ⊤).
    - cbn; auto.
    - intros. eliminate_prim_step Heq; auto.
    - repeat iModIntro. iIntros. eliminate_prim_step Heq; auto.
      rewrite /fun_within_mmio bool_decide_and.
      assert (bool_decide (withinMMIO paddr bytes) = false) as ->.
      { rewrite bool_decide_eq_false.
        destruct bytes; first easy.
        assert (paddr ∈ liveAddrs)%stdpp.
        { apply bv.in_seqBv.
          - cbn (* TODO: add simplifying `xlenbits` to solve_bv *). solve_bv.
          - assert (Z.of_N (bv.bin paddr) < lenAddr)%Z by solve_bv. cbn.
            cbv [bv.ult]. now zify. (* `solve_bv` fails because knowledge of concrete `minAddr`, `lenAddr` needed *)}
        intros HFalse; cbn in HFalse. assert (paddr ∈ mmioAddrs)%stdpp by now destruct bytes.
        eapply mmio_ram_False; eauto.
      }
      iApply wp_value; easy.
  Qed.

  Lemma foreignSemBlockVerif `{sailGS Σ} : RiscvPmpIrisInstanceWithContracts.ForeignSem.
  Proof.
    intros Δ τ f; destruct f;
        eauto using read_ram_sound, write_ram_sound, RiscvPmpModel2.mmio_read_sound, RiscvPmpModel2.mmio_write_sound, within_mmio_sound, decode_sound.
  Qed.

  Ltac destruct_syminstance ι :=
    repeat
      match type of ι with
      | Env _ (ctx.snoc _ (MkB ?s _)) =>
          let id := string_to_ident s in
          let fr := fresh id in
          destruct (env.view ι) as [ι fr];
          destruct_syminstance ι
      | Env _ ctx.nil => destruct (env.view ι)
      | _ => idtac
      end.

  Lemma open_ptsto_instr_sound `{sailGS Σ} :
    ValidLemma RiscvPmpBlockVerifSpec.lemma_open_ptsto_instr.
  Proof.
    intros ι; destruct_syminstance ι; cbn.
    iIntros "[%w (Hptsto & Henc )]".
    iExists w.
    now iFrame.
  Qed.

  Lemma close_ptsto_instr_sound `{sailGS Σ} :
    ValidLemma RiscvPmpBlockVerifSpec.lemma_close_ptsto_instr.
  Proof.
    intros ι; destruct_syminstance ι; cbn.
    iIntros "(Hptsto & Henc )".
    iExists w.
    now iFrame.
  Qed.

  Lemma lemSemBlockVerif `{sailGS Σ} : LemmaSem.
  Proof.
    intros Δ []; intros ι; destruct_syminstance ι; try now iIntros "_".
    - apply Model.RiscvPmpModel2.open_pmp_entries_sound.
    - apply Model.RiscvPmpModel2.close_pmp_entries_sound.
    - apply open_ptsto_instr_sound.
    - apply close_ptsto_instr_sound.
  Qed.

  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifExecutor.Symbolic.

  Lemma contractsSound `{sailGS Σ} : ⊢ ValidContractEnvSem RiscvPmpBlockVerifSpec.CEnv.
  Proof.
    apply (sound foreignSemBlockVerif lemSemBlockVerif).
    intros Γ τ f c Heq.
    destruct (RiscvPmpSpecVerif.ValidContracts f Heq) as [fuel Hvc].
    eapply shallow_vcgen_fuel_soundness, symbolic_vcgen_fuel_soundness.
    eexact Hvc.
  Qed.

End RiscvPmpIrisInstanceWithContracts.
