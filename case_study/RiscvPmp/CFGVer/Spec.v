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
     Iris.BinaryInstance
     Iris.BinaryWeakestPre
     Iris.Base
     Notations
     Bitvector
     Sep.Hoare
     Specification
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor.
From Katamaran Require Import
     MicroSail.RefineExecutor.
From Katamaran Require Import
     MicroSail.Soundness
     RiscvPmp.PmpCheck
     RiscvPmp.IrisModel
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstance
     RiscvPmp.IrisInstanceBinary
     RiscvPmp.Machine
     RiscvPmp.Sig
     RiscvPmp.Contracts.
From Katamaran Require RiscvPmp.ModelBinary.

From iris.program_logic Require Import total_lifting.

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
  Definition MUL (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd false true true.
  Definition MULH (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd true true true.
  Definition MULHSU (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd true true false.
  Definition MULHU (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd true false false.
End Assembly.

Module RiscvPmpBlockVerifSpec <: Specification RiscvPmpBase RiscvPmpSignature RiscvPmpProgram.
  Include SpecificationMixin RiscvPmpBase RiscvPmpSignature RiscvPmpProgram.
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
  (* Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])). *)
  (* Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])). *)
  (* Notation asn_pmp_access addr width es m p := (asn.formula (formula_user pmp_access [addr;width;es;m;p])). *)
  (* Notation asn_inv_mmio bytes := (asn.chunk (chunk_user (inv_mmio bytes) [env])). *)
  (* Notation asn_mmio_checked_write bytes a w := (asn.chunk (chunk_user (mmio_checked_write bytes) [a; w])). *)
  Notation asn_inv_leakage := (asn.chunk (chunk_user inv_leakage [env])).

  Definition term_eqb {Σ} (e1 e2 : Term Σ ty_regno) : Term Σ ty.bool :=
    term_binop (bop.relop bop.eq) e1 e2.

  Definition term_eqb_1 {Σ} (e1 e2 : Term Σ (ty.bvec 1)) : Term Σ ty.bool :=
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

    Definition asn_with_reg_1 {Σ} (r : Term Σ (ty.bvec 1)) (asn : Reg ty_xlenbits -> Assertion Σ) (asn_default : Assertion Σ) : Assertion Σ :=
     asn.match_bool (term_eqb_1 r (term_val (ty.bvec 1) (bv.of_N 0))) (asn_default)
    (asn.match_bool (term_eqb_1 r (term_val (ty.bvec 1) (bv.of_N 1))) (asn x1)⊥).

  Definition asn_reg_ptsto {Σ} (r : Term Σ ty_regno) (w : Term Σ ty_word) : Assertion Σ :=
    asn_with_reg r (fun r => asn.chunk (chunk_ptsreg r w)) (w = term_val ty_word bv.zero).

  Definition asn_reg_ptsto_1 {Σ} (r : Term Σ (ty.bvec 1)) (w : Term Σ ty_word) : Assertion Σ :=
    asn_with_reg_1 r (fun r => asn.chunk (chunk_ptsreg r w)) (w = term_val ty_word bv.zero).

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
  #[global] Notation "r '↦ᵣ' val" := (asn_reg_ptsto r val) (at level 70) : asn_scope.
  #[global] Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70) : asn_scope.
  #[global] Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user (@ptstomem_readonly bytes_per_word) [a; t])) (at level 70) : asn_scope.
  Local Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user ptstoinstr [a; t])) (at level 70).
  Local Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
  Local Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
  Local Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
  Local Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
  Local Notation "x + y" := (term_binop bop.bvadd x y) : exp_scope.
  Local Notation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
  (* Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])). *)
  (* Local Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])). *)
  (* Local Notation asn_pmp_access addr width es m p := (asn.formula (formula_user pmp_access [addr;width;es;m;p])). *)
  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
  (* TODO: clean up above notations to get rid of the following one *)
  Local Notation asn_cur_privilege val := (asn.chunk (chunk_ptsreg cur_privilege val)).
  Local Notation asn_bool t := (asn.formula (formula_bool t)).
  (* Local Notation asn_in_mmio n l := (asn.formula (formula_user (in_mmio n) [l])). *)
  (* Local Notation asn_inv_mmio bytes := (asn.chunk (chunk_user (inv_mmio bytes) [env])). *)
  (* Local Notation asn_mmio_checked_write bytes a w := (asn.chunk (chunk_user (mmio_checked_write bytes) [a; w])). *)
  Import bv.notations.

  Definition sep_contract_rX : SepContractFun rX :=
    {| sep_contract_logic_variables := ["rs" :: ty_regno; "reg_val" :: ty_word];
       sep_contract_localstore      := [term_var "rs"];
      sep_contract_precondition    := asn.formula (formula_secLeak (term_var "rs")) ∗ term_var "rs" ↦ᵣ term_var "reg_val";
       sep_contract_result          := "result_rX";
       sep_contract_postcondition   := asn.formula (formula_propeq (term_var "result_rX") (term_var "reg_val")) ∗
                                       term_var "rs" ↦ᵣ term_var "reg_val";
    |}.

  Definition sep_contract_wX : SepContractFun wX :=
    {| sep_contract_logic_variables := ["rs" :: ty_regno; "v" :: ty_xlenbits; "reg_val" :: ty_xlenbits];
       sep_contract_localstore      := [term_var "rs"; term_var "v"];
      sep_contract_precondition    := asn.formula (formula_secLeak (term_var "rs")) ∗ term_var "rs" ↦ᵣ term_var "reg_val";
       sep_contract_result          := "result_wX";
       sep_contract_postcondition   := term_var "result_wX" = term_val ty.unit tt ∗
                                       if: term_eqb (term_var "rs") (term_val ty_regno [bv 0])
                                       then term_var "rs" ↦ᵣ term_val ty_word bv.zero
                                       else term_var "rs" ↦ᵣ term_var "v"
    |}.

  Definition sep_contract_fetch_instr : SepContractFun fetch :=
    {| sep_contract_logic_variables := ["a" :: ty_xlenbits; "i" :: ty_ast(* ; "entries" :: ty.list ty_pmpentry *)];
       sep_contract_localstore      := [];
       sep_contract_precondition    :=
        asn.formula (formula_secLeak (term_var "a")) ∗ (* Technically this can be concluded from the formula_le, but I think it is better explicit *)
        asn.chunk (chunk_ptsreg pc (term_var "a")) ∗
          term_var "a" ↦ᵢ term_var "i" ∗
          (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "a"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "a")) (term_val ty.int (Z.of_nat bytes_per_instr))) <= term_val ty.int (Z.of_N maxAddr) ∗
                                                                                                                 asn_cur_privilege (term_val ty_privilege Machine) (* ∗ *)
                                                 (* asn_pmp_entries (term_var "entries") ∗ *)
                                                 (* asn_pmp_access (term_var "a") (term_val ty_word bv_instrsize) (term_var "entries") (term_val ty_privilege Machine) (term_val ty_access_type Execute) *) ∗
                                                                                                                 asn.chunk (chunk_user inv_leakage [env]);
       sep_contract_result          := "result_fetch";
       sep_contract_postcondition   :=
        asn.formula (formula_secLeak (term_var "a")) ∗
         asn.chunk (chunk_ptsreg pc (term_var "a")) ∗ term_var "a" ↦ᵢ term_var "i" ∗
         asn.exist "encoded_instr" _
         (term_var "result_fetch" = term_union fetch_result KF_Base (term_var "encoded_instr") ∗
                                      asn.chunk (chunk_user encodes_instr [term_var "encoded_instr"; term_var "i"])
         ∗ asn.formula (formula_secLeak (term_var "encoded_instr"))) ∗
           asn_cur_privilege (term_val ty_privilege Machine) (* ∗ *)
           (* asn_pmp_entries (term_var "entries") *);
    |}.

  Definition sep_contract_checked_mem_read {bytes} {H: restrict_bytes bytes} : SepContractFun (@checked_mem_read bytes H) :=
     {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; "cmem_val" :: ty_bytes bytes];
      sep_contract_localstore      := [term_var "typ"; term_var "paddr"];
      sep_contract_precondition    :=
         asn.formula (formula_secLeak (term_var "inv")) ∗
           asn.formula (formula_secLeak (term_var "paddr")) ∗
        asn.match_bool (term_var "inv")
          (term_var "paddr" ↦ᵣ[ bytes ] term_var "cmem_val")
          (term_var "paddr" ↦ₘ[ bytes ] term_var "cmem_val") ∗
          (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr) ∗
                                                                                                           asn.chunk (chunk_user inv_leakage [env]);
      sep_contract_result          := "result_mem_read";
      sep_contract_postcondition   :=
         asn.formula (formula_secLeak (term_var "inv")) ∗
           asn.formula (formula_secLeak (term_var "paddr")) ∗
           asn.formula (formula_propeq (term_var "result_mem_read") (term_union (memory_op_result bytes) KMemValue (term_var "cmem_val"))) ∗
         asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "cmem_val") (term_var "paddr" ↦ₘ[ bytes ] term_var "cmem_val");
    |}.


  Definition sep_contract_checked_mem_write {bytes} {H: restrict_bytes bytes} : SepContractFun (@checked_mem_write bytes H) :=
    {| sep_contract_logic_variables := [(* "inv" :: ty.bool; *) "paddr" :: ty_xlenbits; "data" :: ty_bytes bytes];
      sep_contract_localstore      := [term_var "paddr"; term_var "data"];
      sep_contract_precondition    :=
        (* asn.match_bool (term_var "inv") *)
        (*   ((* asn_in_mmio bytes (term_var "paddr") ∗ *) *)
        (*     ∃ "w", term_var "paddr" ↦ₘ[ bytes ] term_var "w" ∗ *)
        (*    term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits)))(*  ∗ *) *)
        (*    (* asn_inv_mmio bytes ∗ *) *)
        (*    (* asn_mmio_checked_write bytes (term_var "paddr") (term_var "data") *)) *)
        (*   ( *)
            ∃ "cmem_val", term_var "paddr" ↦ₘ[ bytes ] term_var "cmem_val" ∗
           (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
           (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr)(* ) *) ∗
                                                                                                            asn.chunk (chunk_user inv_leakage [env]) ∗
    asn.formula (formula_secLeak (term_var "paddr"));
      sep_contract_result          := "result_checked_mem_write";
      sep_contract_postcondition   :=
        term_var "result_checked_mem_write" = term_union (memory_op_result 1) KMemValue (term_val ty_byte [bv 1]) ∗
        (* asn.match_bool (term_var "inv") ⊤ *) (term_var "paddr" ↦ₘ[ bytes ] term_var "data");
    |}.

  (* Definition sep_contract_pmpCheck {bytes : nat} {H : restrict_bytes bytes} : SepContractFun (@pmpCheck bytes H) := *)
  (*   {| sep_contract_logic_variables := ["addr" :: ty_xlenbits; "acc" :: ty_access_type; "priv" :: ty_privilege; "entries" :: ty.list ty_pmpentry]; *)
  (*      sep_contract_localstore      := [term_var "addr"; term_var "acc"; term_var "priv"]; *)
  (*      sep_contract_precondition    := *)
  (*       asn_pmp_entries (term_var "entries") *)
  (*         ∗ term_var "priv" = term_val ty_privilege Machine *)
  (*                               ∗ asn_pmp_access (term_var "addr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var "priv") (term_var "acc"); *)
  (*      sep_contract_result          := "result_pmpCheck"; *)
  (*      sep_contract_postcondition   := *)
  (*        term_var "result_pmpCheck" = term_inr (term_val ty.unit tt) *)
  (*        ∗ asn_pmp_entries (term_var "entries"); *)
  (*   |}. *)

  (* Definition sep_contract_pmp_mem_read {bytes} {H : restrict_bytes bytes} : SepContractFun (@pmp_mem_read bytes H) := *)
  (*   {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; "entries" :: ty.list ty_pmpentry; "w" :: ty_bytes bytes; "m" :: ty_privilege]; *)
  (*     sep_contract_localstore      := [term_var "typ"; term_var "m"; term_var "paddr"]; *)
  (*     sep_contract_precondition    := *)
  (*       asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗ *)
  (*         term_var "m" = term_val ty_privilege Machine ∗ *)
  (*         (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗ *)
  (*         (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr) ∗ *)
  (*         asn_cur_privilege (term_var "m") ∗ *)
  (*         asn_pmp_entries (term_var "entries") ∗ *)
  (*         asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var "m") (term_var "typ"); *)
  (*     sep_contract_result          := "result_mem_read"; *)
  (*     sep_contract_postcondition   := *)
  (*       term_var "result_mem_read" = term_union (memory_op_result bytes) KMemValue (term_var "w") ∗ *)
  (*       asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗ *)
  (*       asn_cur_privilege (term_val ty_privilege Machine) ∗ *)
  (*       asn_pmp_entries (term_var "entries"); *)
  (*   |}. *)


  (* Definition sep_contract_pmp_mem_write {bytes} {H: restrict_bytes bytes} : SepContractFun (@pmp_mem_write bytes H) := *)
  (*   {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits; "data" :: ty_bytes bytes; "typ" :: ty_access_type; "m" :: ty_privilege; "entries" :: ty.list ty_pmpentry]; *)
  (*     sep_contract_localstore      := [term_var "paddr"; term_var "data"; term_var "typ"; term_var "m"]; *)
  (*     sep_contract_precondition    := *)
  (*       asn.match_bool (term_var "inv") *)
  (*         (asn_in_mmio bytes (term_var "paddr") ∗ *)
  (*          term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits))) ∗ *)
  (*          asn_inv_mmio bytes ∗ *)
  (*          asn_mmio_checked_write bytes (term_var "paddr") (term_var "data")) *)
  (*         (∃ "w", term_var "paddr" ↦ₘ[ bytes ] term_var "w" ∗ *)
  (*          (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗ *)
  (*          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr)) ∗ *)
  (*       asn_cur_privilege (term_var "m") ∗ *)
  (*       term_var "m" = term_val ty_privilege Machine ∗ *)
  (*       asn_pmp_entries (term_var "entries") ∗ *)
  (*       asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var "m") (term_var "typ"); *)
  (*     sep_contract_result          := "result_mem_write"; *)
  (*     sep_contract_postcondition   := *)
  (*       term_var "result_mem_write" = term_union (memory_op_result 1) KMemValue (term_val ty_byte [bv 1]) ∗ *)
  (*       asn.match_bool (term_var "inv") ⊤ (term_var "paddr" ↦ₘ[ bytes ] term_var "data") ∗ *)
  (*       asn_cur_privilege (term_var "m") ∗ *)
  (*       asn_pmp_entries (term_var "entries"); *)
  (*   |}. *)

  Definition sep_contract_mem_read {bytes} {H : restrict_bytes bytes} : SepContractFun (@mem_read bytes H) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; (* "entries" :: ty.list ty_pmpentry; *) "mem_val" :: ty_bytes bytes];
      sep_contract_localstore      := [term_var "typ"; term_var "paddr"];
      sep_contract_precondition    :=
        asn.formula (formula_secLeak (term_var "inv")) ∗
          asn.formula (formula_secLeak (term_var "paddr")) ∗
        asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "mem_val") (term_var "paddr" ↦ₘ[ bytes ] term_var "mem_val") ∗
          (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr) ∗
          asn_cur_privilege (term_val ty_privilege Machine)(*  ∗ *)
          (* asn_pmp_entries (term_var "entries") ∗ *)
          (* asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_val ty_privilege Machine) (term_var "typ") *) ∗
          asn.chunk (chunk_user inv_leakage [env]);
      sep_contract_result          := "result_mem_read";
      sep_contract_postcondition   :=

        asn.formula (formula_secLeak (term_var "inv")) ∗
          asn.formula (formula_secLeak (term_var "paddr")) ∗
        asn.formula (formula_propeq (term_var "result_mem_read") (term_union (memory_op_result bytes) KMemValue (term_var "mem_val"))) ∗
                                       asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "mem_val") (term_var "paddr" ↦ₘ[ bytes ] term_var "mem_val") ∗
          asn_cur_privilege (term_val ty_privilege Machine)(*  ∗ *)
          (* asn_pmp_entries (term_var "entries") *);
    |}.

  (* Access type `Write` needed here, as `mem_write_value` calls `pmp_mem_write` with this access type*)
  Definition sep_contract_mem_write_value {bytes} {H: restrict_bytes bytes} : SepContractFun (@mem_write_value bytes H) :=
    {| sep_contract_logic_variables := [(* "inv" :: ty.bool; *) "paddr" :: ty_xlenbits; "data" :: ty_bytes bytes(* ; "entries" :: ty.list ty_pmpentry *)];
      sep_contract_localstore      := [term_var "paddr"; term_var "data"];
      sep_contract_precondition    :=
        (* asn.match_bool (term_var "inv") *)
        (*   ((* asn_in_mmio bytes (term_var "paddr") ∗ *) *)
        (*    term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits))) (* ∗ *) *)
        (*    (* asn_inv_mmio bytes ∗ *) *)
        (*    (* asn_mmio_checked_write bytes (term_var "paddr") (term_var "data") *)) *)
          (∃ "mem_val", term_var "paddr" ↦ₘ[ bytes ] term_var "mem_val" ∗
           (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
           (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr)) ∗
        asn_cur_privilege (term_val ty_privilege Machine) (* ∗ *)
        (* asn_pmp_entries (term_var "entries") ∗ *)
        (* asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_val ty_privilege Machine) (term_val ty_access_type Write) *) ∗
        asn.chunk (chunk_user inv_leakage [env]) ∗
    asn.formula (formula_secLeak (term_var "paddr"));
      sep_contract_result          := "result_mem_write";
      sep_contract_postcondition   :=
        term_var "result_mem_write" = term_union (memory_op_result 1) KMemValue (term_val ty_byte [bv 1]) ∗
        (* asn.match_bool (term_var "inv") ⊤ *) (term_var "paddr" ↦ₘ[ bytes ] term_var "data") ∗
        asn_cur_privilege (term_val ty_privilege Machine) (* ∗ *)
        (* asn_pmp_entries (term_var "entries") *);
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
        (term_val ty.int (Z.of_N minAddr) <= paddr_int) ∗
          (term_binop bop.plus paddr_int (term_var "width")) <= term_val ty.int (Z.of_N maxAddr);
       sep_contract_result          := "result_within_phys_mem";
       sep_contract_postcondition   :=
         term_var "result_within_phys_mem" = term_val ty.bool true;
    |}.

  Definition sep_contract_execute_EBREAK : SepContractFun execute_EBREAK :=
    RiscvPmpExecutor.Symbolic.Statistics.extend_postcond_with_debug sep_contract_execute_EBREAK.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | rX                         => Some sep_contract_rX
      | wX                         => Some sep_contract_wX
      | fetch                      => Some sep_contract_fetch_instr
      | @mem_read bytes H          => Some (@sep_contract_mem_read bytes H)
      | @mem_write_value bytes H   => Some (@sep_contract_mem_write_value bytes H)
      | tick_pc                    => Some sep_contract_tick_pc
      (* | @pmpCheck bytes H          => Some (@sep_contract_pmpCheck bytes H) *)
      | within_phys_mem            => Some sep_contract_within_phys_mem
      (* | pmpMatchAddr               => Some sep_contract_pmpMatchAddr *)
      (* | @pmp_mem_read bytes H      => Some (@sep_contract_pmp_mem_read bytes H) *)
      (* | @pmp_mem_write bytes H     => Some (@sep_contract_pmp_mem_write bytes H) *)
      | @checked_mem_read bytes H  => Some (@sep_contract_checked_mem_read bytes H)
      | @checked_mem_write bytes H => Some (@sep_contract_checked_mem_write bytes H)
      | execute_EBREAK            => Some sep_contract_execute_EBREAK
      | _                         => None
      end.

  Lemma linted_cenv :
    forall Δ τ (f : Fun Δ τ),
      match CEnv f with
      | Some c => Linted c
      | None   => True
      end.
  Proof.
    intros ? ? []; try constructor.
  Qed.

  Definition sep_contract_read_ram {bytes} : SepContractFunX (read_ram bytes) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits; "ram_val" :: ty_bytes bytes];
       sep_contract_localstore      := [term_var "paddr"];
       sep_contract_precondition    :=
        asn.match_bool (term_var "inv")  (term_var "paddr" ↦ᵣ[ bytes ] term_var "ram_val") (term_var "paddr" ↦ₘ[ bytes ] term_var "ram_val");
       sep_contract_result          := "result_read_ram";
       sep_contract_postcondition   :=
        asn.match_bool (term_var "inv")
        (term_var "paddr" ↦ᵣ[ bytes ] term_var "ram_val") (term_var "paddr" ↦ₘ[ bytes ] term_var "ram_val") ∗
        asn.formula (formula_propeq (term_var "result_read_ram") (term_var "ram_val"));
    |}.

  Definition sep_contract_write_ram {bytes} : SepContractFunX (write_ram bytes) :=
    {| sep_contract_logic_variables := ["paddr" :: ty_word; "data" :: ty_bytes bytes];
       sep_contract_localstore      := [term_var "paddr"; term_var "data"];
       sep_contract_precondition    := ∃ "ram_val", (asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "ram_val"]));
       sep_contract_result          := "result_write_ram";
       sep_contract_postcondition   :=  term_var "paddr" ↦ₘ[ bytes ] term_var "data";
    |}.

  (* Note; we define the contract like tvhis, because it matches the PRE of `checked_mem_read` quite well*)
  (* Definition sep_contract_within_mmio `(H : restrict_bytes bytes) : SepContractFunX (within_mmio H) := *)
  (*   {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits]; *)
  (*       sep_contract_localstore      := [term_var "paddr"]; *)
  (*       sep_contract_precondition    := *)
  (*       asn.match_bool (term_var "inv") *)
  (*         (asn_in_mmio bytes (term_var "paddr") ∗ *)
  (*          term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits)))) *)
  (*         ((term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗ (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr)); *)
  (*       sep_contract_result          := "result_is_within"; *)
  (*       sep_contract_postcondition   := term_var "result_is_within" = term_var "inv" *)
  (*   |}. *)

  (* NOTE: No new contract for `read`, as femtokernel does not perform any reads for now *)
  (* NOTE: for now no resources in `POST`; add those once we need to reinstate local state *)
  (* NOTE: if overflow is important, a no-overflow statement can be added to the `asn_mmio_checked_write` resource *)
  (* Definition sep_contract_mmio_write (bytes : nat) {H: restrict_bytes bytes} : SepContractFunX (mmio_write H) := *)
  (*   {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "data" :: ty_bytes bytes]; *)
  (*       sep_contract_localstore      := [term_var "paddr"; term_var "data"]; *)
  (*       sep_contract_precondition    := *)
  (*          asn_in_mmio bytes (term_var "paddr") ∗ *)
  (*          asn_inv_mmio bytes ∗ *)
  (*          asn_mmio_checked_write bytes (term_var "paddr") (term_var "data"); *)
  (*       sep_contract_result          := "result_write_mmio"; *)
  (*       sep_contract_postcondition   := ⊤; *)
  (*   |}. *)

  Definition sep_contract_decode    : SepContractFunX decode :=
    {| sep_contract_logic_variables := ["code" :: ty_word; "instr" :: ty_ast];
       sep_contract_localstore      := [term_var "code"];
       sep_contract_precondition    := asn.chunk (chunk_user encodes_instr [term_var "code"; term_var "instr"]);
       sep_contract_result          := "result_decode";
       sep_contract_postcondition   := term_var "result_decode" = term_var "instr";
    |}.

  Definition sep_contract_leak    : SepContractFunX leak :=
    {| sep_contract_logic_variables := ["leak" :: ty_leak_event];
      sep_contract_localstore      := [term_var "leak"];
      sep_contract_precondition    := asn.chunk (chunk_user inv_leakage [env]) ∗
    asn.formula (formula_secLeak (term_var "leak"));
      sep_contract_result          := "result";
      sep_contract_postcondition   := ⊤;
    |}.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | read_ram bytes  => sep_contract_read_ram
      | write_ram bytes => sep_contract_write_ram
      (* | within_mmio res => sep_contract_within_mmio res *)
      (* | mmio_read bytes => sep_contract_mmio_read bytes *)
      (* | mmio_write res  => @sep_contract_mmio_write _ res *)
      | decode          => sep_contract_decode
      | leak            => sep_contract_leak
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
      lemma_postcondition   := ∃ "op", (asn.chunk (chunk_user (ptstomem bytes_per_word) [term_var "paddr"; term_var "op"]) ∗
                                          asn.chunk (chunk_user encodes_instr [term_var "op"; term_var "i"]) ∗
                                          asn.formula (formula_secLeak (term_var "op"))
                                       )
    |}.

  Definition lemma_close_ptsto_instr : SepLemma close_ptsto_instr :=
    {| lemma_logic_variables := ["paddr" :: ty_word; "cl" :: ty_word; "i" :: ty_ast];
       lemma_patterns        := [term_var "paddr"; term_var "cl"];
       lemma_precondition    := asn.chunk (chunk_user (ptstomem bytes_per_word) [term_var "paddr"; term_var "cl"]) ∗
                                  asn.chunk (chunk_user encodes_instr [term_var "cl"; term_var "i"]) ∗
                                  asn.formula (formula_secLeak (term_var "cl"));
       lemma_postcondition   := asn.chunk (chunk_user ptstoinstr [term_var "paddr"; term_var "i"]);
    |}.

  (* Definition lemma_extract_pmp_ptsto bytes : SepLemma (extract_pmp_ptsto bytes) := *)
  (*   {| lemma_logic_variables := ["paddr" :: ty_xlenbits]; *)
  (*      lemma_patterns        := [term_var "paddr"]; *)
  (*      lemma_precondition    := ⊤; *)
  (*      lemma_postcondition   := ⊤; *)
  (*   |}. *)

  (* Definition lemma_return_pmp_ptsto bytes : SepLemma (return_pmp_ptsto bytes) := *)
  (*   {| lemma_logic_variables := ["paddr" :: ty_xlenbits]; *)
  (*      lemma_patterns        := [term_var "paddr"]; *)
  (*      lemma_precondition    := ⊤; *)
  (*      lemma_postcondition   := ⊤; *)
  (*   |}. *)

  Definition map_wordwidth (w : WordWidth) : nat :=
    match w with
    | BYTE => 1
    | HALF => 2
    | WORD => 4 end.

  (* Use bounds Lemma to calculate bounds on truncation *)
  Local Lemma wordwidth_upper_bound widthh : IsTrue (map_wordwidth widthh * byte <=? bytes_per_word * byte)%nat.
  Proof. destruct widthh; now compute. Qed.
  Local Hint Resolve wordwidth_upper_bound : typeclass_instances.

  Import TermNotations.

  (* Definition lemma_close_mmio_write (immm : bv 12) (widthh : WordWidth): SepLemma (close_mmio_write immm widthh) := *)
  (*   {| lemma_logic_variables := ["paddr" :: ty_xlenbits; "w" :: ty_xlenbits]; *)
  (*      lemma_patterns        := [term_var "paddr"; term_var "w"]; *)
  (*      lemma_precondition    := *)
  (*       (term_val ty_xlenbits RiscvPmpIrisInstance.write_addr) = (term_var "paddr" +ᵇ term_sext (term_val (ty.bvec 12) immm)) ∗ *)
  (*       (term_var "w") = (term_val ty_xlenbits (bv.of_nat 42)); *)
  (*      lemma_postcondition   := *)
  (*       asn_mmio_checked_write (map_wordwidth widthh) (term_var "paddr" +ᵇ term_sext (term_val (ty.bvec 12) immm)) (term_truncate (map_wordwidth widthh * byte) (term_var "w")); *)
  (*   |}. *)

   Definition LEnv : LemmaEnv :=
     fun Δ l =>
       match l with
       | open_gprs                    => lemma_open_gprs
       | close_gprs                   => lemma_close_gprs
       | open_ptsto_instr             => lemma_open_ptsto_instr
       | close_ptsto_instr            => lemma_close_ptsto_instr
       (* | open_pmp_entries             => lemma_open_pmp_entries *)
       (* | close_pmp_entries            => lemma_close_pmp_entries *)
       (* | extract_pmp_ptsto bytes      => lemma_extract_pmp_ptsto bytes *)
       (* | return_pmp_ptsto bytes       => lemma_return_pmp_ptsto bytes *)
       (* | close_mmio_write immm widthh => lemma_close_mmio_write immm widthh *)
      end.
End RiscvPmpBlockVerifSpec.

Module RiscvPmpBlockVerifShalExecutor :=
  MakeShallowExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpProgram RiscvPmpBlockVerifSpec.
Module RiscvPmpBlockVerifExecutor :=
  MakeExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpProgram RiscvPmpBlockVerifSpec.

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

  Ltac symbolic_simpl :=
    apply validcontract_with_erasure_sound;
    vm_compute;
    constructor;
    cbn.

  Lemma valid_execute_rX : ValidContract rX.
  Proof.
    now vm_compute.
  Qed.

  Lemma valid_execute_wX : ValidContract wX.
  Proof. now vm_compute. Qed.

  (* Import SymProp.notations. *)
  (* Set Printing Depth 200. *)
  (* Eval vm_compute in (postprocess (RiscvPmpBlockVerifExecutor.SHeapSpecM.vcgen RiscvPmpBlockVerifExecutor.default_config 1 *)
  (*            sep_contract_fetch_instr (FunDef fetch))). *)

  Lemma valid_execute_fetch : ValidContract fetch.
  Proof. now vm_compute. Qed.

  (* Lemma valid_execute_fetch_instr : SMut.ValidContract sep_contract_fetch_instr (FunDef fetch). *)
  (* Proof. compute. Admitted. *)

  Lemma valid_execute_tick_pc : ValidContract tick_pc.
  Proof. now vm_compute. Qed.


  Import RiscvPmpBlockVerifExecutor.

  (* Definition test := (postprocess *)
  (*                       (SPureSpec.replay *)
  (*                          (postprocess (RiscvPmpBlockVerifExecutor.vcgen RiscvPmpBlockVerifExecutor.default_config 1 sep_contract_read fun_checked_read wnil)))). *)
  Import SymProp.notations.
  (* Eval vm_compute in test. *)

  Lemma valid_checked_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@checked_mem_read bytes H).
  Proof. destruct H; now vm_compute. Qed.

  Lemma valid_checked_mem_write {bytes} {H : restrict_bytes bytes} : ValidContract (@checked_mem_write bytes H).
  Proof. destruct H; now vm_compute. Qed.

  (* Lemma valid_pmp_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@pmp_mem_read bytes H). *)
  (* Proof. destruct H; now vm_compute. Qed. *)

  (* Lemma valid_pmp_mem_write {bytes} {H : restrict_bytes bytes} : ValidContract (@pmp_mem_write bytes H). *)
  (* Proof. destruct H; now vm_compute. Qed. *)

  Import Bitvector.bv.notations.

  (* Lemma valid_pmpMatchAddr : ValidContractDebug pmpMatchAddr. *)
  (* Proof. *)
  (*   symbolic_simpl. *)
  (*   intros; split; intros; bv_comp; auto. *)
  (*   destruct (v + v0 <=ᵘ? v1)%bv eqn:?; bv_comp; auto. *)
  (* Qed. *)

  (* Lemma valid_pmpCheck {bytes : nat} {H : restrict_bytes bytes} : ValidContractWithFuelDebug 4 (@pmpCheck bytes H). *)
  (* Proof. *)
  (*   destruct H; apply verification_condition_with_erasure_sound; vm_compute; *)
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

  Lemma valid_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@mem_read bytes H).
  Proof. destruct H; now vm_compute. Qed.

  Lemma valid_mem_write_value {bytes} {H : restrict_bytes bytes} : ValidContract (@mem_write_value bytes H).
  Proof. destruct H; now vm_compute. Qed.

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
    now rewrite Hcenv in Hvc.
  Qed.

  Lemma valid_contract_debug : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContractDebug f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContractDebug in Hvc.
    now rewrite Hcenv in Hvc.
  Qed.

  Lemma ValidContracts : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros.
    destruct f; try discriminate H; eexists.
    - refine (valid_contract _ H valid_execute_rX).
    - refine (valid_contract _ H valid_execute_wX).
    - refine (valid_contract _ H valid_execute_tick_pc).
    - refine (valid_contract_debug _ H valid_contract_within_phys_mem).
    - refine (valid_contract _ H valid_mem_read).
    - refine (valid_contract _ H valid_checked_mem_read).
    - refine (valid_contract _ H valid_checked_mem_write).
    (* - refine (valid_contract _ H valid_pmp_mem_read). *)
    (* - refine (valid_contract _ H valid_pmp_mem_write). *)
    (* - refine (valid_contract_with_fuel_debug _ _ H valid_pmpCheck). *)
    (* - refine (valid_contract_debug _ H valid_pmpMatchAddr). *)
    - refine (valid_contract _ H valid_mem_write_value).
    - refine (valid_contract _ H valid_execute_fetch).
    - refine (valid_contract_debug _ H valid_contract_execute_EBREAK).
  Qed.
End RiscvPmpSpecVerif.

Module RiscvPmpIrisInstanceWithContracts.
  Include ProgramLogicOn RiscvPmpBase RiscvPmpSignature RiscvPmpProgram
    RiscvPmpBlockVerifSpec.
  Include IrisInstanceWithContracts2 RiscvPmpBase RiscvPmpSignature
    RiscvPmpProgram RiscvPmpSemantics RiscvPmpBlockVerifSpec RiscvPmpIrisBase2
    (* RiscvPmpIrisAdeqParameters *) RiscvPmpIrisAdeqParams2
    RiscvPmpIrisInstance2.
  Include MicroSail.ShallowSoundness.Soundness RiscvPmpBase RiscvPmpSignature
    RiscvPmpProgram RiscvPmpBlockVerifSpec RiscvPmpBlockVerifShalExecutor.
  Include MicroSail.RefineExecutor.RefineExecOn RiscvPmpBase RiscvPmpSignature
    RiscvPmpProgram RiscvPmpBlockVerifSpec RiscvPmpBlockVerifShalExecutor
    RiscvPmpBlockVerifExecutor.

  Import RiscvPmpIrisBase2.
  Import RiscvPmpIrisInstance2.
  Import RiscvPmp.Model.

  Import iris.bi.interface.
  Import iris.bi.big_op.
  Import iris.base_logic.lib.iprop.
  Import iris.program_logic.weakestpre.
  Import iris.program_logic.total_weakestpre.
  Import iris.base_logic.lib.gen_heap.
  Import iris.proofmode.string_ident.
  Import iris.proofmode.tactics.

  Lemma read_ram_sound `{sailGS2 Σ} {bytes} :
    ValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_read_ram (read_ram bytes).
  Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι.
      iIntros "H". cbn in *. iApply semWP2_foreign. unfold mem_inv2.
      iIntros (? ? ? ?) "((Hregs1 & Hregs2) & ((%memmapL & HmemL & %HmapL & HtrL & HltrL) & (%memmapR & HmemR & %HmapR & HtrR & HltrR)))".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (resL ? ? resR ? ? Hf).
      rewrite evalValsProjLeftIsProjLeftEvals in Hf. rewrite evalValsProjRightIsProjRightEvals in Hf.
      rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
      inversion H0; inversion H1; subst. clear H0 H1 Hf. do 3 iModIntro.
      iMod "Hclose" as "_". destruct inv.
      { cbn. destruct v.
        - (* readonly case *)
        iDestruct "H" as "#H".
         iInv "H" as "Hptsto" "Hclose_ptsto".
        iDestruct "Hptsto" as "(HptstoL & HptstoR)".
        iDestruct (bi.later_mono _ _ (RiscvPmpModel2.fun_read_ram_works (sg := sailGS2_sailGS_left) HmapL) with "[$HptstoL $HmemL]") as "#>%eq_fun_read_ramL".
        iDestruct (bi.later_mono _ _ (RiscvPmpModel2.fun_read_ram_works (sg := sailGS2_sailGS_right) HmapR) with "[$HptstoR $HmemR]") as "#>%eq_fun_read_ramR".
        iMod ("Hclose_ptsto" with "[$HptstoL $HptstoR]") as "_".
        iFrame "Hregs1 Hregs2 HmemL HmemR HtrL HltrL HtrR HltrR".
        iSplitR; first auto.
        iApply semWP2_val. do 2 iModIntro.
        iExists δ. iSplitR; first auto.
        destruct ram_val.
        + iExists (SyncVal (fun_read_ram μ1 bytes (ty.projLeft paddr))). iSplitR; first by rewrite eq_fun_read_ramR.
          iFrame "H".
          iSplitR; try auto.
          iSplitR; first auto.
          by rewrite eq_fun_read_ramL.
          auto. (* TODO: How to dispatch emp goal, also several admits for this below *)
        + iExists (NonSyncVal (fun_read_ram μ1 bytes (ty.projLeft paddr)) (fun_read_ram μ2 bytes (ty.projRight paddr))). iSplitR; first by rewrite eq_fun_read_ramR.
          iFrame "H".
          iSplitR; try auto.
          iSplitR; first auto.
          by rewrite eq_fun_read_ramL eq_fun_read_ramR.
          auto.
      - (* old case *)
        iModIntro.
        iDestruct "H" as "(HL & HR)".
        iPoseProof (RiscvPmpModel2.fun_read_ram_works (sg := sailGS2_sailGS_left) HmapL with "[$HL $HmemL]") as "%eq_fun_read_ramL".
        iPoseProof (RiscvPmpModel2.fun_read_ram_works (sg := sailGS2_sailGS_right) HmapR with "[$HR $HmemR]") as "%eq_fun_read_ramR".
        iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_left) $! HmapL with "HmemL HtrL HltrL") as "HmemL".
        iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_right) $! HmapR with "HmemR HtrR HltrR") as "HmemR".
        iFrame "Hregs1 Hregs2 HmemL HmemR". iApply semWP2_val.
        iFrame "HL". iFrame "HR".
        iExists δ. iModIntro. iSplitR; first auto.
        destruct ram_val.
        + iExists (SyncVal (fun_read_ram μ1 bytes (ty.projLeft paddr))).
          iSplitR; first by rewrite eq_fun_read_ramR.
          iSplitR; try auto.
          iSplitR; first by rewrite eq_fun_read_ramL.
          auto.
        + iExists (NonSyncVal (fun_read_ram μ1 bytes (ty.projLeft paddr)) (fun_read_ram μ2 bytes (ty.projRight paddr))). iSplitR; first by rewrite eq_fun_read_ramR.
          iSplitR; try auto.
          iSplitR; first auto.
          by rewrite eq_fun_read_ramL eq_fun_read_ramR.
          auto.
      }
      cbn. iDestruct "H" as "%". contradiction.
  Qed.

  Lemma write_ram_sound `{sailGS2 Σ} {bytes} :
    ValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_write_ram (write_ram bytes).
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "[%w (HL & HR)]". iApply semWP2_foreign.
    iIntros (? ? ? ?) "((Hregs1 & Hregs2) & ((%memmapL & HmemL & %HmapL & HtrL) & (%memmapR & HmemR & %HmapR & HtrR)))".
    iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
    iIntros (res1 ? ? res2 ? ? Hf).
    rewrite evalValsProjLeftIsProjLeftEvals in Hf. rewrite evalValsProjRightIsProjRightEvals in Hf.
    rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
    inversion H0; inversion H1; subst. clear H0 H1 Hf. do 3 iModIntro.
    iMod "Hclose" as "_".
    iMod (RiscvPmpModel2.fun_write_ram_works (sg := sailGS2_sailGS_left) with "[$HL $HmemL $HtrL]") as "[$ HL]"; auto.
    iMod (RiscvPmpModel2.fun_write_ram_works (sg := sailGS2_sailGS_right) with "[$HR $HmemR $HtrR]") as "[$ HR]"; auto.
    rewrite semWP2_val. iFrame "Hregs1 Hregs2".
    iExists δ. iSplitR; first auto.
    iExists (SyncVal true). iSplitR; first auto. by iFrame "HL HR".
 Qed.

  (* Important sanity condition on mmio predicates - NOTE: could be in typeclass, together with the condition that reads are either all accepted, or none of them are *)
  Lemma mmio_pred_cons {bytes : nat} t e: event_pred bytes e → mmio_pred bytes t → mmio_pred bytes (cons e t).
  Proof. now apply List.Forall_cons. Qed.

  (* Lemma mmio_write_sound `{!sailGS Σ} `(H: restrict_bytes bytes) : *)
  (*   TValidContractForeign (@RiscvPmpBlockVerifSpec.sep_contract_mmio_write _ H) (mmio_write H). *)
  (* Proof. *)
  (*   intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *. *)
  (*   iIntros "([%Hmmio _] & #Hinv & [-> ->])". iApply semTWP_foreign. *)
  (*   iIntros (? ?) "[Hregs [% (Hmem & %Hmap & Htr)]]". *)
  (*   iInv "Hinv" as (t) " [>Htrf >%Hpred]" "Hclose". *)
  (*   iDestruct (trace.trace_full_frag_eq with "Htr Htrf") as "%Heqt". subst t. *)
  (*   iMod (trace.trace_update _ _ (cons _ _) with "[$Htr $Htrf]") as "[Htr Htrf]". *)
  (*   iMod ("Hclose" with "[Htrf]") as "_". *)
  (*   {(* Instantiate evars *) *)
  (*     iExists _; iFrame. iPureIntro. *)
  (*     apply mmio_pred_cons; [|eauto]. *)
  (*     constructor. } *)
  (*   iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro. *)
  (*   iIntros (res ? ? Hf). rewrite Heq in Hf. cbn in Hf. inversion Hf; subst. *)
  (*   iMod "Hclose" as "_". rewrite semTWP_val. *)
  (*   destruct bytes; first contradiction. *)
  (*   unfold mem_inv, fun_write_mmio; cbn. *)
  (*   now iFrame "Hregs Hmem Htr". *)
  (* Qed. *)

  Lemma decode_sound `{sailGS2 Σ} :
    ValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_decode RiscvPmpProgram.decode.
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "%Hdecode". iApply semWP2_foreign.
    iIntros (? ? ? ?) "((Hregs1 & Hregs2) & ((%memmapL & HmemL & %HmapL & HtrL & HltrL) & (%memmapR & HmemR & %HmapR & HtrR & HltrR)))".
    iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
    iIntros (res1 ? ? res2 ? ? Hf).
    rewrite evalValsProjLeftIsProjLeftEvals in Hf. rewrite evalValsProjRightIsProjRightEvals in Hf.
    rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
    inversion H0; inversion H1; subst. clear H0 H1 Hf. do 3 iModIntro.
    iMod "Hclose" as "_".
    iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_left) $! HmapL with "HmemL HtrL HltrL") as "HmemL".
    iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_right) $! HmapR with "HmemR HtrR HltrR") as "HmemR".
    iFrame "Hregs1 Hregs2 HmemL HmemR".
    destruct code; destruct instr; cbn in *;
    destruct (pure_decode _); inversion Hdecode.
    + rewrite semWP2_val.
      iExists δ. iSplitR; first auto. iExists (SyncVal v0). auto.
    + destruct (pure_decode); inversion Hdecode.
      rewrite semWP2_val.
      iExists δ. iSplitR; first auto. iExists (NonSyncVal v1 v2). auto.
  Qed.

  (* Lemma within_mmio_sound `{!sailGS Σ} `(H: restrict_bytes bytes): *)
  (*   TValidContractForeign (RiscvPmpBlockVerifSpec.sep_contract_within_mmio H) (RiscvPmpProgram.within_mmio H). *)
  (* Proof. *)
  (*   intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *. *)
  (*   iIntros "Hpre". iApply semTWP_foreign. *)
  (*   iIntros (? ?) "(Hregs & Hmem)". *)
  (*   iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro. *)
  (*   iIntros (? ? ? Hf). rewrite Heq in Hf. cbn in Hf. inversion Hf; subst. *)
  (*   rewrite semTWP_val. iMod "Hclose" as "_". iFrame "Hregs Hmem". *)
  (*   repeat iModIntro. *)
  (*   rewrite /fun_within_mmio bool_decide_and. *)
  (*   destruct inv; cbn; iDestruct "Hpre" as "([%Hlft _] & [%Hrght _])". *)
  (*   - iPureIntro; repeat split; auto. *)
  (*     rewrite -bool_decide_and bool_decide_true //. *)
  (*     split; [auto| solve_bv]. *)
  (*   - iPureIntro; repeat split; auto. *)
  (*     assert (bool_decide (withinMMIO paddr bytes) = false) as ->. *)
  (*     { rewrite bool_decide_eq_false. *)
  (*       destruct bytes; first easy. *)
  (*       assert (paddr ∈ liveAddrs)%stdpp. *)
  (*       { apply bv.in_seqBv. *)
  (*         - change (bv.of_N minAddr) with (@bv.zero xlenbits); cbn. (* TODO: add simplifying `xlenbits` to solve_bv *) solve_bv. *)
  (*         - rewrite N2Z.inj_add in Hrght. *)
  (*           change minAddr with 0%N in *; cbn in *. *)
  (*           assert (bv.unsigned paddr < Z.of_N lenAddr)%Z by Lia.lia. cbn. *)
  (*           cbv [bv.ult]. now zify. (* `solve_bv` fails because knowledge of concrete `minAddr`, `lenAddr` needed *)} *)
  (*       intros HFalse; cbn in HFalse. *)
  (*       assert (paddr ∈ mmioAddrs)%stdpp by (destruct bytes; intuition). *)
  (*       eapply mmio_ram_False; eauto. *)
  (*     } *)
  (*     auto. *)
  (* Qed. *)

    Lemma leak_sound `{sailGS2 Σ} :
    ValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_leak RiscvPmpProgram.leak.
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "(Hinv & %HsL & _)". iApply semWP2_foreign.
    iIntros (? ? ? ?) "((Hregs1 & Hregs2) & ((%memmapL & HmemL & %HmapL & HtrL & HltrL) & (%memmapR & HmemR & %HmapR & HtrR & HltrR)))".
    iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
    iIntros (res1 ? ? res2 ? ? Hf).
    rewrite evalValsProjLeftIsProjLeftEvals in Hf. rewrite evalValsProjRightIsProjRightEvals in Hf.
    rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
    inversion H0; inversion H1; subst. clear H0 H1 Hf. do 3 iModIntro.
    iMod "Hclose" as "_".
    iInv "Hinv" as (t) " [>HltrfL >HltrfR]" "Hclose".
    iPoseProof (trace.trace_full_frag_eq with "HltrL HltrfL") as "%eqL".
    iPoseProof (trace.trace_full_frag_eq with "HltrR HltrfR") as "%eqR".
    cbn. subst t.
    rewrite eqR.
    iMod (trace.trace_update _ _ (cons _ _) with "[$HltrL $HltrfL]") as "[HltrL HltrfL]".
    iMod (trace.trace_update _ _ (cons _ _) with "[$HltrR $HltrfR]") as "[HltrR HltrfR]".
    iMod ("Hclose" with "[$HltrfL $HltrfR]") as "_".
    iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_left) (fun_leak μ1 (ty.projLeft leak0)) $! HmapL with "HmemL HtrL HltrL") as "HmemL".
    rewrite <- eqR.
    iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_right) (fun_leak μ2 (ty.projLeft leak0)) $! HmapR with "HmemR HtrR HltrR") as "HmemR".
    apply secLeakOtherDef in HsL. rewrite HsL. cbn.
    iFrame "Hregs1 Hregs2 HmemL HmemR".
    rewrite semWP2_val.
    iExists δ. iSplitR; first auto. iExists (SyncVal tt). auto.
  Qed.

  Lemma foreignSemBlockVerif `{sailGS2 Σ} : ForeignSem.
    intros Δ τ f; destruct f;
        eauto using read_ram_sound, write_ram_sound, (* RiscvPmpModel2.mmio_read_sound, mmio_write_sound, within_mmio_sound, *) decode_sound, leak_sound.
  Qed.

  (* Lemma foreignSemBlockVerif `{sailGS Σ} : ForeignSem. *)
  (* Proof. apply (TForeignSem_ForeignSem TforeignSemBlockVerif). Qed. *)

  Ltac destruct_syminstance ι :=
    repeat
      match type of ι with
      | Env _ (ctx.snoc _ (MkB ?s _)) =>
          string_to_ident_cps s
            ltac:(fun id =>
                    let fr := fresh id in
                    destruct (env.view ι) as [ι fr];
                    destruct_syminstance ι)
      | Env _ ctx.nil => destruct (env.view ι)
      | _ => idtac
      end.

  Lemma open_ptsto_instr_sound `{sailGS2 Σ} :
    ValidLemma RiscvPmpBlockVerifSpec.lemma_open_ptsto_instr.
  Proof.
    intros ι; destruct_syminstance ι; cbn.
    iIntros "[%op (Hptsto & Henc & HsL )]".
    iExists op.
    now iFrame.
  Qed.

  Lemma close_ptsto_instr_sound `{sailGS2 Σ} :
    ValidLemma RiscvPmpBlockVerifSpec.lemma_close_ptsto_instr.
  Proof.
    intros ι; destruct_syminstance ι; cbn.
    iIntros "(Hptsto & Henc & HsL & _)".
    iExists cl.
    now iFrame.
  Qed.

  (* Lemma close_mmio_write_sound `{sailGS Σ} (imm : bv 12) (width : WordWidth): *)
  (*   ValidLemma (RiscvPmpBlockVerifSpec.lemma_close_mmio_write imm width). *)
  (* Proof. *)
  (*   intros ι; destruct_syminstance ι; cbn. *)
  (*   iIntros "([<- _] & [-> _])". *)
  (*   unfold interp_mmio_checked_write. *)
  (*   iPureIntro. *)
  (*   split; auto. *)
  (*   destruct width; now compute. *)
  (* Qed. *)

  Lemma lemSemBlockVerif `{sailGS2 Σ} : LemmaSem.
  Proof.
    intros Δ []; intros ι; destruct_syminstance ι; try now iIntros "_".
    (* - apply Model.RiscvPmpModel2.open_pmp_entries_sound. *)
    (* - apply Model.RiscvPmpModel2.close_pmp_entries_sound. *)
    - apply open_ptsto_instr_sound.
    - apply close_ptsto_instr_sound.
    (* - apply close_mmio_write_sound. *)
  Qed.

  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifExecutor.Symbolic.

  (* Lemma TcontractsSound `{sailGS Σ} : ⊢ TValidContractEnvSem RiscvPmpBlockVerifSpec.CEnv. *)
  (* Proof. *)
  (*   apply (tsound TforeignSemBlockVerif lemSemBlockVerif). *)
  (*   intros Γ τ f c Heq. *)
  (*   pose proof (RiscvPmpSpecVerif.ValidContracts f Heq) as [fuel Hvc]. *)
  (*   eapply shallow_vcgen_fuel_soundness, symbolic_vcgen_fuel_soundness. *)
  (*   eauto. *)
  (* Qed. *)

  (* TODO: prove this lemma as: apply (TValidContractEnvSem_ValidContractEnvSem TcontractsSound). *)
  Lemma contractsSound `{sailGS2 Σ} : ⊢ ValidContractEnvSem RiscvPmpBlockVerifSpec.CEnv.
  Proof.
    apply (sound foreignSemBlockVerif lemSemBlockVerif).
    intros Γ τ f c Heq.
    pose proof (RiscvPmpSpecVerif.ValidContracts f Heq) as [fuel Hvc].
    eapply shallow_vcgen_fuel_soundness, symbolic_vcgen_fuel_soundness.
    eauto.
  Qed.

End RiscvPmpIrisInstanceWithContracts.
