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
     ⊥))))))).

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

  Definition sep_contract_decode    : SepContractFunX decode :=
    {| sep_contract_logic_variables := ["code" :: ty_word; "instr" :: ty_ast];
       sep_contract_localstore      := [term_var "code"];
       sep_contract_precondition    := asn.chunk (chunk_user encodes_instr [term_var "code"; term_var "instr"]);
       sep_contract_result          := "result_decode";
       sep_contract_postcondition   := term_var "result_decode" = term_var "instr";
    |}.

  #[program] Definition sep_contract_vector_subrange {n} (e b : nat) {p : IsTrue (0 <=? b)%nat} {q : IsTrue (b <=? e)%nat} {r : IsTrue (e <? n)%nat} : SepContractFunX (@vector_subrange n e b p q r) :=
    {| sep_contract_logic_variables := ["v" :: ty.bvec n];
       sep_contract_localstore      := [term_var "v"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result_vector_subrange";
       sep_contract_postcondition   :=
         term_var "result_vector_subrange" = @term_vector_subrange _ _ b (e - b + 1) _ (term_var "v");
    |}.
  Next Obligation. intros; now apply convert_foreign_vector_subrange_conditions. Defined.
  #[global] Arguments sep_contract_vector_subrange {_} _ _ {_ _ _}.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | read_ram bytes  => sep_contract_read_ram
      | write_ram bytes => sep_contract_write_ram
      | decode    => sep_contract_decode
      | vector_subrange e b => sep_contract_vector_subrange e b
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
  Import Katamaran.Bitvector.
  Import bv.notations.

  Ltac bv_comp :=
    repeat match goal with
      | H: (?a <ᵘ? ?b) = true |- _ =>
          rewrite bv.ultb_ult in H
      | H: (?a <ᵘ? ?b) = false |- _ =>
          rewrite bv.ultb_uge in H
      | H: (?a <=ᵘ? ?b) = true |- _ =>
          rewrite bv.uleb_ule in H
      | H: (?a <=ᵘ? ?b) = false |- _ =>
          rewrite bv.uleb_ugt in H
      | H: (?P || ?Q)%bool = true |- _ =>
          apply Bool.orb_true_iff in H as [?|?]
      end.

  Ltac bv_comp_bool :=
    repeat match goal with
      | H: ?a <ᵘ ?b |- _ =>
          rewrite ? (proj2 (bv.ultb_ult _ _) H),
            ? (proj2 (bv.uleb_ugt _ _) H);
          clear H
      | H: ?a <=ᵘ ?b |- _ =>
          rewrite ? (proj2 (bv.uleb_ule _ _) H),
            ? (proj2 (bv.ultb_uge _ _) H);
          clear H
      | H: ?a <=ᵘ ?b /\ _ |- _ =>
          destruct H
      | H: ?a <ᵘ ?b /\ _ |- _ =>
          destruct H
      end.

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

  Lemma valid_pmpMatchAddr : ValidContractDebug pmpMatchAddr.
  Proof.
    symbolic_simpl.
    intros; split; intros; bv_comp; auto.
    destruct (v + v0 <=ᵘ? v1)%bv eqn:?; bv_comp; auto.
  Qed.

  Opaque pmp_get_perms.

  Lemma Pmp_access_inversion : forall addr bytes cfg0 addr0 cfg1 addr1 acc,
      Pmp_access addr bytes [(cfg0 , addr0); (cfg1, addr1)]%list Machine acc ->
         (A cfg0 = OFF /\ A cfg1 = OFF)
      \/ (A cfg0 = OFF /\ A cfg1 = TOR /\ addr1 <ᵘ addr0)
      \/ (A cfg0 = OFF /\ A cfg1 = TOR /\ addr0 <=ᵘ addr1 /\ addr + bytes <=ᵘ addr0)
      \/ (A cfg0 = OFF /\ A cfg1 = TOR /\ addr0 <=ᵘ addr1 /\ addr0 <ᵘ addr + bytes /\ addr1 <=ᵘ addr)
      \/ (A cfg0 = OFF /\ A cfg1 = TOR /\ addr0 <=ᵘ addr1 /\ addr0 <ᵘ addr + bytes /\ addr <ᵘ addr1 /\ addr0 <=ᵘ addr /\ addr + bytes <=ᵘ addr1 /\ Access_pmp_perm acc (pmp_get_perms cfg1 Machine))
      \/ (A cfg0 = TOR /\ A cfg1 = OFF /\ addr0 <ᵘ [bv 0x0])
      \/ (A cfg0 = TOR /\ A cfg1 = OFF /\ [bv 0x0] <=ᵘ addr0 /\ addr + bytes <=ᵘ [bv 0x0])
      \/ (A cfg0 = TOR /\ A cfg1 = OFF /\ [bv 0x0] <=ᵘ addr0 /\ [bv 0x0] <ᵘ addr + bytes /\ addr0 <=ᵘ addr)
      \/ (A cfg0 = TOR /\ A cfg1 = OFF /\ [bv 0x0] <=ᵘ addr0 /\ [bv 0x0] <ᵘ addr + bytes /\ addr <ᵘ addr0 /\ [bv 0x0] <=ᵘ addr /\ addr + bytes <=ᵘ addr0 /\ Access_pmp_perm acc (pmp_get_perms cfg0 Machine))
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ addr0 <ᵘ [bv 0x0] /\ addr1 <ᵘ addr0)
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ addr0 <ᵘ [bv 0x0] /\ addr0 <=ᵘ addr1 /\ addr + bytes <=ᵘ addr0)
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ addr0 <ᵘ [bv 0x0] /\ addr0 <=ᵘ addr1 /\ addr0 <ᵘ addr + bytes /\ addr1 <=ᵘ addr)
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ addr0 <ᵘ [bv 0x0] /\ addr0 <=ᵘ addr1 /\ addr0 <ᵘ addr + bytes /\ addr <ᵘ addr1 /\ addr0 <=ᵘ addr /\addr + bytes <=ᵘ addr1 /\ Access_pmp_perm acc (pmp_get_perms cfg1 Machine))
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ [bv 0x0] <=ᵘ addr0 /\ addr + bytes <=ᵘ [bv 0x0] /\ addr1 <ᵘ addr0)
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ [bv 0x0] <=ᵘ addr0 /\ addr + bytes <=ᵘ [bv 0x0] /\ addr0 <=ᵘ addr1 /\ addr + bytes <=ᵘ addr0)
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ [bv 0x0] <=ᵘ addr0 /\ addr + bytes <=ᵘ [bv 0x0] /\ addr0 <=ᵘ addr1 /\ addr0 <ᵘ addr + bytes /\ addr1 <=ᵘ addr)
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ [bv 0x0] <=ᵘ addr0 /\ addr + bytes <=ᵘ [bv 0x0] /\ addr0 <=ᵘ addr1 /\ addr0 <ᵘ addr + bytes /\ addr <ᵘ addr1 /\ addr0 <=ᵘ addr /\ addr + bytes <=ᵘ addr1 /\ Access_pmp_perm acc (pmp_get_perms cfg1 Machine))
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ [bv 0x0] <=ᵘ addr0 /\ [bv 0x0] <ᵘ addr + bytes /\ addr0 <=ᵘ addr /\ addr0 <=ᵘ addr1 /\ addr + bytes <=ᵘ addr0)
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ [bv 0x0] <=ᵘ addr0 /\ [bv 0x0] <ᵘ addr + bytes /\ addr0 <=ᵘ addr /\ addr0 <=ᵘ addr1 /\ addr0 <ᵘ addr + bytes /\ addr1 <=ᵘ addr)
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ [bv 0x0] <=ᵘ addr0 /\ [bv 0x0] <ᵘ addr + bytes /\ addr0 <=ᵘ addr /\ addr0 <=ᵘ addr1 /\ addr0 <ᵘ addr + bytes /\ addr <ᵘ addr1 /\ addr + bytes <=ᵘ addr1 /\ Access_pmp_perm acc (pmp_get_perms cfg1 Machine))
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ [bv 0x0] <=ᵘ addr0 /\ [bv 0x0] <ᵘ addr + bytes /\ addr <ᵘ addr0 /\ [bv 0x0] <=ᵘ addr /\ addr + bytes <=ᵘ addr0 /\ Access_pmp_perm acc (pmp_get_perms cfg0 Machine))
      \/ (A cfg0 = TOR /\ A cfg1 = TOR /\ [bv 0x0] <=ᵘ addr0 /\ [bv 0x0] <ᵘ addr + bytes /\ addr0 <=ᵘ addr /\ addr1 <ᵘ addr0).
  Proof.
    intros addr bytes [? [] ? ? ?] addr0 [? [] ? ? ?] addr1 acc;
      unfold Pmp_access, decide_pmp_access, check_pmp_access, pmp_check, pmp_match_entry,
             pmp_match_addr, pmp_addr_range;
      simpl;
      intros H.
    - left; auto.
    - destruct (addr1 <ᵘ? addr0) eqn:?; bv_comp; auto.
      destruct (addr + bytes <=ᵘ? addr0) eqn:?; bv_comp; simpl in H.
      right; right; left; auto.
      destruct (addr1 <=ᵘ? addr) eqn:?; bv_comp.
      right; right; right; left; auto.
      destruct (addr0 <=ᵘ? addr) eqn:?; bv_comp.
      destruct (addr + bytes <=ᵘ? addr1) eqn:?; bv_comp.
      simpl in H.
      right; right; right; right; left; repeat (split; auto).
      rewrite Bool.andb_false_r in H; inversion H.
      rewrite Bool.andb_false_l in H; inversion H.
    - destruct (addr0 <ᵘ? [bv 0x0]) eqn:?; bv_comp.
      right; right; right; right; right; left; repeat (split; auto).
      destruct (addr + bytes <=ᵘ? [bv 0x0]) eqn:?; bv_comp.
      simpl in H.
      right; right; right; right; right; right; left; repeat (split; auto).
      destruct (addr0 <=ᵘ? addr) eqn:?; bv_comp.
      simpl in H.
      right; right; right; right; right; right; right; left; repeat (split; auto).
      simpl in H.
      destruct ([bv 0x0] <=ᵘ? addr) eqn:?; bv_comp.
      destruct (addr + bytes <=ᵘ? addr0) eqn:?; bv_comp.
      simpl in H.
      right; right; right; right; right; right; right; right; left; repeat (split; auto).
      rewrite Bool.andb_false_r in H; inversion H.
      rewrite Bool.andb_false_l in H; inversion H.
    - destruct (addr0 <ᵘ? [bv 0x0]) eqn:?; bv_comp.
      destruct (addr1 <ᵘ? addr0) eqn:?; bv_comp.
      right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      destruct (addr + bytes <=ᵘ? addr0) eqn:?; bv_comp.
      simpl in H.
      right; right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      destruct (addr1 <=ᵘ? addr) eqn:?; bv_comp.
      simpl in H.
      right; right; right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      simpl in H.
      destruct (addr0 <=ᵘ? addr) eqn:?; bv_comp.
      destruct (addr + bytes <=ᵘ? addr1) eqn:?; bv_comp.
      simpl in H.
      right; right; right; right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      rewrite Bool.andb_false_r in H; inversion H.
      rewrite Bool.andb_false_l in H; inversion H.
      destruct (addr + bytes <=ᵘ? [bv 0x0]) eqn:?; bv_comp.
      simpl in H.
      destruct (addr1 <ᵘ? addr0) eqn:?; bv_comp.
      do 4 right; right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      destruct (addr + bytes <=ᵘ? addr0) eqn:?; bv_comp.
      simpl in H.
      do 4 right; right; right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      destruct (addr1 <=ᵘ? addr) eqn:?; bv_comp.
      simpl in H.
      do 4 right; right; right; right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      simpl in H.
      destruct (addr0 <=ᵘ? addr) eqn:?; bv_comp.
      destruct (addr + bytes <=ᵘ? addr1) eqn:?; bv_comp.
      simpl in H.
      do 4 right; right; right; right; right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      rewrite Bool.andb_false_r in H; inversion H.
      rewrite Bool.andb_false_l in H; inversion H.
      destruct (addr0 <=ᵘ? addr) eqn:?; bv_comp.
      simpl in H.
      destruct (addr1 <ᵘ? addr0) eqn:?; bv_comp.
      do 5 right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; repeat (split; auto).
      destruct (addr + bytes <=ᵘ? addr0) eqn:?; bv_comp.
      simpl in H.
      do 4 right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      destruct (addr1 <=ᵘ? addr) eqn:?; bv_comp.
      simpl in H.
      do 4 right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      simpl in H.
      destruct (addr + bytes <=ᵘ? addr1) eqn:?; bv_comp.
      do 4 right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      inversion H.
      simpl in H.
      destruct ([bv 0x0] <=ᵘ? addr) eqn:?; bv_comp.
      destruct (addr + bytes <=ᵘ? addr0) eqn:?; bv_comp.
      simpl in H.
      do 4 right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; repeat (split; auto).
      rewrite Bool.andb_false_r in H; inversion H.
      rewrite Bool.andb_false_l in H; inversion H.
  Qed.

  Transparent pmp_get_perms.

  Lemma valid_pmpCheck {bytes : nat} {H : restrict_bytes bytes} : ValidContractWithFuelDebug 4 (@pmpCheck bytes H).
  Proof.
    (* update: Pmp_access not defined in a way that makes it easy to destruct here... *)
    destruct H as [-> |[-> | ->]];
    (* Set Printing Depth 200. *)
    hnf; apply verification_condition_with_erasure_sound; vm_compute;
    constructor; cbn;
    intros paddr acc addr0 addr1 L0 A0 X0 W0 R0 L1 A1 X1 W1 R1;
    repeat try split; intros; subst; intros;
      repeat
        match goal with
        | H: Pmp_access ?a ?b ?es Machine ?acc |- _ =>
            apply Pmp_access_inversion in H;
            simpl in H
        | H: (?b1 || ?b2)%bool = true |- _ =>
            apply Bool.orb_true_iff in H
        | H: ?P /\ ?Q |- _ =>
            destruct H
        | H: ?P \/ ?Q |- _ =>
            destruct H as [H|H]
        | H: negb ?b = true |- _ =>
            apply Bool.negb_true_iff in H;
            subst
        | H1: ?a <=ᵘ ?b, H2: ?b <ᵘ ?a |- False =>
            unfold bv.ult, bv.ule in *; apply N.le_ngt in H1; apply (H1 H2)
        end;
      bv_comp;
      unfold Access_pmp_perm, decide_access_pmp_perm in *;
      try discriminate.
    all: try destruct X1; try destruct W1; try destruct R1; try destruct X0; try destruct W0; try destruct R0; try discriminate.
  Qed.

  Lemma valid_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@mem_read bytes H).
  Proof.
    destruct H as [->|[->| ->]]; reflexivity.
  Qed.

  Lemma valid_contract_within_phys_mem : ValidContractDebug within_phys_mem.
  Proof. symbolic_simpl. intros. Lia.lia. Qed.

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
    intros Γ es δ ι Heq.
    destruct (env.view ι) as [ι w].
    destruct (env.view ι) as [ι paddr].
    destruct (env.view ι) as [ι b].
    destruct (env.view ι). cbn in Heq |- *.
    iIntros "ptsto_addr_w".
    rewrite <-semWP_unfold_nolc. cbn.
    iIntros (γ1 μ1) "[Hregs Hmem]".
    iDestruct "Hmem" as (memmap) "[Hmem' %Hmap]".
    destruct b; cbn.
    - iDestruct "ptsto_addr_w" as "#ptsto_addr_w".
      unfold interp_ptstomem_readonly.
      iInv "ptsto_addr_w" as "Hptsto" "Hclose_ptsto".
      iMod (fupd_mask_subseteq empty) as "Hclose_rest"; first set_solver.
      iModIntro.
      iIntros (s2 δ2 γ2 μ2 Hstep).
      dependent elimination Hstep.
      rewrite Heq in f1.
      dependent elimination f1. cbn.
      do 3 iModIntro.
      iPoseProof (Model.RiscvPmpModel2.fun_read_ram_works Hmap with "[$Hptsto $Hmem']") as "%eq_fun_read_ram".
      iMod "Hclose_rest" as "_".
      iMod ("Hclose_ptsto" with "Hptsto") as "_".
      iModIntro.
      iFrame "Hregs".
      iSplitL "Hmem'".
      iExists memmap.
      now iFrame.
      iApply wp_value.
      iSplitL; last easy.
      now iSplitL.
    - iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iIntros (s2 δ2 γ2 μ2 Hstep).
      dependent elimination Hstep.
      rewrite Heq in f1.
      dependent elimination f1. cbn.
      do 3 iModIntro.
      iPoseProof (Model.RiscvPmpModel2.fun_read_ram_works Hmap with "[$ptsto_addr_w $Hmem']") as "%eq_fun_read_ram".
      iMod "Hclose" as "_".
      iModIntro.
      iSplitL "Hmem' Hregs".
      iSplitL "Hregs"; first iFrame.
      iExists memmap.
      iSplitL "Hmem'"; first iFrame.
      iPureIntro; assumption.
      iApply wp_value.
      iSplitL; last easy.
      now iSplitL.
  Qed.

  Lemma write_ram_sound `{sailGS Σ} {bytes} :
    ValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_write_ram (write_ram bytes).
  Proof.
    intros Γ es δ ι Heq.
    destruct (env.view ι) as [ι data].
    destruct (env.view ι) as [ι paddr].
    destruct (env.view ι). cbn in Heq |- *.
    iIntros "[% ptsto_addr]".
    rewrite <-semWP_unfold_nolc. cbn.
    iIntros (γ1 μ1 ) "[Hregs Hmem]".
    iDestruct "Hmem" as (memmap) "[Hmem' %Hmap]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iIntros (e2 δ2 γ2 μ2 Hstep).
    dependent elimination Hstep.
    rewrite Heq in f1. cbn in f1.
    dependent elimination f1. cbn.
    do 3 iModIntro.
    iMod (@Model.RiscvPmpModel2.fun_write_ram_works _ _ μ1 bytes paddr data memmap v Hmap
                 with "[$ptsto_addr $Hmem' $Hclose]") as "[Hmem >Haddr]".
    iFrame.
    now iApply wp_value.
  Qed.

  Lemma decode_sound `{sailGS Σ} :
    ValidContractForeign RiscvPmpBlockVerifSpec.sep_contract_decode RiscvPmpProgram.decode.
  Proof.
    intros Γ es δ ι Heq.
    destruct (env.view ι) as [ι instr].
    destruct (env.view ι) as [ι code].
    destruct (env.view ι). cbn.
    iIntros "%Hdecode".
    rewrite <-semWP_unfold_nolc. cbn.
    iIntros (γ1 μ1) "[Hregs Hmem]".
    iDestruct "Hmem" as (memmap) "[Hmem' %]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iIntros (e2 δ2 γ2 μ2 Hstep).
    dependent elimination Hstep.
    rewrite Heq in f1. cbv in f1.
    dependent elimination f1. rewrite Hdecode. cbn.
    do 3 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iSplitL "Hmem' Hregs".
    iSplitL "Hregs"; first iFrame.
    iExists memmap.
    iSplitL "Hmem'"; first iFrame.
    iPureIntro; assumption.
    iApply wp_value; auto.
  Qed.

  Lemma vector_subrange_sound `{sailGS Σ} {n} (e b : nat)
    {p : IsTrue (0 <=? b)%nat} {q : IsTrue (b <=? e)%nat} {r : IsTrue (e <? n)%nat} :
    ValidContractForeign (@RiscvPmpBlockVerifSpec.sep_contract_vector_subrange n e b p q r)
      (vector_subrange e b).
  Proof.
    intros Γ es δ ι Heq.
    destruct (env.view ι) as [ι v].
    iIntros "_".
    rewrite <-semWP_unfold_nolc.
    cbn in *.
    iIntros (? ?) "[Hregs Hmem]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    repeat iModIntro.
    iIntros (e2 δ2 γ2 μ2 Hstep).
    dependent elimination Hstep.
    rewrite Heq in f1.
    dependent elimination f1.
    repeat iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iApply wp_value.
    iSplitL; first iPureIntro; auto.
  Qed.

  Lemma foreignSemBlockVerif `{sailGS Σ} : ForeignSem.
  Proof.
    intros Δ τ f. destruct f.
    - apply read_ram_sound.
    - apply write_ram_sound.
    - apply decode_sound.
    - apply vector_subrange_sound.
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
