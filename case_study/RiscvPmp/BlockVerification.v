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
     Lists.List
     micromega.Lia
     Strings.String.
From RiscvPmp Require Import
     Machine.
From RiscvPmp Require
     Model
     Contracts
     LoopVerification
     .
From Katamaran Require Import
     Iris.Model
     Notations
     Shallow.Executor
     Shallow.Soundness
     Sep.Hoare
     Sep.Logic
     Semantics
     Specification
     Symbolic.Executor
     Symbolic.Solver
     Symbolic.Soundness
     Symbolic.Propositions
     Symbolic.Worlds.
From Equations Require Import
     Equations.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Module ns := stdpp.namespaces.

(*   Definition pmp_entry_cfg := ty_prod ty_pmpcfg_ent ty_xlenbits. *)

Module RiscvPmpBlockVerifSpec <: Specification RiscvPmpBase Contracts.RiscvPmpSignature.
  Import Contracts.RiscvPmpSignature.
  Import Contracts.
  Section ContractDefKit.

  Notation "a '↦ₘ' t" := (asn_chunk (chunk_user ptsto [a; t])) (at level 70).
  Notation "a '↦ᵢ' t" := (asn_chunk (chunk_user ptstoinstr [a; t])) (at level 70).
  Notation "p '∗' q" := (asn_sep p q).
  Notation "a '=' b" := (asn_eq a b).
  Notation "'∃' w ',' a" := (asn_exist w _ a) (at level 79, right associativity).
  Notation "a '∨' b" := (asn_or a b).
  Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
  Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
  Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
  Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
  Notation asn_match_option T opt xl alt_inl alt_inr := (asn_match_sum T ty.unit opt xl alt_inl "_" alt_inr).
  Notation asn_pmp_entries l := (asn_chunk (chunk_user pmp_entries [l])).

  Definition term_eqb {Σ} (e1 e2 : Term Σ ty_regno) : Term Σ ty.bool :=
    term_binop bop.eq e1 e2.

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
        @asn_exists Σ Γ (asn_exist x τ asn)
    end.

  Definition asn_with_reg {Σ} (r : Term Σ ty_regno) (asn : Reg ty_xlenbits -> Assertion Σ) (asn_default : Assertion Σ) : Assertion Σ :=
     asn_if (r =? term_val ty_regno (bv.of_N 0)) (asn_default)
    (asn_if (r =? term_val ty_regno (bv.of_N 1)) (asn x1)
    (asn_if (r =? term_val ty_regno (bv.of_N 2)) (asn x2)
    (asn_if (r =? term_val ty_regno (bv.of_N 3)) (asn x3)
    (asn_if (r =? term_val ty_regno (bv.of_N 4)) (asn x4)
    (asn_if (r =? term_val ty_regno (bv.of_N 5)) (asn x5)
    (asn_if (r =? term_val ty_regno (bv.of_N 6)) (asn x6)
    (asn_if (r =? term_val ty_regno (bv.of_N 7)) (asn x7)
     asn_false))))))).

  Definition asn_reg_ptsto {Σ} (r : Term Σ ty_regno) (w : Term Σ ty_word) : Assertion Σ :=
    asn_with_reg r (fun r => asn_chunk (chunk_ptsreg r w)) (asn_eq w (term_val ty.int 0%Z)).

  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

  Notation "r '↦' val" := (asn_chunk (asn_reg_ptsto [r; val])) (at level 79).
  (* TODO: abstract away the concrete type, look into unions for that *)
  (* TODO: length of list should be 16, no duplicates *)
  Definition pmp_entries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfgidx ty_pmpaddridx)) :=
    term_list
      (cons (term_val ty_pmpcfgidx PMP0CFG ,ₜ term_val ty_pmpaddridx PMPADDR0)
            (cons (term_val ty_pmpcfgidx PMP1CFG ,ₜ term_val ty_pmpaddridx PMPADDR1) nil)).

  End ContractDefKit.

  Local Notation "r '↦' val" := (asn_reg_ptsto r val) (at level 79).
  Local Notation "a '↦ₘ' t" := (asn_chunk (chunk_user ptsto [a; t])) (at level 70).
  Local Notation "a '↦ᵢ' t" := (asn_chunk (chunk_user ptstoinstr [a; t])) (at level 70).
  Local Notation "p '∗' q" := (asn_sep p q).
  Local Notation "a '=' b" := (asn_eq a b).
  Local Notation "'∃' w ',' a" := (asn_exist w _ a) (at level 79, right associativity).
  Local Notation "a '∨' b" := (asn_or a b).
  Local Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
  Local Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
  Local Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
  Local Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
  Local Notation asn_match_option T opt xl alt_inl alt_inr := (asn_match_sum T ty.unit opt xl alt_inl "_" alt_inr).
  Local Notation asn_pmp_entries l := (asn_chunk (chunk_user pmp_entries [l])).
  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
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
                                       asn_if (term_eqb (term_var "rs") (term_val ty_regno [bv 0]))
                                         (term_var "rs" ↦ term_val ty.int 0%Z)
                                         (term_var "rs" ↦ term_var "v")
    |}.

  Definition sep_contract_fetch : SepContractFun fetch :=
    {| sep_contract_logic_variables := ["a" :: ty_xlenbits; "w" :: ty.int];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn_chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ₘ term_var "w";
       sep_contract_result          := "result_fetch";
       sep_contract_postcondition   := asn_chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ₘ term_var "w" ∗
                                                 term_var "result_fetch" = term_union fetch_result KF_Base (term_var "w");
    |}.

  Definition sep_contract_fetch_instr : SepContractFun fetch :=
    {| sep_contract_logic_variables := ["a" :: ty_xlenbits; "i" :: ty_ast];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn_chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ᵢ term_var "i";
       sep_contract_result          := "result_fetch";
       sep_contract_postcondition   :=
         asn_chunk (chunk_ptsreg pc (term_var "a")) ∗ term_var "a" ↦ᵢ term_var "i" ∗
         asn_exist "w" _
           (term_var "result_fetch" = term_union fetch_result KF_Base (term_var "w") ∗
            asn_chunk (chunk_user encodes_instr [term_var "w"; term_var "i"]));
    |}.

  Definition sep_contract_mem_read : SepContractFun mem_read :=
    {| sep_contract_logic_variables := ["typ" :: ty_access_type; "paddr" :: ty_xlenbits; "w" :: ty_xlenbits];
       sep_contract_localstore      := [term_var "typ"; term_var "paddr"];
       sep_contract_precondition    := term_var "paddr" ↦ₘ term_var "w";
       sep_contract_result          := "result_mem_read";
       sep_contract_postcondition   :=
      term_var "result_mem_read" = term_union memory_op_result KMemValue (term_var "w") ∗
                                              term_var "paddr" ↦ₘ term_var "w";
    |}.

  Definition sep_contract_tick_pc : SepContractFun tick_pc :=
    {| sep_contract_logic_variables := ["ao" :: ty_xlenbits; "an" :: ty_xlenbits];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn_chunk (chunk_ptsreg pc (term_var "ao")) ∗
                                                 asn_chunk (chunk_ptsreg nextpc (term_var "an"));
       sep_contract_result          := "result_tick_pc";
       sep_contract_postcondition   := asn_chunk (chunk_ptsreg pc (term_var "an")) ∗
                                                 asn_chunk (chunk_ptsreg nextpc (term_var "an")) ∗
                                                 term_var "result_tick_pc" = term_val ty.unit tt;
    |}.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | rX                    => Some sep_contract_rX
      | wX                    => Some sep_contract_wX
      | fetch                 => Some sep_contract_fetch_instr
      | mem_read              => Some sep_contract_mem_read
      | tick_pc               => Some sep_contract_tick_pc
      | _                     => None
      end.

  Lemma linted_cenv :
    forall Δ τ (f : Fun Δ τ),
      match CEnv f with
      | Some c => Linted c
      | None   => True
      end.
  Proof. intros ? ? []; try constructor. Qed.

  Definition sep_contract_read_ram : SepContractFunX read_ram :=
    {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "w" :: ty_xlenbits];
       sep_contract_localstore      := [term_var "paddr"];
       sep_contract_precondition    := term_var "paddr" ↦ₘ term_var "w";
       sep_contract_result          := "result_read_ram";
       sep_contract_postcondition   := term_var "result_read_ram" = term_var "w";
    |}.

  Definition sep_contract_write_ram : SepContractFunX write_ram :=
    {| sep_contract_logic_variables := ["paddr" :: ty.int; "data" :: ty_word];
       sep_contract_localstore      := [term_var "paddr"; term_var "data"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_write_ram";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition sep_contract_decode    : SepContractFunX decode :=
    {| sep_contract_logic_variables := ["code" :: ty.int; "instr" :: ty_ast];
       sep_contract_localstore      := [term_var "code"];
       sep_contract_precondition    := asn_chunk (chunk_user encodes_instr [term_var "code"; term_var "instr"]);
       sep_contract_result          := "result_decode";
       sep_contract_postcondition   := term_var "result_decode" = term_var "instr";
    |}.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | read_ram  => sep_contract_read_ram
      | write_ram => sep_contract_write_ram
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
       lemma_precondition    := asn_true;
       lemma_postcondition   := asn_true;
    |}.

  Definition lemma_close_gprs : SepLemma close_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := asn_true;
       lemma_postcondition   := asn_true;
    |}.

  Definition lemma_open_pmp_entries : SepLemma open_pmp_entries :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := asn_true;
       lemma_postcondition   := asn_true;
    |}.

  Definition lemma_close_pmp_entries : SepLemma close_pmp_entries :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := asn_true;
       lemma_postcondition   := asn_true;
    |}.

  Definition lemma_update_pmp_entries : SepLemma update_pmp_entries :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := asn_true;
       lemma_postcondition   := asn_true;
    |}.

  Definition lemma_extract_pmp_ptsto : SepLemma extract_pmp_ptsto :=
    {| lemma_logic_variables := ["paddr" :: ty_xlenbits];
       lemma_patterns        := [term_var "paddr"];
       lemma_precondition    := asn_true;
       lemma_postcondition   := asn_true;
    |}.

  Definition lemma_return_pmp_ptsto : SepLemma return_pmp_ptsto :=
    {| lemma_logic_variables := ["paddr" :: ty_xlenbits];
       lemma_patterns        := [term_var "paddr"];
       lemma_precondition    := asn_true;
       lemma_postcondition   := asn_true;
    |}.

  Definition LEnv : LemmaEnv :=
    fun Δ l =>
      match l with
      | open_gprs      => lemma_open_gprs
      | close_gprs     => lemma_close_gprs
      | open_pmp_entries => lemma_open_pmp_entries
      | close_pmp_entries => lemma_close_pmp_entries
      | update_pmp_entries => lemma_update_pmp_entries
      | extract_pmp_ptsto => lemma_extract_pmp_ptsto
      | return_pmp_ptsto => lemma_return_pmp_ptsto
      end.
End RiscvPmpBlockVerifSpec.

Module RiscvPmpSpecVerif.

  Import Contracts.
  Import RiscvPmpSignature.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpProgram.
  Module RiscvPmpSolverKit := DefaultSolverKit RiscvPmpBase RiscvPmpSignature.
  Module RiscvPmpSolver := MakeSolver RiscvPmpBase RiscvPmpSignature RiscvPmpSolverKit.

  Module Import RiscvPmpExecutor :=
    MakeExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec RiscvPmpSolver.
  Import Symbolic.

  Notation "r '↦' val" := (chunk_ptsreg r val) (at level 79).

  Import ModalNotations.

  Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContractReflect c (FunDef f)
    | None => False
    end.

  Lemma valid_execute_rX : ValidContract rX.
  Proof. reflexivity. Qed.

  Lemma valid_execute_wX : ValidContract wX.
  Proof. reflexivity. Qed.

  Lemma valid_execute_fetch : ValidContract fetch.
  Proof. Admitted.

  (* Lemma valid_execute_fetch_instr : SMut.ValidContract sep_contract_fetch_instr (FunDef fetch). *)
  (* Proof. compute. Admitted. *)

  Lemma valid_execute_tick_pc : ValidContract tick_pc.
  Proof. reflexivity. Qed.

  Lemma defined_contracts_valid : forall {Δ τ} (f : Fun Δ τ),
      match CEnv f with
      | Some c => ValidContract f
      | None => True
      end.
  Proof.
    destruct f; try now cbv.
  Admitted.

End RiscvPmpSpecVerif.

Module BlockVerification.

  Import Contracts.
  Import RiscvPmpSignature.
  Import RiscvPmpBlockVerifSpec.
  Module RiscvPmpSolverKit := DefaultSolverKit RiscvPmpBase RiscvPmpSignature.
  Module RiscvPmpSolver := MakeSolver RiscvPmpBase RiscvPmpSignature RiscvPmpSolverKit.

  Module Import RiscvPmpExecutor :=
    MakeExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec RiscvPmpSolver.
  Import Symbolic.

  Notation "r '↦' val" := (chunk_ptsreg r val) (at level 79).

  Import ModalNotations.
  Import bv.notations.

  Definition M : TYPE -> TYPE := SHeapSpecM [] [].

  Definition pure {A} : ⊢ A -> M A := SHeapSpecM.pure.
  Definition bind {A B} : ⊢ M A -> □(A -> M B) -> M B := SHeapSpecM.bind.
  Definition angelic {σ} : ⊢ M (STerm σ) := @SHeapSpecM.angelic [] None σ.
  Definition assert : ⊢ Formula -> M Unit := SHeapSpecM.assert_formula.
  Definition assume : ⊢ Formula -> M Unit := SHeapSpecM.assume_formula.

  Definition produce_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.produce_chunk.
  Definition consume_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.consume_chunk.

  Definition produce : ⊢ Assertion -> □(M Unit) := SHeapSpecM.produce.
  Definition consume : ⊢ Assertion -> □(M Unit) := SHeapSpecM.consume.

  Notation "ω ∣ x <- ma ;; mb" :=
    (bind ma (fun _ ω x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Definition rX (r : Reg ty_xlenbits) : ⊢ M (STerm ty_xlenbits) :=
    fun _ =>
      ω01 ∣ v1 <- @angelic ty_xlenbits _ ;;
      ω12 ∣ _  <- consume_chunk (r ↦ v1) ;;
      let v2 := persist__term v1 ω12 in
      ω23 ∣ _ <- produce_chunk (r ↦ v2) ;;
      let v3 := persist__term v2 ω23 in
      pure v3.

  Definition wX (r : Reg ty_xlenbits) : ⊢ STerm ty_xlenbits -> M Unit :=
    fun _ u0 =>
      ω01 ∣ v1 <- @angelic ty_xlenbits _ ;;
      ω12 ∣ _  <- consume_chunk (r ↦ v1) ;;
      let u2 := persist__term u0 (acc_trans ω01 ω12) in
      produce_chunk (r ↦ u2).

  Definition exec_rtype (rs2 rs1 rd : Reg ty_xlenbits) (op : ROP) : ⊢ M Unit :=
    fun _ =>
      ω01 ∣ v11 <- @rX rs1 _ ;;
      ω12 ∣ v22 <- @rX rs2 _ ;;
      let v12 := persist__term v11 ω12 in
      let bop := match op with
                 | RISCV_ADD => bop.plus
                 | RISCV_SUB => bop.minus
                 end in
      wX rd (peval_binop bop v12 v22).

  Definition exec_instruction (i : AST) : ⊢ M Unit :=
    match i with
    | RTYPE rs2 rs1 rd op =>
        match reg_convert rs2, reg_convert rs1, reg_convert rd with
        | Some rs2, Some rs1, Some rd => exec_rtype rs2 rs1 rd op
        | _, _, _ => fun _ => pure tt
        end
    | _                   => fun _ => pure tt
    end.

  (* Ideally, a block should be a list of non-branching
     instruction plus one final branching instruction *)
  Fixpoint exec_block (b : list AST) : ⊢ M Unit :=
    fun _ =>
      match b with
      | nil       => pure tt
      | cons i b' =>
        _ ∣ _ <- @exec_instruction i _ ;;
        @exec_block b' _
      end.

  Definition ADD (rd rs1 rs2 : RegIdx) : AST :=
    RTYPE rs2 rs1 rd RISCV_ADD.
  Definition SUB (rd rs1 rs2 : RegIdx) : AST :=
    RTYPE rs2 rs1 rd RISCV_SUB.
  Definition BEQ (rs1 rs2 : RegIdx) (imm : Z) : AST :=
    BTYPE imm rs2 rs1 RISCV_BEQ.
  Definition BNE (rs1 rs2 : RegIdx) (imm : Z) : AST :=
    BTYPE imm rs2 rs1 RISCV_BNE.
  Definition ADDI (rd rs1 : RegIdx) (imm : Z) : AST :=
    ITYPE imm rs1 rd RISCV_ADDI.
  Definition JALR (rd rs1 : RegIdx) (imm : Z) : AST :=
    RISCV_JALR imm rs1 rd.
  Definition RET : AST :=
    JALR [bv 0] [bv 1] 0%Z.
  Definition MV (rd rs1 : RegIdx) : AST :=
    ADDI rd rs1 0%Z.

  Definition exec_double {Σ : World}
    (req : Assertion Σ) (b : list AST) : M Unit Σ :=
    ω1 ∣ _ <- T (produce req) ;;
    @exec_block b _.

  Definition exec_triple {Σ : World}
    (req : Assertion Σ) (b : list AST) (ens : Assertion Σ) : M Unit Σ :=
    ω ∣ _ <- exec_double req b ;;
    consume ens ω.

  Module Post := Postprocessing.
  (* This is a VC for triples, for doubles we probably need to talk
     about the continuation of a block. *)
  Definition VC {Σ : LCtx} (req : Assertion Σ) (b : list AST) (ens : Assertion Σ) : 𝕊 Σ :=
    Post.prune (Post.solve_uvars (Post.prune (Post.solve_evars (Post.prune
      (@exec_triple
        {| wctx := Σ; wco := nil |}
        req b ens
        (* Could include leakcheck here *)
        (fun _ _ _ _ h => SymProp.block)
        []%env []%list))))).

  Section Example.

    Import ListNotations.
    Notation "p '∗' q" := (asn_sep p q).

    Example block1 : list AST :=
      [ ADD [bv 1] [bv 1] [bv 2]
      ; SUB [bv 2] [bv 1] [bv 2]
      ; SUB [bv 1] [bv 1] [bv 2]
      ].

    Let Σ1 : LCtx := ["x" :: ty_xlenbits; "y" :: ty_xlenbits].

    Local Notation "r '↦' val" := (asn_chunk (chunk_ptsreg r val)) (at level 79).

    Example pre1 : Assertion Σ1 :=
      x1 ↦ term_var "x" ∗
      x2 ↦ term_var "y".

    Example post1 : Assertion Σ1 :=
      x1 ↦ term_var "y" ∗
      x2 ↦ term_var "x".

    Example VC1 : 𝕊 Σ1 := VC pre1 block1 post1.

    Eval compute in VC1.

  End Example.

  Module SUM.

    Definition zero : RegIdx := [bv 0].
    Definition ra : RegIdx := [bv 1].
    Definition a0 : RegIdx := [bv 2].
    Definition a4 : RegIdx := [bv 3].
    Definition a5 : RegIdx := [bv 4].
    Definition rra := x1.
    Definition ra0 := x2.
    Definition ra4 := x3.
    Definition ra5 := x4.

    (* C SOURCE *)
    (* int sum(int n) { *)
    (*     int s = 0; *)
    (*     for (int i = 0; i != n; ++i) { *)
    (*         s = s + i; *)
    (*     } *)
    (*     return s; *)
    (* } *)

    (* 0000000000000000 <sum>: *)
    (*    0:	00050713          	addi	a4,a0,0 *)
    (*    4:	00050e63          	beq	a0,zero,20 <.L4> *)
    (*    8:	00000793          	addi	a5,zero,0 *)
    (*    c:	00000513          	addi	a0,zero,0 *)
    (* 0000000000000010 <.L3>: *)
    (*   10:	00f5053b          	addw	a0,a0,a5 *)
    (*   14:	0017879b          	addiw	a5,a5,1 *)
    (*   18:	fef71ce3          	bne	a4,a5,10 <.L3> *)
    (*   1c:	00008067          	jalr	zero,0(ra) *)
    (* 0000000000000020 <.L4>: *)
    (*   20:	00008067          	jalr	zero,0(ra) *)

    Example block_sum : list AST :=
      [ ADDI a4 a0 0
      ; BEQ a0 zero 0x20
      ; ADDI a5 zero 0
      ; ADDI a0 zero 0
      ].

    Example block_l3 : list AST :=
      [ ADD a0 a0 a5
      ; ADDI a5 a5 1
      ; BNE a4 a5 (-0x8)
      ].

    Example block_l4 : list AST :=
      [ RET
      ].

    Example sum : list AST :=
      block_sum ++ block_l3 ++ block_l4.

    Local Notation "p '∗' q" := (asn_sep p q).
    Local Notation "r '↦' val" := (asn_chunk (chunk_ptsreg r val)) (at level 79).
    Local Notation "'∃' w ',' a" := (asn_exist w _ a) (at level 79, right associativity).
    Local Notation "x - y" := (term_binop bop.minus x y) : exp_scope.
    Local Notation "x + y" := (term_binop bop.plus x y) : exp_scope.
    Local Notation "x * y" := (term_binop bop.times x y) : exp_scope.

    Section BlockSum.

      Let Σ1 : LCtx := ["n" ∷ ty.int].

      Example sum_pre : Assertion Σ1 :=
        asn_exist "s" _ (ra0 ↦ term_var "s") ∗
        ra4 ↦ term_var "n" ∗
        asn_exist "i" _ (ra5 ↦ term_var "i") ∗
        asn_bool (term_binop bop.le (term_val ty.int 0%Z) (term_var "n")).

      Example sum_post : Assertion Σ1 :=
        ra0 ↦ term_val ty.int 0%Z ∗
        ra4 ↦ term_var "n" ∗
        ra5 ↦ term_val ty.int 0%Z ∗
        asn_bool (term_binop bop.le (term_val ty.int 0%Z) (term_var "n")).

      Example vc_sum : 𝕊 Σ1 :=
        VC sum_pre block_sum sum_post.

      Eval compute in vc_sum.

    End BlockSum.

    Let Σ1 : LCtx := ["n" ∷ ty.int; "s" ∷ ty.int; "i" ∷ ty.int].

    (* Example sum_pre : Assertion Σ1 := *)
    (*   ra0 ↦ term_var "s" ∗ *)
    (*   ra4 ↦ term_var "n" ∗ *)
    (*   ra5 ↦ term_var "i" ∗ *)
    (*   asn_bool (term_binop bop.le (term_val ty.int 0%Z) (term_var "n")) ∗ *)
    (*   asn_eq (term_val ty.int 0%Z) (term_var "s") ∗ *)
    (*   asn_eq (term_val ty.int 0%Z) (term_var "i"). *)

    (* Example sum_loop : Assertion Σ1 := *)
    (*   ra0 ↦ term_var "s" ∗ *)
    (*   ra4 ↦ term_var "n" ∗ *)
    (*   ra5 ↦ term_var "i" ∗ *)
    (*   asn_eq *)
    (*     (term_val ty.int 2%Z * term_var "s") *)
    (*     (term_var "i" * (term_var "i" - term_val ty.int 1%Z)). *)

    (* Example sum_post : Assertion Σ1 := *)
    (*   ra0 ↦ term_var "s" ∗ *)
    (*   ra4 ↦ term_var "n" ∗ *)
    (*   ra5 ↦ term_var "i" ∗ *)
    (*   asn_eq (term_var "i") (term_var "n") ∗ *)
    (*   asn_eq *)
    (*     (term_val ty.int 2%Z * term_var "s") *)
    (*     (term_var "n" * (term_var "n" - term_val ty.int 1%Z)). *)

 End SUM.

  Section MemCopy.

    Import ListNotations.
    Open Scope hex_Z_scope.

    (* C SOURCE *)
    (* #include <stdlib.h> *)
    (* void mcpy(char* dst, char* src, size_t size) { *)
    (*     for (; size != 0; --size) { *)
    (*         *dst = *src; *)
    (*         ++dst; *)
    (*         ++src; *)
    (*     } *)
    (* } *)

    (* ASSEMBLY SOURCE (modified) *)
    (* mcpy: *)
    (*   beq a2,zero,.L2 *)
    (* .L1: *)
    (*   lb a3,0(a1) *)
    (*   sb a3,0(a0) *)
    (*   addi a0,a0,1 *)
    (*   addi a1,a1,1 *)
    (*   addi a2,a2,-1 *)
    (*   bne a2,zero,.L1 *)
    (* .L2: *)
    (*   ret *)

    (* DISASSEMBLY *)
    (* 0000000000000000 <mcpy>: *)
    (*    0:	00060e63          	beqz	a2,1c <.L2> *)
    (* 0000000000000004 <.L1>: *)
    (*    4:	00058683          	lb	a3,0(a1) *)
    (*    8:	00d50023          	sb	a3,0(a0) *)
    (*    c:	00150513          	addi	a0,a0,1 *)
    (*   10:	00158593          	addi	a1,a1,1 *)
    (*   14:	fff60613          	addi	a2,a2,-1 *)
    (*   18:	fe0616e3          	bnez	a2,4 <.L1> *)
    (* 000000000000001c <.L2>: *)
    (*   1c:	00008067          	ret *)

    Definition zero : RegIdx := [bv 0].
    Definition ra : RegIdx := [bv 1].
    Definition a0 : RegIdx := [bv 2].
    Definition a1 : RegIdx := [bv 3].
    Definition a2 : RegIdx := [bv 4].
    Definition a3 : RegIdx := [bv 5].
    Definition rra := x1.
    Definition ra0 := x2.
    Definition ra1 := x3.
    Definition ra2 := x4.
    Definition ra3 := x5.

    Example memcpy : list AST :=
      [ BEQ a2 zero 0x1c
      ; LOAD 0 a1 a3
      ; STORE 0 a3 a0
      ; ADDI a0 a0 1
      ; ADDI a1 a1 1
      ; ADDI a2 a2 (-1)
      ; BNE a2 zero (-0x14)
      ; RET
      ].

    Let Σ1 : LCtx :=
          ["dst" :: ty_xlenbits; "src" :: ty_xlenbits; "size" :: ty.int;
           "srcval" :: ty.list ty_word; "ret" :: ty_xlenbits].

    Local Notation "p '∗' q" := (asn_sep p q).
    Local Notation "r '↦' val" := (asn_chunk (chunk_ptsreg r val)) (at level 79).
    Local Notation "a '↦[' n ']' xs" := (asn_chunk (chunk_user ptstomem [a; n; xs])) (at level 79).
    Local Notation "'∃' w ',' a" := (asn_exist w _ a) (at level 79, right associativity).

    Example memcpy_pre : Assertion Σ1 :=
      pc  ↦ term_val ty_xlenbits 0%Z ∗
      rra ↦ term_var "ret" ∗
      ra0 ↦ term_var "dst" ∗
      ra1 ↦ term_var "src" ∗
      ra2 ↦ term_var "size" ∗
      term_var "src" ↦[ term_var "size" ] term_var "srcval" ∗
      (∃ "dstval", term_var "dst" ↦[ term_var "size" ] term_var "dstval").

    Example memcpy_post : Assertion Σ1 :=
      pc ↦ term_var "ret" ∗
      rra ↦ term_var "ret" ∗
      (∃ "v", ra0 ↦ term_var "v") ∗
      (∃ "v", ra1 ↦ term_var "v") ∗
      (∃ "v", ra2 ↦ term_var "v") ∗
      term_var "src" ↦[ term_var "size" ] term_var "srcval" ∗
      term_var "dst" ↦[ term_var "size" ] term_var "srcval".

    Example memcpy_loop : Assertion Σ1 :=
      pc  ↦ term_val ty_xlenbits 0%Z ∗
      rra ↦ term_var "ret" ∗
      ra0 ↦ term_var "dst" ∗
      ra1 ↦ term_var "src" ∗
      ra2 ↦ term_var "size" ∗
      asn_formula (formula_neq (term_var "size") (term_val ty.int 0)) ∗
      term_var "src" ↦[ term_var "size" ] term_var "srcval" ∗
      (∃ "dstval", term_var "dst" ↦[ term_var "size" ] term_var "dstval").

  End MemCopy.

End BlockVerification.


Module BlockVerificationDerived.

  Import Contracts.
  Import RiscvPmpSignature.
  Import RiscvPmpBlockVerifSpec.

  Module RiscvPmpSolverKit := DefaultSolverKit RiscvPmpBase RiscvPmpSignature.
  Module RiscvPmpSolver := MakeSolver RiscvPmpBase RiscvPmpSignature RiscvPmpSolverKit.

  Module Import RiscvPmpExecutor :=
    MakeExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec RiscvPmpSolver.
  Import Symbolic.

  Import ModalNotations.

  Definition M : TYPE -> TYPE := SHeapSpecM [] [].

  Definition pure {A} : ⊢ A -> M A := SHeapSpecM.pure.
  Definition bind {A B} : ⊢ M A -> □(A -> M B) -> M B := SHeapSpecM.bind.
  Definition angelic {σ} : ⊢ M (STerm σ) := @SHeapSpecM.angelic [] None σ.
  Definition demonic {σ} : ⊢ M (STerm σ) := @SHeapSpecM.demonic [] None σ.
  Definition assert : ⊢ Formula -> M Unit := SHeapSpecM.assert_formula.
  Definition assume : ⊢ Formula -> M Unit := SHeapSpecM.assume_formula.

  Definition produce_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.produce_chunk.
  Definition consume_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.consume_chunk.

  Definition produce : ⊢ Assertion -> □(M Unit) := SHeapSpecM.produce.
  Definition consume : ⊢ Assertion -> □(M Unit) := SHeapSpecM.consume.

  Notation "ω ∣ x <- ma ;; mb" :=
    (bind ma (fun _ ω x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Definition exec_instruction' (i : AST) : ⊢ M (STerm ty_retired) :=
    let inline_fuel := 3%nat in
    fun w0 POST _ =>
      SHeapSpecM.exec
        default_config inline_fuel (FunDef execute)
        (fun w1 ω01 res _ => POST w1 ω01 res []%env)
        [term_val (type ("ast" :: ty_ast)) i]%env.

  Definition exec_instruction (i : AST) : ⊢ M Unit :=
    fun _ =>
      _ ∣ msg <- @exec_instruction' i _ ;;
      assert (formula_eq msg (term_val ty_retired RETIRE_SUCCESS)).

  (* Ideally, a block should be a list of non-branching
     instruction plus one final branching instruction *)
  Fixpoint exec_block (b : list AST) : ⊢ M Unit :=
    fun _ =>
      match b with
      | nil       => pure tt
      | cons i b' =>
        _ ∣ _ <- @exec_instruction i _ ;;
        @exec_block b' _
      end.


  Definition exec_double {Σ : World}
    (req : Assertion Σ) (b : list AST) : M Unit Σ :=
    ω1 ∣ _ <- T (produce req) ;;
    @exec_block b _.

  Definition exec_triple {Σ : World}
    (req : Assertion Σ) (b : list AST) (ens : Assertion Σ) : M Unit Σ :=
    ω ∣ _ <- exec_double req b ;;
    consume ens ω.

  (* This is a VC for triples, for doubles we probably need to talk
     about the continuation of a block. *)
  Definition VC {Σ : LCtx} (req : Assertion Σ) (b : list AST) (ens : Assertion Σ) : 𝕊 ε :=
    SymProp.demonic_close
      (@exec_triple
         {| wctx := Σ; wco := nil |}
         req b ens
         (* Could include leakcheck here *)
         (fun _ _ _ _ h => SymProp.block)
         []%env []%list).
  Section Example.

    Import ListNotations.
    Import bv.notations.

    Notation "p '∗' q" := (asn_sep p q).
    Notation "r '↦r' val" :=
      (asn_chunk
         (chunk_ptsreg r val))
         (at level 79).

    Definition ADD (rd rs1 rs2 : RegIdx) : AST :=
      RTYPE rs2 rs1 rd RISCV_ADD.
    Definition SUB (rd rs1 rs2 : RegIdx) : AST :=
      RTYPE rs2 rs1 rd RISCV_SUB.

    Example block1 : list AST :=
      [ ADD [bv 1] [bv 1] [bv 2]
      ; SUB [bv 2] [bv 1] [bv 2]
      ; SUB [bv 1] [bv 1] [bv 2]
      ].

    Section Contract.

      Let Σ1 : LCtx := ["x" :: ty_xlenbits; "y" :: ty_xlenbits].

      Example pre1 : Assertion Σ1 :=
        x1 ↦r term_var "x" ∗
        x2 ↦r term_var "y".

      Example post1 : Assertion Σ1 :=
        x1 ↦r term_var "y" ∗
        x2 ↦r term_var "x".

    End Contract.

    Example vc1 : 𝕊 ε :=
      let vc1 := BlockVerificationDerived.VC pre1 block1 post1 in
      let vc2 := Postprocessing.prune vc1 in
      let vc3 := Postprocessing.solve_evars vc2 in
      let vc4 := Postprocessing.solve_uvars vc3 in
      vc4.

    Notation "x" := (@term_var _ x%string _ (@ctx.MkIn _ (x%string :: _) _ _ _)) (at level 1, only printing).
    Notation "s = t" := (@formula_eq _ _ s t) (only printing).
    Notation "' t" := (@formula_bool _ t) (at level 0, only printing, format "' t").
    Notation "F ∧ P" := (@SymProp.assertk _ F _ P) (at level 80, right associativity, only printing).
    (* Notation "F → P" := (@SymProp.assumek _ F P) (at level 99, right associativity, only printing). *)
    Notation "'∃' x '∷' σ , P" := (SymProp.angelicv (x,σ) P) (at level 200, right associativity, only printing, format "'∃'  x '∷' σ ,  '/' P").
    Notation "'∀' x '∷' σ , P" := (SymProp.demonicv (x,σ) P) (at level 200, right associativity, only printing, format "'∀'  x '∷' σ ,  '/' P").
    Notation "⊤" := (@SymProp.block _).
    Notation "x - y" := (term_binop bop.minus x y) : exp_scope.
    Notation "x + y" := (term_binop bop.plus x y) : exp_scope.

    Lemma sat_vc1 : VerificationConditionWithErasure (Erasure.erase_symprop vc1).
    Proof.
      compute. constructor. cbv - [Z.sub Z.add]. lia.
    Qed.

  End Example.

End BlockVerificationDerived.

Module BlockVerificationDerived2.

  Import Contracts.
  Import RiscvPmpSignature.
  Import RiscvPmpBlockVerifSpec.

  Module RiscvPmpSolverKit := DefaultSolverKit RiscvPmpBase RiscvPmpSignature.
  Module RiscvPmpSolver := MakeSolver RiscvPmpBase RiscvPmpSignature RiscvPmpSolverKit.

  Module Import RiscvPmpExecutor :=
    MakeExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec RiscvPmpSolver.
  Import Symbolic.

  Import ModalNotations.

  Definition M : TYPE -> TYPE := SHeapSpecM [] [].

  Definition pure {A} : ⊢ A -> M A := SHeapSpecM.pure.
  Definition bind {A B} : ⊢ M A -> □(A -> M B) -> M B := SHeapSpecM.bind.
  Definition angelic {σ} : ⊢ M (STerm σ) := @SHeapSpecM.angelic [] None σ.
  Definition demonic {σ} : ⊢ M (STerm σ) := @SHeapSpecM.demonic [] None σ.
  Definition assert : ⊢ Formula -> M Unit := SHeapSpecM.assert_formula.
  Definition assume : ⊢ Formula -> M Unit := SHeapSpecM.assume_formula.

  Definition produce_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.produce_chunk.
  Definition consume_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.consume_chunk.

  Definition produce : ⊢ Assertion -> □(M Unit) := SHeapSpecM.produce.
  Definition consume : ⊢ Assertion -> □(M Unit) := SHeapSpecM.consume.

  Notation "ω ∣ x <- ma ;; mb" :=
    (bind ma (fun _ ω x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Definition exec_instruction_any (i : AST) : ⊢ STerm ty_xlenbits -> M (STerm ty_xlenbits) :=
    let inline_fuel := 10%nat in
    fun _ a =>
      ω2 ∣ _ <- T (produce (asn_chunk (chunk_ptsreg pc a))) ;;
      ω4 ∣ _ <- T (produce (asn_chunk (chunk_user ptstoinstr [persist__term a ω2; term_val ty_ast i]))) ;;
      ω6 ∣ an <- @demonic _ _ ;;
      ω7 ∣ _ <- T (produce (asn_chunk (chunk_ptsreg nextpc an))) ;;
      ω8 ∣ _ <- SHeapSpecM.exec default_config inline_fuel (FunDef step) ;;
      ω9 ∣ _ <- T (consume (asn_chunk (chunk_user ptstoinstr [persist__term a (ω2 ∘ ω4 ∘ ω6 ∘ ω7 ∘ ω8); term_val ty_ast i]))) ;;
      ω10 ∣ na <- @angelic _ _ ;;
      ω11 ∣ _ <- T (consume (asn_chunk (chunk_ptsreg nextpc na))) ;;
      ω12 ∣ _ <- T (consume (asn_chunk (chunk_ptsreg pc (persist__term na ω11)))) ;;
      pure (persist__term na (ω11 ∘ ω12)).

  Definition exec_instruction (i : AST) : ⊢ M Unit :=
    let inline_fuel := 10%nat in
    fun _ =>
      ω1 ∣ a <- @demonic _ _ ;;
      ω2 ∣ na <- exec_instruction_any i a ;;
      assert (formula_eq na (term_binop bop.plus (persist__term a ω2) (term_val ty_exc_code 4))).

  Fixpoint exec_block_addr (b : list AST) : ⊢ STerm ty_xlenbits -> M (STerm ty_xlenbits) :=
    fun _ a =>
      match b with
      | nil       => pure a
      | cons i b' =>
        ω ∣ a' <- exec_instruction_any i a ;;
        (* TODO: assert that a' = a + 4 *)
        @exec_block_addr b' _ a'
      end.

  Definition exec_double_addr {Σ : World}
    (req : (□ (STerm ty_xlenbits -> Assertion)) Σ) (b : list AST) : M (STerm ty_xlenbits) Σ :=
    ω1 ∣ an <- @demonic _ _ ;;
    ω2 ∣ _ <- T (produce (req _ ω1 an)) ;;
    @exec_block_addr b _ (persist__term an ω2).

  Definition exec_triple_addr {Σ : World}
    (req : □ (STerm ty_xlenbits -> Assertion) Σ) (b : list AST)
    (ens : (□ (STerm ty_xlenbits -> STerm ty_xlenbits -> Assertion)) Σ) : M Unit Σ :=
    ω1 ∣ a <- @demonic _ _ ;;
    ω2 ∣ _ <- T (produce (req _ ω1 a)) ;;
    ω3 ∣ na <- @exec_block_addr b _ (persist__term a ω2) ;;
    T (consume (ens _ (ω1 ∘ ω2 ∘ ω3) (persist__term a (ω2 ∘ ω3)) na)).

  (* This is a VC for triples, for doubles we probably need to talk
     about the continuation of a block. *)
  Definition VC__addr {Σ : LCtx} (req : □ (STerm ty_xlenbits -> Assertion) {| wctx := Σ; wco := nil |}) (b : list AST)
    (ens : (□ (STerm ty_xlenbits -> STerm ty_xlenbits -> Assertion)) {| wctx := Σ; wco := nil |}) : 𝕊 ε :=
    SymProp.demonic_close
      (@exec_triple_addr
         {| wctx := Σ; wco := nil |}
         req b ens
         (* Could include leakcheck here *)
         (fun _ _ _ _ h => SymProp.block)
         []%env []%list).

  Section Example.

    Import ListNotations.
    Import bv.notations.

    Notation "p '∗' q" := (asn_sep p q).
    Notation "r '↦r' val" :=
      (asn_chunk
         (chunk_ptsreg r val))
         (at level 79).

    Definition ADD (rd rs1 rs2 : RegIdx) : AST :=
      RTYPE rs2 rs1 rd RISCV_ADD.
    Definition SUB (rd rs1 rs2 : RegIdx) : AST :=
      RTYPE rs2 rs1 rd RISCV_SUB.

    Example block1 : list AST :=
      [ ADD [bv 1] [bv 1] [bv 2]
      ; SUB [bv 2] [bv 1] [bv 2]
      ; SUB [bv 1] [bv 1] [bv 2]
      ].

    Section Contract.

      Let Σ1 : LCtx := ["x" :: ty_xlenbits; "y" :: ty_xlenbits].

      Example pre1 : Assertion Σ1 :=
        x1 ↦r term_var "x" ∗
        x2 ↦r term_var "y".

      Example post1 : Assertion Σ1 :=
        x1 ↦r term_var "y" ∗
        x2 ↦r term_var "x".

    End Contract.

    Notation "x" := (@term_var _ x%string _ (@ctx.MkIn _ (x%string :: _) _ _ _)) (at level 1, only printing).
    Notation "s = t" := (@formula_eq _ _ s t) (only printing).
    Notation "' t" := (@formula_bool _ t) (at level 0, only printing, format "' t").
    Notation "F ∧ P" := (@SymProp.assertk _ F _ P) (at level 80, right associativity, only printing).
    (* Notation "F → P" := (@SymProp.assumek _ F P) (at level 99, right associativity, only printing). *)
    Notation "'∃' x '∷' σ , P" := (SymProp.angelicv (x,σ) P) (at level 200, right associativity, only printing, format "'∃'  x '∷' σ ,  '/' P").
    Notation "'∀' x '∷' σ , P" := (SymProp.demonicv (x,σ) P) (at level 200, right associativity, only printing, format "'∀'  x '∷' σ ,  '/' P").
    Notation "⊤" := (@SymProp.block _).
    Notation "x - y" := (term_binop bop.minus x y) : exp_scope.
    Notation "x + y" := (term_binop bop.plus x y) : exp_scope.

    Section ContractAddr.

      Let Σ1 : LCtx := ["x" :: ty_xlenbits; "y" :: ty_xlenbits].

      Example pre1' : □ (STerm ty_xlenbits -> Assertion)  {| wctx := Σ1 ; wco := nil |} :=
        fun _ ω a =>
        persist (A := Assertion) (x1 ↦r term_var "x") ω ∗
        persist (A := Assertion) (x2 ↦r term_var "y") ω.

      Example post1' : □ (STerm ty_xlenbits -> STerm ty_xlenbits -> Assertion)  {| wctx := Σ1 ; wco := nil |} :=
        fun _ ω a an =>
          persist (A := Assertion) (x1 ↦r term_var "y") ω ∗
          persist (A := Assertion) (x2 ↦r term_var "x") ω ∗
          asn_formula (formula_eq an (term_binop bop.plus a (term_val _ (Z.of_nat 12 : Val ty.int)))).

    End ContractAddr.

    Example vc1 : 𝕊 ε :=
      let vc1 := BlockVerificationDerived2.VC__addr pre1' block1 post1' in
      let vc2 := Postprocessing.prune vc1 in
      let vc3 := Postprocessing.solve_evars vc2 in
      let vc4 := Postprocessing.solve_uvars vc3 in
      vc4.

    Lemma sat_vc1' : VerificationConditionWithErasure (Erasure.erase_symprop vc1).
    Proof.
      compute. constructor. cbv - [Z.sub Z.add]. lia.
    Qed.

  End Example.

  Section FemtoKernel.
    Import bv.notations.
    Import ListNotations.
    Open Scope hex_Z_scope.

    Definition zero : RegIdx := [bv 0].
    Definition ra : RegIdx := [bv 1].
(*     MAX := 2^30; *)
(* (*     assembly source: *) *)
(* CODE:   UTYPE #HERE ra RISCV_AUIPC *) (* 0 *)
(*         ADDI RA, RA, (ADV - #PREVHERE) *) (* 4 *)
(*         CSR pmpaddr0 ra r0 CSRRW; *) (* 8 *)
(*         UTYPE MAX ra RISCV_LUI; *) (* 12 *)
(*         CSR pmpaddr1 ra r0 CSRRW; *) (* 16 *)
(*         UTYPE (pure_pmpcfg_ent_to_bits { L := false; A := OFF; X := false; W := false; R := false }) ra RISCV_LUI; *) (* 20 *)
(*         CSR pmp0cfg ra r0 CSRRW; *) (* 24 *)
(*         UTYPE (pure_pmpcfg_ent_to_bits { L := false; A := TOR; X := true; W := true; R := true }) ra RISCV_LUI; *) (* 28 *)
(*         CSR pmp1cfg ra r0 CSRRW; *) (* 32 *)
(*         UTYPE #HERE ra RISCV_AUIPC *) (* 36 *)
(*         ADDI RA, RA, (ADV - #PREVHERE) *) (* 40 *)
(*         CSR epc ra r0 CSRRW; *) (* 44 *)
(*         UTYPE #HERE ra RISCV_AUIPC *) (* 48 *)
(*         ADDI RA, RA, (IH - #PREVHERE) *) (* 52 *)
(*         CSR Tvec ra r0 CSRRW; *) (* 56 *)
(*         UTYPE (pure_mstatus_to_bits { MPP := User }) ra RISCV_LUI; *) (* 60 *)
(*         CSR Mstatus ra r0 CSRRW; *) (* 64 *)
(*         MRET *) (* 68 *)

(*     IH: UTYPE 0 ra RISCV_AUIPC *) (* 72 *)
(*         load (#HERE - 4 - DATA) ra ra; *) (* 76 *)
(*         MRET *) (* 80 *)
(* DATA:   42 *) (* 84 *)
(* ADV:    ... (anything) *) (* 88 *)
(*     } *)

    Definition pure_privilege_to_bits : Privilege -> Xlenbits :=
      fun p => match p with | Machine => 3%Z | User => 0%Z end.

    Definition pure_mstatus_to_bits : Mstatus -> Xlenbits :=
      fun '(MkMstatus mpp) => Z.shiftl (pure_privilege_to_bits mpp) 11.

    Definition pure_pmpAddrMatchType_to_bits : PmpAddrMatchType -> Z:=
      fun mt => match mt with
                | OFF => 0%Z
                | TOR => 1%Z
                end.

    Definition pure_pmpcfg_ent_to_bits : Pmpcfg_ent -> Xlenbits :=
      fun ent =>
        match ent with
        | MkPmpcfg_ent L A X W R =>
            let l := Z.shiftl (if L then 1 else 0) 7 in
            let a := Z.shiftl (pure_pmpAddrMatchType_to_bits A) 3 in
            let x := Z.shiftl (if X then 1 else 0) 2 in
            let w := Z.shiftl (if W then 1 else 0) 1 in
            let r := Z.shiftl (if R then 1 else 0) 0 in
            Z.lor l (Z.lor a (Z.lor x (Z.lor w r)))
        end%Z.

    Definition femto_address_max := 2^30.
    Definition femto_pmpcfg_ent0 : Pmpcfg_ent := MkPmpcfg_ent false OFF false false false.
    Definition femto_pmpcfg_ent0_bits : Val ty_xlenbits := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent0.
    Definition femto_pmpcfg_ent1 : Pmpcfg_ent := MkPmpcfg_ent false TOR true true true.
    Definition femto_pmpcfg_ent1_bits : Val ty_xlenbits := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent1.
    Definition femto_pmpentries : list PmpEntryCfg := [(femto_pmpcfg_ent0, 88); (femto_pmpcfg_ent1, femto_address_max)]%list.

    Definition femto_mstatus := pure_mstatus_to_bits (MkMstatus User ).

    Example femtokernel_init : list AST :=
      [
        UTYPE 0 ra RISCV_AUIPC
      ; ITYPE 88 ra ra RISCV_ADDI
      ; CSR MPMPADDR0 ra zero CSRRW
      ; UTYPE femto_address_max ra RISCV_LUI
      ; CSR MPMPADDR1 ra zero CSRRW
      ; UTYPE femto_pmpcfg_ent0_bits ra RISCV_LUI
      ; CSR MPMP0CFG ra zero CSRRW
      ; UTYPE femto_pmpcfg_ent1_bits ra RISCV_LUI
      ; CSR MPMP1CFG ra zero CSRRW
      ; UTYPE 0 ra RISCV_AUIPC
      ; ITYPE 52 ra ra RISCV_ADDI
      ; CSR MEpc ra zero CSRRW
      ; UTYPE 0 ra RISCV_AUIPC
      ; ITYPE 24 ra ra RISCV_ADDI
      ; CSR MTvec ra zero CSRRW
      ; UTYPE femto_mstatus ra RISCV_LUI
      ; CSR MStatus ra zero CSRRW
      ; MRET
      ].

    Example femtokernel_handler : list AST :=
      [ UTYPE 0 ra RISCV_AUIPC
      ; LOAD 12 ra ra
      ; MRET
      ].

    Local Notation "p '∗' q" := (asn_sep p q).
    Local Notation "r '↦' val" := (asn_chunk (chunk_ptsreg r val)) (at level 79).
    Local Notation "a '↦[' n ']' xs" := (asn_chunk (chunk_user ptstomem [a; n; xs])) (at level 79).
    Local Notation "a '↦ₘ' t" := (asn_chunk (chunk_user ptsto [a; t])) (at level 70).
    Local Notation "'∃' w ',' a" := (asn_exist w _ a) (at level 79, right associativity).
    Local Notation "x + y" := (term_binop bop.plus x y) : exp_scope.
    Local Notation "a '=' b" := (asn_eq a b).

    Let Σ__femtoinit : LCtx := [].
    Let W__femtoinit : World := MkWorld Σ__femtoinit [].

    Example femtokernel_default_pmpcfg : Pmpcfg_ent :=
      {| L := false; A := OFF; X := false; W := false; R := false |}.

    (* DOMI: TODO: replace the pointsto chunk for 84 ↦ 42 with a corresponding invariant *)
    Example femtokernel_init_pre : □ (WTerm ty_xlenbits -> Assertion) W__femtoinit :=
      fun _ _ a =>
        (a = term_val ty_word 0) ∗
      (∃ "v", mstatus ↦ term_var "v") ∗
      (∃ "v", mtvec ↦ term_var "v") ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (∃ "v", mepc ↦ term_var "v") ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      (∃ "v", x1 ↦ term_var "v") ∗
      (∃ "v", x2 ↦ term_var "v") ∗
      (∃ "v", x3 ↦ term_var "v") ∗
      (∃ "v", x4 ↦ term_var "v") ∗
      (∃ "v", x5 ↦ term_var "v") ∗
      (∃ "v", x6 ↦ term_var "v") ∗
      (∃ "v", x7 ↦ term_var "v") ∗
      (pmp0cfg ↦ term_val ty_pmpcfg_ent femtokernel_default_pmpcfg)  ∗
      (pmp1cfg ↦ term_val ty_pmpcfg_ent femtokernel_default_pmpcfg)  ∗
      (∃ "v", pmpaddr0 ↦ term_var "v") ∗
      (∃ "v", pmpaddr1 ↦ term_var "v") ∗
      (a + (term_val ty_xlenbits 84) ↦ₘ term_val ty_xlenbits 42)%exp.

    Example femtokernel_init_post : □ (WTerm ty_xlenbits -> WTerm ty_xlenbits -> Assertion) W__femtoinit :=
      fun _ _ a na =>
      (
        (∃ "v", mstatus ↦ term_var "v") ∗
          (mtvec ↦ (a + term_val ty_xlenbits 72)) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (∃ "v", mepc ↦ term_var "v") ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          (∃ "v", x1 ↦ term_var "v") ∗
          (∃ "v", x2 ↦ term_var "v") ∗
          (∃ "v", x3 ↦ term_var "v") ∗
          (∃ "v", x4 ↦ term_var "v") ∗
          (∃ "v", x5 ↦ term_var "v") ∗
          (∃ "v", x6 ↦ term_var "v") ∗
          (∃ "v", x7 ↦ term_var "v") ∗
          (pmp0cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent0) ∗
          (pmp1cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent1) ∗
          (pmpaddr0 ↦ a + term_val ty_xlenbits 88) ∗
          (pmpaddr1 ↦ term_val ty_xlenbits femto_address_max) ∗
          (a + (term_val ty_xlenbits 84) ↦ₘ term_val ty_xlenbits 42) ∗
          asn_formula (formula_eq na (a + term_val ty_xlenbits 88))
      )%exp.

    Example vc__femtoinit : 𝕊 Σ__femtoinit :=
      let vc1 := VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post in
      let vc2 := Postprocessing.prune vc1 in
      let vc3 := Postprocessing.solve_evars vc2 in
      let vc4 := Postprocessing.solve_uvars vc3 in
      let vc5 := Postprocessing.prune vc4 in
      vc5.
    (* Import SymProp.notations. *)
    (* Set Printing Depth 200. *)
    (* Print vc__femtoinit. *)

    Lemma sat__femtoinit : VerificationConditionWithErasure (Erasure.erase_symprop vc__femtoinit).
    Proof.
      vm_compute. constructor. vm_compute. intros. auto.
    Qed.

    Let Σ__femtohandler : LCtx := ["epc"::ty_exc_code; "mpp"::ty_privilege].
    Let W__femtohandler : World := MkWorld Σ__femtohandler [].

    Example femtokernel_handler_pre : □ (WTerm ty_xlenbits -> Assertion) W__femtohandler :=
      fun _ ω a =>
        (asn_eq a (term_val ty_word 72)) ∗
      (mstatus ↦ term_record rmstatus [ persist__term (term_var "mpp") ω ]) ∗
      (mtvec ↦ term_val ty_word 72) ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (mepc ↦ persist__term (term_var "epc") ω) ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      (∃ "v", x1 ↦ term_var "v") ∗
      (∃ "v", x2 ↦ term_var "v") ∗
      (∃ "v", x3 ↦ term_var "v") ∗
      (∃ "v", x4 ↦ term_var "v") ∗
      (∃ "v", x5 ↦ term_var "v") ∗
      (∃ "v", x6 ↦ term_var "v") ∗
      (∃ "v", x7 ↦ term_var "v") ∗
      (pmp0cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent0) ∗
      (pmp1cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent1) ∗
      (pmpaddr0 ↦ a + term_val ty_xlenbits 16) ∗
      (pmpaddr1 ↦ term_val ty_xlenbits femto_address_max) ∗
      (a + (term_val ty_xlenbits 12) ↦ₘ term_val ty_xlenbits 42)%exp.

    Example femtokernel_handler_post : □ (WTerm ty_xlenbits -> WTerm ty_xlenbits -> Assertion) W__femtohandler :=
      fun _ ω a na =>
      (
          (mstatus ↦ term_val (ty.record rmstatus) {| MPP := User |}) ∗
          (mtvec ↦ term_val ty_word 72) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (mepc ↦ persist__term (term_var "epc") ω) ∗
          cur_privilege ↦ persist__term (term_var "mpp") ω ∗
          (∃ "v", x1 ↦ term_var "v") ∗
          (∃ "v", x2 ↦ term_var "v") ∗
          (∃ "v", x3 ↦ term_var "v") ∗
          (∃ "v", x4 ↦ term_var "v") ∗
          (∃ "v", x5 ↦ term_var "v") ∗
          (∃ "v", x6 ↦ term_var "v") ∗
          (∃ "v", x7 ↦ term_var "v") ∗
          (pmp0cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent0) ∗
          (pmp1cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent1) ∗
          (pmpaddr0 ↦ a + term_val ty_xlenbits 16) ∗
          (pmpaddr1 ↦ term_val ty_xlenbits femto_address_max) ∗
          (a + (term_val ty_xlenbits 12) ↦ₘ term_val ty_xlenbits 42) ∗
          asn_formula (formula_eq na (persist__term (term_var "epc") ω))
      )%exp.

    Time Example vc__femtohandler : 𝕊 [] :=
      Eval vm_compute in
      let vc1 := VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post in
      let vc2 := Postprocessing.prune vc1 in
      let vc3 := Postprocessing.solve_evars vc2 in
      let vc4 := Postprocessing.solve_uvars vc3 in
      let vc5 := Postprocessing.prune vc4 in
      vc5.
    (* Import SymProp.notations. *)
    (* Set Printing Depth 200. *)
    (* Print vc__femtohandler. *)

    Lemma sat__femtohandler : SymProp.safe vc__femtohandler env.nil.
    Proof.
      vm_compute; auto.
    Qed.

  End FemtoKernel.

End BlockVerificationDerived2.

Module BlockVerificationDerivedSem.
  Import Contracts.
  Import RiscvPmpBlockVerifSpec.
  Import weakestpre.
  Import tactics.
  Import BlockVerificationDerived.
  Import Katamaran.Shallow.Executor.
  Import Model.
  Import RiscvPmpModel.
  Import RiscvPmpIrisResources.
  Module PLOG <: ProgramLogicOn RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec.
    Include ProgramLogicOn RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec.
  End PLOG.

  Module Import RiscvPmpIrisModel := IrisInstanceWithContracts RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec RiscvPmpSemantics RiscvPmpIrisPrelims RiscvPmpIrisParams RiscvPmpIrisResources RiscvPmpIrisPredicates RiscvPmpModel PLOG.

  Lemma foreignSemBlockVerif `{sailGS Σ} : ForeignSem.
  Proof.
    intros Γ τ Δ f es δ.
    destruct f; cbn.
  Admitted.

  Lemma lemSemBlockVerif `{sailGS Σ} : LemmaSem.
  Proof.
    intros Δ [].
    - intros ι. now iIntros "_".
    - intros ι. now iIntros "_".
    - intros ι. now iIntros "_".
    - intros ι. now iIntros "_".
    - intros ι. now iIntros "_".
    - intros ι. now iIntros "_".
    - intros ι. now iIntros "_".
  Qed.

  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.

  Definition semTripleOneInstr `{sailGS Σ} (PRE : iProp Σ) (a : AST) (POST : iProp Σ) : iProp Σ :=
    semTriple [a : Val (type ("ast" :: ty_ast))]%env PRE (FunDef execute) (fun ret _ => ⌜ret = RETIRE_SUCCESS⌝ ∗ POST)%I.

  Module ValidContractsBlockVerif.
    Import Contracts.
    Import RiscvPmpSignature.
    Include ShallowExecOn RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec.
    Include ProgramLogicOn RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec.
    Include SymbolicExecOn RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec RiscvPmpSolver.
    Include Shallow.Soundness.Soundness RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec.
    Include Katamaran.Symbolic.Soundness.Soundness RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec RiscvPmpSolver.

    Lemma contractsVerified `{sailGS Σ} : ProgramLogic.ValidContractCEnv (PI := PredicateDefIProp).
    Proof.
      intros Γ τ f.
      destruct f; intros c eq; inversion eq; subst; clear eq.
      - eapply shallow_vcgen_soundness.
        eapply symbolic_vcgen_soundness.
        eapply Symbolic.validcontract_reflect_sound.
        eapply RiscvPmpSpecVerif.valid_execute_rX.
      - eapply shallow_vcgen_soundness.
        eapply symbolic_vcgen_soundness.
        eapply Symbolic.validcontract_reflect_sound.
        eapply RiscvPmpSpecVerif.valid_execute_wX.
    Admitted.

    Lemma contractsSound `{sailGS Σ} : ⊢ ValidContractEnvSem CEnv.
    Proof.
      eauto using sound, foreignSemBlockVerif, lemSemBlockVerif, contractsVerified.
    Admitted.

    Lemma sound_exec_instruction {ast} `{sailGS Σ} :
      SymProp.safe (exec_instruction (w := wnil) ast (fun _ _ res _ h => SymProp.block) env.nil []%list) env.nil ->
      ⊢ semTripleOneInstr emp%I ast emp%I.
    Proof.
      unfold exec_instruction, exec_instruction', assert.
      iIntros (safe_exec) "".
      rewrite <-SymProp.safe_debug_safe in safe_exec.
      rewrite <-SymProp.wsafe_safe in safe_exec.
      iApply (sound_stm foreignSemBlockVerif lemSemBlockVerif).
    Admitted.
    (*   - refine (exec_sound 3 _ _ _ []%list _). *)
    (*     enough (CMut.bind (CMut.exec 3 (FunDef execute)) (fun v => CMut.assert_formula (v = RETIRE_SUCCESS)) (fun _ _ _ => True) [ast] []%list). *)
    (*     + unfold CMut.bind, CMut.assert_formula, CMut.dijkstra, CDijk.assert_formula in H0. *)
    (*       refine (exec_monotonic _ _ _ _ _ _ _ H0). *)
    (*       intros ret δ h [-> _]; cbn. *)
    (*       iIntros "_". iPureIntro. now split. *)
    (*     + refine (approx_exec _ _ _ _ _ safe_exec); cbn; try trivial; try reflexivity. *)
    (*       intros w ω ι _ Hpc tr ? -> δ δ' Hδ h h' Hh. *)
    (*       refine (approx_assert_formula _ _ _ (a := fun _ _ _ => True) _ _ _); *)
    (*         try assumption; try reflexivity. *)
    (*       constructor. *)
    (*   - do 2 iModIntro. *)
    (*     iApply contractsSound. *)
    (* Qed. *)
  End ValidContractsBlockVerif.

End BlockVerificationDerivedSem.

Module BlockVerificationDerived2Concrete.
  Import Contracts.
  Import RiscvPmpSignature.
  Include ShallowExecOn RiscvPmpBase RiscvPmpSignature RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifSpec.

  Definition M : Type -> Type := CHeapSpecM [] [].

  Definition pure {A} : A -> M A := CHeapSpecM.pure.
  Definition bind {A B} : M A -> (A -> M B) -> M B := CHeapSpecM.bind.
  Definition angelic {σ} : M (Val σ) := @CHeapSpecM.angelic [] σ.
  Definition demonic {σ} : M (Val σ) := @CHeapSpecM.demonic [] σ.
  Definition assert : Prop -> M unit := CHeapSpecM.assert_formula.
  Definition assume : Prop -> M unit := CHeapSpecM.assume_formula.

  Definition produce_chunk : SCChunk -> M unit := CHeapSpecM.produce_chunk.
  Definition consume_chunk : SCChunk -> M unit := CHeapSpecM.consume_chunk.

  Definition produce {Σ} : Valuation Σ -> Assertion Σ -> M unit := CHeapSpecM.produce.
  Definition consume {Σ} : Valuation Σ -> Assertion Σ -> M unit := CHeapSpecM.consume.

  Local Notation "x <- ma ;; mb" :=
    (bind ma (fun x => mb))
      (at level 80, ma at level 90, mb at level 200, right associativity).

  Print SCChunk.

  Definition exec_instruction_any__c (i : AST) : Val ty_xlenbits -> M (Val ty_xlenbits) :=
    let inline_fuel := 3%nat in
    fun a =>
      _ <- produce_chunk (scchunk_ptsreg pc a) ;;
      _ <- produce_chunk (scchunk_user ptstoinstr [a; i]) ;;
      an <- @demonic _ ;;
      _ <- produce_chunk (scchunk_ptsreg nextpc an) ;;
      _ <- CHeapSpecM.exec inline_fuel (FunDef step) ;;
      _ <- consume_chunk (scchunk_ptsreg pc a) ;; (* TODO: a + 4! *)
      _ <- consume_chunk (scchunk_user ptstoinstr [a ; i]) ;;
      na <- @angelic _ ;;
      _ <- consume_chunk (scchunk_ptsreg nextpc na) ;;
      pure na.

  Fixpoint exec_block_addr__c (b : list AST) : Val ty_xlenbits -> M (Val ty_xlenbits) :=
    fun a =>
      match b with
      | nil       => pure a
      | cons i b' =>
        a' <- exec_instruction_any__c i a ;;
        @exec_block_addr__c b' a'
      end.

  (* Definition exec_double_addr__c *)
  (*   (req : (Val ty_xlenbits -> Prop)) (b : list AST) : M (Val ty_xlenbits) := *)
  (*   an <- @demonic _ ;; *)
  (*   _ <- produce (req an) ;; *)
  (*   @exec_block_addr__c b _ an. *)

End BlockVerificationDerived2Concrete.

Module BlockVerificationDerived2Sem.
  Import Contracts.
  Import RiscvPmpSignature.
  Import BlockVerificationDerivedSem.
  Import RiscvPmpBlockVerifSpec.
  Import weakestpre.
  Import tactics.
  Import BlockVerificationDerived.
  Import Shallow.Executor.
  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.
  Import Model.RiscvPmpModel.
  Import Model.RiscvPmpModel2.
  Import RiscvPmpIrisParams.
  Import RiscvPmpIrisPredicates.
  Import RiscvPmpIrisPrelims.
  Import RiscvPmpIrisResources.

  Definition semTripleOneInstrStep `{sailGS Σ} (PRE : Z -> iProp Σ) (instr : AST) (POST : Z -> Z -> iProp Σ) : iProp Σ :=
    ∀ a an,
    semTriple [] (PRE a ∗ lptsreg pc a ∗ interp_ptsto_instr (mG := sailGS_memGS) a instr)
      (FunDef RiscvPmpProgram.step)
      (fun ret _ => lptsreg pc an ∗ interp_ptsto_instr (mG := sailGS_memGS) a instr ∗ POST a an)%I.

  Lemma sound_exec_instruction2 `{sailGS Σ} {instr} :
    SymProp.safe (exec_instruction (w := wnil) instr (fun _ _ res _ h => SymProp.block) env.nil []%list) env.nil ->
    ⊢ semTripleOneInstrStep (fun _ => emp)%I instr (fun _ _ => emp)%I.
  Proof.
  Admitted.

  Local Notation "a '↦' t" := (reg_pointsTo a t) (at level 79).
  Local Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 79).

  Fixpoint ptsto_instrs `{sailGS Σ} (a : Z) (instrs : list AST) : iProp Σ :=
    match instrs with
    | cons inst insts => (interp_ptsto_instr (mG := sailGS_memGS) a inst ∗ ptsto_instrs (a + 4) insts)%I
    | nil => True%I
    end.

  Definition advAddrs := seqZ 88 (maxAddr - 88 + 1).

  (* Lemma liveAddr_split : liveAddrs = seqZ minAddr 88 ++ advAddrs. *)
  (* Proof. *)
  (*   unfold liveAddrs. *)
  (*   change 88%Z with (minAddr + 88)%Z at 2. *)
  (*   replace (maxAddr - minAddr + 1)%Z with (88 + (maxAddr - 88 - minAddr + 1))%Z by lia. *)
  (*   eapply seqZ_app; unfold minAddr, maxAddr; lia. *)
  (* Qed. *)

  Global Instance dec_has_some_access {ents p1} : forall x, Decision (exists p2, Pmp_access x ents p1 p2).
  Proof.
    intros x.
    eapply finite.exists_dec.
    intros p2.
    unfold Pmp_access.
    destruct (decide_pmp_access x ents p1 p2); [left|right]; intuition.
  Defined.

  Lemma liveAddr_filter_advAddr : filter
                 (λ x : Val ty_exc_code,
                    (∃ p : Val ty_access_type, Pmp_access x BlockVerificationDerived2.femto_pmpentries User p)%type)
                 liveAddrs = advAddrs.
  Proof.
    now compute.
  Qed.

  Lemma big_sepL_filter `{BiAffine PROP} {A : Type} {l : list A}
      {φ : A → Prop} (dec : ∀ x, Decision (φ x)) (Φ : A -> PROP) :
    ([∗ list] x ∈ filter φ l, Φ x) ⊣⊢
    ([∗ list] x ∈ l, ⌜φ x⌝ -∗ Φ x).
  Proof. induction l.
         - now cbn.
         - cbn.
           destruct (decide (φ a)) as [Hφ|Hnφ].
           + rewrite big_opL_cons.
             rewrite <-IHl.
             iSplit; iIntros "[Ha Hl]"; iFrame; try done.
             now iApply ("Ha" $! Hφ).
           + rewrite <-IHl.
             iSplit.
             * iIntros "Hl"; iFrame; iIntros "%Hφ"; intuition.
             * iIntros "[Ha Hl]"; now iFrame.
  Qed.

  Lemma memAdv_pmpPolicy `{sailGS Σ} :
    (ptstoSthL (mG := sailGS_memGS) advAddrs ⊢
      interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs BlockVerificationDerived2.femto_pmpentries User)%I.
  Proof.
    iIntros "Hadv".
    unfold interp_pmp_addr_access.
    rewrite <-(big_sepL_filter).
    unfold ptstoSthL.
    now rewrite <- liveAddr_filter_advAddr.
  Qed.

  Definition femto_inv_ns : ns.namespace := (ns.ndot ns.nroot "femto_inv_ns").

  Import iris.base_logic.lib.invariants.
  (* This lemma transforms the postcondition of femtokernel_init into the precondition of the universal contract, so that we can use the UC to verify the invocation of untrusted code.
   *)

  Definition femto_inv_fortytwo `{sailGS Σ} : iProp Σ :=
        inv femto_inv_ns (interp_ptsto (mG := sailGS_memGS) 84 42).

  Definition femto_handler_pre `{sailGS Σ} mpp epc : iProp Σ :=
      (mstatus ↦ {| MPP := mpp |}) ∗
      (mtvec ↦ 72) ∗
      (∃ v, mcause ↦ v) ∗
      (mepc ↦ epc) ∗
      cur_privilege ↦ Machine ∗
      (∃ v, x1 ↦ v) ∗
      (∃ v, x2 ↦ v) ∗
      (∃ v, x3 ↦ v) ∗
      (∃ v, x4 ↦ v) ∗
      (∃ v, x5 ↦ v) ∗
      (∃ v, x6 ↦ v) ∗
      (∃ v, x7 ↦ v) ∗
      interp_pmp_entries BlockVerificationDerived2.femto_pmpentries ∗
      femto_inv_fortytwo ∗
      pc ↦ 72 ∗
      ptsto_instrs 72 BlockVerificationDerived2.femtokernel_handler.

    Example femto_handler_post `{sailGS Σ} epc : iProp Σ :=
      (mstatus ↦ {| MPP := User |}) ∗
        (mtvec ↦ 72) ∗
        (∃ v, mcause ↦ v) ∗
        (mepc ↦ epc) ∗
        cur_privilege ↦ User ∗
        (∃ v, x1 ↦ v) ∗
        (∃ v, x2 ↦ v) ∗
        (∃ v, x3 ↦ v) ∗
        (∃ v, x4 ↦ v) ∗
        (∃ v, x5 ↦ v) ∗
        (∃ v, x6 ↦ v) ∗
        (∃ v, x7 ↦ v) ∗
        interp_pmp_entries BlockVerificationDerived2.femto_pmpentries ∗
        femto_inv_fortytwo ∗
        pc ↦ epc ∗
        ptsto_instrs 72 BlockVerificationDerived2.femtokernel_handler.

  Definition femto_handler_contract `{sailGS Σ} : iProp Σ :=
    ∀ epc mpp,
        femto_handler_pre mpp epc -∗
          (femto_handler_post epc -∗ LoopVerification.WP_loop) -∗
          LoopVerification.WP_loop.

  Axiom femto_handler_verified : forall `{sailGS Σ}, ⊢ femto_handler_contract.

  Lemma femtokernel_hander_safe `{sailGS Σ} {mepcv}:
    ⊢ mstatus ↦ {| MPP := User |} ∗
       (mtvec ↦ 72) ∗
        (∃ v, mcause ↦ v) ∗
        (mepc ↦ mepcv) ∗
        cur_privilege ↦ Machine ∗
        interp_gprs ∗
        interp_pmp_entries BlockVerificationDerived2.femto_pmpentries ∗
        femto_inv_fortytwo ∗
        (pc ↦ 72) ∗
        interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs BlockVerificationDerived2.femto_pmpentries User ∗
        (∃ v, nextpc ↦ v) ∗
        (* ptsto_instrs 0 femtokernel_init ∗  (domi: init code not actually needed anymore, can be dropped) *)
        ptsto_instrs 72 BlockVerificationDerived2.femtokernel_handler
        -∗
        LoopVerification.WP_loop.
  Proof.
    unfold interp_gprs; cbn -[interp_pmp_entries].
    rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
    iIntros "".
    iLöb as "Hind".
    iIntros "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmpentries & Hfortytwo & Hpc & Hmem & Hnextpc & Hinstrs)".

    iApply (femto_handler_verified $! mepcv User with "[Hmstatus Hmtvec Hmcause Hmepc Hcurpriv Hgprs Hpmpentries Hfortytwo Hpc Hinstrs] [Hmem Hnextpc]").
    - unfold femto_handler_pre; iFrame.
      iDestruct "Hgprs" as "(? & ? & ? & ? & ? & ? & ? & ? & _)".
      now iFrame.
    - iIntros "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & Hpmpentries & Hfortytwo & Hpc & Hinstrs)".
      iApply LoopVerification.valid_semTriple_loop.
      iSplitL "Hmem Hnextpc Hmstatus Hmtvec Hmcause Hmepc Hcurpriv Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hpmpentries Hpc".
      + unfold LoopVerification.Execution.
        iFrame.
        iSplitR "Hpc".
        * unfold interp_gprs; cbn -[interp_pmp_entries].
          rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
          now iFrame.
        * now iExists _.
      + iSplitL "".
        iModIntro.
        unfold LoopVerification.CSRMod.
        iIntros "(_ & _ & _ & %eq & _)".
        inversion eq.

        iSplitR "".
        iModIntro.
        unfold LoopVerification.Trap.
        iIntros "(Hmem & Hgprs & Hpmpentries & Hmcause & Hcurpriv & Hnextpc & Hpc & Hmtvec & Hmstatus & Hmepc)".
        iApply "Hind".
        unfold interp_gprs; cbn -[interp_pmp_entries].
        rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
        iFrame.
        now iExists _.

        iModIntro.
        unfold LoopVerification.Recover.
        iIntros "(_ & _ & _ & %eq & _)".
        inversion eq.
  Qed.

  Lemma femtokernel_manualStep2 `{sailGS Σ} :
    ⊢ (∃ mpp, mstatus ↦ {| MPP := mpp |}) ∗
       (mtvec ↦ 72) ∗
        (∃ v, mcause ↦ v) ∗
        (∃ v, mepc ↦ v) ∗
        cur_privilege ↦ User ∗
        interp_gprs ∗
        interp_pmp_entries BlockVerificationDerived2.femto_pmpentries ∗
         (interp_ptsto (mG := sailGS_memGS) 84 42) ∗
        (pc ↦ 88) ∗
        (∃ v, nextpc ↦ v) ∗
        (* ptsto_instrs 0 femtokernel_init ∗  (domi: init code not actually needed anymore, can be dropped) *)
        ptsto_instrs 72 BlockVerificationDerived2.femtokernel_handler ∗
        ptstoSthL (mG := sailGS_memGS) advAddrs
        ={⊤}=∗
        ∃ mpp mepcv, LoopVerification.loop_pre User User 72 72 BlockVerificationDerived2.femto_pmpentries BlockVerificationDerived2.femto_pmpentries mpp mepcv ∗
        femto_inv_fortytwo.
  Proof.
    iIntros "([%mpp Hmst] & Hmtvec & [%mcause Hmcause] & [%mepc Hmepc] & Hcurpriv & Hgprs & Hpmpcfg & Hfortytwo & Hpc & Hnpc & Hhandler & Hmemadv)".
    iExists mpp, mepc.
    unfold LoopVerification.loop_pre, LoopVerification.Execution, interp_gprs.
    rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
    iFrame.

    iMod (inv_alloc femto_inv_ns ⊤ (interp_ptsto (mG := sailGS_memGS) 84 42) with "Hfortytwo") as "#Hinv".
    change (inv femto_inv_ns (84 ↦ₘ 42)) with femto_inv_fortytwo.
    iModIntro.

    iSplitR ""; try done.
    iSplitL "Hmcause Hpc Hmemadv".
    iSplitL "Hmemadv".
    now iApply memAdv_pmpPolicy.
    iSplitL "Hmcause".
    now iExists mcause.
    iExists 88; iFrame.

    iSplitL "".
    iModIntro.
    unfold LoopVerification.CSRMod.
    iIntros "(_ & _ & _ & %eq & _)".
    inversion eq.

    iSplitL.
    unfold LoopVerification.Trap.
    iModIntro.
    iIntros "(Hmem & Hgprs & Hpmpents & Hmcause & Hcurpriv & Hnpc & Hpc & Hmtvec & Hmstatus & Hmepc)".
    iApply femtokernel_hander_safe.
    iFrame.
    iSplitR; try done.
    now iExists _.

    iModIntro.
    unfold LoopVerification.Recover.
    iIntros "(_ & _ & _ & %eq & _)".
    inversion eq.
  Qed.

  Definition femto_init_pre `{sailGS Σ} : iProp Σ :=
      (∃ v, mstatus ↦ v) ∗
      (∃ v, mtvec ↦ v) ∗
      (∃ v, mcause ↦ v) ∗
      (∃ v, mepc ↦ v) ∗
      cur_privilege ↦ Machine ∗
      (∃ v, x1 ↦ v) ∗
      (∃ v, x2 ↦ v) ∗
      (∃ v, x3 ↦ v) ∗
      (∃ v, x4 ↦ v) ∗
      (∃ v, x5 ↦ v) ∗
      (∃ v, x6 ↦ v) ∗
      (∃ v, x7 ↦ v) ∗
      pmp0cfg ↦ BlockVerificationDerived2.femtokernel_default_pmpcfg ∗
      pmp1cfg ↦ BlockVerificationDerived2.femtokernel_default_pmpcfg ∗
      (∃ v, pmpaddr0 ↦ v) ∗
      (∃ v, pmpaddr1 ↦ v) ∗
      pc ↦ 0 ∗
      ptsto_instrs 0 BlockVerificationDerived2.femtokernel_init.

    Example femto_init_post `{sailGS Σ} : iProp Σ :=
      (∃ v, mstatus ↦ v) ∗
        (mtvec ↦ 72) ∗
        (∃ v, mcause ↦ v) ∗
        (∃ v, mepc ↦ v) ∗
        cur_privilege ↦ User ∗
        (∃ v, x1 ↦ v) ∗
        (∃ v, x2 ↦ v) ∗
        (∃ v, x3 ↦ v) ∗
        (∃ v, x4 ↦ v) ∗
        (∃ v, x5 ↦ v) ∗
        (∃ v, x6 ↦ v) ∗
        (∃ v, x7 ↦ v) ∗
        pmp0cfg ↦ BlockVerificationDerived2.femto_pmpcfg_ent0 ∗
        pmp1cfg ↦ BlockVerificationDerived2.femto_pmpcfg_ent1 ∗
        (pmpaddr0 ↦ 88) ∗
        (pmpaddr1 ↦ BlockVerificationDerived2.femto_address_max) ∗
        pc ↦ 88 ∗
        ptsto_instrs 0 BlockVerificationDerived2.femtokernel_init.

  Definition femto_init_contract `{sailGS Σ} : iProp Σ :=
    femto_init_pre -∗
      (femto_init_post -∗ LoopVerification.WP_loop) -∗
          LoopVerification.WP_loop.

  Axiom femto_init_verified : forall `{sailGS Σ}, ⊢ femto_init_contract.

  Lemma femtokernel_init_safe `{sailGS Σ} :
    ⊢ (∃ v, mstatus ↦ v) ∗
      (∃ v, mtvec ↦ v) ∗
      (∃ v, mcause ↦ v) ∗
      (∃ v, mepc ↦ v) ∗
      cur_privilege ↦ Machine ∗
      interp_gprs ∗
      reg_pointsTo pmp0cfg BlockVerificationDerived2.femtokernel_default_pmpcfg ∗
      (∃ v, reg_pointsTo pmpaddr0 v) ∗
      reg_pointsTo pmp1cfg BlockVerificationDerived2.femtokernel_default_pmpcfg ∗
      (∃ v, reg_pointsTo pmpaddr1 v) ∗
      (pc ↦ 0) ∗
      interp_ptsto (mG := sailGS_memGS) 84 42 ∗
      ptstoSthL (mG := sailGS_memGS) advAddrs ∗
      (∃ v, nextpc ↦ v) ∗
      ptsto_instrs 0 BlockVerificationDerived2.femtokernel_init ∗
      ptsto_instrs 72 BlockVerificationDerived2.femtokernel_handler
      -∗
      LoopVerification.WP_loop.
  Proof.
    iIntros "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1 & Hpc & Hfortytwo & Hadv & Hnextpc & Hinit & Hhandler)".
    unfold interp_gprs.
    rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
    iDestruct "Hgprs" as "(_ & Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & _)".
    iApply (femto_init_verified with "[Hmstatus Hmtvec Hmcause Hmepc Hcurpriv Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hpmp0cfg Hpmpaddr0 Hpmp1cfg Hpmpaddr1 Hpc Hinit]").
    - unfold femto_init_pre.
      iFrame.
    - iIntros "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1 & Hpc & Hinit)".
      iAssert (interp_pmp_entries BlockVerificationDerived2.femto_pmpentries) with "[Hpmp0cfg Hpmpaddr0 Hpmp1cfg Hpmpaddr1]" as "Hpmpents".
      { unfold interp_pmp_entries; cbn; iFrame. }
      iAssert interp_gprs with "[Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7]" as "Hgprs".
      { unfold interp_gprs.
        rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
        iFrame.
        now iExists 0.
      }
      iApply fupd_wp.
      iMod (femtokernel_manualStep2 with "[Hmstatus Hmtvec Hmcause Hgprs Hcurpriv Hpmpents Hfortytwo Hpc Hnextpc Hhandler Hadv Hmepc ]") as "[%mpp [%mepcv [Hlooppre Hfortytwo]]]".
      { iFrame.
        iDestruct "Hmstatus" as "[%mst Hmstatus]".
        destruct mst as [mpp].
        now iExists mpp.
      }
      iApply (LoopVerification.valid_semTriple_loop $! User User 72 72 BlockVerificationDerived2.femto_pmpentries BlockVerificationDerived2.femto_pmpentries mpp mepcv).
      iModIntro.
      iExact "Hlooppre".
  Qed.

  Print Assumptions femtokernel_init_safe.

End BlockVerificationDerived2Sem.
