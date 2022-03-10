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
     Model.
From Katamaran Require Import
     Iris.Model
     Notations
     SemiConcrete.Mutator
     SemiConcrete.Sound
     Sep.Hoare
     Sep.Logic
     Semantics
     Specification
     Symbolic.Mutator
     Symbolic.Solver
     Symbolic.Sound
     Symbolic.Propositions
     Symbolic.Worlds.
From Equations Require Import
     Equations.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Inductive PurePredicate : Set :=
.

Inductive Predicate : Set :=
| pmp_entries
| ptsto
| encodes_instr
| ptstomem
(* | reg_ptsto *)
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

Module RiscvPmpSpec <: Specification RiscvPmpBase.
Module PROG := RiscvPmpProgram.

Section PredicateKit.

  Definition 𝑷 := PurePredicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    end.
  Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
    match p with
    end.

  Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

  Definition pmp_entry_cfg := ty_prod ty_pmpcfg_ent ty_xlenbits.

  Definition 𝑯 := Predicate.
  Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
    match p with
    | pmp_entries => [ty_list pmp_entry_cfg]
    | ptsto       => [ty_xlenbits; ty_xlenbits]
    | encodes_instr => [ty_int; ty_ast]
    | ptstomem    => [ty_xlenbits; ty_int; ty_list ty_word]
    (* | reg_ptsto   => [ty_regno; ty_xlenbits] *)
    end.

  Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
    is_duplicable p :=
      match p with
      | pmp_entries => false
      | ptsto       => false
      | encodes_instr       => true
      | ptstomem    => false
      (* | reg_ptsto   => false *)
      end
    }.
  Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

  Local Arguments Some {_} &.
  Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
    match p with
    | ptsto => Some (MkPrecise [ty_xlenbits] [ty_word] eq_refl)
    | encodes_instr => Some (MkPrecise [ty_int] [ty_ast] eq_refl)
    (* | reg_ptsto => Some (MkPrecise [ty_regno] [ty_word] eq_refl) *)
    | ptstomem    => Some (MkPrecise [ty_xlenbits; ty_int] [ty_list ty_word] eq_refl)
    | _ => None
    end.

End PredicateKit.

Include ContractDeclMixin RiscvPmpBase RiscvPmpProgram.

Section ContractDefKit.

  Notation "a '↦ₘ' t" := (asn_chunk (chunk_user ptsto [a; t])) (at level 70).
  Notation "p '∗' q" := (asn_sep p q).
  Notation "a '=' b" := (asn_eq a b).
  Notation "'∃' w ',' a" := (asn_exist w _ a) (at level 79, right associativity).
  Notation "a '∨' b" := (asn_or a b).
  Notation "a <ₜ b" := (term_binop binop_lt a b) (at level 60).
  Notation "a <=ₜ b" := (term_binop binop_le a b) (at level 60).
  Notation "a &&ₜ b" := (term_binop binop_and a b) (at level 80).
  Notation "a ||ₜ b" := (term_binop binop_or a b) (at level 85).
  Notation asn_match_option T opt xl alt_inl alt_inr := (asn_match_sum T ty_unit opt xl alt_inl "_" alt_inr).
  Notation asn_pmp_entries l := (asn_chunk (chunk_user pmp_entries [l])).

  Definition term_eqb {Σ} (e1 e2 : Term Σ ty_regno) : Term Σ ty_bool :=
    term_binop binop_eq e1 e2.

  Local Notation "e1 '=?' e2" := (term_eqb e1 e2).

  Definition z_term {Σ} : Z -> Term Σ ty_int := term_val ty_int.

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
    asn_if (r =? term_val ty_regno (bv.of_N 1))
           (asn x1)
           (asn_if (r =? term_val ty_regno (bv.of_N 2))
                   (asn x2)
                   (asn_if (r =? term_val ty_regno (bv.of_N 3))
                           (asn x3)
                           asn_default)).

  Definition asn_reg_ptsto {Σ} (r : Term Σ ty_regno) (w : Term Σ ty_word) : Assertion Σ :=
    asn_with_reg r (fun r => asn_chunk (chunk_ptsreg r w)) asn_false.

  Local Notation "e1 ',ₜ' e2" := (term_binop binop_pair e1 e2) (at level 100).

  Notation "r '↦' val" := (asn_chunk (asn_reg_ptsto [r; val])) (at level 70).
  (* TODO: abstract away the concrete type, look into unions for that *)
  (* TODO: length of list should be 16, no duplicates *)
  Definition pmp_entries {Σ} : Term Σ (ty_list (ty_prod ty_pmpcfgidx ty_pmpaddridx)) :=
    term_list
      (cons (term_val ty_pmpcfgidx PMP0CFG ,ₜ term_val ty_pmpaddridx PMPADDR0)
            (cons (term_val ty_pmpcfgidx PMP1CFG ,ₜ term_val ty_pmpaddridx PMPADDR1) nil)).

  End ContractDefKit.

  Local Notation "r '↦' val" := (asn_reg_ptsto r val) (at level 70).
  Local Notation "a '↦ₘ' t" := (asn_chunk (chunk_user ptsto [a; t])) (at level 70).
  Local Notation "p '∗' q" := (asn_sep p q).
  Local Notation "a '=' b" := (asn_eq a b).
  Local Notation "'∃' w ',' a" := (asn_exist w _ a) (at level 79, right associativity).
  Local Notation "a '∨' b" := (asn_or a b).
  Local Notation "a <ₜ b" := (term_binop binop_lt a b) (at level 60).
  Local Notation "a <=ₜ b" := (term_binop binop_le a b) (at level 60).
  Local Notation "a &&ₜ b" := (term_binop binop_and a b) (at level 80).
  Local Notation "a ||ₜ b" := (term_binop binop_or a b) (at level 85).
  Local Notation asn_match_option T opt xl alt_inl alt_inr := (asn_match_sum T ty_unit opt xl alt_inl "_" alt_inr).
  Local Notation asn_pmp_entries l := (asn_chunk (chunk_user pmp_entries [l])).
  Local Notation "e1 ',ₜ' e2" := (term_binop binop_pair e1 e2) (at level 100).


  Definition sep_contract_rX : SepContractFun rX :=
    {| sep_contract_logic_variables := ["rs" :: ty_regno; "w" :: ty_word];
       sep_contract_localstore      := [term_var "rs"];
       sep_contract_precondition    := term_var "rs" ↦ term_var "w";
       sep_contract_result          := "result_rX";
       sep_contract_postcondition   := term_var "rs" ↦ term_var "w" ∗
                                                term_var "result_rX" = term_var "w"
    |}.

  Definition sep_contract_wX : SepContractFun wX :=
    {| sep_contract_logic_variables := ["rs" :: ty_regno; "v" :: ty_xlenbits; "w" :: ty_xlenbits];
       sep_contract_localstore      := [term_var "rs"; term_var "v"];
       sep_contract_precondition    := term_var "rs" ↦ term_var "w";
       sep_contract_result          := "result_wX";
       sep_contract_postcondition   := term_var "rs" ↦ term_var "v" ∗
         term_var "result_wX" = term_val ty_unit tt;
    |}.

  Definition sep_contract_fetch : SepContractFun fetch :=
    {| sep_contract_logic_variables := ["a" :: ty_xlenbits; "w" :: ty_int];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn_chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ₘ term_var "w";
       sep_contract_result          := "result_fetch";
       sep_contract_postcondition   := asn_chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ₘ term_var "w" ∗
                                                 term_var "result_fetch" = term_union fetch_result KF_Base (term_var "w");
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
                                                 term_var "result_tick_pc" = term_val ty_unit tt;
    |}.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | rX                    => Some sep_contract_rX
      | wX                    => Some sep_contract_wX
      | fetch                 => Some sep_contract_fetch
      | mem_read              => Some sep_contract_mem_read
      | tick_pc               => Some sep_contract_tick_pc
      | _                     => None
      end.

  Definition sep_contract_read_ram : SepContractFunX read_ram :=
    {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "w" :: ty_xlenbits];
       sep_contract_localstore      := [term_var "paddr"];
       sep_contract_precondition    := term_var "paddr" ↦ₘ term_var "w";
       sep_contract_result          := "result_read_ram";
       sep_contract_postcondition   := term_var "result_read_ram" = term_var "w";
    |}.

  Definition sep_contract_write_ram : SepContractFunX write_ram :=
    {| sep_contract_logic_variables := ["paddr" :: ty_int; "data" :: ty_word];
       sep_contract_localstore      := [term_var "paddr"; term_var "data"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_write_ram";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition sep_contract_decode    : SepContractFunX decode :=
    {| sep_contract_logic_variables := ["code" :: ty_int; "instr" :: ty_ast];
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

  Definition LEnv : LemmaEnv :=
    fun Δ l =>
      match l with
      | open_gprs      => lemma_open_gprs
      | close_gprs     => lemma_close_gprs
      | open_pmp_entries => lemma_open_pmp_entries
      | close_pmp_entries => lemma_close_pmp_entries
      end.

  Include SpecificationMixin RiscvPmpBase RiscvPmpProgram.
End RiscvPmpSpec.

Module RiscvPmpSpecVerif.

  Import RiscvPmpSpec.
  Module RiscvPmpSolverKit := DefaultSolverKit RiscvPmpBase RiscvPmpSpec.
  Module RiscvPmpSolver := MakeSolver RiscvPmpBase RiscvPmpSpec RiscvPmpSolverKit.

  Module Import RiscvPmpExecutor :=
    MakeExecutor RiscvPmpBase RiscvPmpSpec RiscvPmpSolver.
  Import SMut.
  Import SMut.SMutNotations.

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
  Proof. reflexivity. Qed.

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

  Import RiscvPmpSpec.
  Module RiscvPmpSolverKit := DefaultSolverKit RiscvPmpBase RiscvPmpSpec.
  Module RiscvPmpSolver := MakeSolver RiscvPmpBase RiscvPmpSpec RiscvPmpSolverKit.

  Module Import RiscvPmpExecutor :=
    MakeExecutor RiscvPmpBase RiscvPmpSpec RiscvPmpSolver.
  Import SMut.
  Import SMut.SMutNotations.

  Notation "r '↦' val" := (chunk_ptsreg r val) (at level 79).

  Import ModalNotations.
  Import bv.notations.

  Definition M : TYPE -> TYPE := SMut [] [].

  Definition pure {A} : ⊢ A -> M A := SMut.pure.
  Definition bind {A B} : ⊢ M A -> □(A -> M B) -> M B := SMut.bind.
  Definition angelic {σ} : ⊢ M (STerm σ) := @SMut.angelic [] None σ.
  Definition assert : ⊢ Formula -> M Unit := SMut.assert_formula.
  Definition assume : ⊢ Formula -> M Unit := SMut.assume_formula.

  Definition produce_chunk : ⊢ Chunk -> M Unit := SMut.produce_chunk.
  Definition consume_chunk : ⊢ Chunk -> M Unit := SMut.consume_chunk.

  Definition produce : ⊢ Assertion -> □(M Unit) := SMut.produce.
  Definition consume : ⊢ Assertion -> □(M Unit) := SMut.consume.

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
                 | RISCV_ADD => binop_plus
                 | RISCV_SUB => binop_minus
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
          ["dst" :: ty_xlenbits; "src" :: ty_xlenbits; "size" :: ty_int;
           "srcval" :: ty_list ty_word; "ret" :: ty_xlenbits].

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
      asn_formula (formula_neq (term_var "size") (term_val ty_int 0)) ∗
      term_var "src" ↦[ term_var "size" ] term_var "srcval" ∗
      (∃ "dstval", term_var "dst" ↦[ term_var "size" ] term_var "dstval").

  End MemCopy.

End BlockVerification.


Module BlockVerificationDerived.

  Import RiscvPmpSpec.

  Module RiscvPmpSolverKit := DefaultSolverKit RiscvPmpBase RiscvPmpSpec.
  Module RiscvPmpSolver := MakeSolver RiscvPmpBase RiscvPmpSpec RiscvPmpSolverKit.

  Module Import RiscvPmpExecutor :=
    MakeExecutor RiscvPmpBase RiscvPmpSpec RiscvPmpSolver.
  Import SMut.
  Import SMut.SMutNotations.

  Import ModalNotations.

  Definition M : TYPE -> TYPE := SMut [] [].

  Definition pure {A} : ⊢ A -> M A := SMut.pure.
  Definition bind {A B} : ⊢ M A -> □(A -> M B) -> M B := SMut.bind.
  Definition angelic {σ} : ⊢ M (STerm σ) := @SMut.angelic [] None σ.
  Definition demonic {σ} : ⊢ M (STerm σ) := @SMut.demonic [] None σ.
  Definition assert : ⊢ Formula -> M Unit := SMut.assert_formula.
  Definition assume : ⊢ Formula -> M Unit := SMut.assume_formula.

  Definition produce_chunk : ⊢ Chunk -> M Unit := SMut.produce_chunk.
  Definition consume_chunk : ⊢ Chunk -> M Unit := SMut.consume_chunk.

  Definition produce : ⊢ Assertion -> □(M Unit) := SMut.produce.
  Definition consume : ⊢ Assertion -> □(M Unit) := SMut.consume.

  Notation "ω ∣ x <- ma ;; mb" :=
    (bind ma (fun _ ω x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Definition exec_instruction' (i : AST) : ⊢ M (STerm ty_retired) :=
    let inline_fuel := 3%nat in
    fun w0 POST _ =>
      exec
        default_config inline_fuel (FunDef execute)
        (fun w1 ω01 res _ => POST w1 ω01 res []%env)
        [term_val (type ("ast" :: ty_ast)) i]%env.

  Definition exec_instruction (i : AST) : ⊢ M Unit :=
    fun _ =>
      _ ∣ msg <- @exec_instruction' i _ ;;
      assert (formula_eq msg (term_val ty_retired RETIRE_SUCCESS)).

  Definition exec_instruction2 (i : AST) : ⊢ M Unit :=
    let inline_fuel := 3%nat in
    fun _ =>
      ω1 ∣ a <- @demonic _ _ ;;
      ω2 ∣ _ <- T (produce (asn_chunk (chunk_ptsreg pc a))) ;;
      ω3 ∣ code <- @demonic _ _ ;;
      ω4 ∣ _ <- T (produce (asn_chunk (chunk_user ptsto [persist__term a (ω2 ∘ ω3); code]))) ;;
      ω5 ∣ _ <- T (produce (asn_chunk (chunk_user encodes_instr [ persist__term code ω4 ; term_val ty_ast i]))) ;;
      ω6 ∣ an <- @demonic _ _ ;;
      ω7 ∣ _ <- T (produce (asn_chunk (chunk_ptsreg nextpc an))) ;;
      ω8 ∣ _ <- exec default_config inline_fuel (FunDef step) ;;
      ω9 ∣ _ <- T (consume (asn_chunk (chunk_ptsreg pc (term_binop binop_plus (persist__term a (ω2 ∘ ω3 ∘ ω4 ∘ ω5 ∘ ω6 ∘ ω7 ∘ ω8)) (term_val ty_exc_code 4))))) ;;
      ω10 ∣ _ <- T (consume (asn_chunk (chunk_user ptsto [persist__term a (ω2 ∘ ω3 ∘ ω4 ∘ ω5 ∘ ω6 ∘ ω7 ∘ ω8 ∘ ω9); persist__term code (ω4 ∘ ω5 ∘ ω6 ∘ ω7 ∘ ω8 ∘ ω9)]))) ;;
      ω11 ∣ _ <- T (consume (asn_chunk (chunk_ptsreg nextpc (term_binop binop_plus (persist__term a (ω2 ∘ ω3 ∘ ω4 ∘ ω5 ∘ ω6 ∘ ω7 ∘ ω8 ∘ ω9 ∘ ω10)) (term_val ty_exc_code 4))))) ;;
      pure tt.

  (* Ideally, a block should be a list of non-branching
     instruction plus one final branching instruction *)
  Fixpoint exec_block (b : list AST) : ⊢ M Unit :=
    fun _ =>
      match b with
      | nil       => pure tt
      | cons i b' =>
        _ ∣ _ <- @exec_instruction2 i _ ;;
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

      Let Σ1 : LCtx := ["x" :: ty_xlenbits, "y" :: ty_xlenbits].

      Example pre1 : Assertion Σ1 :=
        x1 ↦r term_var "x" ∗
        x2 ↦r term_var "y".

      Example post1 : Assertion Σ1 :=
        x1 ↦r term_var "y" ∗
        x2 ↦r term_var "x".

    End Contract.

    Time Example vc1 : 𝕊 ε :=
      Eval compute in
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
    Notation "x - y" := (term_binop binop_minus x y) : exp_scope.
    Notation "x + y" := (term_binop binop_plus x y) : exp_scope.

    Lemma sat_vc : SymProp.safe vc1 env.nil.
    Proof.
      cbn.
      repeat constructor; lia.
    Qed.

  End Example.

End BlockVerificationDerived.

Module BlockVerificationDerivedSem.
  Import RiscvPmpSpec.
  Import weakestpre.
  Import tactics.
  Import BlockVerificationDerived.
  Import Katamaran.SemiConcrete.Mutator.
  Include ProgramLogicOn RiscvPmpBase RiscvPmpSpec.
  Include Iris RiscvPmpBase RiscvPmpSpec Model.RiscvPmpSemantics.

  Module RiscvPmpIrisHeapKit <: IrisHeapKit.
    Variable maxAddr : nat.

    Section WithIrisNotations.
      Import iris.bi.interface.
      Import iris.bi.big_op.
      Import iris.base_logic.lib.iprop.
      Import iris.base_logic.lib.gen_heap.

      Definition MemVal : Set := Word.

      Class mcMemGS Σ :=
        McMemGS {
            (* ghost variable for tracking state of registers *)
            mc_ghGS :> gen_heapGS Addr MemVal Σ;
            mc_invNs : namespace
          }.

      Definition memGpreS : gFunctors -> Set := fun Σ => gen_heapGpreS Z MemVal Σ.
      Definition memGS : gFunctors -> Set := mcMemGS.
      Definition memΣ : gFunctors := gen_heapΣ Addr MemVal.

      Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ :=
        fun {Σ} => subG_gen_heapGpreS (Σ := Σ) (L := Addr) (V := MemVal).

      Definition mem_inv : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
        fun {Σ} mG μ => (True)%I.

      Definition mem_res : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
        fun {Σ} mG μ => (True)%I.

      Definition liveAddrs := seqZ 0 maxAddr.
      Definition initMemMap μ := (list_to_map (map (fun a => (a , μ a)) liveAddrs) : gmap Addr MemVal).

      Lemma initMemMap_works μ : map_Forall (λ (a : Addr) (v : MemVal), μ a = v) (initMemMap μ).
      Proof.
        unfold initMemMap.
        rewrite map_Forall_to_list.
        rewrite Forall_forall.
        intros (a , v).
        rewrite elem_of_map_to_list.
        intros el.
        apply elem_of_list_to_map_2 in el.
        apply elem_of_list_In in el.
        apply in_map_iff in el.
        by destruct el as (a' & <- & _).
      Qed.

      Lemma mem_inv_init : forall Σ (μ : Memory), memGpreS Σ ->
        ⊢ |==> ∃ mG : memGS Σ, (mem_inv mG μ ∗ mem_res mG μ)%I.
      Proof.
        iIntros (Σ μ gHP).
        iMod (gen_heap_init (gen_heapGpreS0 := gHP) (L := Addr) (V := MemVal)) as (gH) "[inv _]".
        Unshelve.
        iModIntro.
        iExists (McMemGS gH (nroot .@ "addr_inv")).
        unfold mem_inv, mem_res.
        done.
        apply initMemMap; auto.
      Qed.

      Definition reg_file : gset (bv 2) :=
        list_to_set (finite.enum (bv 2)).

      Definition interp_ptsreg `{sailRegGS Σ} (r : RegIdx) (v : Z) : iProp Σ :=
        match reg_convert r with
        | Some x => reg_pointsTo x v
        | None => True
        end.

      Definition luser_inst `{sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) (p : Predicate) : Env Val (𝑯_Ty p) -> iProp Σ :=
        match p return Env Val (𝑯_Ty p) -> iProp Σ with
        | ptsto           => fun _  => True%I (* TODO: interp_ptst *)
        | BlockVerification.pmp_entries     => fun ts => True%I (* interp_pmp_entries (env.head ts) *)
        | encodes_instr   => fun _ => True%I
        | ptstomem        => fun _ => True%I
        end.

    Definition lduplicate_inst `{sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst mG p ts) ⊢ (luser_inst mG p ts ∗ luser_inst mG p ts).
    Proof.
      iIntros (p ts hdup) "H".
      destruct p; inversion hdup;
      iDestruct "H" as "#H";
      auto.
    Qed.

    End WithIrisNotations.
  End RiscvPmpIrisHeapKit.

  Module Import RiscvPmpIrisInstance := IrisInstance RiscvPmpIrisHeapKit.
  Lemma foreignSem `{sg : sailGS Σ} : ForeignSem (Σ := Σ).
  Proof.
    intros Γ τ Δ f es δ.
    destruct f; cbn.
  Admitted.

  Lemma lemSem `{sg : sailGS Σ} : LemmaSem (Σ := Σ).
  Proof.
    intros Δ [].
    - intros ι. now iIntros "_".
    - intros ι. now iIntros "_".
    - intros ι. now iIntros "_".
    - intros ι. now iIntros "_".
  Qed.

  Include SemiConcrete RiscvPmpBase RiscvPmpSpec.
  Include Katamaran.SemiConcrete.Sound.Soundness RiscvPmpBase RiscvPmpSpec.
  Include RiscvPmpExecutor.
  Include Katamaran.Symbolic.Sound.Soundness RiscvPmpBase RiscvPmpSpec RiscvPmpSolver.
  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.

  Definition semTripleOneInstr `{sailGS Σ} (PRE : iProp Σ) (a : AST) (POST : iProp Σ) : iProp Σ :=
    semTriple [a : Val (type ("ast" :: ty_ast))]%env PRE (FunDef execute) (fun ret _ => ⌜ret = RETIRE_SUCCESS⌝ ∗ POST)%I.

  Lemma contractsVerified `{sG : sailGS Σ} : ValidContractCEnv (PI := PredicateDefIProp (sG := sG)).
  Proof.
    intros Γ τ f.
    destruct f; intros c eq; inversion eq; subst; clear eq.
    - eapply contract_sound.
      eapply symbolic_sound.
      eapply SMut.validcontract_reflect_sound.
      eapply RiscvPmpSpecVerif.valid_execute_rX.
    - eapply contract_sound.
      eapply symbolic_sound.
      eapply SMut.validcontract_reflect_sound.
      eapply RiscvPmpSpecVerif.valid_execute_wX.
  Admitted.

  Lemma contractsSound `{sailGS Σ} : ⊢ ValidContractEnvSem CEnv.
  Proof.
    eauto using sound, foreignSem, lemSem, contractsVerified.
  Qed.

  Lemma sound_exec_instruction `{sailGS Σ} {ast} :
    SymProp.safe (exec_instruction (w := wnil) ast (fun _ _ res _ h => SymProp.block) env.nil []%list) env.nil ->
    ⊢ semTripleOneInstr emp%I ast emp%I.
  Proof.
    unfold exec_instruction, exec_instruction', assert.
    iIntros (safe_exec) "".
    rewrite <-SymProp.safe_debug_safe in safe_exec.
    rewrite <-SymProp.wsafe_safe in safe_exec.
    iApply (sound_stm foreignSem lemSem).
    - refine (exec_sound 3 _ _ _ []%list _).
      enough (CMut.bind (CMut.exec 3 (FunDef execute)) (fun v => CMut.assert_formula (v = RETIRE_SUCCESS)) (fun _ _ _ => True) [ast] []%list).
      + unfold CMut.bind, CMut.assert_formula, CMut.dijkstra, CDijk.assert_formula in H0.
        refine (exec_monotonic _ _ _ _ _ _ _ H0).
        intros ret δ h [-> _]; cbn.
        iIntros "_". iPureIntro. now split.
      + refine (approx_exec _ _ _ _ _ safe_exec); cbn; try trivial; try reflexivity.
        intros w ω ι _ Hpc tr ? -> δ δ' Hδ h h' Hh.
        refine (approx_assert_formula _ _ _ (a := fun _ _ _ => True) _ _ _);
          try assumption; try reflexivity.
        constructor.
    - do 2 iModIntro.
      iApply contractsSound.
  Qed.



End BlockVerificationDerivedSem.
