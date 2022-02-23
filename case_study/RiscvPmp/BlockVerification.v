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
    (* | reg_ptsto   => [ty_regno; ty_xlenbits] *)
    end.

  Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
    is_duplicable p :=
      match p with
      | pmp_entries => false
      | ptsto       => false
      (* | reg_ptsto   => false *)
      end
    }.
  Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

  Local Arguments Some {_} &.
  Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
    match p with
    | ptsto => Some (MkPrecise [ty_xlenbits] [ty_word] eq_refl)
    (* | reg_ptsto => Some (MkPrecise [ty_regno] [ty_word] eq_refl) *)
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

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | rX                    => Some sep_contract_rX
      | wX                    => Some sep_contract_wX
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
    {| sep_contract_logic_variables := ["bv" :: ty_int];
       sep_contract_localstore      := [term_var "bv"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_decode";
       sep_contract_postcondition   := asn_true;
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
    Import bv.notations.
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

  Definition exec_instruction (i : AST) : ⊢ M (STerm ty_retired) :=
    let inline_fuel := 3%nat in
    fun w0 POST _ =>
      exec
        default_config inline_fuel (FunDef execute)
        (fun w1 ω01 res _ => POST w1 ω01 res []%env)
        [term_val (type ("ast" :: ty_ast)) i]%env.

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

      Let Σ1 : LCtx := ["x" :: ty_xlenbits, "y" :: ty_xlenbits].

      Example pre1 : Assertion Σ1 :=
        x1 ↦r term_var "x" ∗
        x2 ↦r term_var "y".

      Example post1 : Assertion Σ1 :=
        x1 ↦r term_var "y" ∗
        x2 ↦r term_var "x".

    End Contract.

    Time Example vc1 : 𝕊 ε :=
      Eval cbv in
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
      unfold vc1.
      repeat constructor;
        cbn; lia.
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
        | pmp_entries     => fun ts => True%I (* interp_pmp_entries (env.head ts) *)
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

  Lemma sound_exec_triple `{sailGS Σ} {ast} :
    SymProp.safe (exec_instruction (w := wnil) ast (fun _ _ res _ h => SymProp.assertk (formula_eq res (term_val ty_retired RETIRE_SUCCESS)) (MkAMessage (BT := RiscvPmpBase.Unit)_ tt) SymProp.block) env.nil []%list) env.nil ->
    ⊢ semTripleOneInstr True%I ast True%I.
  Proof.
    unfold exec_instruction.
    iIntros (safe_exec) "".
    iApply (sound_stm foreignSem lemSem).
    - refine (exec_sound 3 _ _ _ []%list _).
      rewrite <-SymProp.wsafe_safe in safe_exec.
      refine (approx_exec _ _ _ _ _ safe_exec); cbn; try trivial; try reflexivity.
      intros w ω ι _ Hpc tr _ -> δ _ -> h _ -> hyp.
      rewrite SymProp.wsafe_safe in hyp.
      cbn in hyp.
      destruct hyp as [[eq] _].
      cbn in eq; cbn.
      iIntros "_".
      iPureIntro; now split.
    - do 2 iModIntro.
      iIntros (σs σ f).
      destruct f; try done; cbn.
      admit.
      admit.
  Admitted.

End BlockVerificationDerivedSem.
