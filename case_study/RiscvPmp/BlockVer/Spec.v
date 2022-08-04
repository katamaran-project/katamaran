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
     Strings.String.
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
     RiscvPmp.Sig.

Import RiscvPmpProgram.

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
  Definition BEQ (rs1 rs2 : RegIdx) (imm : Z) : AST :=
    BTYPE imm rs2 rs1 RISCV_BEQ.
  Definition BNE (rs1 rs2 : RegIdx) (imm : Z) : AST :=
    BTYPE imm rs2 rs1 RISCV_BNE.
  Definition ADDI (rd rs1 : RegIdx) (imm : Z) : AST :=
    ITYPE imm rs1 rd RISCV_ADDI.
  Definition JALR (rd rs1 : RegIdx) (imm : Z) : AST :=
    RISCV_JALR imm rs1 rd.
  Definition RET : AST :=
    JALR (bv.of_N 0) (bv.of_N 1) 0%Z.
  Definition MV (rd rs1 : RegIdx) : AST :=
    ADDI rd rs1 0%Z.
End Assembly.

Module RiscvPmpBlockVerifSpec <: Specification RiscvPmpBase RiscvPmpProgram RiscvPmpSignature.
  Include SpecificationMixin RiscvPmpBase RiscvPmpProgram RiscvPmpSignature.
  Section ContractDefKit.

  Import asn.notations.
  Notation "a '↦ₘ' t" := (asn.chunk (chunk_user ptsto [a; t])) (at level 70).
  Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user ptstoinstr [a; t])) (at level 70).
  Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
  Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
  Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
  Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
  Notation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
  Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

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
    asn_with_reg r (fun r => asn.chunk (chunk_ptsreg r w)) (w = term_val ty.int 0%Z).

  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

  (* TODO: abstract away the concrete type, look into unions for that *)
  (* TODO: length of list should be 16, no duplicates *)
  Definition pmp_entries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfgidx ty_pmpaddridx)) :=
    term_list
      (cons (term_val ty_pmpcfgidx PMP0CFG ,ₜ term_val ty_pmpaddridx PMPADDR0)
            (cons (term_val ty_pmpcfgidx PMP1CFG ,ₜ term_val ty_pmpaddridx PMPADDR1) nil)).

  End ContractDefKit.

  Import asn.notations.
  (* TODO: This notation is already defined with a different meaning in
     asn.notations. Resolve this.
   *)
  Local Notation "r '↦' val" := (asn_reg_ptsto r val) : asn_scope.
  Local Notation "a '↦ₘ' t" := (asn.chunk (chunk_user ptsto [a; t])) (at level 70).
  Local Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user ptstoinstr [a; t])) (at level 70).
  Local Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
  Local Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
  Local Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
  Local Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
  Local Notation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
  Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).
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
                                       if: term_eqb (term_var "rs") (term_val ty_regno [bv 0])
                                       then term_var "rs" ↦ term_val ty.int 0%Z
                                       else term_var "rs" ↦ term_var "v"
    |}.

  Definition sep_contract_fetch : SepContractFun fetch :=
    {| sep_contract_logic_variables := ["a" :: ty_xlenbits; "w" :: ty.int];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn.chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ₘ term_var "w";
       sep_contract_result          := "result_fetch";
       sep_contract_postcondition   := asn.chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ₘ term_var "w" ∗
                                                 term_var "result_fetch" = term_union fetch_result KF_Base (term_var "w");
    |}.

  Definition sep_contract_fetch_instr : SepContractFun fetch :=
    {| sep_contract_logic_variables := ["a" :: ty_xlenbits; "i" :: ty_ast];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn.chunk (chunk_ptsreg pc (term_var "a")) ∗
                                                 term_var "a" ↦ᵢ term_var "i";
       sep_contract_result          := "result_fetch";
       sep_contract_postcondition   :=
         asn.chunk (chunk_ptsreg pc (term_var "a")) ∗ term_var "a" ↦ᵢ term_var "i" ∗
         asn.exist "w" _
           (term_var "result_fetch" = term_union fetch_result KF_Base (term_var "w") ∗
            asn.chunk (chunk_user encodes_instr [term_var "w"; term_var "i"]));
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
       sep_contract_precondition    := asn.chunk (chunk_ptsreg pc (term_var "ao")) ∗
                                                 asn.chunk (chunk_ptsreg nextpc (term_var "an"));
       sep_contract_result          := "result_tick_pc";
       sep_contract_postcondition   := asn.chunk (chunk_ptsreg pc (term_var "an")) ∗
                                                 asn.chunk (chunk_ptsreg nextpc (term_var "an")) ∗
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
       sep_contract_postcondition   := term_var "paddr" ↦ₘ term_var "w" ∗
                                       term_var "result_read_ram" = term_var "w";
    |}.

  Definition sep_contract_write_ram : SepContractFunX write_ram :=
    {| sep_contract_logic_variables := ["paddr" :: ty.int; "data" :: ty_word];
       sep_contract_localstore      := [term_var "paddr"; term_var "data"];
       sep_contract_precondition    := ∃ "w", (term_var "paddr" ↦ₘ term_var "w");
       sep_contract_result          := "result_write_ram";
       sep_contract_postcondition   := term_var "paddr" ↦ₘ term_var "data" ∗
                                       term_var "result_write_ram" = term_val ty.int 1%Z;
    |}.

  Definition sep_contract_decode    : SepContractFunX decode :=
    {| sep_contract_logic_variables := ["code" :: ty.int; "instr" :: ty_ast];
       sep_contract_localstore      := [term_var "code"];
       sep_contract_precondition    := asn.chunk (chunk_user encodes_instr [term_var "code"; term_var "instr"]);
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
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_close_gprs : SepLemma close_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_open_pmp_entries : SepLemma open_pmp_entries :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_close_pmp_entries : SepLemma close_pmp_entries :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_update_pmp_entries : SepLemma update_pmp_entries :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_extract_pmp_ptsto : SepLemma extract_pmp_ptsto :=
    {| lemma_logic_variables := ["paddr" :: ty_xlenbits];
       lemma_patterns        := [term_var "paddr"];
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_return_pmp_ptsto : SepLemma return_pmp_ptsto :=
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
      | open_pmp_entries => lemma_open_pmp_entries
      | close_pmp_entries => lemma_close_pmp_entries
      | update_pmp_entries => lemma_update_pmp_entries
      | extract_pmp_ptsto => lemma_extract_pmp_ptsto
      | return_pmp_ptsto => lemma_return_pmp_ptsto
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

  Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContractReflect c (FunDef f)
    | None => True
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

  Lemma valid_execute_mem_read : ValidContract mem_read.
  Proof. Admitted.

  Lemma valid_contracts {Δ τ} (f : Fun Δ τ) :
    ValidContract f.
  Proof.
    unfold ValidContract; destruct f; cbn [CEnv]; try exact I.
    - apply valid_execute_rX.
    - apply valid_execute_wX.
    - apply valid_execute_tick_pc.
    - apply valid_execute_mem_read.
    - apply valid_execute_fetch.
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

  Lemma read_ram_sound `{sailGS Σ} {Γ} (es : NamedEnv (Exp Γ) ["paddr"∷ty_exc_code]) (δ : CStore Γ) :
    ∀ paddr w,
      evals es δ = [env].["paddr"∷ty_exc_code ↦ paddr]
      → ⊢ semTriple δ (interp_ptsto paddr w) (stm_foreign read_ram es)
          (λ (v : Z) (δ' : NamedEnv Val Γ), (interp_ptsto paddr w ∗ ⌜v = w⌝ ∧ emp) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (paddr w Heq) "ptsto_addr_w".
    rewrite wp_unfold. cbn.
    iIntros (σ' ns ks1 ks nt) "[Hregs Hmem]".
    iDestruct "Hmem" as (memmap) "[Hmem' %]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first easy.
    iIntros (e2 σ'' efs Hstep).
    dependent elimination Hstep.
    dependent elimination s.
    rewrite Heq in f1. cbv in f1.
    dependent elimination f1. cbn.
    do 3 iModIntro.
    unfold interp_ptsto.
    iAssert (⌜ memmap !! paddr = Some w ⌝)%I with "[ptsto_addr_w Hmem']" as "%".
    { iApply (gen_heap.gen_heap_valid with "Hmem' ptsto_addr_w"). }
    iMod "Hclose" as "_".
    iModIntro.
    iSplitL "Hmem' Hregs".
    iSplitL "Hregs"; first iFrame.
    iExists memmap.
    iSplitL "Hmem'"; first iFrame.
    iPureIntro; assumption.
    iSplitL; last easy.
    apply map_Forall_lookup_1 with (i := paddr) (x := w) in H0; auto.
    cbn in H0. subst.
    iApply wp_value.
    iSplitL; last easy.
    iSplitL; last easy.
    iAssumption.
  Qed.

  Lemma write_ram_sound `{sailGS Σ} {Γ}
    (es : NamedEnv (Exp Γ) ["paddr"∷ty_exc_code; "data"∷ty_exc_code]) (δ : CStore Γ) :
    ∀ paddr data : Z,
      evals es δ = [env].["paddr"∷ty_exc_code ↦ paddr].["data"∷ty_exc_code ↦ data]
      → ⊢ semTriple δ (∃ v : Z, interp_ptsto paddr v)
            (stm_foreign write_ram es)
            (λ (v : Z) (δ' : NamedEnv Val Γ),
              (interp_ptsto paddr data ∗ ⌜v = 1%Z⌝ ∧ emp) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (paddr data Heq) "[% ptsto_addr]".
    rewrite wp_unfold. cbn.
    iIntros (σ' ns ks1 ks nt) "[Hregs Hmem]".
    iDestruct "Hmem" as (memmap) "[Hmem' %]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first easy.
    iIntros (e2 σ'' efs Hstep).
    dependent elimination Hstep.
    dependent elimination s.
    rewrite Heq in f1. cbn in f1.
    dependent elimination f1. cbn.
    do 3 iModIntro.
    unfold interp_ptsto.
    iMod (gen_heap.gen_heap_update _ _ _ data with "Hmem' ptsto_addr") as "[Hmem' ptsto_addr]".
    iMod "Hclose" as "_".
    iModIntro.
    iSplitL "Hmem' Hregs".
    iSplitL "Hregs"; first iFrame.
    iExists (<[paddr:=data]> memmap).
    iSplitL "Hmem'"; first iFrame.
    iPureIntro.
    { apply map_Forall_lookup.
      intros i x Hl.
      unfold fun_write_ram.
      destruct (Z.eqb_spec paddr i).
      + subst. apply (lookup_insert_rev memmap i); assumption.
      + rewrite -> map_Forall_lookup in H0.
        rewrite -> lookup_insert_ne in Hl; auto.
    }
    iSplitL; last easy.
    iApply wp_value.
    iSplitL; trivial.
    iSplitL; trivial.
  Qed.

  Lemma decode_sound `{sailGS Σ} {Γ}
    (es : NamedEnv (Exp Γ) ["bv"∷ty_exc_code]) (δ : CStore Γ) :
    ∀ code instr,
      evals es δ = [env].["bv"∷ty_exc_code ↦ code]
      → ⊢ semTriple δ ⌜pure_decode code = inr instr⌝ (stm_foreign RiscvPmpProgram.decode es)
            (λ (v : AST) (δ' : NamedEnv Val Γ), (⌜v = instr⌝ ∧ emp) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (code instr Heq) "%Hdecode".
    rewrite wp_unfold. cbn.
    iIntros (σ' ns ks1 ks nt) "[Hregs Hmem]".
    iDestruct "Hmem" as (memmap) "[Hmem' %]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first easy.
    iIntros (e2 σ'' efs Hstep).
    dependent elimination Hstep.
    dependent elimination s.
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
    iSplitL; last easy.
    iApply wp_value; auto.
  Qed.

  Lemma foreignSemBlockVerif `{sailGS Σ} : ForeignSem.
  Proof.
    intros Γ τ Δ f es δ.
    destruct f; cbn.
    - intros *; apply read_ram_sound.
    - intros *; apply write_ram_sound.
    - intros *; apply decode_sound.
  Qed.

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

  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifExecutor.Symbolic.

  Lemma contractsSound `{sailGS Σ} : ⊢ ValidContractEnvSem RiscvPmpBlockVerifSpec.CEnv.
  Proof.
    apply (sound foreignSemBlockVerif lemSemBlockVerif).
    intros Γ τ f c Heq.
    apply shallow_vcgen_soundness, symbolic_vcgen_soundness, validcontract_reflect_sound.
    generalize (RiscvPmpSpecVerif.valid_contracts f).
    unfold RiscvPmpSpecVerif.ValidContract. now rewrite Heq.
  Qed.

End RiscvPmpIrisInstanceWithContracts.
