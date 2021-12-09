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
     Strings.String.
From RiscvPmp Require Import
     Machine.
From Katamaran Require Import
     Symbolic.Mutator
     SemiConcrete.Mutator
     Sep.Spec
     Syntax.
From Equations Require Import
     Equations.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Import ListNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Inductive PurePredicate : Set :=
.

Inductive Predicate : Set :=
| pmp_entries
| ptsreg
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

Module Export RiscvPmpAssertionKit <: (AssertionKit RiscvPmpTermKit RiscvPmpProgramKit).
  Export RiscvPmpProgramKit.

  Definition 𝑷 := PurePredicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    end.
  Definition 𝑷_inst (p : 𝑷) : abstract Lit (𝑷_Ty p) Prop :=
    match p with
    end.

  Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

  Definition 𝑯 := Predicate.
  Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
    match p with
    | pmp_entries => [ty_list (ty_prod ty_pmpcfg_ent ty_xlenbits)]
    | ptsreg      => [ty_regidx, ty_xlenbits]
    end.

  Instance 𝑯_is_dup : IsDuplicable Predicate := {
    is_duplicable p :=
      match p with
      | pmp_entries => false
      | ptsreg      => false
      end
    }.
  Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.
End RiscvPmpAssertionKit.

Module RiscvPmpSymbolicContractKit <: (SymbolicContractKit RiscvPmpTermKit
                                                           RiscvPmpProgramKit
                                                           RiscvPmpAssertionKit).
  Module Export ASS := Assertions RiscvPmpTermKit
                                  RiscvPmpProgramKit
                                  RiscvPmpAssertionKit.

  Local Notation "'rs'"      := "rs" : string_scope.
  Local Notation "'rs1'"     := "rs1" : string_scope.
  Local Notation "'rs2'"     := "rs2" : string_scope.
  Local Notation "'rd'"      := "rd" : string_scope.
  Local Notation "'op'"      := "op" : string_scope.
  Local Notation "'v'"       := "v" : string_scope.
  Local Notation "'w'"       := "w" : string_scope.
  Local Notation "'imm'"     := "imm" : string_scope.
  Local Notation "'t'"       := "t" : string_scope.
  Local Notation "'addr'"    := "addr" : string_scope.
  Local Notation "'paddr'"   := "paddr" : string_scope.
  Local Notation "'typ'"     := "typ" : string_scope.
  Local Notation "'acc'"     := "acc" : string_scope.
  Local Notation "'value'"   := "value" : string_scope.
  Local Notation "'data'"    := "data" : string_scope.
  Local Notation "'bv'"      := "bv" : string_scope.

  Local Notation "r '↦' val" := (asn_chunk (chunk_ptsreg r val)) (at level 100).
  Local Notation "r '↦r' val" := (asn_chunk (chunk_user ptsreg (env_nil ► (ty_regidx ↦ r) ► (ty_xlenbits ↦ val)))) (at level 100).
  Local Notation "p '∗' q" := (asn_sep p q) (at level 150).
  Local Notation asn_pmp_entries l := (asn_chunk (chunk_user pmp_entries (env_nil ► (ty_list (ty_prod ty_pmpcfg_ent ty_xlenbits) ↦ l)))).

  Definition sep_contract_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
    ctx_map (fun '(x::σ) => x::σ) Δ ▻▻ Σ.

  Definition create_localstore (Δ : PCtx) (Σ : LCtx) : SStore Δ (sep_contract_logvars Δ Σ) :=
    (env_tabulate (fun '(x::σ) xIn =>
                     @term_var
                       (sep_contract_logvars Δ Σ)
                       x
                       σ
                       (inctx_cat_left Σ (inctx_map (fun '(y::τ) => y::τ) xIn)))).

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepLemma {Δ} (f : Lem Δ) : Type :=
    Lemma Δ.

  Fixpoint asn_exists {Σ} (Γ : NCtx string Ty) : Assertion (Σ ▻▻ Γ) -> Assertion Σ :=
    match Γ return Assertion (Σ ▻▻ Γ) -> Assertion Σ with
    | ctx_nil => fun asn => asn
    | ctx_snoc Γ (x :: τ) =>
      fun asn =>
        @asn_exists Σ Γ (asn_exist x τ asn)
    end.

  Definition regidx_to_reg (r : RegIdx) : Reg ty_xlenbits :=
    match r with
    | X0 => x0
    | X1 => x1
    | X2 => x2
    end.

  Definition asn_and_regs {Σ} (f : RegIdx -> Assertion Σ) : Assertion Σ :=
    f X0 ∗ f X1 ∗ f X2.

  (* ∀ r : regidx, ∃ w : xlenbits, r ↦r w *)
  Definition asn_regs_ptsto {Σ} : Assertion Σ :=
    asn_and_regs
      (fun r => asn_exist w ty_xlenbits (term_lit ty_regidx r ↦r term_var w)).

  (* TODO: abstract away the concrete type, look into unions for that *)
  (* TODO: length of list should be 16, no duplicates *)
  Definition pmp_entries {Σ} : Term Σ (ty_list (ty_prod ty_pmpcfgidx ty_pmpaddridx)) :=
    term_list (cons (term_binop binop_pair
                                (term_lit ty_pmpcfgidx PMP0CFG) (* PMP0CFG ↦ ... *)
                                (term_lit ty_pmpaddridx PMPADDR0)) nil). (* PMPADDR0 ↦ ... *)

  (** Machine Invariant **)
  (*
    TODO: - there should be 2 cases in the @pre, one handling if we execute just fine and one if we end up in the trap (only with these 2 can we prove the @post)
          - this should work for the execute{,_/x/} functions, but step and loop will update 
            the pc, so this should be reflected in their contract (2nd pc(i) -> pc(i + 4)?)



    @pre ∀ m h i . mode(m) ∗ mtvec(h) ∗ pmp_entries(ents) ∗ pc(i) ∗ mepc(_) ∗ mpp(_)
    @post pmp_entries(ents) ∗ (mode(m) ∗ pc(i)) ∨ (mode(M) ∗ pc(h) ...)
    τ f(Δ...)*)
  Definition mach_inv_contract {τ Δ} : SepContract Δ τ :=
    let Σ := ["m" ∶ ty_privilege, "h" ∶ ty_xlenbits, "i" ∶ ty_xlenbits, "entries" ∶ ty_list (ty_prod ty_pmpcfg_ent ty_xlenbits)] in
    {| sep_contract_logic_variables := sep_contract_logvars Δ Σ;
       sep_contract_localstore      := create_localstore Δ Σ;
       sep_contract_precondition    :=
         cur_privilege ↦ (term_var "m") ∗
         mtvec ↦ (term_var "h") ∗
         pc ↦ (term_var "i") ∗
         asn_pmp_entries (term_var "entries") ∗
         asn_regs_ptsto;
       sep_contract_result          := "result_mach_inv";
       sep_contract_postcondition   :=
         asn_pmp_entries (term_var "entries") ∗
         asn_regs_ptsto ∗
         asn_or (cur_privilege ↦ (term_var "m") ∗ pc ↦ (term_var "i"))
                (cur_privilege ↦ (term_lit ty_privilege Machine) ∗
                 pc ↦ (term_var "h") ∗
                 mepc ↦ (term_var "i") ∗
                 mstatus ↦ (term_record rmstatus [ term_lit ty_privilege User ]))
    |}.

  Definition sep_contract_execute_RTYPE : SepContractFun execute_RTYPE :=
    mach_inv_contract.

  Definition sep_contract_rX : SepContractFun rX :=
    {| sep_contract_logic_variables := [rs ∶ ty_regidx, v ∶ ty_xlenbits];
       sep_contract_localstore      := [term_var rs]%arg;
       sep_contract_precondition    := 
         asn_match_enum
           regidx (term_var rs)
           (fun k => match k with
                     | X0 => asn_true
                     | _  => term_var rs ↦r term_var v
                     end);
       sep_contract_result          := "result_rX";
       sep_contract_postcondition   :=
         asn_match_enum
           regidx (term_var rs)
           (fun k => match k with
                     | X0 => asn_eq (term_var "result_rX") (term_lit ty_int 0%Z)
                     | _  => asn_eq (term_var "result_rX") (term_var v)
                             ∗ term_var rs ↦r term_var v 
                     end)
    |}.

  Definition sep_contract_wX : SepContractFun wX :=
    {| sep_contract_logic_variables := [rs ∶ ty_regidx, v ∶ ty_xlenbits];
       sep_contract_localstore      := [term_var rs, term_var v]%arg;
       sep_contract_precondition    :=
         asn_match_enum
           regidx (term_var rs)
           (fun k => match k with
                     | X0 => asn_true
                     | _  => asn_exist w ty_xlenbits (term_var rs ↦r term_var w)
                     end);
       sep_contract_result          := "result_wX";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_wX") (term_lit ty_unit tt)
         ∗ asn_match_enum
           regidx (term_var rs)
           (fun k => match k with
                     | X0 => asn_true
                     | _  => term_var rs ↦r term_var v
                     end);
    |}.

  Definition sep_contract_read_ram : SepContractFunX read_ram :=
    {| sep_contract_logic_variables := [paddr ∶ ty_int];
       sep_contract_localstore      := [term_var paddr]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_read_ram";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition sep_contract_write_ram : SepContractFunX write_ram :=
    {| sep_contract_logic_variables := [paddr ∶ ty_int, data ∶ ty_word];
       sep_contract_localstore      := [term_var paddr, term_var data]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_write_ram";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition sep_contract_decode    : SepContractFunX decode :=
    {| sep_contract_logic_variables := [bv ∶ ty_int];
       sep_contract_localstore      := [term_var bv]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_decode";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition lemma_open_ptsreg : SepLemma open_ptsreg :=
    {| lemma_logic_variables := [ rs ∶ ty_regidx, w ∶ ty_xlenbits];
       lemma_patterns        := [term_var rs]%arg;
       lemma_precondition    := term_var rs ↦r term_var w;
       lemma_postcondition   :=
         asn_match_enum
           regidx (term_var rs)
           (fun k => match k with
                     | X0 => asn_true
                     | X1 => x1 ↦ term_var "w"
                     | X2 => x2 ↦ term_var "w"
                     end)
    |}.

  Definition lemma_close_ptsreg (r : RegIdx) : SepLemma (close_ptsreg r) :=
    {| lemma_logic_variables := [w ∶ ty_xlenbits];
       lemma_patterns        := env_nil;
       lemma_precondition    := regidx_to_reg r ↦ term_var w;
       lemma_postcondition   := term_enum regidx r ↦r term_var w
    |}.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | execute_RTYPE => Some sep_contract_execute_RTYPE
      | rX            => Some sep_contract_rX
      | wX            => Some sep_contract_wX
      | _             => None
      end.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | read_ram  => sep_contract_read_ram
      | write_ram => sep_contract_write_ram
      | decode    => sep_contract_decode
      end.

  Definition LEnv : LemmaEnv :=
    fun Δ l =>
      match l with
      | open_ptsreg    => lemma_open_ptsreg
      | close_ptsreg r => lemma_close_ptsreg r
      end.

  Lemma linted_cenvex :
    forall Δ τ (f : FunX Δ τ),
      Linted (CEnvEx f).
  Proof.
    intros ? ? []; try constructor.
  Qed.

  Definition solver_user : option SoundSolver := None.

End RiscvPmpSymbolicContractKit.

Module RiscvPmpMutators :=
  Mutators
    RiscvPmpTermKit
    RiscvPmpProgramKit
    RiscvPmpAssertionKit
    RiscvPmpSymbolicContractKit.
Import RiscvPmpMutators.
Import SMut.

Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
  match CEnv f with
  | Some c => ValidContractReflect c (Pi f)
  | None => False
  end.

Definition ValidContractDebug {Δ τ} (f : Fun Δ τ) : Prop :=
  match CEnv f with
  | Some c => SMut.ValidContract c (Pi f)
  | None => False
  end.

Lemma valid_contract_rX : ValidContract rX.
Proof. reflexivity. Qed.

Lemma valid_contract_wX : ValidContract wX.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_RTYPE : ValidContractDebug execute_RTYPE.
Proof. compute; firstorder. Qed.
Lemma valid_contract_execute_RTYPE' : ValidContract execute_RTYPE.
Proof. Admitted. (* reflexivity. Qed. *)
