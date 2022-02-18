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
     Notations
     SemiConcrete.Mutator
     Specification
     Symbolic.Mutator
     Symbolic.Solver
     Symbolic.Propositions
     Symbolic.Worlds.
From Equations Require Import
     Equations.

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
| pmp_addr_access
| gprs
| ptsto
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

Module Import RiscvPmpSpecification <: Specification RiscvPmpBase.
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
    | pmp_entries     => [ty_list pmp_entry_cfg]
    | pmp_addr_access => [ty_list pmp_entry_cfg; ty_privilege]
    | gprs            => ctx.nil
    | ptsto           => [ty_xlenbits; ty_xlenbits]
    end.

  Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
    is_duplicable p :=
      match p with
      | pmp_entries     => false
      | pmp_addr_access => false
      | gprs            => false
      | ptsto           => false
      end
    }.
  Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

  Local Arguments Some {_} &.
  Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
    match p with
    | ptsto => Some (MkPrecise [ty_xlenbits] [ty_word] eq_refl)
    | _ => None
    end.

End PredicateKit.

Include ContractDeclMixin RiscvPmpBase RiscvPmpProgram.

Section ContractDefKit.

  Local Notation "r '↦' val" := (asn_chunk (chunk_ptsreg r val)) (at level 70).
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
  Local Notation asn_pmp_addr_access l m := (asn_chunk (chunk_user pmp_addr_access [l; m])).
  Local Notation asn_gprs := (asn_chunk (chunk_user gprs env.nil)).


  Definition term_eqb {Σ} (e1 e2 : Term Σ ty_int) : Term Σ ty_bool :=
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

  Definition asn_with_reg {Σ} (r : Term Σ ty_int) (asn : Reg ty_xlenbits -> Assertion Σ) (asn_default : Assertion Σ) : Assertion Σ :=
    asn_if (r =? z_term 1)
           (asn x1)
           (asn_if (r =? z_term 2)
                   (asn x2)
                   (asn_if (r =? z_term 3)
                           (asn x3)
                           asn_default)).

  Definition asn_and_regs {Σ} (f : Reg ty_xlenbits -> Assertion Σ) : Assertion Σ :=
    f x1 ∗ f x2 ∗ f x3.

  Definition asn_regs_ptsto {Σ} : Assertion Σ :=
    asn_and_regs
      (fun r => ∃ "w", r ↦ term_var "w").

  Local Notation "e1 ',ₜ' e2" := (term_binop binop_pair e1 e2) (at level 100).

  (* TODO: abstract away the concrete type, look into unions for that *)
  (* TODO: length of list should be 16, no duplicates *)
  Definition pmp_entries {Σ} : Term Σ (ty_list (ty_prod ty_pmpcfgidx ty_pmpaddridx)) :=
    term_list
      (cons (term_val ty_pmpcfgidx PMP0CFG ,ₜ term_val ty_pmpaddridx PMPADDR0)
            (cons (term_val ty_pmpcfgidx PMP1CFG ,ₜ term_val ty_pmpaddridx PMPADDR1) nil)).

  Section Contracts.
    Import RiscvNotations.

  (** Machine Invariant **)
  (*
    TODO: - this should work for the execute{,_/x/} functions, but step and loop will update 
            the pc, so this should be reflected in their contract (2nd pc(i) -> pc(i + 4)?)



    TODO: short notation out of sync with actual contract
    @pre ∀ m h i . mode(m) ∗ mtvec(h) ∗ pmp_entries(ents) ∗ pc(i) ∗ mepc(_) ∗ mpp(_)
    @post pmp_entries(ents) ∗ (mode(m) ∗ pc(i)) ∨ (mode(M) ∗ pc(h) ...)
    τ f(Δ...)*)
  Definition instr_exec_contract {τ Δ} : SepContract Δ τ :=
    let Σ := ["m" :: ty_privilege; "h" :: ty_xlenbits; "i" :: ty_xlenbits; "entries" :: ty_list (ty_prod ty_pmpcfg_ent ty_xlenbits); "mpp" :: ty_privilege; "mepc" :: ty_xlenbits; "npc" :: ty_xlenbits] in
    {| sep_contract_logic_variables := sep_contract_logvars Δ Σ;
       sep_contract_localstore      := create_localstore Δ Σ;
       sep_contract_precondition    :=
                     cur_privilege ↦ term_var "m" ∗
                     mtvec         ↦ term_var "h" ∗
                     pc            ↦ term_var "i" ∗
                     nextpc        ↦ term_var "npc" ∗
         ∃ "mcause", mcause        ↦ term_var "mcause" ∗
                     mepc          ↦ term_var "mepc" ∗
                     mstatus       ↦ term_record rmstatus [ term_var "mpp" ] ∗
                     asn_pmp_entries (term_var "entries") ∗
                     asn_gprs;
       sep_contract_result          := "result_mach_inv";
       sep_contract_postcondition   :=
                     asn_pmp_entries (term_var "entries") ∗
                     asn_gprs ∗
                     pc     ↦ term_var "i" ∗
         ∃ "mcause", mcause ↦ term_var "mcause" ∗
         (  (* Executing normally *)
                 cur_privilege ↦ term_var "m" ∗
            ∃ v, nextpc        ↦ term_var v ∗
                 mtvec         ↦ term_var "h" ∗
                 mstatus       ↦ term_record rmstatus [ term_var "mpp" ] ∗
                 mepc          ↦ term_var "mepc"
          ∨
            (* Modified CSRs, requires Machine mode *)
                           term_var "m"  =  term_val ty_privilege Machine ∗
                           cur_privilege ↦ term_val ty_privilege Machine ∗
                           nextpc        ↦ term_var "npc" ∗
            ∃ "new_mtvec", mtvec         ↦ term_var "new_mtvec" ∗
            ∃ "new_mpp",   mstatus       ↦ term_record rmstatus [ term_var "new_mpp" ] ∗
            ∃ "new_mepc",  mepc          ↦ term_var "new_mepc"
          ∨
            (* Trap occured -> Go into M-mode *)
            cur_privilege ↦ (term_val ty_privilege Machine) ∗
            nextpc        ↦ term_var "h" ∗
            mtvec         ↦ term_var "h" ∗
            mstatus       ↦ term_record rmstatus [ term_var "m" ] ∗
            mepc          ↦ term_var "i"
          ∨
            (* MRET = Recover *)
            term_var "m"  =  term_val ty_privilege Machine ∗
            cur_privilege ↦ term_var "mpp" ∗
            nextpc        ↦ term_var "mepc" ∗
            mtvec         ↦ term_var "h" ∗
            mstatus       ↦ term_record rmstatus [ term_val ty_privilege User ] ∗
            mepc          ↦ term_var "mepc")
    |}.

  Definition sep_contract_execute_RTYPE : SepContractFun execute_RTYPE :=
    instr_exec_contract.

  Definition sep_contract_execute_ITYPE : SepContractFun execute_ITYPE :=
    instr_exec_contract.

  Definition sep_contract_execute_UTYPE : SepContractFun execute_UTYPE :=
    instr_exec_contract.

  Definition sep_contract_execute_BTYPE : SepContractFun execute_BTYPE :=
    instr_exec_contract.

  Definition sep_contract_execute_RISCV_JAL : SepContractFun execute_RISCV_JAL :=
    instr_exec_contract.

  Definition sep_contract_execute_RISCV_JALR : SepContractFun execute_RISCV_JALR :=
    instr_exec_contract.

  Definition sep_contract_execute_ECALL : SepContractFun execute_ECALL :=
    instr_exec_contract.

  Definition sep_contract_execute_MRET : SepContractFun execute_MRET :=
    instr_exec_contract.

  Definition sep_contract_execute_CSR : SepContractFun execute_CSR :=
    instr_exec_contract.

  Definition sep_contract_readCSR : SepContractFun readCSR :=
    {| sep_contract_logic_variables := [csr :: ty_csridx; "mpp" :: ty_privilege;
                                        "mtvec" :: ty_xlenbits; "mcause" :: ty_exc_code;
                                        "mepc" :: ty_xlenbits];
       sep_contract_localstore      := [term_var csr];
       sep_contract_precondition    :=
         mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ mtvec ↦ term_var "mtvec"
         ∗ mcause ↦ term_var "mcause"
         ∗ mepc ↦ term_var "mepc";
       sep_contract_result          := "result_readCSR";
       sep_contract_postcondition   :=
         ∃ "result", term_var "result_readCSR" = term_var "result"
         ∗ mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ mtvec ↦ term_var "mtvec"
         ∗ mcause ↦ term_var "mcause"
         ∗ mepc ↦ term_var "mepc";
    |}.

  Definition sep_contract_writeCSR : SepContractFun writeCSR :=
    {| sep_contract_logic_variables := [csr :: ty_csridx; value :: ty_xlenbits];
       sep_contract_localstore      := [term_var csr; term_var value];
       sep_contract_precondition    :=
         ∃ "mpp", mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ ∃ "mtvec", mtvec ↦ term_var "mtvec"
         ∗ ∃ "mcause", mcause ↦ term_var "mcause"
         ∗ ∃ "mepc", mepc ↦ term_var "mepc";
       sep_contract_result          := "result_writeCSR";
       sep_contract_postcondition   :=
         term_var "result_writeCSR" = term_val ty_unit tt
         ∗ ∃ "mpp", mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ ∃ "mtvec", mtvec ↦ term_var "mtvec"
         ∗ ∃ "mcause", mcause ↦ term_var "mcause"
         ∗ ∃ "mepc", mepc ↦ term_var "mepc";
    |}.

  Definition sep_contract_check_CSR : SepContractFun check_CSR :=
    {| sep_contract_logic_variables := [csr :: ty_csridx; p :: ty_privilege];
       sep_contract_localstore      := [term_var csr; term_var p];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_check_CSR";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var p)
                        (fun K => match K with
                                  | Machine => term_var "result_check_CSR" = term_val ty_bool true
                                  | User    => term_var "result_check_CSR" = term_val ty_bool false
                                  end)
    |}.

  Definition sep_contract_is_CSR_defined : SepContractFun is_CSR_defined :=
    {| sep_contract_logic_variables := [csr :: ty_csridx; p :: ty_privilege];
       sep_contract_localstore      := [term_var csr; term_var p];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_is_CSR_defined";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var p)
                        (fun K => match K with
                                  | Machine => term_var "result_is_CSR_defined" =
                                                 term_val ty_bool true
                                  | User    =>term_var "result_is_CSR_defined" =
                                                term_val ty_bool false
                                  end);
    |}.

  Definition sep_contract_check_CSR_access : SepContractFun check_CSR_access :=
    {| sep_contract_logic_variables := [csrrw :: ty_access_type; csrpr :: ty_privilege; p :: ty_privilege];
       sep_contract_localstore      := [term_var csrrw; term_var csrpr; term_var p];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_check_CSR_access";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var csrpr)
                        (fun K => match K with
                                  | Machine =>
                                      asn_match_enum privilege (term_var p)
                                                     (fun K => match K with
                                                               | Machine => term_var "result_check_CSR_access" =
                                                                              term_val ty_bool true
                                                               | User    => term_var "result_check_CSR_access" =
                                                                              term_val ty_bool false
                                                               end)
                                  | User =>
                                      asn_match_enum privilege (term_var p)
                                                     (fun K => match K with
                                                               | Machine => term_var "result_check_CSR_access" =
                                                                              term_val ty_bool true
                                                               | User    => term_var "result_check_CSR_access" =
                                                                                   term_val ty_bool true
                                                               end)
                                  end);
    |}.

  Definition sep_contract_privLevel_to_bits : SepContractFun privLevel_to_bits :=
    {| sep_contract_logic_variables := [p :: ty_privilege];
       sep_contract_localstore      := [term_var p];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_privLevel_to_bits";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var p)
                        (fun K => match K with
                                  | Machine => term_var "result_privLevel_to_bits" =
                                                 term_val ty_xlenbits 3%Z
                                  | User    => term_var "result_privLevel_to_bits" =
                                                 term_val ty_xlenbits 0%Z
                                  end);
    |}.

  Definition sep_contract_mstatus_to_bits : SepContractFun mstatus_to_bits :=
    {| sep_contract_logic_variables := [value :: ty_mstatus];
       sep_contract_localstore      := [term_var value];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_mstatus_to_bits";
       sep_contract_postcondition   :=
         ∃ "result", term_var "result_mstatus_to_bits" = term_var "result";
    |}.

  Definition sep_contract_mstatus_from_bits : SepContractFun mstatus_from_bits :=
    {| sep_contract_logic_variables := [value :: ty_xlenbits];
       sep_contract_localstore      := [term_var value];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_mstatus_from_bits";
       sep_contract_postcondition   :=
         ∃ "MPP", term_var "result_mstatus_from_bits" = term_record rmstatus [ term_var "MPP" ];
    |}.

  Definition sep_contract_csrAccess : SepContractFun csrAccess :=
    {| sep_contract_logic_variables := [csr :: ty_csridx];
       sep_contract_localstore      := [term_var csr];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_csrAccess";
       sep_contract_postcondition   :=
         term_var "result_csrAccess" = term_val ty_access_type ReadWrite;
    |}.

  Definition sep_contract_csrPriv : SepContractFun csrPriv :=
    {| sep_contract_logic_variables := [csr :: ty_csridx];
       sep_contract_localstore      := [term_var csr];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_csrPriv";
       sep_contract_postcondition   :=
         term_var "result_csrPriv" = term_val ty_privilege Machine;
    |}.

  Definition sep_contract_exception_handler : SepContractFun exception_handler :=
    {| sep_contract_logic_variables := [cur_priv :: ty_privilege; ctl :: ty_ctl_result; "pc" :: ty_xlenbits; "mpp" :: ty_privilege; "mepc" :: ty_xlenbits; tvec :: ty_xlenbits; p :: ty_privilege];
       sep_contract_localstore      := [term_var cur_priv; term_var ctl; term_var "pc"];
       sep_contract_precondition    :=
         cur_privilege ↦ (term_var p)
         ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
         ∗             mstatus       ↦ (term_record rmstatus [ term_var "mpp" ])
         ∗             mtvec         ↦ (term_var tvec)
         ∗             mepc          ↦ (term_var "mepc");
       sep_contract_result          := "result_exception_handler";
       sep_contract_postcondition   := asn_match_union ctl_result (term_var ctl)
        (fun K => match K with
                | KCTL_TRAP => ctx.snoc ε (e ∷ ty_exception_type)
                | KCTL_MRET => ε
                end)
        (fun K => match K with
                | KCTL_TRAP => pat_var e
                | KCTL_MRET => pat_unit
                end)
        (fun K => match K with
                | KCTL_TRAP =>
                    term_var "result_exception_handler" = term_var tvec
                    ∗ cur_privilege ↦ term_val ty_privilege Machine
                    ∗ ∃ "mcause", mcause ↦ term_var "mcause"
                    ∗ mstatus ↦ term_record rmstatus [ term_var p ]
                    ∗ mepc ↦ term_var "pc"
                    ∗ mtvec ↦ term_var tvec
                | KCTL_MRET =>
                    term_var "result_exception_handler" = term_var "mepc"
                    ∗ cur_privilege ↦ term_var "mpp"
                    ∗ ∃ "mcause", mcause ↦ term_var "mcause"
                    ∗ mstatus ↦ term_record rmstatus [ term_val ty_privilege User ]
                    ∗ mtvec ↦ term_var tvec
                    ∗ mepc ↦ term_var "mepc"
                end);
    |}.

  Definition sep_contract_handle_illegal : SepContractFun handle_illegal :=
    {| sep_contract_logic_variables := [p :: ty_privilege; "pc" :: ty_xlenbits; tvec :: ty_xlenbits];
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    :=
         cur_privilege ↦ term_var p
         ∗ pc ↦ term_var "pc"
         ∗ ∃ "mcause_val", mcause  ↦ term_var "mcause_val"
         ∗ ∃ "mpp", mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ ∃ "mepc_val", mepc ↦ term_var "mepc_val"
         ∗ mtvec ↦ term_var tvec
         ∗ ∃ v, nextpc ↦ term_var v;
       sep_contract_result          := "result_handle_illegal";
       sep_contract_postcondition   :=
         term_var "result_handle_illegal" = term_val ty_unit tt
         ∗ cur_privilege ↦ term_val ty_privilege Machine
         ∗ pc ↦ term_var "pc"
         ∗ ∃ "mcause", mcause ↦ term_var "mcause"
         ∗ mstatus ↦ term_record rmstatus [ term_var p ]
         ∗ mepc ↦ term_var "pc"
         ∗ mtvec ↦ term_var tvec
         ∗ nextpc ↦ term_var tvec
    |}.

  Definition sep_contract_trap_handler : SepContractFun trap_handler :=
    {| sep_contract_logic_variables := [del_priv :: ty_privilege; c :: ty_exc_code; "pc" :: ty_xlenbits; p :: ty_privilege; tvec :: ty_xlenbits];
       sep_contract_localstore      := [term_var del_priv; term_var c; term_var "pc"];
       sep_contract_precondition    :=
         cur_privilege ↦ term_var p
         ∗ ∃ "mcause_val", mcause  ↦ term_var "mcause_val"
         ∗ ∃ "mstatus_val", mstatus ↦ term_var "mstatus_val"
         ∗ ∃ "mepc_val", mepc    ↦ term_var "mepc_val"
         ∗ mtvec ↦ term_var tvec;
       sep_contract_result          := "result_trap_handler";
       sep_contract_postcondition   :=
         term_var "result_trap_handler" = term_var tvec
         ∗ term_var del_priv = term_val ty_privilege Machine
         ∗ cur_privilege ↦ term_var del_priv
         ∗ mcause        ↦ term_var c
         ∗ mstatus       ↦ term_record rmstatus [ term_var p ]
         ∗ mepc          ↦ term_var "pc"
         ∗ mtvec         ↦ term_var tvec;
    |}.

  Definition sep_contract_prepare_trap_vector : SepContractFun prepare_trap_vector :=
    {| sep_contract_logic_variables := [p :: ty_privilege; cause :: ty_mcause; tvec :: ty_xlenbits];
       sep_contract_localstore      := [term_var p; term_var cause];
       sep_contract_precondition    := mtvec ↦ term_var tvec;
       sep_contract_result          := "result_prepare_trap_vector";
       sep_contract_postcondition   :=
         term_var "result_prepare_trap_vector" = term_var tvec
         ∗ term_var p = term_val ty_privilege Machine
         ∗ mtvec ↦ term_var tvec;
    |}.

  Definition sep_contract_tvec_addr : SepContractFun tvec_addr :=
    {| sep_contract_logic_variables := [m :: ty_xlenbits; c :: ty_mcause];
       sep_contract_localstore      := [term_var m; term_var c];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_tvec_addr";
       sep_contract_postcondition   :=
         term_var "result_tvec_addr" = term_inl (term_var m);
    |}.

  Definition sep_contract_exceptionType_to_bits : SepContractFun exceptionType_to_bits :=
    {| sep_contract_logic_variables := [e :: ty_exception_type];
       sep_contract_localstore      := [term_var e];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_exceptionType_to_bits";
       sep_contract_postcondition   :=
         ∃ result, term_var "result_exceptionType_to_bits" = term_var result
    |}.

  Definition sep_contract_exception_delegatee : SepContractFun exception_delegatee :=
    {| sep_contract_logic_variables := [p :: ty_privilege];
       sep_contract_localstore      := [term_var p];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_exception_delegatee";
       sep_contract_postcondition   :=
        term_var "result_exception_delegatee" = term_val ty_privilege Machine
    |}.

  Definition sep_contract_get_arch_pc : SepContractFun get_arch_pc :=
    {| sep_contract_logic_variables := [v :: ty_xlenbits];
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    := pc ↦ term_var v;
       sep_contract_result          := "result_get_arch_pc";
       sep_contract_postcondition   :=
         term_var "result_get_arch_pc" = term_var v
         ∗ pc ↦ term_var v;
    |}.

  Definition sep_contract_set_next_pc : SepContractFun set_next_pc :=
    {| sep_contract_logic_variables := [addr :: ty_xlenbits];
       sep_contract_localstore      := [term_var addr];
       sep_contract_precondition    := ∃ v, nextpc ↦ term_var v;
       sep_contract_result          := "result_set_next_pc";
       sep_contract_postcondition   :=
         term_var "result_set_next_pc" = term_val ty_unit tt
         ∗ nextpc ↦ term_var addr;
    |}.

  Definition sep_contract_get_next_pc : SepContractFun get_next_pc :=
    {| sep_contract_logic_variables := [v :: ty_xlenbits];
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    := nextpc ↦ term_var v;
       sep_contract_result          := "result_get_next_pc";
       sep_contract_postcondition   :=
         term_var "result_get_next_pc" = term_var v
         ∗ nextpc ↦ term_var v;
    |}.

  Definition sep_contract_rX : SepContractFun rX :=
    {| sep_contract_logic_variables := [rs :: ty_regno];
       sep_contract_localstore      := [term_var rs];
       sep_contract_precondition    := asn_gprs;
       sep_contract_result          := "result_rX";
       sep_contract_postcondition   := asn_gprs;
    |}.

  Definition sep_contract_wX : SepContractFun wX :=
    {| sep_contract_logic_variables := [rs :: ty_regno; v :: ty_xlenbits];
       sep_contract_localstore      := [term_var rs; term_var v];
       sep_contract_precondition    := asn_gprs;
       sep_contract_result          := "result_wX";
       sep_contract_postcondition   :=
         term_var "result_wX" = term_val ty_unit tt
         ∗ asn_gprs;
    |}.

  Definition sep_contract_abs : SepContractFun abs :=
    {| sep_contract_logic_variables := [v :: ty_int];
       sep_contract_localstore      := [term_var v];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_abs";
       sep_contract_postcondition   := asn_true;
    |}.

  (* TODO: read perm in pre: perm_access(paddr, ?p) ∗ R ≤ ?p *)
  Definition sep_contract_checked_mem_read : SepContractFun checked_mem_read :=
    {| sep_contract_logic_variables := [t :: ty_access_type; paddr :: ty_xlenbits; w :: ty_xlenbits];
       sep_contract_localstore      := [term_var t; term_var paddr];
       sep_contract_precondition    := term_var paddr ↦ₘ term_var w;
       sep_contract_result          := "result_checked_mem_read";
       sep_contract_postcondition   :=
         term_var "result_checked_mem_read" = term_union memory_op_result KMemValue (term_var w);
    |}.

  (* TODO: post: we should "close" the pmp_addr_access predicate again after
                 extracting a ptsto from it *)
  Definition sep_contract_pmp_mem_read : SepContractFun pmp_mem_read :=
    {| sep_contract_logic_variables := [t :: ty_access_type; p :: ty_privilege; paddr :: ty_xlenbits; "entries" :: ty_list pmp_entry_cfg];
       sep_contract_localstore      := [term_var t; term_var p; term_var paddr];
       sep_contract_precondition    :=
         asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
       sep_contract_result          := "result_pmp_mem_read";
       sep_contract_postcondition   := (* TODO *) asn_true;
    |}.

  Definition sep_contract_pmpCheck : SepContractFun pmpCheck :=
    {| sep_contract_logic_variables := [addr :: ty_xlenbits; acc :: ty_access_type; priv :: ty_privilege; "entries" :: ty_list pmp_entry_cfg];
       sep_contract_localstore      := [term_var addr; term_var acc; term_var priv];
       sep_contract_precondition    :=
         asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var priv);
       sep_contract_result          := "result_pmpCheck";
       sep_contract_postcondition   := (* TODO *) asn_true;
    |}.

  Definition sep_contract_pmpCheckPerms : SepContractFun pmpCheckPerms :=
    let Σ : LCtx := [acc :: ty_access_type; priv :: ty_privilege; L :: ty_bool; A :: ty_pmpaddrmatchtype; X :: ty_bool; W :: ty_bool; R :: ty_bool] in
    let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := [nenv entry; term_var acc; term_var priv];
       sep_contract_precondition    := (* TODO: predicate that states ent ∈ entries? *)
         asn_true;
       sep_contract_result          := "result_pmpCheckPerms";
       sep_contract_postcondition   :=
         ∃ "result", term_var "result_pmpCheckPerms" = term_var "result";
    |}.

  Definition sep_contract_pmpCheckRWX : SepContractFun pmpCheckRWX :=
    let Σ : LCtx := [acc :: ty_access_type; L :: ty_bool; A :: ty_pmpaddrmatchtype; X :: ty_bool; W :: ty_bool; R :: ty_bool] in
    let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := [nenv entry; term_var acc];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpCheckRWX";
       sep_contract_postcondition   :=
         asn_match_union access_type (term_var acc)
           (fun _ => ε)
           (fun _ => pat_unit)
           (fun K => match K with
                     | KRead      => term_var "result_pmpCheckRWX" = term_var R
                     | KWrite     => term_var "result_pmpCheckRWX" = term_var W
                     | KReadWrite => term_var "result_pmpCheckRWX" = term_binop binop_and (term_var R) (term_var W)
                     | KExecute   => term_var "result_pmpCheckRWX" = term_var X
                     end);
    |}.

  Definition sep_contract_pmpAddrRange : SepContractFun pmpAddrRange :=
    let Σ : LCtx := [pmpaddr :: ty_xlenbits; prev_pmpaddr :: ty_xlenbits; L :: ty_bool; A :: ty_pmpaddrmatchtype; X :: ty_bool; W :: ty_bool; R :: ty_bool] in
    let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := [nenv entry; term_var pmpaddr; term_var prev_pmpaddr];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpAddrRange";
       sep_contract_postcondition   :=
         asn_match_enum pmpaddrmatchtype (term_var A)
           (fun K => match K with
                     | OFF => term_var "result_pmpAddrRange" = term_inr (term_val ty_unit tt)
                     | TOR => term_var "result_pmpAddrRange" = term_inl (term_var prev_pmpaddr ,ₜ term_var pmpaddr)
                     end);
    |}.

  Definition sep_contract_pmpMatchAddr : SepContractFun pmpMatchAddr :=
    {| sep_contract_logic_variables := [addr :: ty_xlenbits; rng :: ty_pmp_addr_range];
       sep_contract_localstore      := [term_var addr; term_var rng];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpMatchAddr";
       sep_contract_postcondition   :=
         asn_match_option
           _ (term_var rng) v
           (asn_match_prod
              (term_var v) lo hi
              (asn_match_enum pmpaddrmatch (term_var "result_pmpMatchAddr")
                (fun K => match K with
                          | PMP_NoMatch =>
                              asn_bool (term_var hi <ₜ term_var lo) ∨ asn_bool (term_var addr <ₜ term_var lo ||ₜ term_var hi <ₜ term_var addr)
                          | PMP_PartialMatch => asn_bool
                                                  (term_not
                                                     (term_var lo <=ₜ term_var addr &&ₜ term_var addr <=ₜ term_var hi))
                          | PMP_Match => asn_formula (formula_bool (term_var lo <=ₜ term_var addr)) ∗ asn_formula (formula_bool (term_var addr <=ₜ term_var hi))
                        end)))
              (term_var "result_pmpMatchAddr" = term_val ty_pmpaddrmatch PMP_NoMatch);
    |}.

  Definition sep_contract_pmpMatchEntry : SepContractFun pmpMatchEntry :=
    let Σ : LCtx := [addr :: ty_xlenbits; acc :: ty_access_type; priv :: ty_privilege; ent :: ty_pmpcfg_ent; pmpaddr :: ty_xlenbits; prev_pmpaddr :: ty_xlenbits; L :: ty_bool; A :: ty_pmpaddrmatchtype; X :: ty_bool; W :: ty_bool; R :: ty_bool] in
    let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := [nenv term_var addr; term_var acc; term_var priv; entry; term_var pmpaddr; term_var prev_pmpaddr];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpMatchEntry";
       sep_contract_postcondition   :=
         ∃ "result", term_var "result_pmpMatchEntry" = term_var "result";
    |}.

  Definition sep_contract_pmpLocked : SepContractFun pmpLocked :=
    let Σ : LCtx := [L :: ty_bool; A :: ty_pmpaddrmatchtype; X :: ty_bool; W :: ty_bool; R :: ty_bool] in
    let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := env.snoc env.nil (_::_) entry;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpLocked";
       sep_contract_postcondition   := term_var "result_pmpLocked" = term_var L;
    |}.

  Definition sep_contract_read_ram : SepContractFunX read_ram :=
    {| sep_contract_logic_variables := [paddr :: ty_xlenbits; w :: ty_xlenbits];
       sep_contract_localstore      := [term_var paddr];
       sep_contract_precondition    := term_var paddr ↦ₘ term_var w;
       sep_contract_result          := "result_read_ram";
       sep_contract_postcondition   := term_var "result_read_ram" = term_var w;
    |}.

  Definition sep_contract_write_ram : SepContractFunX write_ram :=
    {| sep_contract_logic_variables := [paddr :: ty_int; data :: ty_word];
       sep_contract_localstore      := [term_var paddr; term_var data];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_write_ram";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition sep_contract_decode    : SepContractFunX decode :=
    {| sep_contract_logic_variables := [bv :: ty_int];
       sep_contract_localstore      := [term_var bv];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_decode";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition lemma_open_gprs : SepLemma open_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := asn_gprs;
       lemma_postcondition   := asn_regs_ptsto;
    |}.

  Definition lemma_close_gprs : SepLemma close_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := asn_regs_ptsto;
       lemma_postcondition   := asn_gprs;
    |}.

  End Contracts.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | execute_RTYPE         => Some sep_contract_execute_RTYPE
      | execute_ITYPE         => Some sep_contract_execute_ITYPE
      | execute_UTYPE         => Some sep_contract_execute_UTYPE
      | execute_BTYPE         => Some sep_contract_execute_BTYPE
      | execute_RISCV_JAL     => Some sep_contract_execute_RISCV_JAL
      | execute_RISCV_JALR    => Some sep_contract_execute_RISCV_JALR
      | execute_ECALL         => Some sep_contract_execute_ECALL
      | execute_MRET          => Some sep_contract_execute_MRET
      | execute_CSR           => Some sep_contract_execute_CSR
      | get_arch_pc           => Some sep_contract_get_arch_pc
      | get_next_pc           => Some sep_contract_get_next_pc
      | set_next_pc           => Some sep_contract_set_next_pc
      | exception_handler     => Some sep_contract_exception_handler
      | handle_illegal        => Some sep_contract_handle_illegal
      | trap_handler          => Some sep_contract_trap_handler
      | prepare_trap_vector   => Some sep_contract_prepare_trap_vector
      | tvec_addr             => Some sep_contract_tvec_addr
      | exceptionType_to_bits => Some sep_contract_exceptionType_to_bits
      | exception_delegatee   => Some sep_contract_exception_delegatee
      | rX                    => Some sep_contract_rX
      | wX                    => Some sep_contract_wX
      | abs                   => Some sep_contract_abs
      | readCSR               => Some sep_contract_readCSR
      | writeCSR              => Some sep_contract_writeCSR
      | check_CSR             => Some sep_contract_check_CSR
      | is_CSR_defined        => Some sep_contract_is_CSR_defined
      | check_CSR_access      => Some sep_contract_check_CSR_access
      | privLevel_to_bits     => Some sep_contract_privLevel_to_bits
      | mstatus_to_bits       => Some sep_contract_mstatus_to_bits
      | mstatus_from_bits     => Some sep_contract_mstatus_from_bits
      | csrAccess             => Some sep_contract_csrAccess
      | csrPriv               => Some sep_contract_csrPriv
      | checked_mem_read      => Some sep_contract_checked_mem_read
      | pmp_mem_read          => Some sep_contract_pmp_mem_read
      | pmpCheck              => Some sep_contract_pmpCheck
      | pmpCheckPerms         => Some sep_contract_pmpCheckPerms
      | pmpCheckRWX           => Some sep_contract_pmpCheckRWX
      | pmpAddrRange          => Some sep_contract_pmpAddrRange
      | pmpMatchAddr          => Some sep_contract_pmpMatchAddr
      | pmpMatchEntry         => Some sep_contract_pmpMatchEntry
      | pmpLocked             => Some sep_contract_pmpLocked
      | _                     => None
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
      | open_gprs      => lemma_open_gprs
      | close_gprs     => lemma_close_gprs
      end.

  Lemma linted_cenvex :
    forall Δ τ (f : FunX Δ τ),
      Linted (CEnvEx f).
  Proof.
    intros ? ? []; try constructor.
  Qed.

End ContractDefKit.

Include SpecificationMixin RiscvPmpBase RiscvPmpProgram.

End RiscvPmpSpecification.

Module RiscvPmpSolverKit := DefaultSolverKit RiscvPmpBase RiscvPmpSpecification.
Module RiscvPmpSolver := MakeSolver RiscvPmpBase RiscvPmpSpecification RiscvPmpSolverKit.

Module Import RiscvPmpExecutor :=
  MakeExecutor RiscvPmpBase RiscvPmpSpecification RiscvPmpSolver.
Import SMut.
Import SMut.SMutNotations.

Notation "r '↦' val" := (chunk_ptsreg r val) (at level 79).

Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
  match CEnv f with
  | Some c => ValidContractReflect c (FunDef f)
  | None => False
  end.

Definition ValidContractDebug {Δ τ} (f : Fun Δ τ) : Prop :=
  match CEnv f with
  | Some c => SMut.ValidContract c (FunDef f)
  | None => False
  end.

Lemma valid_contract_checked_mem_read : ValidContract checked_mem_read.
Proof. reflexivity. Qed.

Lemma valid_contract_pmp_mem_read : ValidContract pmp_mem_read.
Proof. Admitted.

Lemma valid_contract_pmpCheck : ValidContract pmpCheck.
Proof. Admitted.

Lemma valid_contract_pmpCheckPerms : ValidContract pmpCheckPerms.
Proof. reflexivity. Qed.

Lemma valid_contract_pmpCheckRWX : ValidContract pmpCheckRWX.
Proof. reflexivity. Qed.

Lemma valid_contract_pmpAddrRange : ValidContract pmpAddrRange.
Proof. reflexivity. Qed.

Lemma valid_contract_pmpMatchAddr : ValidContract pmpMatchAddr.
Proof. reflexivity. Qed.

Lemma valid_contract_pmpMatchEntry : ValidContract pmpMatchEntry.
Proof. Admitted.

Lemma valid_contract_pmpLocked : ValidContract pmpLocked.
Proof. reflexivity. Qed.

Lemma valid_contract_readCSR : ValidContract readCSR.
Proof. reflexivity. Qed.

Lemma valid_contract_writeCSR : ValidContract writeCSR.
Proof. reflexivity. Qed.

Lemma valid_contract_check_CSR : ValidContract check_CSR.
Proof. reflexivity. Qed.

Lemma valid_contract_is_CSR_defined : ValidContract is_CSR_defined.
Proof. reflexivity. Qed.

Lemma valid_contract_check_CSR_access : ValidContract check_CSR_access.
Proof. reflexivity. Qed.

Lemma valid_contract_csrAccess : ValidContract csrAccess.
Proof. reflexivity. Qed.

Lemma valid_contract_csrPriv : ValidContract csrPriv.
Proof. reflexivity. Qed.

Lemma valid_contract_privLevel_to_bits : ValidContract privLevel_to_bits.
Proof. reflexivity. Qed.

Lemma valid_contract_mstatus_to_bits : ValidContract mstatus_to_bits.
Proof. reflexivity. Qed.

Lemma valid_contract_mstatus_from_bits : ValidContract mstatus_from_bits.
Proof. reflexivity. Qed.

Lemma valid_contract_exception_handler : ValidContract exception_handler.
Proof. reflexivity. Qed.

Lemma valid_contract_handle_illegal : ValidContract handle_illegal.
Proof. reflexivity. Qed.

Lemma valid_contract_trap_handler : ValidContract trap_handler.
Proof. reflexivity. Qed.

Lemma valid_contract_prepare_trap_vector : ValidContract prepare_trap_vector.
Proof. reflexivity. Qed.

Lemma valid_contract_tvec_addr : ValidContract tvec_addr.
Proof. reflexivity. Qed.

Lemma valid_contract_exceptionType_to_bits : ValidContract exceptionType_to_bits.
Proof. reflexivity. Qed.

Lemma valid_contract_exception_delegatee : ValidContract exception_delegatee.
Proof. reflexivity. Qed.

Lemma valid_contract_get_arch_pc : ValidContract get_arch_pc.
Proof. reflexivity. Qed.

Lemma valid_contract_get_next_pc : ValidContract get_next_pc.
Proof. reflexivity. Qed.

Lemma valid_contract_set_next_pc : ValidContract set_next_pc.
Proof. reflexivity. Qed.

Lemma valid_contract_rX : ValidContract rX.
Proof. reflexivity. Qed.

Lemma valid_contract_wX : ValidContract wX.
Proof. reflexivity. Qed.

Lemma valid_contract_abs : ValidContract abs.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_RTYPE : ValidContract execute_RTYPE.
Proof. reflexivity. Qed. 

Lemma valid_contract_execute_ITYPE : ValidContract execute_ITYPE.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_UTYPE : ValidContract execute_UTYPE.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_BTYPE : ValidContract execute_BTYPE.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_RISCV_JAL : ValidContract execute_RISCV_JAL.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_RISCV_JALR : ValidContract execute_RISCV_JALR.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_ECALL : ValidContract execute_ECALL.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_MRET : ValidContract execute_MRET.
Proof. reflexivity. Qed.

Lemma valid_execute_CSR : ValidContract execute_CSR.
Proof. reflexivity. Qed.

Section Debug.
  Import RiscvNotations.
  Import RiscvμSailNotations.
  Import SymProp.notations.
  Coercion stm_exp : Exp >-> Stm.
End Debug.

(* TODO: this is just to make sure that all contracts defined so far are valid
         (i.e. ensure no contract was defined and then forgotten to validate it) *)
Lemma defined_contracts_valid : forall {Δ τ} (f : Fun Δ τ),
    match CEnv f with
    | Some c => ValidContract f
    | None => True
    end.
Proof.
  destruct f; simpl; trivial;
    try reflexivity.
Admitted.

Module BlockVerification.

  Import ModalNotations.

  Definition M : TYPE -> TYPE :=
    fun A => □(A -> SHeap -> 𝕊) -> SHeap -> 𝕊.

  Definition pure {A} : ⊢ A -> M A. Admitted.
  Definition bind {A B} : ⊢ M A -> □(A -> M B) -> M B. Admitted.
  Definition angelic {σ} : ⊢ M (STerm σ). Admitted.
  Definition assert : ⊢ Formula -> M Unit. Admitted.
  Definition assume : ⊢ Formula -> M Unit. Admitted.

  Axiom produce_chunk : ⊢ Chunk -> M Unit.
  Axiom consume_chunk : ⊢ Chunk -> M Unit.

  Axiom produce : ⊢ Assertion -> □(M Unit).
  Axiom consume : ⊢ Assertion -> □(M Unit).

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
      ω12 ∣ v22 <- @rX rs1 _ ;;
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

  (* This is a VC for triples, for doubles we probably need to talk
     about the continuation of a block. *)
  Definition VC {Σ : LCtx} (req : Assertion Σ) (b : list AST) (ens : Assertion Σ) : 𝕊 Σ :=
    @exec_triple
      {| wctx := Σ; wco := nil |}
      req b ens
      (* Could include leakcheck here *)
      (fun _ _ _ h => SymProp.block)
      []%list.

  Section Example.

    Import ListNotations.
    Import bv.notations.
    Notation "p '∗' q" := (asn_sep p q).

    Example block1 : list AST :=
      [ ADD [bv 1] [bv 1] [bv 2];
        SUB [bv 2] [bv 1] [bv 2];
        SUB [bv 1] [bv 1] [bv 2]
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

    (* After implementing all the functions. *)
    (* Eval compute in VC1. *)

  End Example.

End BlockVerification.
