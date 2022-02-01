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
| gprs
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

  Definition 𝑯 := Predicate.
  Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
    match p with
    | pmp_entries  => [ty_list (ty_prod ty_pmpcfg_ent ty_xlenbits)]
    | gprs         => ctx.nil
    end.

  Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
    is_duplicable p :=
      match p with
      | pmp_entries  => false
      | gprs         => false
      end
    }.
  Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

  Local Arguments Some {_} &.
  Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
    match p with
    | _ => None
    end.

End PredicateKit.

Include ContractDeclMixin RiscvPmpBase RiscvPmpProgram.

Section ContractDefKit.

  Local Notation "r '↦' val" := (asn_chunk (chunk_ptsreg r val)) (at level 79).
  Local Notation "p '∗' q" := (asn_sep p q).
  Local Notation asn_pmp_entries l := (asn_chunk (chunk_user pmp_entries (env.nil ► (ty_list (ty_prod ty_pmpcfg_ent ty_xlenbits) ↦ l)))).
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
      (fun r => asn_exist "w" ty_xlenbits (r ↦ term_var "w")).

  (* TODO: abstract away the concrete type, look into unions for that *)
  (* TODO: length of list should be 16, no duplicates *)
  Definition pmp_entries {Σ} : Term Σ (ty_list (ty_prod ty_pmpcfgidx ty_pmpaddridx)) :=
    term_list (cons (term_binop binop_pair
                                (term_val ty_pmpcfgidx PMP0CFG) (* PMP0CFG ↦ ... *)
                                (term_val ty_pmpaddridx PMPADDR0)) nil). (* PMPADDR0 ↦ ... *)

  Section Contracts.
    Import RiscvNotations.

  (** Machine Invariant **)
  (*
    TODO: - there should be 2 cases in the @pre, one handling if we execute just fine and one if we end up in the trap (only with these 2 can we prove the @post)
          - this should work for the execute{,_/x/} functions, but step and loop will update 
            the pc, so this should be reflected in their contract (2nd pc(i) -> pc(i + 4)?)



    @pre ∀ m h i . mode(m) ∗ mtvec(h) ∗ pmp_entries(ents) ∗ pc(i) ∗ mepc(_) ∗ mpp(_)
    @post pmp_entries(ents) ∗ (mode(m) ∗ pc(i)) ∨ (mode(M) ∗ pc(h) ...)
    τ f(Δ...)*)
  Definition instr_exec_contract {τ Δ} : SepContract Δ τ :=
    let Σ := ["m" ∶ ty_privilege, "h" ∶ ty_xlenbits, "i" ∶ ty_xlenbits, "entries" ∶ ty_list (ty_prod ty_pmpcfg_ent ty_xlenbits), "mpp" ∶ ty_privilege, "mepc" ∶ ty_xlenbits, "npc" ∶ ty_xlenbits] in
    {| sep_contract_logic_variables := sep_contract_logvars Δ Σ;
       sep_contract_localstore      := create_localstore Δ Σ;
       sep_contract_precondition    :=
         cur_privilege ↦ (term_var "m") ∗
         mtvec ↦ (term_var "h") ∗
         pc ↦ (term_var "i") ∗
         asn_pmp_entries (term_var "entries") ∗
         nextpc ↦ term_var "npc" ∗
         asn_exist "mcause" ty_exc_code (mcause ↦ (term_var "mcause")) ∗
         mepc ↦ (term_var "mepc") ∗
         mstatus ↦ (term_record rmstatus [ term_var "mpp" ]) ∗
         asn_gprs;
       sep_contract_result          := "result_mach_inv";
       sep_contract_postcondition   :=
         asn_pmp_entries (term_var "entries") ∗
         asn_gprs ∗
         pc ↦ (term_var "i") ∗
         asn_exist "mcause" ty_exc_code (mcause ↦ (term_var "mcause")) ∗
         asn_or ((* Executing normally *)
                 cur_privilege ↦ term_var "m" ∗
                 asn_exist v ty_xlenbits (nextpc ↦ (term_var v)) ∗
                 mtvec ↦ (term_var "h") ∗
                 mstatus ↦ (term_record rmstatus [ term_var "mpp" ]) ∗
                 mepc ↦ (term_var "mepc"))
                (asn_or ((* Modified CSRs, requires Machine mode *)
                         asn_eq (term_var "m") (term_val ty_privilege Machine) ∗
                         cur_privilege ↦ (term_val ty_privilege Machine) ∗
                         nextpc ↦ (term_var "npc") ∗
                         asn_exist "new_mtvec" ty_xlenbits (mtvec ↦ (term_var "new_mtvec")) ∗
                         asn_exist "new_mpp" ty_privilege (mstatus ↦ (term_record rmstatus [ term_var "new_mpp" ])) ∗
                         asn_exist "new_mepc" ty_xlenbits (mepc ↦ (term_var "new_mepc")))
                        (asn_or ((* Trap occured -> Go into M-mode *)
                                 cur_privilege ↦ (term_val ty_privilege Machine) ∗
                                 nextpc ↦ (term_var "h") ∗
                                 mtvec ↦ (term_var "h") ∗
                                 mstatus ↦ (term_record rmstatus [ term_var "m" ]) ∗
                                 mepc ↦ (term_var "i"))
                                ((* MRET = Recover *)
                                 asn_eq (term_var "m") (term_val ty_privilege Machine) ∗
                                 cur_privilege ↦ (term_var "mpp") ∗
                                 nextpc ↦ (term_var "mepc") ∗
                                 mtvec ↦ (term_var "h") ∗
                                 mstatus ↦ (term_record rmstatus [ term_val ty_privilege User ]) ∗
                                 mepc ↦ (term_var "mepc"))))
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
    {| sep_contract_logic_variables := [csr ∶ ty_csridx, "mpp" ∶ ty_privilege,
                                        "mtvec" ∶ ty_xlenbits, "mcause" ∶ ty_exc_code,
                                        "mepc" ∶ ty_xlenbits];
       sep_contract_localstore      := [term_var csr]%arg;
       sep_contract_precondition    :=
         mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ mtvec ↦ term_var "mtvec"
         ∗ mcause ↦ term_var "mcause"
         ∗ mepc ↦ term_var "mepc";
       sep_contract_result          := "result_readCSR";
       sep_contract_postcondition   :=
         asn_exist "result" ty_xlenbits (asn_eq (term_var "result_readCSR") (term_var "result"))
         ∗ mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ mtvec ↦ term_var "mtvec"
         ∗ mcause ↦ term_var "mcause"
         ∗ mepc ↦ term_var "mepc";
    |}.

  Definition sep_contract_writeCSR : SepContractFun writeCSR :=
    {| sep_contract_logic_variables := [csr ∶ ty_csridx, value ∶ ty_xlenbits];
       sep_contract_localstore      := [term_var csr, term_var value]%arg;
       sep_contract_precondition    :=
         asn_exist "mpp" ty_privilege (mstatus ↦ term_record rmstatus [term_var "mpp"])
         ∗ asn_exist "mtvec" ty_xlenbits (mtvec ↦ term_var "mtvec")
         ∗ asn_exist "mcause" ty_exc_code (mcause ↦ term_var "mcause")
         ∗ asn_exist "mepc" ty_xlenbits (mepc ↦ term_var "mepc");
       sep_contract_result          := "result_writeCSR";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_writeCSR") (term_val ty_unit tt)
         ∗ asn_exist "mpp" ty_privilege (mstatus ↦ term_record rmstatus [term_var "mpp"])
         ∗ asn_exist "mtvec" ty_xlenbits (mtvec ↦ term_var "mtvec")
         ∗ asn_exist "mcause" ty_exc_code (mcause ↦ term_var "mcause")
         ∗ asn_exist "mepc" ty_xlenbits (mepc ↦ term_var "mepc");
    |}.

  Definition sep_contract_check_CSR : SepContractFun check_CSR :=
    {| sep_contract_logic_variables := [csr ∶ ty_csridx, p ∶ ty_privilege];
       sep_contract_localstore      := [term_var csr, term_var p]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_check_CSR";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var p)
                        (fun K => match K with
                                  | Machine => asn_eq (term_var "result_check_CSR") (term_val ty_bool true)
                                  | User    => asn_eq (term_var "result_check_CSR") (term_val ty_bool false)
                                  end)
    |}.

  Definition sep_contract_is_CSR_defined : SepContractFun is_CSR_defined :=
    {| sep_contract_logic_variables := [csr ∶ ty_csridx, p ∶ ty_privilege];
       sep_contract_localstore      := [term_var csr, term_var p]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_is_CSR_defined";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var p)
                        (fun K => match K with
                                  | Machine => asn_eq (term_var "result_is_CSR_defined")
                                                      (term_val ty_bool true)
                                  | User =>    asn_eq (term_var "result_is_CSR_defined")
                                                      (term_val ty_bool false)
                                  end);
    |}.

  Definition sep_contract_check_CSR_access : SepContractFun check_CSR_access :=
    {| sep_contract_logic_variables := [csrrw ∶ ty_access_type, csrpr ∶ ty_privilege, p ∶ ty_privilege];
       sep_contract_localstore      := [term_var csrrw, term_var csrpr, term_var p]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_check_CSR_access";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var csrpr)
                        (fun K => match K with
                                  | Machine =>
                                      asn_match_enum privilege (term_var p)
                                                     (fun K => match K with
                                                               | Machine =>    asn_eq (term_var "result_check_CSR_access")
                                                                                   (term_val ty_bool true)
                                                               | User =>    asn_eq (term_var "result_check_CSR_access")
                                                                                   (term_val ty_bool false)
                                                               end)
                                  | User =>
                                      asn_match_enum privilege (term_var p)
                                                     (fun K => match K with
                                                               | Machine => asn_eq (term_var "result_check_CSR_access")
                                                                                   (term_val ty_bool true)
                                                               | User =>    asn_eq (term_var "result_check_CSR_access")
                                                                                   (term_val ty_bool true)
                                                               end)
                                  end);
    |}.

  Definition sep_contract_privLevel_to_bits : SepContractFun privLevel_to_bits :=
    {| sep_contract_logic_variables := [p ∶ ty_privilege];
       sep_contract_localstore      := [term_var p]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_privLevel_to_bits";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var p)
                        (fun K => match K with
                                  | Machine => asn_eq (term_var "result_privLevel_to_bits")
                                                      (term_val ty_xlenbits 3%Z)
                                  | User =>    asn_eq (term_var "result_privLevel_to_bits")
                                                      (term_val ty_xlenbits 0%Z)
                                  end);
    |}.

  Definition sep_contract_mstatus_to_bits : SepContractFun mstatus_to_bits :=
    {| sep_contract_logic_variables := [value ∶ ty_mstatus];
       sep_contract_localstore      := [term_var value]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_mstatus_to_bits";
       sep_contract_postcondition   := asn_exist "result" ty_xlenbits
                                                 (asn_eq (term_var "result_mstatus_to_bits") (term_var "result"));
    |}.

  Definition sep_contract_mstatus_from_bits : SepContractFun mstatus_from_bits :=
    {| sep_contract_logic_variables := [value ∶ ty_xlenbits];
       sep_contract_localstore      := [term_var value]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_mstatus_from_bits";
       sep_contract_postcondition   :=
         asn_exist "MPP" ty_privilege (asn_eq (term_var "result_mstatus_from_bits")
                                              (term_record rmstatus [ term_var "MPP" ]));
    |}.

  Definition sep_contract_csrAccess : SepContractFun csrAccess :=
    {| sep_contract_logic_variables := [csr ∶ ty_csridx];
       sep_contract_localstore      := [term_var csr]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_csrAccess";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_csrAccess") (term_val ty_access_type ReadWrite);
    |}.

  Definition sep_contract_csrPriv : SepContractFun csrPriv :=
    {| sep_contract_logic_variables := [csr ∶ ty_csridx];
       sep_contract_localstore      := [term_var csr]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_csrPriv";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_csrPriv") (term_val ty_privilege Machine);
    |}.

  Definition sep_contract_exception_handler : SepContractFun exception_handler :=
    {| sep_contract_logic_variables := [cur_priv ∶ ty_privilege, ctl ∶ ty_ctl_result, "pc" ∶ ty_xlenbits, "mpp" ∶ ty_privilege, "mepc" ∶ ty_xlenbits, tvec ∶ ty_xlenbits, p ∶ ty_privilege];
       sep_contract_localstore      := [term_var cur_priv, term_var ctl, term_var "pc"]%arg;
       sep_contract_precondition    :=
         cur_privilege ↦ (term_var p)
         ∗ asn_exist "mcause" ty_exc_code  (mcause        ↦ (term_var "mcause"))
         ∗                                  mstatus       ↦ (term_record rmstatus [ term_var "mpp" ])
         ∗                                  mtvec         ↦ (term_var tvec)
         ∗                                  mepc          ↦ (term_var "mepc");
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
                    asn_eq (term_var "result_exception_handler") (term_var tvec)
                    ∗ cur_privilege ↦ (term_val ty_privilege Machine)
                    ∗ asn_exist "mcause" ty_exc_code (mcause ↦ (term_var "mcause"))
                    ∗ mstatus ↦ (term_record rmstatus [ term_var p ])
                    ∗ mepc ↦ (term_var "pc")
                    ∗ mtvec ↦ (term_var tvec)
                | KCTL_MRET =>
                    asn_eq (term_var "result_exception_handler") (term_var "mepc")
                    ∗ cur_privilege ↦ (term_var "mpp")
                    ∗ asn_exist "mcause" ty_exc_code (mcause ↦ (term_var "mcause"))
                    ∗ mstatus ↦ (term_record rmstatus [ term_val ty_privilege User ])
                    ∗ mtvec ↦ (term_var tvec)
                    ∗ mepc ↦ (term_var "mepc")
                end);
    |}.

  Definition sep_contract_handle_illegal : SepContractFun handle_illegal :=
    {| sep_contract_logic_variables := [p ∶ ty_privilege, "pc" ∶ ty_xlenbits, tvec ∶ ty_xlenbits];
       sep_contract_localstore      := env.nil%arg;
       sep_contract_precondition    :=
         cur_privilege ↦ (term_var p)
         ∗ pc ↦ (term_var "pc")
         ∗ asn_exist "mcause_val"  ty_exc_code (mcause  ↦ (term_var "mcause_val"))
         ∗ asn_exist "mpp" ty_privilege  (mstatus ↦ (term_record rmstatus [term_var "mpp"]))
         ∗ asn_exist "mepc_val"    ty_xlenbits (mepc    ↦ (term_var "mepc_val"))
         ∗ mtvec ↦ (term_var tvec)
         ∗ asn_exist v ty_xlenbits (nextpc ↦ term_var v);
       sep_contract_result          := "result_handle_illegal";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_handle_illegal") (term_val ty_unit tt)
         ∗ cur_privilege ↦ (term_val ty_privilege Machine)
         ∗ pc ↦ (term_var "pc")
         ∗ asn_exist "mcause" ty_exc_code (mcause ↦ (term_var "mcause"))
         ∗ mstatus ↦ (term_record rmstatus [ term_var p ])
         ∗ mepc ↦ (term_var "pc")
         ∗ mtvec ↦ (term_var tvec)
         ∗ nextpc ↦ (term_var tvec)
    |}.

  Definition sep_contract_trap_handler : SepContractFun trap_handler :=
    {| sep_contract_logic_variables := [del_priv ∶ ty_privilege, c ∶ ty_exc_code, "pc" ∶ ty_xlenbits, p ∶ ty_privilege, tvec ∶ ty_xlenbits];
       sep_contract_localstore      := [term_var del_priv, term_var c, term_var "pc"]%arg;
       sep_contract_precondition    :=
         cur_privilege ↦ (term_var p)
         ∗ asn_exist "mcause_val"  ty_exc_code (mcause  ↦ (term_var "mcause_val"))
         ∗ asn_exist "mstatus_val" ty_mstatus  (mstatus ↦ (term_var "mstatus_val"))
         ∗ asn_exist "mepc_val"    ty_xlenbits (mepc    ↦ (term_var "mepc_val"))
         ∗ mtvec ↦ (term_var tvec);
       sep_contract_result          := "result_trap_handler";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_trap_handler") (term_var tvec)
         ∗ asn_eq (term_var del_priv) (term_val ty_privilege Machine)
         ∗ cur_privilege ↦ (term_var del_priv)
         ∗ mcause        ↦ (term_var c)
         ∗ mstatus       ↦ (term_record rmstatus [ term_var p ])
         ∗ mepc          ↦ (term_var "pc")
         ∗ mtvec         ↦ (term_var tvec);
    |}.

  Definition sep_contract_prepare_trap_vector : SepContractFun prepare_trap_vector :=
    {| sep_contract_logic_variables := [p ∶ ty_privilege, cause ∶ ty_mcause, tvec ∶ ty_xlenbits];
       sep_contract_localstore      := [term_var p, term_var cause]%arg;
       sep_contract_precondition    := mtvec ↦ (term_var tvec);
       sep_contract_result          := "result_prepare_trap_vector";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_prepare_trap_vector") (term_var tvec)
         ∗ asn_eq (term_var p) (term_val ty_privilege Machine)
         ∗ mtvec ↦ (term_var tvec);
    |}.

  Definition sep_contract_tvec_addr : SepContractFun tvec_addr :=
    {| sep_contract_logic_variables := [m ∶ ty_xlenbits, c ∶ ty_mcause];
       sep_contract_localstore      := [term_var m, term_var c]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_tvec_addr";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_tvec_addr") (term_inl (term_var m));
    |}.

  Definition sep_contract_exceptionType_to_bits : SepContractFun exceptionType_to_bits :=
    {| sep_contract_logic_variables := [e ∶ ty_exception_type];
       sep_contract_localstore      := [term_var e]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_exceptionType_to_bits";
       sep_contract_postcondition   :=
        asn_exist result ty_exc_code
                  (asn_eq (term_var "result_exceptionType_to_bits") (term_var result))
    |}.

  Definition sep_contract_exception_delegatee : SepContractFun exception_delegatee :=
    {| sep_contract_logic_variables := [p ∶ ty_privilege];
       sep_contract_localstore      := [term_var p]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_exception_delegatee";
       sep_contract_postcondition   :=
        asn_eq (term_var "result_exception_delegatee") (term_val ty_privilege Machine)
    |}.

  Definition sep_contract_get_arch_pc : SepContractFun get_arch_pc :=
    {| sep_contract_logic_variables := [v ∶ ty_xlenbits];
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    := pc ↦ term_var v;
       sep_contract_result          := "result_get_arch_pc";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_get_arch_pc") (term_var v)
         ∗ pc ↦ term_var v;
    |}.

  Definition sep_contract_set_next_pc : SepContractFun set_next_pc :=
    {| sep_contract_logic_variables := [addr ∶ ty_xlenbits];
       sep_contract_localstore      := [term_var addr]%arg;
       sep_contract_precondition    := asn_exist v ty_xlenbits (nextpc ↦ term_var v);
       sep_contract_result          := "result_set_next_pc";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_set_next_pc") (term_val ty_unit tt)
         ∗ nextpc ↦ term_var addr;
    |}.

  Definition sep_contract_get_next_pc : SepContractFun get_next_pc :=
    {| sep_contract_logic_variables := [v ∶ ty_xlenbits];
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    := nextpc ↦ term_var v;
       sep_contract_result          := "result_get_next_pc";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_get_next_pc") (term_var v)
         ∗ nextpc ↦ term_var v;
    |}.

  Definition sep_contract_rX : SepContractFun rX :=
    {| sep_contract_logic_variables := [rs ∶ ty_regno];
       sep_contract_localstore      := [term_var rs]%arg;
       sep_contract_precondition    := asn_gprs;
       sep_contract_result          := "result_rX";
       sep_contract_postcondition   := asn_gprs;
    |}.

  Definition sep_contract_wX : SepContractFun wX :=
    {| sep_contract_logic_variables := [rs ∶ ty_regno, v ∶ ty_xlenbits];
       sep_contract_localstore      := [term_var rs, term_var v]%arg;
       sep_contract_precondition    := asn_gprs;
       sep_contract_result          := "result_wX";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_wX") (term_val ty_unit tt)
         ∗ asn_gprs;
    |}.

  Definition sep_contract_abs : SepContractFun abs :=
    {| sep_contract_logic_variables := [v ∶ ty_int];
       sep_contract_localstore      := [term_var v]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_abs";
       sep_contract_postcondition   := asn_true;
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
Qed.

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
      [].

  Section Example.

    Import ListNotations.
    Import bv.notations.
    Notation "p '∗' q" := (asn_sep p q).

    Example block1 : list AST :=
      [ ADD [bv 1] [bv 1] [bv 2];
        SUB [bv 2] [bv 1] [bv 2];
        SUB [bv 1] [bv 1] [bv 2]
      ].

    Let Σ1 : LCtx := ["x" :: ty_xlenbits, "y" :: ty_xlenbits].

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
