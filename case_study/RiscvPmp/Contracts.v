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
     Lists.List
     Strings.String
     ZArith.ZArith
     micromega.Lia.
From Katamaran Require Import
     Notations
     Bitvector
     Shallow.Executor
     Specification
     Symbolic.Executor
     Symbolic.Solver
     Symbolic.Propositions
     Symbolic.Worlds
     RiscvPmp.PmpCheck
     RiscvPmp.Machine
     RiscvPmp.Sig.
From Equations Require Import
     Equations.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import bv.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

(* NOTE: same as for mincaps, avoid Lemma in definition body for coqwc *)
Definition KatamaranLem := Lemma.

Module Import RiscvPmpSpecification <: Specification RiscvPmpBase RiscvPmpSignature RiscvPmpProgram.
  Include SpecificationMixin RiscvPmpBase RiscvPmpSignature RiscvPmpProgram.

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepLemma {Δ} (f : Lem Δ) : Type :=
    KatamaranLem Δ.

  Section Contracts.
    Section ContractDefKit.
      Import asn.notations.
      Import rv_notations.
      Local Notation "a <ᵘₜ b" := (term_binop (bop.relop bop.bvult) a b) (at level 60).
      Local Notation "a <=ᵘₜ b" := (term_binop (bop.relop bop.bvule) a b) (at level 60).
      Local Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
      Local Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
      Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

      Section ContractDef.
        Import RiscvNotations.
        Import RiscvPmpSignature.notations.

        (** Machine Invariant **)
        (* TODO: - this should work for the execute{,_/x/} functions, but step and loop will update
                   the pc, so this should be reflected in their contract (2nd pc(i) -> pc(i + 4)?)



           TODO: short notation out of sync with actual contract
           @pre ∀ m h i . mode(m) ∗ mtvec(h) ∗ pmp_entries(ents) ∗ pc(i) ∗ mepc(_) ∗ mpp(_)
           @post pmp_entries(ents) ∗ (mode(m) ∗ pc(i)) ∨ (mode(M) ∗ pc(h) ...)
           τ f(Δ...)*)
        Definition instr_exec_contract {τ Δ} : SepContract Δ τ :=
          let Σ := ["m" :: ty_privilege; "h" :: ty_xlenbits; "i" :: ty_xlenbits; "entries" :: ty.list ty_pmpentry; "mpp" :: ty_privilege; "mepc" :: ty_xlenbits; "npc" :: ty_xlenbits] in
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
                           asn_pmp_addr_access (term_var "entries") (term_var "m") ∗
                           asn_gprs;
             sep_contract_result          := "result_mach_inv";
             sep_contract_postcondition   :=
                           asn_pmp_addr_access (term_var "entries") (term_var "m") ∗
                           asn_gprs ∗
                           pc     ↦ term_var "i" ∗
               ∃ "mcause", mcause ↦ term_var "mcause" ∗
               (  (* Executing normally *)
                       asn_pmp_entries (term_var "entries") ∗
                       cur_privilege ↦ term_var "m" ∗
                  ∃ v, nextpc        ↦ term_var v ∗
                       mtvec         ↦ term_var "h" ∗
                       mstatus       ↦ term_record rmstatus [ term_var "mpp" ] ∗
                       mepc          ↦ term_var "mepc"
                ∨
                  (* Modified CSRs, requires Machine mode *)
                                 term_var "m"  =  term_val ty_privilege Machine ∗
                  ∃ "entries",   asn_pmp_entries (term_var "entries") ∗
                                 cur_privilege ↦ term_val ty_privilege Machine ∗
                                 nextpc        ↦ term_var "npc" ∗
                  ∃ "new_mtvec", mtvec         ↦ term_var "new_mtvec" ∗
                  ∃ "new_mpp",   mstatus       ↦ term_record rmstatus [ term_var "new_mpp" ] ∗
                  ∃ "new_mepc",  mepc          ↦ term_var "new_mepc"
                ∨
                  (* Trap occured -> Go into M-mode *)
                  asn_pmp_entries (term_var "entries") ∗
                  cur_privilege ↦ (term_val ty_privilege Machine) ∗
                  nextpc        ↦ term_var "h" ∗
                  mtvec         ↦ term_var "h" ∗
                  mstatus       ↦ term_record rmstatus [ term_var "m" ] ∗
                  mepc          ↦ term_var "i"
                ∨
                  (* MRET = Recover *)
                  asn_pmp_entries (term_var "entries") ∗
                  term_var "m"  =  term_val ty_privilege Machine ∗
                  cur_privilege ↦ term_var "mpp" ∗
                  nextpc        ↦ term_var "mepc" ∗
                  mtvec         ↦ term_var "h" ∗
                  mstatus       ↦ term_record rmstatus [ term_val ty_privilege User ] ∗
                  mepc          ↦ term_var "mepc")
          |}.

        Definition sep_contract_execute_RTYPE : SepContractFun execute_RTYPE :=
          instr_exec_contract.

        Definition sep_contract_execute_MUL : SepContractFun execute_MUL :=
          instr_exec_contract.

        Definition sep_contract_execute_ITYPE : SepContractFun execute_ITYPE :=
          instr_exec_contract.

        Definition sep_contract_execute_SHIFTIOP : SepContractFun execute_SHIFTIOP :=
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

        Definition sep_contract_execute_EBREAK : SepContractFun execute_EBREAK :=
          {| sep_contract_logic_variables := ctx.nil;
             sep_contract_localstore      := env.nil;
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_execute_EBREAK";
             sep_contract_postcondition   := ⊤;
          |}.

        Definition sep_contract_execute_MRET : SepContractFun execute_MRET :=
          instr_exec_contract.

        Definition sep_contract_execute_CSR : SepContractFun execute_CSR :=
          instr_exec_contract.

        Definition sep_contract_execute_STORE : SepContractFun execute_STORE :=
          instr_exec_contract.

        Definition sep_contract_execute_LOAD : SepContractFun execute_LOAD :=
          instr_exec_contract.

        Definition sep_contract_execute : SepContractFun execute :=
          instr_exec_contract.

        Definition sep_contract_process_load (bytes : nat) {pr : IsTrue (width_constraint bytes)} : SepContractFun (process_load bytes) :=
          {| sep_contract_logic_variables := [rd :: ty_regno; vaddr :: ty_xlenbits; value :: ty_memory_op_result bytes; is_unsigned :: ty.bool; "i" :: ty_xlenbits; tvec :: ty_xlenbits; p :: ty_privilege; "mpp" :: ty_privilege; "mepc" :: ty_xlenbits; "npc" :: ty_xlenbits; "mcause" :: ty_mcause];
             sep_contract_localstore      := [term_var rd; term_var vaddr; term_var value; term_var is_unsigned];
             sep_contract_precondition    :=
               asn_gprs
               ∗ pc            ↦ term_var "i"
               ∗ nextpc        ↦ term_var "npc"
               ∗ cur_privilege ↦ term_var p
               ∗ mcause        ↦ term_var "mcause"
               ∗ mstatus       ↦ term_record rmstatus [ term_var "mpp" ]
               ∗ mtvec         ↦ term_var tvec
               ∗ mepc          ↦ term_var "mepc";
             sep_contract_result          := "result_process_load";
             sep_contract_postcondition   :=
               asn_gprs ∗
               asn.match_union_alt (memory_op_result bytes) (term_var value)
                (fun K =>
                   match K with
                   | KMemValue     => MkAlt (pat_var v)
                                        (term_var "result_process_load" = term_val ty_retired RETIRE_SUCCESS
                                         ∗ pc            ↦ term_var "i"
                                         ∗ nextpc        ↦ term_var "npc"
                                         ∗ cur_privilege ↦ term_var p
                                         ∗ mcause        ↦ term_var "mcause"
                                         ∗ mstatus       ↦ term_record rmstatus [ term_var "mpp" ]
                                         ∗ mtvec         ↦ term_var tvec
                                         ∗ mepc          ↦ term_var "mepc")
                   | KMemException => MkAlt (pat_var e)
                                        (term_var "result_process_load" = term_val ty_retired RETIRE_FAIL
                                         ∗             pc            ↦ term_var "i"
                                         ∗             nextpc        ↦ term_var tvec
                                         ∗             cur_privilege ↦ term_val ty_privilege Machine
                                         ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
                                         ∗             mstatus       ↦ term_record rmstatus [ term_var p ]
                                         ∗             mepc          ↦ term_var "i"
                                         ∗             mtvec         ↦ term_var tvec)
                   end);
          |}.

        Definition sep_contract_readCSR : SepContractFun readCSR :=
          {| sep_contract_logic_variables := [csr :: ty_csridx; "mpp" :: ty_privilege;
                                              "mtvec" :: ty_xlenbits; "mcause" :: ty_mcause;
                                              "mepc" :: ty_xlenbits; "cfg0" :: ty_pmpcfg_ent; "cfg1" :: ty_pmpcfg_ent; "addr0" :: ty_xlenbits; "addr1" :: ty_xlenbits];
             sep_contract_localstore      := [term_var csr];
             sep_contract_precondition    :=
               mstatus ↦ term_record rmstatus [term_var "mpp"]
               ∗ mtvec ↦ term_var "mtvec"
               ∗ mcause ↦ term_var "mcause"
               ∗ mepc ↦ term_var "mepc"
               ∗ pmp0cfg ↦ term_var "cfg0"
               ∗ pmp1cfg ↦ term_var "cfg1"
               ∗ pmpaddr0 ↦ term_var "addr0"
               ∗ pmpaddr1 ↦ term_var "addr1";
             sep_contract_result          := "result_readCSR";
             sep_contract_postcondition   :=
               ∃ "result", term_var "result_readCSR" = term_var "result"
               ∗ mstatus ↦ term_record rmstatus [term_var "mpp"]
               ∗ mtvec ↦ term_var "mtvec"
               ∗ mcause ↦ term_var "mcause"
               ∗ mepc ↦ term_var "mepc"
               ∗ pmp0cfg ↦ term_var "cfg0"
               ∗ pmp1cfg ↦ term_var "cfg1"
               ∗ pmpaddr0 ↦ term_var "addr0"
               ∗ pmpaddr1 ↦ term_var "addr1";
          |}.

        Definition sep_contract_writeCSR : SepContractFun writeCSR :=
          {| sep_contract_logic_variables := [csr :: ty_csridx; value :: ty_xlenbits];
             sep_contract_localstore      := [term_var csr; term_var value];
             sep_contract_precondition    :=
               ∃ "mpp", mstatus ↦ term_record rmstatus [term_var "mpp"]
               ∗ ∃ "mtvec", mtvec ↦ term_var "mtvec"
               ∗ ∃ "mcause", mcause ↦ term_var "mcause"
               ∗ ∃ "mepc", mepc ↦ term_var "mepc"
               ∗ ∃ "cfg0", (pmp0cfg ↦ term_var "cfg0" ∗ asn_expand_pmpcfg_ent (term_var "cfg0"))
               ∗ ∃ "cfg1", (pmp1cfg ↦ term_var "cfg1" ∗ asn_expand_pmpcfg_ent (term_var "cfg1"))
               ∗ ∃ "addr0", pmpaddr0 ↦ term_var "addr0"
               ∗ ∃ "addr1", pmpaddr1 ↦ term_var "addr1";
             sep_contract_result          := "result_writeCSR";
             sep_contract_postcondition   :=
               term_var "result_writeCSR" = term_val ty.unit tt
               ∗ ∃ "mpp", mstatus ↦ term_record rmstatus [term_var "mpp"]
               ∗ ∃ "mtvec", mtvec ↦ term_var "mtvec"
               ∗ ∃ "mcause", mcause ↦ term_var "mcause"
               ∗ ∃ "mepc", mepc ↦ term_var "mepc"
               ∗ ∃ "cfg0", pmp0cfg ↦ term_var "cfg0"
               ∗ ∃ "cfg1", pmp1cfg ↦ term_var "cfg1"
               ∗ ∃ "addr0", pmpaddr0 ↦ term_var "addr0"
               ∗ ∃ "addr1", pmpaddr1 ↦ term_var "addr1";
          |}.

        Definition sep_contract_check_CSR : SepContractFun check_CSR :=
          {| sep_contract_logic_variables := [csr :: ty_csridx; p :: ty_privilege];
             sep_contract_localstore      := [term_var csr; term_var p];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_check_CSR";
             sep_contract_postcondition   :=
               asn.match_enum privilege (term_var p)
                 (fun K => match K with
                           | Machine => term_var "result_check_CSR" = term_val ty.bool true
                           | User    => term_var "result_check_CSR" = term_val ty.bool false
                           end)
          |}.

        Definition sep_contract_is_CSR_defined : SepContractFun is_CSR_defined :=
          {| sep_contract_logic_variables := [csr :: ty_csridx; p :: ty_privilege];
             sep_contract_localstore      := [term_var csr; term_var p];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_is_CSR_defined";
             sep_contract_postcondition   :=
               asn.match_enum privilege (term_var p)
                 (fun K => match K with
                           | Machine => term_var "result_is_CSR_defined" =
                                          term_val ty.bool true
                           | User    =>term_var "result_is_CSR_defined" =
                                         term_val ty.bool false
                           end);
          |}.

        Definition sep_contract_check_CSR_access : SepContractFun check_CSR_access :=
          {| sep_contract_logic_variables := [csrrw :: ty_access_type; csrpr :: ty_privilege; p :: ty_privilege];
             sep_contract_localstore      := [term_var csrrw; term_var csrpr; term_var p];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_check_CSR_access";
             sep_contract_postcondition   :=
               asn.match_enum privilege (term_var csrpr)
                 (fun K => match K with
                           | Machine =>
                               asn.match_enum privilege (term_var p)
                                 (fun K => match K with
                                           | Machine => term_var "result_check_CSR_access" =
                                                          term_val ty.bool true
                                           | User    => term_var "result_check_CSR_access" =
                                                          term_val ty.bool false
                                           end)
                           | User =>
                               asn.match_enum privilege (term_var p)
                                 (fun K => match K with
                                           | Machine => term_var "result_check_CSR_access" =
                                                          term_val ty.bool true
                                           | User    => term_var "result_check_CSR_access" =
                                                          term_val ty.bool true
                                           end)
                           end);
          |}.

        Definition sep_contract_privLevel_to_bits : SepContractFun privLevel_to_bits :=
          {| sep_contract_logic_variables := [p :: ty_privilege];
             sep_contract_localstore      := [term_var p];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_privLevel_to_bits";
             sep_contract_postcondition   :=
               asn.match_enum privilege (term_var p)
                 (fun K => match K with
                           | Machine => term_var "result_privLevel_to_bits" =
                                          term_val ty_priv_level [bits 11]
                           | User    => term_var "result_privLevel_to_bits" =
                                          term_val ty_priv_level [bits 00]
                           end);
          |}.

        Definition sep_contract_csrAccess : SepContractFun csrAccess :=
          {| sep_contract_logic_variables := [csr :: ty_csridx];
             sep_contract_localstore      := [term_var csr];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_csrAccess";
             sep_contract_postcondition   :=
               term_var "result_csrAccess" = term_val ty_access_type ReadWrite;
          |}.

        Definition sep_contract_csrPriv : SepContractFun csrPriv :=
          {| sep_contract_logic_variables := [csr :: ty_csridx];
             sep_contract_localstore      := [term_var csr];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_csrPriv";
             sep_contract_postcondition   :=
               term_var "result_csrPriv" = term_val ty_privilege Machine;
          |}.

        Definition sep_contract_handle_mem_exception : SepContractFun handle_mem_exception :=
          {| sep_contract_logic_variables := [addr :: ty_xlenbits; e :: ty_exception_type; "i" :: ty_xlenbits; tvec :: ty_xlenbits; p :: ty_privilege; "mpp" :: ty_privilege; "mepc" :: ty_xlenbits];
             sep_contract_localstore      := [term_var addr; term_var e];
             sep_contract_precondition    :=
                             pc            ↦ term_var "i"
               ∗ ∃ "npc",    nextpc        ↦ term_var "npc"
               ∗             cur_privilege ↦ term_var p
               ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
               ∗             mstatus       ↦ term_record rmstatus [ term_var "mpp" ]
               ∗             mtvec         ↦ term_var tvec
               ∗             mepc          ↦ term_var "mepc";
             sep_contract_result          := "result_handle_mem_exception";
             sep_contract_postcondition   :=
               term_var "result_handle_mem_exception" = term_val ty.unit tt
               ∗             pc            ↦ term_var "i"
               ∗             nextpc        ↦ term_var tvec
               ∗             cur_privilege ↦ term_val ty_privilege Machine
               ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
               ∗             mstatus       ↦ term_record rmstatus [ term_var p ]
               ∗             mepc          ↦ term_var "i"
               ∗             mtvec         ↦ term_var tvec
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
             sep_contract_postcondition   :=
              asn.match_union_alt ctl_result (term_var ctl)
                (fun K => match K with
                          | KCTL_TRAP => MkAlt (pat_var e)
                                           (term_var "result_exception_handler" = term_var tvec
                                            ∗             cur_privilege ↦ term_val ty_privilege Machine
                                            ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
                                            ∗             mstatus       ↦ term_record rmstatus [ term_var p ]
                                            ∗             mepc          ↦ term_var "pc"
                                            ∗             mtvec         ↦ term_var tvec)
                          | KCTL_MRET => MkAlt pat_unit
                                           (term_var "result_exception_handler" = term_var "mepc"
                                            ∗             cur_privilege ↦ term_var "mpp"
                                            ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
                                            ∗             mstatus       ↦ term_record rmstatus [ term_val ty_privilege User ]
                                            ∗             mtvec         ↦ term_var tvec
                                            ∗             mepc          ↦ term_var "mepc")
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
               term_var "result_handle_illegal" = term_val ty.unit tt
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
               ∗ mcause        ↦ term_zext (term_var c)
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
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_tvec_addr";
             sep_contract_postcondition   :=
               term_var "result_tvec_addr" = term_inl (term_var m);
          |}.

        Definition sep_contract_exceptionType_to_bits : SepContractFun exceptionType_to_bits :=
          {| sep_contract_logic_variables := [e :: ty_exception_type];
             sep_contract_localstore      := [term_var e];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_exceptionType_to_bits";
             sep_contract_postcondition   :=
               ∃ result, term_var "result_exceptionType_to_bits" = term_var result
          |}.

        Definition sep_contract_exception_delegatee : SepContractFun exception_delegatee :=
          {| sep_contract_logic_variables := [p :: ty_privilege];
             sep_contract_localstore      := [term_var p];
             sep_contract_precondition    := ⊤;
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
               term_var "result_set_next_pc" = term_val ty.unit tt
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

        Definition sep_contract_tick_pc : SepContractFun tick_pc :=
          {| sep_contract_logic_variables := ["npc" :: ty_xlenbits];
             sep_contract_localstore      := env.nil;
             sep_contract_precondition    := nextpc ↦ term_var "npc" ∗ ∃ "i", pc ↦ term_var "i";
             sep_contract_result          := "result_tick_pc";
             sep_contract_postcondition   :=
               term_var "result_tick_pc" = term_val ty.unit tt
               ∗ nextpc ↦ term_var "npc"
               ∗ pc     ↦ term_var "npc";
          |}.

        Definition sep_contract_to_bits (l : nat) : SepContractFun (to_bits l) :=
          {| sep_contract_logic_variables := [value :: ty.int];
             sep_contract_localstore      := [term_var value];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_to_bits";
             sep_contract_postcondition   :=
               term_var "result_to_bits" = term_get_slice_int (term_var value);
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
               term_var "result_wX" = term_val ty.unit tt
               ∗ asn_gprs;
          |}.

        (* Definition sep_contract_abs : SepContractFun abs := *)
        (*   {| sep_contract_logic_variables := [v :: ty.int]; *)
        (*      sep_contract_localstore      := [term_var v]; *)
        (*      sep_contract_precondition    := ⊤; *)
        (*      sep_contract_result          := "result_abs"; *)
        (*      sep_contract_postcondition   := ⊤; *)
        (*   |}. *)

        Definition sep_contract_step {τ Δ} : SepContract Δ τ :=
          let Σ := ["m" :: ty_privilege; "h" :: ty_xlenbits; "entries" :: ty.list ty_pmpentry; "mpp" :: ty_privilege; "i" :: ty_xlenbits] in
          {| sep_contract_logic_variables := sep_contract_logvars Δ Σ;
             sep_contract_localstore      := create_localstore Δ Σ;
             sep_contract_precondition    :=
                           cur_privilege ↦ term_var "m" ∗
                           mtvec         ↦ term_var "h" ∗
                           pc            ↦ term_var "i" ∗
               ∃ "npc",    nextpc        ↦ term_var "npc" ∗
               ∃ "mcause", mcause        ↦ term_var "mcause" ∗
               ∃ "mepc",   mepc          ↦ term_var "mepc" ∗
                           mstatus       ↦ term_record rmstatus [ term_var "mpp" ] ∗
                           asn_pmp_entries (term_var "entries") ∗
                           asn_pmp_addr_access (term_var "entries") (term_var "m") ∗
                           asn_gprs;
             sep_contract_result          := "result_mach_inv";
             sep_contract_postcondition   :=
               (  (* Executing normally *)
                              asn_pmp_addr_access (term_var "entries") (term_var "m") ∗
                              asn_gprs ∗
                              asn_pmp_entries (term_var "entries") ∗
                  ∃ "mcause", mcause ↦ term_var "mcause" ∗
                              cur_privilege ↦ term_var "m" ∗
                  ∃ v,       (nextpc        ↦ term_var v ∗
                              pc            ↦ term_var v) ∗
                              mtvec         ↦ term_var "h" ∗
                              mstatus       ↦ term_record rmstatus [ term_var "mpp" ] ∗
                  ∃ v,        mepc          ↦ term_var v
                ∨
                  (* Modified CSRs, requires Machine mode *)
                                 asn_pmp_addr_access (term_var "entries") (term_var "m") ∗
                                 asn_gprs ∗
                  ∃ "entries",   asn_pmp_entries (term_var "entries") ∗
                                 term_var "m"  =  term_val ty_privilege Machine ∗
                  ∃ "mcause", mcause ↦ term_var "mcause" ∗
                                 cur_privilege ↦ term_val ty_privilege Machine ∗
                  ∃ v, (nextpc        ↦ term_var v ∗ (* tick, nextpc + 4 *)
                        pc            ↦ term_var v) ∗
                  ∃ "new_mtvec", mtvec         ↦ term_var "new_mtvec" ∗
                  ∃ "new_mpp",   mstatus       ↦ term_record rmstatus [ term_var "new_mpp" ] ∗
                  ∃ "new_mepc",  mepc          ↦ term_var "new_mepc"
                ∨
                  (* Trap occured -> Go into M-mode *)
                  asn_pmp_addr_access (term_var "entries") (term_var "m") ∗
                  asn_gprs ∗
                  asn_pmp_entries (term_var "entries") ∗
                  ∃ "mcause", mcause ↦ term_var "mcause" ∗
                  cur_privilege ↦ (term_val ty_privilege Machine) ∗
                  nextpc        ↦ term_var "h" ∗
                  pc            ↦ term_var "h" ∗
                  mtvec         ↦ term_var "h" ∗
                  mstatus       ↦ term_record rmstatus [ term_var "m" ] ∗
                  mepc          ↦ term_var "i"
                ∨
                  (* MRET = Recover *)
                  asn_pmp_addr_access (term_var "entries") (term_var "m") ∗
                  asn_gprs ∗
                  asn_pmp_entries (term_var "entries") ∗
                  term_var "m"  =  term_val ty_privilege Machine ∗
                  ∃ "mcause", mcause ↦ term_var "mcause" ∗
                  cur_privilege ↦ term_var "mpp" ∗
                  ∃ "mepc", (mepc          ↦ term_var "mepc" ∗
                             nextpc        ↦ term_var "mepc" ∗
                             pc            ↦ term_var "mepc") ∗
                  mtvec         ↦ term_var "h" ∗
                  mstatus       ↦ term_record rmstatus [ term_val ty_privilege User ])
          |}.

        Definition sep_contract_fetch : SepContractFun fetch :=
          {| sep_contract_logic_variables := ["i" :: ty_xlenbits; p :: ty_privilege; "entries" :: ty.list ty_pmpentry];
             sep_contract_localstore      := env.nil;
             sep_contract_precondition    :=
                 pc ↦ term_var "i"
                 ∗ cur_privilege ↦ term_var p
                 ∗ asn_pmp_entries (term_var "entries")
                 ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
             sep_contract_result          := "result_fetch";
             sep_contract_postcondition   :=
               pc ↦ term_var "i"
               ∗ cur_privilege ↦ term_var p
               ∗ asn_pmp_entries (term_var "entries")
               ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
          |}.

        Definition sep_contract_init_model : SepContractFun init_model :=
          {| sep_contract_logic_variables := ctx.nil;
             sep_contract_localstore      := env.nil;
             sep_contract_precondition    :=
               ∃ p, cur_privilege ↦ term_var p
               ∗ ∃ "es", asn_pmp_entries (term_var "es");
             sep_contract_result          := "result_init_model";
             sep_contract_postcondition   :=
               term_var "result_init_model" = term_val ty.unit tt
               ∗ cur_privilege ↦ term_val ty_privilege Machine
               ∗ ∃ "es", asn_pmp_entries (term_var "es");
          |}.

        Definition sep_contract_init_sys : SepContractFun init_sys :=
          {| sep_contract_logic_variables := ctx.nil;
             sep_contract_localstore      := env.nil;
             sep_contract_precondition    :=
               ∃ p, cur_privilege ↦ term_var p
               ∗ ∃ "es", asn_pmp_entries (term_var "es");
             sep_contract_result          := "result_init_sys";
             sep_contract_postcondition   :=
               term_var "result_init_sys" = term_val ty.unit tt
               ∗ cur_privilege ↦ term_val ty_privilege Machine
               ∗ ∃ "es", asn_pmp_entries (term_var "es");
          |}.

        Definition sep_contract_init_pmp : SepContractFun init_pmp :=
          {| sep_contract_logic_variables := ctx.nil;
             sep_contract_localstore      := env.nil;
             sep_contract_precondition    :=
               ∃ "cfg0", pmp0cfg ↦ term_var "cfg0" ∗ ∃ "cfg1", pmp1cfg ↦ term_var "cfg1";
             sep_contract_result          := "result_init_pmp";
             sep_contract_postcondition   :=
               ∃ "cfg0", pmp0cfg ↦ term_var "cfg0" ∗ ∃ "cfg1", pmp1cfg ↦ term_var "cfg1"
               ∗ term_var "result_init_pmp" = term_val ty.unit tt;
          |}.

        Definition sep_contract_within_phys_mem : SepContractFun within_phys_mem :=
          {| sep_contract_logic_variables := [paddr :: ty_xlenbits; width :: ty.int];
             sep_contract_localstore      := [term_var paddr; term_var width];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_within_phys_mem";
             sep_contract_postcondition   :=
              let paddr_int : Term _ ty.int := term_unsigned (term_var paddr) in
               if: term_var "result_within_phys_mem"
               then term_val ty.int (Z.of_nat minAddr) <= paddr_int
                    ∗ (term_binop bop.plus paddr_int (term_var width)) <= term_val ty.int (Z.of_nat maxAddr)
               else (paddr_int < term_val ty.int (Z.of_nat minAddr)
                     ∨ term_val ty.int (Z.of_nat maxAddr) < (term_binop bop.plus paddr_int (term_var width)));
          |}.

        Definition sep_contract_checked_mem_read (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@checked_mem_read bytes H) :=
          {| sep_contract_logic_variables := [t :: ty_access_type; paddr :: ty_xlenbits; p :: ty_privilege; "entries" :: ty.list ty_pmpentry];
             sep_contract_localstore      := [term_var t; term_var paddr];
             sep_contract_precondition    :=
                 term_union access_type KRead (term_val ty.unit tt) ⊑ term_var t
                 ∗ cur_privilege ↦ term_var p
                 ∗ asn_pmp_entries (term_var "entries")
                 ∗ asn_pmp_addr_access (term_var "entries") (term_var p)
                 ∗ asn_pmp_access (term_var paddr) (term_val ty_xlenbits (Bitvector.bv.of_nat bytes)) (term_var "entries") (term_var p) (term_var t);
             sep_contract_result          := "result_checked_mem_read";
             sep_contract_postcondition   :=
               cur_privilege ↦ term_var p
               ∗ asn_pmp_entries (term_var "entries")
               ∗ asn_pmp_addr_access (term_var "entries") (term_var p)
          |}.

        Definition sep_contract_checked_mem_write (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@checked_mem_write bytes H) :=
          {| sep_contract_logic_variables := [paddr :: ty_xlenbits; data :: ty_bytes bytes; p :: ty_privilege; "entries" :: ty.list ty_pmpentry; acc :: ty_access_type];
             sep_contract_localstore      := [term_var paddr; term_var data];
             sep_contract_precondition    :=
                asn_pmp_access (term_var paddr) (term_val ty_xlenbits (Bitvector.bv.of_nat bytes)) (term_var "entries") (term_var p) (term_var acc)
                ∗ term_union access_type KWrite (term_val ty.unit tt) ⊑ term_var acc
                ∗ cur_privilege ↦ term_var p
                ∗ asn_pmp_entries (term_var "entries")
                ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
             sep_contract_result          := "result_checked_mem_write";
             sep_contract_postcondition   :=
               cur_privilege ↦ term_var p
               ∗ asn_pmp_entries (term_var "entries")
               ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
          |}.

        Definition sep_contract_pmp_mem_read (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@pmp_mem_read bytes H) :=
          {| sep_contract_logic_variables := [t :: ty_access_type; p :: ty_privilege; paddr :: ty_xlenbits; "entries" :: ty.list ty_pmpentry];
             sep_contract_localstore      := [term_var t; term_var p; term_var paddr];
             sep_contract_precondition    :=
                 term_union access_type KRead (term_val ty.unit tt) ⊑ term_var t
               ∗ cur_privilege ↦ term_var p
               ∗ asn_pmp_entries (term_var "entries")
               ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
             sep_contract_result          := "result_pmp_mem_read";
             sep_contract_postcondition   :=
               cur_privilege ↦ term_var p
               ∗ asn_pmp_entries (term_var "entries")
               ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
          |}.

        Definition sep_contract_pmp_mem_write (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@pmp_mem_write bytes H) :=
          {| sep_contract_logic_variables := [paddr :: ty_xlenbits; data :: ty_bytes bytes; typ :: ty_access_type; priv :: ty_privilege; "entries" :: ty.list ty_pmpentry];
             sep_contract_localstore      := [term_var paddr; term_var data; term_var typ; term_var priv];
             sep_contract_precondition    := (* NOTE: only ever called with typ = Write *)
               (term_var typ = term_union access_type KWrite (term_val ty.unit tt)
                ∨ term_var typ = term_union access_type KReadWrite (term_val ty.unit tt))
               ∗ cur_privilege ↦ term_var priv
               ∗ asn_pmp_entries (term_var "entries")
               ∗ asn_pmp_addr_access (term_var "entries") (term_var priv);
             sep_contract_result          := "result_pmp_mem_write";
             sep_contract_postcondition   :=
               cur_privilege ↦ term_var priv
               ∗ asn_pmp_entries (term_var "entries")
               ∗ asn_pmp_addr_access (term_var "entries") (term_var priv);
          |}.

        Definition sep_contract_mem_write_value (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@mem_write_value bytes H) :=
          {| sep_contract_logic_variables := [paddr :: ty_xlenbits; value :: ty_bytes bytes; p :: ty_privilege; "entries" :: ty.list ty_pmpentry];
             sep_contract_localstore      := [term_var paddr; term_var value];
             sep_contract_precondition    :=
               cur_privilege ↦ term_var p
               ∗ asn_pmp_entries (term_var "entries")
               ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
             sep_contract_result          := "result_pmp_mem_write";
             sep_contract_postcondition   :=
               cur_privilege ↦ term_var p
               ∗ asn_pmp_entries (term_var "entries")
               ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
          |}.

        Definition sep_contract_mem_read (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@mem_read bytes H) :=
          {| sep_contract_logic_variables := [typ :: ty_access_type; paddr :: ty_xlenbits; p :: ty_privilege; "entries" :: ty.list ty_pmpentry];
             sep_contract_localstore      := [term_var typ; term_var paddr];
             sep_contract_precondition    :=
                (term_var typ = term_union access_type KRead (term_val ty.unit tt)
                 ∨ term_var typ = term_union access_type KExecute (term_val ty.unit tt))
               ∗ cur_privilege ↦ term_var p
               ∗ asn_pmp_entries (term_var "entries")
               ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
             sep_contract_result          := "result_mem_read";
             sep_contract_postcondition   :=
               cur_privilege ↦ term_var p
               ∗ asn_pmp_entries (term_var "entries")
               ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
          |}.

        Definition sep_contract_pmpCheck (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@pmpCheck bytes H) :=
          {| sep_contract_logic_variables := [addr :: ty_xlenbits; acc :: ty_access_type; priv :: ty_privilege; "entries" :: ty.list ty_pmpentry];
             sep_contract_localstore      := [term_var addr; term_var acc; term_var priv];
             sep_contract_precondition    :=
               asn_pmp_entries (term_var "entries");
             sep_contract_result          := "result_pmpCheck";
             sep_contract_postcondition   :=
               asn_match_option
                 _ (term_var "result_pmpCheck") e
                 (asn_pmp_entries (term_var "entries"))
                 (asn_pmp_entries (term_var "entries") ∗ asn_pmp_access (term_var addr) (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var priv) (term_var acc));
          |}.


        Definition sep_contract_pmpCheckPerms : SepContractFun pmpCheckPerms :=
          let Σ : LCtx := [acc :: ty_access_type; priv :: ty_privilege; L :: ty.bool; A :: ty_pmpaddrmatchtype; X :: ty.bool; W :: ty.bool; R :: ty.bool] in
          let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
          {| sep_contract_logic_variables := Σ;
             sep_contract_localstore      := [nenv entry; term_var acc; term_var priv];
             sep_contract_precondition    :=
               ⊤;
             sep_contract_result          := "result_pmpCheckPerms";
             sep_contract_postcondition   :=
               let entry := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
               if: term_var "result_pmpCheckPerms"
               then asn_pmp_check_perms entry (term_var acc) (term_var priv)
               else ⊤;
          |}.

        Definition sep_contract_pmpCheckRWX : SepContractFun pmpCheckRWX :=
          let Σ : LCtx := [acc :: ty_access_type; L :: ty.bool; A :: ty_pmpaddrmatchtype; X :: ty.bool; W :: ty.bool; R :: ty.bool] in
          let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
          {| sep_contract_logic_variables := Σ;
             sep_contract_localstore      := [nenv entry; term_var acc];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_pmpCheckRWX";
             sep_contract_postcondition   :=
               let entry := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
               if: term_var "result_pmpCheckRWX"
               then asn_pmp_check_rwx entry (term_var acc)
               else ⊤;
          |}.

        Definition sep_contract_pmpAddrRange : SepContractFun pmpAddrRange :=
          let Σ : LCtx := [pmpaddr :: ty_xlenbits; prev_pmpaddr :: ty_xlenbits; L :: ty.bool; A :: ty_pmpaddrmatchtype; X :: ty.bool; W :: ty.bool; R :: ty.bool] in
          let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
          {| sep_contract_logic_variables := Σ;
             sep_contract_localstore      := [nenv entry; term_var pmpaddr; term_var prev_pmpaddr];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_pmpAddrRange";
             sep_contract_postcondition   :=
               asn.match_enum pmpaddrmatchtype (term_var A)
                 (fun K => match K with
                           | OFF => term_var "result_pmpAddrRange" = term_inr (term_val ty.unit tt)
                           | TOR => term_var "result_pmpAddrRange" = term_inl (term_var prev_pmpaddr ,ₜ term_var pmpaddr)
                           end);
          |}.

        Definition sep_contract_pmpMatchAddr : SepContractFun pmpMatchAddr :=
          {| sep_contract_logic_variables := [addr :: ty_xlenbits; width :: ty_xlenbits; rng :: ty_pmp_addr_range];
             sep_contract_localstore      := [term_var addr; term_var width; term_var rng];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_pmpMatchAddr";
             sep_contract_postcondition   :=
               asn_match_option
                 _ (term_var rng) v
                 (asn.match_prod
                    (term_var v) lo hi
                    (asn.match_enum pmpaddrmatch (term_var "result_pmpMatchAddr")
                      (fun K => match K with
                                | PMP_NoMatch =>
                                    asn_bool (term_var hi <ᵘₜ term_var lo)
                                    ∨ (asn_bool (term_var lo <=ᵘₜ term_var hi) ∗ asn_bool (term_binop bop.bvadd (term_var addr) (term_var width) <=ᵘₜ term_var lo))
                                    ∨ (asn_bool (term_var lo <=ᵘₜ term_var hi) ∗ asn_bool (term_var lo <ᵘₜ term_binop bop.bvadd (term_var addr) (term_var width)) ∗ asn_bool (term_var hi <=ᵘₜ term_var addr))
                                | PMP_PartialMatch =>
                                    term_var lo <=ᵘ term_var hi ∗
                                    term_var lo <ᵘ term_binop bop.bvadd (term_var addr) (term_var width) ∗
                                    term_var addr <ᵘ term_var hi ∗
                                    (term_var addr <ᵘ term_var lo ∨ term_var hi <ᵘ (term_binop bop.bvadd (term_var addr) (term_var width)))
                                | PMP_Match =>
                                      (term_var lo) <=ᵘ (term_var hi)
                                    ∗ (term_var lo) <ᵘ  (term_binop bop.bvadd (term_var addr) (term_var width))
                                    ∗ (term_var lo) <=ᵘ (term_var addr)
                                    ∗ (term_var addr) <ᵘ (term_var hi)
                                    ∗ (term_binop bop.bvadd (term_var addr) (term_var width)) <=ᵘ (term_var hi)
                                end)))
                 (term_var "result_pmpMatchAddr" = term_val ty_pmpaddrmatch PMP_NoMatch);
          |}.

        Definition sep_contract_pmpMatchEntry : SepContractFun pmpMatchEntry :=
          let Σ : LCtx := [addr :: ty_xlenbits; width :: ty_xlenbits; acc :: ty_access_type; priv :: ty_privilege; pmpaddr :: ty_xlenbits; prev_pmpaddr :: ty_xlenbits; L :: ty.bool; A :: ty_pmpaddrmatchtype; X :: ty.bool; W :: ty.bool; R :: ty.bool] in
          let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
          {| sep_contract_logic_variables := Σ;
             sep_contract_localstore      := [nenv term_var addr; term_var width; term_var acc; term_var priv; entry; term_var pmpaddr; term_var prev_pmpaddr];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_pmpMatchEntry";
             sep_contract_postcondition   :=
               let entry := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
               asn.match_enum pmpmatch (term_var "result_pmpMatchEntry")
                 (fun K => match K with
                           | PMP_Continue =>
                                    term_var A = term_val ty_pmpaddrmatchtype OFF
                                    ∨ (asn.formula (formula_relop bop.neq (term_var A) (term_val ty_pmpaddrmatchtype OFF)) ∗
                                         (asn_bool (term_var pmpaddr <ᵘₜ term_var prev_pmpaddr)
                                          ∨ (asn_bool (term_var prev_pmpaddr <=ᵘₜ term_var pmpaddr) ∗ asn_bool (term_binop bop.bvadd (term_var addr) (term_var width) <=ᵘₜ term_var prev_pmpaddr))
                                          ∨ (asn_bool (term_var prev_pmpaddr <=ᵘₜ term_var pmpaddr) ∗ asn_bool (term_var prev_pmpaddr <ᵘₜ term_binop bop.bvadd (term_var addr) (term_var width)) ∗ asn_bool (term_var pmpaddr <=ᵘₜ term_var addr))))
                           | PMP_Fail     =>
                               asn_bool (term_not
                                           (term_var prev_pmpaddr <=ᵘₜ term_var addr &&ₜ term_var addr <ᵘₜ term_var pmpaddr))
                               ∨ ⊤ (* TODO: either we have a partial match, or we don't have the required permissions! *)
                           | PMP_Success  =>
                                  (term_var prev_pmpaddr) <=ᵘ (term_var pmpaddr)
                                ∗ (term_var prev_pmpaddr) <ᵘ  (term_binop bop.bvadd (term_var addr) (term_var width))
                                ∗ (term_var prev_pmpaddr) <=ᵘ (term_var addr)
                                ∗ (term_var addr) <ᵘ (term_var pmpaddr)
                                ∗ (term_binop bop.bvadd (term_var addr) (term_var width)) <=ᵘ (term_var pmpaddr)
                               ∗ asn_pmp_check_perms entry (term_var acc) (term_var priv)
                               ∗ term_var A = term_val ty_pmpaddrmatchtype TOR
                           end);
          |}.

        Definition sep_contract_pmpLocked : SepContractFun pmpLocked :=
          let Σ : LCtx := [L :: ty.bool; A :: ty_pmpaddrmatchtype; X :: ty.bool; W :: ty.bool; R :: ty.bool] in
          let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
          {| sep_contract_logic_variables := Σ;
             sep_contract_localstore      := env.snoc env.nil (_::_) entry;
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_pmpLocked";
             sep_contract_postcondition   := term_var "result_pmpLocked" = term_var L;
          |}.

        Definition sep_contract_pmpWriteCfg : SepContractFun pmpWriteCfg :=
          {| sep_contract_logic_variables := [cfg :: ty_pmpcfg_ent; value :: ty_byte];
             sep_contract_localstore      := [term_var cfg; term_var value];
             sep_contract_precondition    := asn_expand_pmpcfg_ent (term_var cfg);
             sep_contract_result          := "result_pmpWriteCfg";
             sep_contract_postcondition   :=
               ∃ "cfg", term_var "result_pmpWriteCfg" = term_var "cfg";
          |}.


        Definition sep_contract_pmpWriteCfgReg (n : nat) {H: (n < 1)%nat} : SepContractFun (@pmpWriteCfgReg n H) :=
          {| sep_contract_logic_variables := [value :: ty_xlenbits];
             sep_contract_localstore      := [term_var value];
             sep_contract_precondition    :=
                  ∃ "cfg0", (pmp0cfg ↦ term_var "cfg0" ∗ asn_expand_pmpcfg_ent (term_var "cfg0"))
                  ∗ ∃ "cfg1", (pmp1cfg ↦ term_var "cfg1" ∗ asn_expand_pmpcfg_ent (term_var "cfg1"));
             sep_contract_result          := "result_pmpWriteCfgReg";
             sep_contract_postcondition   :=
               term_var "result_pmpWriteCfgReg" = term_val ty.unit tt
               ∗ ∃ "cfg0", pmp0cfg ↦ term_var "cfg0"
               ∗ ∃ "cfg1", pmp1cfg ↦ term_var "cfg1";
          |}.

        Definition sep_contract_pmpWriteAddr : SepContractFun pmpWriteAddr :=
          {| sep_contract_logic_variables := [locked :: ty.bool; addr :: ty_xlenbits; value :: ty_xlenbits];
             sep_contract_localstore      := [term_var locked; term_var addr; term_var value];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_pmpWriteAddr";
             sep_contract_postcondition   :=
               if: term_var locked
               then term_var "result_pmpWriteAddr" = term_var addr
               else term_var "result_pmpWriteAddr" = term_var value;
          |}.

        Definition CEnv : SepContractEnv :=
          fun Δ τ fn =>
            match fn with
            | execute_RTYPE           => Some sep_contract_execute_RTYPE
            | execute_ITYPE           => Some sep_contract_execute_ITYPE
            | execute_SHIFTIOP        => Some sep_contract_execute_SHIFTIOP
            | execute_UTYPE           => Some sep_contract_execute_UTYPE
            | execute_BTYPE           => Some sep_contract_execute_BTYPE
            | execute_RISCV_JAL       => Some sep_contract_execute_RISCV_JAL
            | execute_RISCV_JALR      => Some sep_contract_execute_RISCV_JALR
            | execute_ECALL           => Some sep_contract_execute_ECALL
            | execute_EBREAK          => Some sep_contract_execute_EBREAK
            | execute_MRET            => Some sep_contract_execute_MRET
            | execute_CSR             => Some sep_contract_execute_CSR
            | execute_STORE           => Some sep_contract_execute_STORE
            | execute_LOAD            => Some sep_contract_execute_LOAD
            | execute_MUL             => Some sep_contract_execute_MUL
            | process_load bytes      => Some (sep_contract_process_load bytes)
            | get_arch_pc             => Some sep_contract_get_arch_pc
            | get_next_pc             => Some sep_contract_get_next_pc
            | set_next_pc             => Some sep_contract_set_next_pc
            | tick_pc                 => Some sep_contract_tick_pc
            | to_bits l               => Some (sep_contract_to_bits l)
            | exception_handler       => Some sep_contract_exception_handler
            | handle_mem_exception    => Some sep_contract_handle_mem_exception
            | handle_illegal          => Some sep_contract_handle_illegal
            | trap_handler            => Some sep_contract_trap_handler
            | prepare_trap_vector     => Some sep_contract_prepare_trap_vector
            | tvec_addr               => Some sep_contract_tvec_addr
            | exceptionType_to_bits   => Some sep_contract_exceptionType_to_bits
            | exception_delegatee     => Some sep_contract_exception_delegatee
            | rX                      => Some sep_contract_rX
            | wX                      => Some sep_contract_wX
            (* | abs                     => Some sep_contract_abs *)
            | within_phys_mem         => Some sep_contract_within_phys_mem
            | readCSR                 => Some sep_contract_readCSR
            | writeCSR                => Some sep_contract_writeCSR
            | check_CSR               => Some sep_contract_check_CSR
            | is_CSR_defined          => Some sep_contract_is_CSR_defined
            | check_CSR_access        => Some sep_contract_check_CSR_access
            | privLevel_to_bits       => Some sep_contract_privLevel_to_bits
            | csrAccess               => Some sep_contract_csrAccess
            | csrPriv                 => Some sep_contract_csrPriv
            | @checked_mem_read bytes H => Some (@sep_contract_checked_mem_read bytes H)
            | @checked_mem_write bytes H => Some (@sep_contract_checked_mem_write bytes H)
            | @pmp_mem_read bytes H   => Some (@sep_contract_pmp_mem_read bytes H)
            | @pmp_mem_write bytes H  => Some (@sep_contract_pmp_mem_write bytes H)
            | @pmpCheck bytes H       => Some (@sep_contract_pmpCheck bytes H)
            | pmpCheckPerms           => Some sep_contract_pmpCheckPerms
            | pmpCheckRWX             => Some sep_contract_pmpCheckRWX
            | pmpAddrRange            => Some sep_contract_pmpAddrRange
            | pmpMatchAddr            => Some sep_contract_pmpMatchAddr
            | pmpMatchEntry           => Some sep_contract_pmpMatchEntry
            | pmpLocked               => Some sep_contract_pmpLocked
            | @pmpWriteCfgReg n H     => Some (@sep_contract_pmpWriteCfgReg n H)
            | pmpWriteCfg             => Some sep_contract_pmpWriteCfg
            | pmpWriteAddr            => Some sep_contract_pmpWriteAddr
            | @mem_write_value bytes H => Some (@sep_contract_mem_write_value bytes H)
            | @mem_read bytes H       => Some (@sep_contract_mem_read bytes H)
            | init_model              => Some sep_contract_init_model
            | init_sys                => Some sep_contract_init_sys
            | init_pmp                => Some sep_contract_init_pmp
            | fetch                   => Some sep_contract_fetch
            | execute                 => Some sep_contract_execute
            | step                    => Some sep_contract_step
            | _                       => None
            end.

        Lemma linted_cenv :
          forall Δ τ (fn : Fun Δ τ),
            match CEnv fn with
            | Some cnt => Linted cnt
            | None   => True
            end.
        Proof. intros ? ? []; try constructor. Qed.

      End ContractDef.

      Section ForeignDef.
        Import RiscvPmpSignature.notations.
        Local Notation "e1 '=?' e2" := (term_binop (bop.relop bop.eq) e1 e2).

        Definition sep_contract_read_ram (bytes : nat) : SepContractFunX (read_ram bytes) :=
          {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "w" :: ty_bytes bytes];
             sep_contract_localstore      := [term_var "paddr"];
             sep_contract_precondition    :=
               asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]);
             sep_contract_result          := "result_read_ram";
             sep_contract_postcondition   := term_var "result_read_ram" = term_var "w"
              ∗ asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]);
          |}.

        Definition sep_contract_write_ram (bytes : nat) : SepContractFunX (write_ram bytes) :=
          {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "data" :: ty_bytes bytes];
             sep_contract_localstore      := [term_var "paddr"; term_var "data"];
             sep_contract_precondition    :=
              ∃ "w", asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]);
             sep_contract_result          := "result_write_ram";
             sep_contract_postcondition   :=
               asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "data"])
          |}.

        (* NOTE: for now, this always returns False, since we do not provide the adversary with access to MMIO. In the future, this could just branch non-deterministically in the post. *)
        (* TODO: return `is_mmio`-chunk here once untrusted code gains access to MMIO *)

        Definition sep_contract_within_mmio (bytes : nat) {H: restrict_bytes bytes}: SepContractFunX (@within_mmio bytes H) :=
          {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "p" :: ty_privilege; "entries" :: ty.list ty_pmpentry];
             sep_contract_localstore      := [term_var "paddr"];
             sep_contract_precondition    :=
                 cur_privilege ↦ term_var "p"
                 ∗ asn_pmp_entries (term_var "entries")
                 ∗ asn_pmp_addr_access (term_var "entries") (term_var "p")
                 ∗ (∃ "t", asn_pmp_access (term_var "paddr") (term_val ty_xlenbits (Bitvector.bv.of_nat bytes)) (term_var "entries") (term_var "p") (term_var "t"));
             sep_contract_result          := "result_is_within";
             sep_contract_postcondition   := term_var "result_is_within" = term_val ty.bool false
                 ∗ cur_privilege ↦ term_var "p"
                 ∗ asn_pmp_entries (term_var "entries")
                 ∗ asn_pmp_addr_access (term_var "entries") (term_var "p")
          |}.

        (* NOTE: no need for sensible contracts for `mmio_read`/`mmio_write` yet, as we will not grant untrusted code access to `mmio` directly *)
       Definition sep_contract_mmio_read (bytes : nat) : SepContractFunX (mmio_read bytes) :=
          {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits];
             sep_contract_localstore      := [term_var "paddr"];
             sep_contract_precondition    := ⊥;
             sep_contract_result          := "result_read_mmio";
             sep_contract_postcondition   := ⊥;
          |}.
       Definition sep_contract_mmio_write (bytes : nat) (H : restrict_bytes bytes) : SepContractFunX (mmio_write H) :=
          {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "data" :: ty_bytes bytes];
             sep_contract_localstore      := [term_var "paddr"; term_var "data"];
             sep_contract_precondition    := ⊥;
             sep_contract_result          := "result_write_mmio";
             sep_contract_postcondition   := ⊥;
          |}.

        Definition sep_contract_decode    : SepContractFunX decode :=
          {| sep_contract_logic_variables := ["bv" :: ty_xlenbits];
             sep_contract_localstore      := [term_var "bv"];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_decode";
             sep_contract_postcondition   := ⊤;
          |}.

        Definition sep_contract_vector_subrange {n} (e b : nat)
          {p : IsTrue (0 <=? b)%nat} {q : IsTrue (b <=? e)%nat} {r : IsTrue (e <? n)%nat}
          : SepContractFunX (@vector_subrange n e b _ _ _) :=
          {| sep_contract_logic_variables := ["bv" :: ty.bvec n];
             sep_contract_localstore      := [term_var "bv"];
             sep_contract_precondition    := ⊤;
             sep_contract_result          := "result_vector_subrange";
             sep_contract_postcondition   := ⊤;
          |}.
        #[global] Arguments sep_contract_vector_subrange {n} e b {p q r}.

        Definition CEnvEx : SepContractEnvEx :=
          fun Δ τ fn =>
            match fn with
            | read_ram bytes  => sep_contract_read_ram bytes
            | write_ram bytes => sep_contract_write_ram bytes
            | @within_mmio bytes H => @sep_contract_within_mmio bytes H
            | mmio_read bytes  => sep_contract_mmio_read bytes
            | mmio_write bytes => sep_contract_mmio_write bytes
            | decode          => sep_contract_decode
            | vector_subrange e b => sep_contract_vector_subrange e b
            end.

        Lemma linted_cenvex :
          forall Δ τ (fn : FunX Δ τ),
            Linted (CEnvEx fn).
        Proof.
          intros ? ? []; try constructor.
        Qed.
      End ForeignDef.

      Section LemDef.
        Import RiscvPmpSignature.notations.
        Import RiscvNotations.

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

        Definition lemma_open_ptsto_instr : SepLemma open_ptsto_instr :=
          {| lemma_logic_variables := [paddr :: ty_xlenbits];
             lemma_patterns        := [term_var paddr];
             lemma_precondition    := ⊤;
             lemma_postcondition   := ⊤;
          |}.

        Definition lemma_close_ptsto_instr : SepLemma close_ptsto_instr :=
          {| lemma_logic_variables := [paddr :: ty_xlenbits; w :: ty_word];
             lemma_patterns        := [term_var paddr; term_var w];
             lemma_precondition    := ⊤;
             lemma_postcondition   := ⊤;
          |}.

        Definition lemma_open_pmp_entries : SepLemma open_pmp_entries :=
          {| lemma_logic_variables := ["entries" :: ty.list ty_pmpentry];
             lemma_patterns        := env.nil;
             lemma_precondition    := asn_pmp_entries (term_var "entries");
             lemma_postcondition   := ∃ "cfg0", ∃ "addr0", ∃ "cfg1", ∃ "addr1",
                (pmp0cfg ↦ term_var "cfg0" ∗ pmpaddr0 ↦ term_var "addr0" ∗
                 pmp1cfg ↦ term_var "cfg1" ∗ pmpaddr1 ↦ term_var "addr1" ∗
                 asn_expand_pmpcfg_ent (term_var "cfg0") ∗
                 asn_expand_pmpcfg_ent (term_var "cfg1") ∗
                 term_var "entries" = term_list [(term_var "cfg0" ,ₜ term_var "addr0");
                                                 (term_var "cfg1" ,ₜ term_var "addr1")]);
          |}.

        Definition lemma_close_pmp_entries : SepLemma close_pmp_entries :=
          {| lemma_logic_variables := ["cfg0" :: ty_pmpcfg_ent; "addr0" :: _;
                                       "cfg1" :: ty_pmpcfg_ent; "addr1" :: _];
             lemma_patterns        := env.nil;
             lemma_precondition    :=
               pmp0cfg ↦ term_var "cfg0" ∗ pmpaddr0 ↦ term_var "addr0" ∗
               pmp1cfg ↦ term_var "cfg1" ∗ pmpaddr1 ↦ term_var "addr1";
             lemma_postcondition   :=
               asn_pmp_entries (term_list [(term_var "cfg0" ,ₜ term_var "addr0");
                                           (term_var "cfg1" ,ₜ term_var "addr1")]);
          |}.

        Definition lemma_extract_pmp_ptsto (bytes : nat) : SepLemma (extract_pmp_ptsto bytes) :=
          let Σ := [paddr :: ty_xlenbits; acc :: ty_access_type; "entries" :: ty.list ty_pmpentry; p :: ty_privilege] in
          let bv_bytes : Term Σ _ := term_val ty_xlenbits (Bitvector.bv.of_nat bytes) in
          {| lemma_logic_variables := Σ;
             lemma_patterns        := [term_var paddr];
             lemma_precondition    :=
              let paddr_int : Term _ ty.int := term_unsigned (term_var paddr) in
                asn_pmp_addr_access (term_var "entries") (term_var p)
                ∗ term_val ty.int (Z.of_nat minAddr) <= paddr_int
                ∗ (term_binop bop.plus paddr_int (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_nat maxAddr)
                ∗ asn_pmp_access (term_var paddr) bv_bytes (term_var "entries") (term_var p) (term_var acc);
             lemma_postcondition   :=
                asn_pmp_addr_access_without (term_var paddr) bytes (term_var "entries") (term_var p)
                ∗ ∃ "w", asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]);
          |}.

        Definition lemma_return_pmp_ptsto (bytes : nat) : SepLemma (return_pmp_ptsto bytes) :=
          let Σ := [paddr :: ty_xlenbits; "entries" :: ty.list ty_pmpentry; p :: ty_privilege] in
          let bv_bytes : Term Σ _ := term_val ty_xlenbits (Bitvector.bv.of_nat bytes) in
          {| lemma_logic_variables := Σ;
             lemma_patterns        := [term_var paddr];
             lemma_precondition    :=
               asn_pmp_addr_access_without (term_var paddr) bytes (term_var "entries") (term_var p)
                ∗ ∃ "w", asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]);
             lemma_postcondition   :=
               asn_pmp_addr_access (term_var "entries") (term_var p)
          |}.

        Definition lemma_close_mmio_write (immm : Bitvector.bv.bv 12) (widthh : WordWidth): SepLemma (close_mmio_write immm widthh) :=
          {| lemma_logic_variables := ["paddr" :: ty_xlenbits; "w" :: ty_xlenbits];
             lemma_patterns        := [term_var "paddr"; term_var "w"];
             lemma_precondition    := ⊤;
             lemma_postcondition   := ⊤;
          |}.

        Definition LEnv : LemmaEnv :=
          fun Δ l =>
            match l with
            | open_gprs               => lemma_open_gprs
            | close_gprs              => lemma_close_gprs
            | open_pmp_entries        => lemma_open_pmp_entries
            | close_pmp_entries       => lemma_close_pmp_entries
            | open_ptsto_instr        => lemma_open_ptsto_instr
            | close_ptsto_instr       => lemma_close_ptsto_instr
            | extract_pmp_ptsto bytes => lemma_extract_pmp_ptsto bytes
            | return_pmp_ptsto bytes  => lemma_return_pmp_ptsto bytes
            | close_mmio_write immm widthh => lemma_close_mmio_write immm widthh
            end.

      End LemDef.

  End ContractDefKit.

  End Contracts.

End RiscvPmpSpecification.

Module RiscvPmpExecutor :=
  MakeExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpProgram RiscvPmpSpecification.

Module RiscvPmpShallowExecutor :=
  MakeShallowExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpProgram RiscvPmpSpecification.

Module RiscvPmpValidContracts.
  Import RiscvPmpExecutor.
  Import RiscvPmpShallowExecutor.

  Inductive Fuel : Set :=
  | NoInlining
  | InlineOneLevel.

  Definition fuel_to_nat (f : Fuel) : nat :=
    match f with
    | NoInlining     => 1
    | InlineOneLevel => 2
    end.

  Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContractReflect c (FunDef f)
    | None   => False
    end.

  Definition ValidContractWithFuel {Δ τ} (fuel : Fuel) (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContractReflectWithFuel (fuel_to_nat fuel) c (FunDef f)
    | None   => False
    end.


  Definition ValidContractDebug {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContract c (FunDef f)
    | None => False
    end.

  Ltac symbolic_simpl :=
    apply Symbolic.validcontract_with_erasure_sound;
    compute;
    constructor;
    cbn.

  Section Debug.
    Coercion stm_exp : Exp >-> Stm.
    Local Notation "'use' 'lemma' lem args" := (stm_lemma lem args%env) (at level 10, lem at next level) : exp_scope.
    Local Notation "'use' 'lemma' lem" := (stm_lemma lem env.nil) (at level 10, lem at next level) : exp_scope.

    (* Import RiscvNotations.
     Import RiscvμSailNotations. *)
    Import SymProp.notations.

  End Debug.

  (* TODO: proof with new PMP addressing mode (NA4) *)
  Lemma valid_contract_pmpCheck (bytes : nat) {H : restrict_bytes bytes} : ValidContractDebug (@pmpCheck bytes H).
  Proof.
    destruct H; apply Symbolic.validcontract_with_erasure_sound; vm_compute;
      constructor; cbn; repeat (intros; split; bv_comp); auto 11.
  Qed.

  Lemma valid_contract_step : ValidContract step.
  Proof. reflexivity. Qed.

  Lemma valid_contract_pmpWriteCfgReg (n : nat) {H : (n < 1)%nat} : ValidContract (@pmpWriteCfgReg n H).
  Proof. destruct n; reflexivity. Qed.

  Lemma valid_contract_pmpWriteCfg : ValidContract pmpWriteCfg.
  Proof. reflexivity. Qed.

  Lemma valid_contract_pmpWriteAddr : ValidContract pmpWriteAddr.
  Proof. reflexivity. Qed.

  Lemma valid_contract_init_model : ValidContract init_model.
  Proof. reflexivity. Qed.

  Lemma valid_contract_fetch : ValidContract fetch.
  Proof. reflexivity. Qed.

  Lemma valid_contract_execute : ValidContract execute.
  Proof. reflexivity. Qed.

  Lemma valid_contract_init_sys : ValidContract init_sys.
  Proof. reflexivity. Qed.

  Lemma valid_contract_init_pmp : ValidContract init_pmp.
  Proof. reflexivity. Qed.

  Lemma valid_contract_handle_mem_exception : ValidContract handle_mem_exception.
  Proof. reflexivity. Qed.

  Lemma valid_contract_mem_write_value (bytes : nat) {H : restrict_bytes bytes} : ValidContract (@mem_write_value bytes H).
  Proof. reflexivity. Qed.

  Lemma valid_contract_mem_read (bytes : nat) {H : restrict_bytes bytes} : ValidContract (@mem_read bytes H).
  Proof. reflexivity. Qed.

  Lemma valid_contract_process_load (bytes : nat) {pr : IsTrue (width_constraint bytes)} : ValidContractWithFuel InlineOneLevel (process_load bytes).
  Proof. reflexivity. Qed.

  Lemma valid_contract_checked_mem_read (bytes : nat) {H : restrict_bytes bytes} : ValidContractDebug (@checked_mem_read bytes H).
  Proof. destruct H; symbolic_simpl; eauto. Qed.

  (* TODO: remove? *)
  (* Lemma valid_contract_checked_mem_read_shallow (bytes : nat) : Shallow.ValidContract (sep_contract_checked_mem_read bytes) (fun_checked_mem_read bytes). *)
  (* Proof. *)
  (*   econstructor. *)
  (*   cbv [CPureSpecM.pure *)
  (*          CPureSpecM.bind *)
  (*          CHeapSpecM.bind *)
  (*          CHeapSpecM.bind_right *)
  (*          CHeapSpecM.consume *)
  (*          CHeapSpecM.lift_purem *)
  (*          CHeapSpecM.assert_eq_nenv *)
  (*          CPureSpecM.angelic]. *)
  (*   exists (Z.of_nat bytes). *)
  (*   cbv [inst inst_store inst_env inst_chunk]. *)
  (*   cbv [evals eval]. *)
  (*   compute. *)
  (* Admitted. *)

  (* Lemma valid_contract_checked_mem_read (bytes : nat) : ValidContractDebug (checked_mem_read bytes). *)
  (* Proof with trivial. *)
    (* apply Symbolic.validcontract_with_erasure_sound. *)
    (* compute. *)
    (* constructor. *)
    (* cbn. *)
    (* intros acc paddr p entries Hsub Hacc **. *)
    (* exists acc. split... exists acc. split... split... *)
  (* Admitted. *)

  Lemma valid_contract_checked_mem_write (bytes : nat) {H : restrict_bytes bytes} : ValidContractDebug (@checked_mem_write bytes H).
  Proof. destruct H; symbolic_simpl; eauto. Qed.

  Lemma valid_contract_pmp_mem_read (bytes : nat) {H : restrict_bytes bytes} : ValidContractDebug (@pmp_mem_read bytes H).
  Proof. destruct H; now symbolic_simpl. Qed.

  Lemma valid_contract_pmp_mem_write (bytes : nat) {H : restrict_bytes bytes} : ValidContractDebug (@pmp_mem_write bytes H).
  Proof.
    destruct H; symbolic_simpl;
      intros; (split; intros; [now exists Write|now exists ReadWrite]).
  Qed.

  Lemma valid_contract_pmpCheckRWX : ValidContract pmpCheckRWX.
  Proof. reflexivity. Qed.

  Lemma valid_contract_pmpCheckPerms : ValidContract pmpCheckPerms.
  Proof. reflexivity. Qed.

  Lemma valid_contract_pmpAddrRange : ValidContract pmpAddrRange.
  Proof. reflexivity. Qed.

  Lemma valid_contract_pmpMatchAddr : ValidContractDebug pmpMatchAddr.
  Proof.
    symbolic_simpl.
    intros; split; intros; bv_comp; auto.
    destruct (v + v0 <=ᵘ? v1)%bv eqn:?; bv_comp; auto.
  Qed.

  Lemma valid_contract_pmpMatchEntry : ValidContract pmpMatchEntry.
  Proof. reflexivity. Qed.

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

  Lemma valid_contract_tick_pc : ValidContract tick_pc.
  Proof. reflexivity. Qed.

  Lemma valid_contract_to_bits (l : nat) : ValidContract (to_bits l).
  Proof. reflexivity. Qed.

  Lemma valid_contract_rX : ValidContract rX.
  Proof. reflexivity. Qed.

  Lemma valid_contract_wX : ValidContract wX.
  Proof. reflexivity. Qed.

  (* Lemma valid_contract_abs : ValidContract abs. *)
  (* Proof. reflexivity. Qed. *)

  Lemma valid_contract_within_phys_mem : ValidContractDebug within_phys_mem.
  Proof.
    apply Symbolic.validcontract_with_erasure_sound.
    vm_compute. constructor. cbn. intros.
    lia.
  Qed.

  Lemma valid_contract_execute_RTYPE : ValidContractWithFuel InlineOneLevel execute_RTYPE.
  Proof. reflexivity. Qed.

  Lemma valid_contract_execute_ITYPE : ValidContractWithFuel InlineOneLevel execute_ITYPE.
  Proof. reflexivity. Qed.

  Lemma valid_contract_execute_SHIFTIOP : ValidContractWithFuel InlineOneLevel execute_SHIFTIOP.
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

  Lemma valid_contract_execute_EBREAK : ValidContractDebug execute_EBREAK.
  Proof. now symbolic_simpl. Qed.

  Lemma valid_contract_execute_MRET : ValidContract execute_MRET.
  Proof. reflexivity. Qed.

  Lemma valid_contract_execute_STORE : ValidContract execute_STORE.
  Proof. reflexivity. Qed.

  Lemma valid_contract_execute_LOAD : ValidContract execute_LOAD.
  Proof. reflexivity. Qed.

  Lemma valid_contract_execute_CSR : ValidContract execute_CSR.
  Proof. reflexivity. Qed.

  Lemma valid_contract_execute_MUL : ValidContract execute_MUL.
  Proof. reflexivity. Qed.


  Lemma pmp_check_perms_gives_access :
    forall acc p L0 A0 X0 W0 R0,
      Pmp_check_perms {| L := L0; A := A0; X := X0; W := W0; R := R0 |} acc p ->
      decide_access_pmp_perm acc
                             (pmp_get_perms {| L := L0; A := A0; X := X0; W := W0; R := R0 |} p) = true.
  Proof.
    intros; destruct p, acc, L0, X0, W0, R0;
      simpl; cbv in H; subst; auto.
  Qed.

  Open Scope N_scope.

  Lemma valid_contract : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContract f ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContract in Hvc.
    rewrite Hcenv in Hvc.
    exists 1%nat.
    apply Symbolic.validcontract_reflect_sound.
    apply Hvc.
  Qed.

  Lemma valid_contract_with_fuel : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ) (fuel : Fuel),
      CEnv f = Some c ->
      ValidContractWithFuel fuel f ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros ? ? f c fuel Hcenv Hvc.
    unfold ValidContractWithFuel in Hvc.
    rewrite Hcenv in Hvc.
    exists (fuel_to_nat fuel).
    now apply Symbolic.validcontract_reflect_fuel_sound.
  Qed.

  Lemma valid_contract_debug : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContractDebug f ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContractDebug in Hvc.
    rewrite Hcenv in Hvc.
    exists 1%nat.
    apply Hvc.
  Qed.

  Lemma ValidContracts : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros.
    destruct f.
    - apply (valid_contract _ H valid_contract_rX).
    - apply (valid_contract _ H valid_contract_wX).
    - cbn in H; inversion H.
    - cbn in H; inversion H.
    - cbn in H; inversion H.
    - apply (valid_contract _ H valid_contract_get_arch_pc).
    - apply (valid_contract _ H valid_contract_get_next_pc).
    - apply (valid_contract _ H valid_contract_set_next_pc).
    - apply (valid_contract _ H valid_contract_tick_pc).
    - apply (valid_contract _ H (valid_contract_to_bits l)).
    (* - apply (valid_contract _ H valid_contract_abs). *)
    - apply (valid_contract_debug _ H valid_contract_within_phys_mem).
    - apply (valid_contract _ H (@valid_contract_mem_read bytes H0)).
    - apply (valid_contract_debug _ H (@valid_contract_checked_mem_read bytes H0)).
    - apply (valid_contract_debug _ H (@valid_contract_checked_mem_write bytes H0)).
    - apply (valid_contract_debug _ H (@valid_contract_pmp_mem_read bytes H0)).
    - apply (valid_contract_debug _ H (@valid_contract_pmp_mem_write bytes H0)).
    - apply (valid_contract _ H valid_contract_pmpLocked).
    - apply (valid_contract _ H valid_contract_pmpWriteCfgReg).
    - apply (valid_contract _ H valid_contract_pmpWriteCfg).
    - apply (valid_contract _ H valid_contract_pmpWriteAddr).
    - apply (valid_contract_debug _ H valid_contract_pmpCheck).
    - apply (valid_contract _ H valid_contract_pmpCheckPerms).
    - apply (valid_contract _ H valid_contract_pmpCheckRWX).
    - apply (valid_contract _ H valid_contract_pmpMatchEntry).
    - apply (valid_contract _ H valid_contract_pmpAddrRange).
    - apply (valid_contract_debug _ H valid_contract_pmpMatchAddr).
    - apply (valid_contract_with_fuel _ _ H (@valid_contract_process_load bytes p)).
    - apply (valid_contract _ H (@valid_contract_mem_write_value bytes H0)).
    - cbn in H; inversion H.
    - apply (valid_contract _ H valid_contract_init_model).
    - cbn in H; inversion H.
    - apply (valid_contract _ H valid_contract_step).
    - apply (valid_contract _ H valid_contract_fetch).
    - apply (valid_contract _ H valid_contract_init_sys).
    - apply (valid_contract _ H valid_contract_init_pmp).
    - apply (valid_contract _ H valid_contract_exceptionType_to_bits).
    - apply (valid_contract _ H valid_contract_privLevel_to_bits).
    - apply (valid_contract _ H valid_contract_handle_mem_exception).
    - apply (valid_contract _ H valid_contract_exception_handler).
    - apply (valid_contract _ H valid_contract_exception_delegatee).
    - apply (valid_contract _ H valid_contract_trap_handler).
    - apply (valid_contract _ H valid_contract_prepare_trap_vector).
    - apply (valid_contract _ H valid_contract_tvec_addr).
    - apply (valid_contract _ H valid_contract_handle_illegal).
    - apply (valid_contract _ H valid_contract_check_CSR).
    - apply (valid_contract _ H valid_contract_is_CSR_defined).
    - apply (valid_contract _ H valid_contract_csrAccess).
    - apply (valid_contract _ H valid_contract_csrPriv).
    - apply (valid_contract _ H valid_contract_check_CSR_access).
    - apply (valid_contract _ H valid_contract_readCSR).
    - apply (valid_contract _ H valid_contract_writeCSR).
    - apply (valid_contract _ H valid_contract_execute).
    - apply (valid_contract_with_fuel _ _ H valid_contract_execute_RTYPE).
    - apply (valid_contract_with_fuel _ _ H valid_contract_execute_ITYPE).
    - apply (valid_contract_with_fuel _ _ H valid_contract_execute_SHIFTIOP).
    - apply (valid_contract _ H valid_contract_execute_UTYPE).
    - apply (valid_contract _ H valid_contract_execute_BTYPE).
    - apply (valid_contract _ H valid_contract_execute_RISCV_JAL).
    - apply (valid_contract _ H valid_contract_execute_RISCV_JALR).
    - apply (valid_contract _ H valid_contract_execute_LOAD).
    - apply (valid_contract _ H valid_contract_execute_STORE).
    - apply (valid_contract _ H valid_contract_execute_ECALL).
    - apply (valid_contract_debug _ H valid_contract_execute_EBREAK).
    - apply (valid_contract _ H valid_contract_execute_MRET).
    - apply (valid_contract _ H valid_contract_execute_CSR).
    - apply (valid_contract _ H valid_contract_execute_MUL).
  Qed.
End RiscvPmpValidContracts.
