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
     Program.Tactics
     Strings.String
     ZArith.ZArith
     Classes.EquivDec
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     MinimalCaps.Machine
     MinimalCaps.Sig
     MinimalCaps.Contracts.Notations
     Notations
     Specification
     Shallow.Executor
     Symbolic.Executor
     Symbolic.Solver.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Module Import MinCapsSpecification <: Specification MinCapsBase MinCapsSignature MinCapsProgram.
  Include SpecificationMixin MinCapsBase MinCapsSignature MinCapsProgram.
  Import MinCapsSignature.
  Import MinCapsContractNotations.
  Import Notations.

  Section ContractDefKit.
    Section ContractDef.
      Import ContractNotations.
      (* mach_inv_contract is the contract used for the machine for an
         individual step, as well as for all the execute functions. The contract
         requires ownership over all registers of the machine and gives back
         the ownership. Note that in the postcondition we can end up with either
         a safe pc, or a pc for which the expression relation holds (in the case
         a jump to an enter capability occured). *)
      Definition mach_inv_contract {Δ τ} : SepContract Δ τ :=
        {| sep_contract_logic_variables := sep_contract_logvars Δ [];
           sep_contract_localstore      := create_localstore Δ [];
           sep_contract_precondition    := asn_gprs ∗ asn_pc_correct pc ∗ asn_IH;
           sep_contract_result          := "result_mach_inv";
           sep_contract_postcondition   := asn_gprs ∗ (asn_pc_safe pc ∨ asn_pc_expr pc);
        |}.

      Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
        SepContract Δ τ.

      Definition sep_contract_read_reg : SepContractFun read_reg :=
        {{ asn_gprs }}
          fn read_reg ["rs" :: ty.enum regname] ty.word
        {{ "result_read_reg",
           asn_gprs ∗ 𝒱(term_var "result_read_reg") }}.

      Definition sep_contract_read_reg_cap : SepContractFun read_reg_cap :=
        {{ asn_gprs }}
          fn read_reg_cap ["cs" :: ty.enum regname] ty.cap
        {{ "result_read_reg_cap",
            asn_gprs ∗ asn_match_cap (term_var "result_read_reg_cap") "p" "b" "e" "a"
                                     (𝒱(term_var "result_read_reg_cap")) }}.

      Definition sep_contract_read_reg_num : SepContractFun read_reg_num :=
        {{ asn_gprs }}
          fn read_reg_num ["rs" :: ty.enum regname] ty.int
        {{ "result_read_reg_num",
            asn_gprs ∗ 𝒱(term_var "result_read_reg_num") }}.

      Definition sep_contract_write_reg : SepContractFun write_reg :=
        {{ asn_gprs ∗ 𝒱(term_var "w") }}
          fn write_reg ["rd" :: ty.enum regname; "w" :: ty.word] ty.unit
        {{ "result_write_reg",
            term_var "result_write_reg" = term_val ty.unit tt ∗ asn_gprs }}.

      Definition sep_contract_next_pc : SepContractFun next_pc :=
        {{ pc ↦ term_var "opc" }}
          fn next_pc [] ty.cap
        {{ "result_next_pc",
            pc ↦ term_var "opc" ∗
            asn_match_cap (term_var "opc") "p" "b" "e" "a"
              (term_var "result_next_pc" = (term_var "p", term_var "b", term_var "e",
                                             (term_var "a") + (term_val ty.addr 1))) }}
        with ["opc" :: ty.cap].

      Definition sep_contract_update_pc : SepContractFun update_pc :=
        {{ pc ↦ term_var "opc" ∗ 𝒱(term_var "opc") ∗ asn_correctPC (term_var "opc") }}
          fn update_pc [] ty.unit
        {{ "result_update_pc",
            term_var "result_update_pc" = term_val ty.unit tt ∗
            asn.exist "npc" ty.cap (pc ↦ term_var "npc" ∗ 𝒱(term_var "npc")) }}
        with ["opc" :: ty.cap].

      Definition sep_contract_update_pc_perm : SepContractFun update_pc_perm :=
        {{ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a") }}
          fn update_pc_perm [("p", "b", "e", "a") :: ty.cap] ty.cap
        {{ "result_update_pc_perm",
          asn.exist "p'" ty.perm
                    (let c : Term _ _  := (term_var "p", term_var "b", term_var "e", term_var "a") in
                     let c' : Term _ _ := (term_var "p'", term_var "b", term_var "e", term_var "a") in
                     term_var "result_update_pc_perm" = c' ∗
                     term_var "p'" ≠ₚ term_val ty.perm E ∗
                     asn.match_enum permission (term_var "p")
                       (fun p => match p with
                                 | E => asn_expr c'
                                 | _ => 𝒱(c') ∗ c = c'
                                 end)) }}.

      Definition sep_contract_is_correct_pc : SepContractFun is_correct_pc :=
        {{ ⊤ }}
          fn is_correct_pc ["c" :: ty.cap] ty.bool
        {{ "result_is_correct_pc",
            if:  term_var "result_is_correct_pc"
            then asn_correctPC (term_var "c")
            else ⊤ }}.

      Definition sep_contract_is_perm : SepContractFun is_perm :=
        {{ ⊤ }}
          fn is_perm ["p" :: ty.perm; "p'" :: ty.perm] ty.bool
        {{ "result_is_perm",
            if:  term_var "result_is_perm"
            then term_var "p" = term_var "p'"
            else term_var "p" ≠ₚ term_var "p'" }}.

      Definition sep_contract_add_pc : SepContractFun add_pc :=
        {{ pc ↦ term_var "opc" ∗ 𝒱(term_var "opc")
           ∗ asn_correctPC (term_var "opc") }}
          fn add_pc ["offset" :: ty.int] ty.unit
        {{ "result_add_pc",
            term_var "result_add_pc" = term_val ty.unit tt ∗
            asn.exist "npc" ty.cap (pc ↦ term_var "npc" ∗ 𝒱(term_var "npc")) }}
        with ["opc" :: ty.cap].

      Definition sep_contract_read_mem : SepContractFun read_mem :=
        {{ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a")
           ∗ term_val ty.perm R <=ₚ term_var "p" }}
          fn read_mem [("p", "b", "e", "a") :: ty.cap] ty.memval
        {{ "result_read_mem", 𝒱(term_var "result_read_mem") }}.

      Definition sep_contract_write_mem : SepContractFun write_mem :=
        {{ 𝒱(term_var "v")
           ∗ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a")
           ∗ term_val ty.perm RW <=ₚ term_var "p" }}
          fn write_mem [("p", "b", "e", "a") :: ty.cap; "v" :: ty.memval] ty.unit
        {{ "result_write_mem",
            term_var "result_write_mem" = term_val ty.unit tt
            ∗ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a") }}.

      Definition sep_contract_read_allowed : SepContractFun read_allowed :=
        {{ ⊤ }}
          fn read_allowed ["p" :: ty.perm] ty.bool
        {{ "result_read_allowed",
            if: term_var "result_read_allowed"
            then term_val ty.perm R <=ₚ term_var "p"
            else ⊤ }}.

      Definition sep_contract_write_allowed : SepContractFun write_allowed :=
        {{ ⊤ }}
          fn write_allowed ["p" :: ty.perm] ty.bool
        {{ "result_write_allowed",
            if: term_var "result_write_allowed"
            then term_val ty.perm RW <=ₚ term_var "p"
            else ⊤ }}.

      Definition sep_contract_within_bounds : SepContractFun within_bounds :=
        {{ ⊤ }}
          fn within_bounds [("p", "b", "e", "a") :: ty.cap] ty.bool
        {{ "result_within_bounds",
            term_var "result_within_bounds" =
            term_binop bop.and
              (term_binop (bop.relop bop.le) (term_var "b") (term_var "a"))
              (term_binop (bop.relop bop.le) (term_var "a") (term_var "e")) }}.

      Definition sep_contract_exec_jalr_cap : SepContractFun exec_jalr_cap :=
        mach_inv_contract.

      Definition sep_contract_exec_cjalr : SepContractFun exec_cjalr :=
        mach_inv_contract.

      Definition sep_contract_exec_cjal : SepContractFun exec_cjal :=
        mach_inv_contract.

      Definition sep_contract_exec_bne : SepContractFun exec_bne :=
        mach_inv_contract.

      Definition sep_contract_exec_cmove : SepContractFun exec_cmove :=
        mach_inv_contract.

      Definition sep_contract_exec_ld : SepContractFun exec_ld :=
        mach_inv_contract.

      Definition sep_contract_exec_sd : SepContractFun exec_sd :=
        mach_inv_contract.

      Definition sep_contract_exec_cincoffset : SepContractFun exec_cincoffset :=
        mach_inv_contract.

      Definition sep_contract_exec_candperm : SepContractFun exec_candperm :=
        mach_inv_contract.

      Definition sep_contract_exec_csetbounds : SepContractFun exec_csetbounds :=
        mach_inv_contract.

      Definition sep_contract_exec_csetboundsimm : SepContractFun exec_csetboundsimm :=
        mach_inv_contract.

      Definition sep_contract_exec_addi : SepContractFun exec_addi :=
        mach_inv_contract.

      Definition sep_contract_exec_add : SepContractFun exec_add :=
        mach_inv_contract.

      Definition sep_contract_exec_sub : SepContractFun exec_sub :=
        mach_inv_contract.

      Definition sep_contract_exec_slt : SepContractFun exec_slt :=
        mach_inv_contract.

      Definition sep_contract_exec_slti : SepContractFun exec_slti :=
        mach_inv_contract.

      Definition sep_contract_exec_sltu : SepContractFun exec_sltu :=
        mach_inv_contract.

      Definition sep_contract_exec_sltiu : SepContractFun exec_sltiu :=
        mach_inv_contract.

      Definition sep_contract_perm_to_bits : SepContractFun perm_to_bits :=
        {{ ⊤ }} fn perm_to_bits ["p" :: ty.perm] ty.int {{ "_", ⊤ }}.

      Definition sep_contract_perm_from_bits : SepContractFun perm_from_bits :=
        {{ ⊤ }} fn perm_from_bits ["i" :: ty.int] ty.perm {{ "_", ⊤ }}.

      Definition sep_contract_and_perm : SepContractFun and_perm :=
        {{ ⊤ }}
          fn and_perm ["p1" :: ty.perm; "p2" :: ty.perm] ty.perm
        {{ "result_and_perm",
            term_var "result_and_perm" <=ₚ term_var "p1" ∗
            term_var "result_and_perm" <=ₚ term_var "p2" }}.

      Definition sep_contract_abs : SepContractFun abs :=
        {{ ⊤ }} fn abs ["i" :: ty.int] ty.int {{ "_", ⊤ }}.

      Definition sep_contract_is_not_zero : SepContractFun is_not_zero :=
        {{ ⊤ }}
          fn is_not_zero ["i" :: ty.int] ty.bool
        {{ "result_is_not_zero",
            if: term_var "result_is_not_zero"
            then term_var "i" ≠ term_val ty.int 0%Z
            else term_var "i" = term_val ty.int 0 }}.

      Definition sep_contract_can_incr_cursor : SepContractFun can_incr_cursor :=
        {{ ⊤ }}
          fn can_incr_cursor [("p", "b", "e", "a") :: ty.cap; "imm" :: ty.int] ty.bool
        {{ "result_can_incr_cursor",
            if: term_var "result_can_incr_cursor"
            then
              term_var "p" ≠ₚ term_val ty.perm E
              ∨
              (term_var "imm" = term_val ty.int 0%Z ∗ term_var "a" = term_binop bop.plus (term_var "a") (term_var "imm"))
            else ⊤ }}.

      Definition sep_contract_is_sub_perm : SepContractFun is_sub_perm :=
        {{ ⊤ }}
          fn is_sub_perm ["p" :: ty.perm; "p'" :: ty.perm] ty.bool
        {{ "result_is_sub_perm",
            if: term_var "result_is_sub_perm"
            then term_var "p" <=ₚ term_var "p'"
            else ⊤ }}.

      Definition sep_contract_is_within_range : SepContractFun is_within_range :=
        {{ ⊤ }}
          fn is_within_range ["b'" :: ty.addr; "e'" :: ty.addr; "b" :: ty.addr; "e" :: ty.addr] ty.bool
        {{ "result_is_within_range",
            term_var "result_is_within_range" =
            term_binop bop.and
              (term_binop (bop.relop bop.le) (term_var "b") (term_var "b'"))
              (term_binop (bop.relop bop.le) (term_var "e'") (term_var "e")) }}.
      
      Definition sep_contract_exec_cgettag : SepContractFun exec_cgettag :=
        mach_inv_contract.

      Definition sep_contract_exec_cgetperm : SepContractFun exec_cgetperm :=
        mach_inv_contract.

      Definition sep_contract_exec_cgetbase : SepContractFun exec_cgetbase :=
        mach_inv_contract.

      Definition sep_contract_exec_cgetlen : SepContractFun exec_cgetlen :=
        mach_inv_contract.

      Definition sep_contract_exec_cgetaddr : SepContractFun exec_cgetaddr :=
        mach_inv_contract.

      Definition sep_contract_exec_fail : SepContractFun exec_fail :=
        mach_inv_contract.

      Definition sep_contract_exec_ret : SepContractFun exec_ret :=
        mach_inv_contract.

      Definition sep_contract_exec_instr : SepContractFun exec_instr :=
        mach_inv_contract.

      Definition sep_contract_exec : SepContractFun exec :=
        mach_inv_contract.

      Definition sep_contract_step : SepContractFun step :=
        mach_inv_contract.

      Definition CEnv : SepContractEnv :=
        fun Δ τ f =>
          match f with
          | read_allowed           => Some sep_contract_read_allowed
          | write_allowed          => Some sep_contract_write_allowed
          | within_bounds          => Some sep_contract_within_bounds
          | read_reg               => Some sep_contract_read_reg
          | read_reg_cap           => Some sep_contract_read_reg_cap
          | read_reg_num           => Some sep_contract_read_reg_num
          | write_reg              => Some sep_contract_write_reg
          | next_pc                => Some sep_contract_next_pc
          | add_pc                 => Some sep_contract_add_pc
          | update_pc              => Some sep_contract_update_pc
          | update_pc_perm         => Some sep_contract_update_pc_perm
          | is_correct_pc          => Some sep_contract_is_correct_pc
          | MinCapsProgram.is_perm => Some sep_contract_is_perm
          | read_mem               => Some sep_contract_read_mem
          | write_mem              => Some sep_contract_write_mem
          | perm_to_bits           => Some sep_contract_perm_to_bits
          | perm_from_bits         => Some sep_contract_perm_from_bits
          | and_perm               => Some sep_contract_and_perm
          | is_sub_perm            => Some sep_contract_is_sub_perm
          | is_within_range        => Some sep_contract_is_within_range
          | abs                    => Some sep_contract_abs
          | is_not_zero            => Some sep_contract_is_not_zero
          | can_incr_cursor        => Some sep_contract_can_incr_cursor
          | exec_jalr_cap          => Some sep_contract_exec_jalr_cap
          | exec_cjalr             => Some sep_contract_exec_cjalr
          | exec_cjal              => Some sep_contract_exec_cjal
          | exec_bne               => Some sep_contract_exec_bne
          | exec_cmove             => Some sep_contract_exec_cmove
          | exec_ld                => Some sep_contract_exec_ld
          | exec_sd                => Some sep_contract_exec_sd
          | exec_cincoffset        => Some sep_contract_exec_cincoffset
          | exec_candperm          => Some sep_contract_exec_candperm
          | exec_csetbounds        => Some sep_contract_exec_csetbounds
          | exec_csetboundsimm     => Some sep_contract_exec_csetboundsimm
          | exec_addi              => Some sep_contract_exec_addi
          | exec_add               => Some sep_contract_exec_add
          | exec_sub               => Some sep_contract_exec_sub
          | exec_slt               => Some sep_contract_exec_slt
          | exec_slti              => Some sep_contract_exec_slti
          | exec_sltu              => Some sep_contract_exec_sltu
          | exec_sltiu             => Some sep_contract_exec_slti
          | exec_cgettag           => Some sep_contract_exec_cgettag
          | exec_cgetperm          => Some sep_contract_exec_cgetperm
          | exec_cgetbase          => Some sep_contract_exec_cgetbase
          | exec_cgetlen           => Some sep_contract_exec_cgetlen
          | exec_cgetaddr          => Some sep_contract_exec_cgetaddr
          | exec_fail              => Some sep_contract_exec_fail
          | exec_ret               => Some sep_contract_exec_ret
          | exec_instr             => Some sep_contract_exec_instr
          | exec                   => Some sep_contract_exec
          | step                   => Some sep_contract_step
          | loop                   => None
          end.

      Lemma linted_cenv :
        forall Δ τ (f : Fun Δ τ),
          match CEnv f with
          | Some c => Linted c
          | None   => True
          end.
      Proof. intros ? ? []; try constructor. Qed.
    End ContractDef.

    Section LemDef.
      Import LemmaNotations.

      Definition SepLemma {Δ} (f : Lem Δ) : Type :=
        KatamaranLem Δ.

      Definition lemma_correctPC_subperm_R : SepLemma correctPC_subperm_R :=
        {{ asn_correctPC (term_var "p", term_var "b", term_var "e", term_var "a") }}
          lem correctPC_subperm_R [("p", "b", "e", "a") :: ty.cap]
        {{ term_val ty.perm R <=ₚ term_var "p" }}.

      Definition lemma_subperm_not_E : SepLemma subperm_not_E :=
        {{ (term_var "p" = term_val ty.perm R ∨ term_var "p" = term_val ty.perm RW) ∗
             term_var "p" <=ₚ term_var "p'" }}
          lem subperm_not_E ["p" :: ty.perm; "p'" :: ty.perm]
        {{ term_var "p'" ≠ₚ term_val ty.perm E }}.

      Definition lemma_safe_to_execute : SepLemma safe_to_execute :=
        {{ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a")
           ∗ term_var "p" = term_val ty.perm E }}
          lem safe_to_execute [("p", "b", "e", "a") :: ty.cap]
        {{ let p : Term _ (type (_ :: _)) := term_val ty.perm R in
           asn_expr (p, term_var "b", term_var "e", term_var "a") }}.

      Definition lemma_open_gprs : SepLemma open_gprs :=
        {{ asn_gprs }} lem open_gprs [] {{ asn_regs_ptsto_safe }}.

      Definition lemma_close_gprs : SepLemma close_gprs :=
        {{ asn_regs_ptsto_safe }} lem close_gprs [] {{ asn_gprs }}.

      Definition lemma_safe_move_cursor : SepLemma safe_move_cursor :=
        {{ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a")
           ∗ (term_var "p" ≠ₚ term_val ty.perm E ∨ term_var "a" = term_var "a'") }}
          lem safe_move_cursor [("p", "b", "e", "a'") :: ty.cap; ("p", "b", "e", "a") :: ty.cap]
        {{ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a")
           ∗ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a'") }}.

      Definition lemma_safe_sub_perm : SepLemma safe_sub_perm :=
        {{ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a")
           ∗ term_var "p'" <=ₚ term_var "p" ∗ asn_IH }}
          lem safe_sub_perm [("p'", "b", "e", "a") :: ty.cap; ("p", "b", "e", "a") :: ty.cap]
        {{ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a")
           ∗ 𝒱(term_var "p'", term_var "b", term_var "e", term_var "a") }}.

      Definition lemma_safe_within_range : SepLemma safe_within_range :=
        {{ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a")
           ∗ term_var "p" ≠ₚ term_val ty.perm E ∗ asn_IH
           ∗  asn.formula
                (formula_bool
                  (term_binop bop.and
                     (term_binop (bop.relop bop.le) (term_var "b") (term_var "b'"))
                     (term_binop (bop.relop bop.le) (term_var "e'") (term_var "e")))) }}
          lem safe_within_range [("p", "b'", "e'", "a'") :: ty.cap; ("p", "b", "e", "a") :: ty.cap]
        {{ 𝒱(term_var "p", term_var "b", term_var "e", term_var "a")
           ∗ 𝒱(term_var "p", term_var "b'", term_var "e'", term_var "a") }}. 

      Definition lemma_int_safe : SepLemma int_safe :=
        {{ ⊤ }} lem int_safe ["i" :: ty.int] {{ 𝒱(term_var "i") }}.

      Definition LEnv : LemmaEnv :=
        fun Δ l =>
          match l with
          | open_gprs           => lemma_open_gprs
          | close_gprs          => lemma_close_gprs
          | safe_move_cursor    => lemma_safe_move_cursor
          | safe_sub_perm       => lemma_safe_sub_perm
          | safe_within_range   => lemma_safe_within_range
          | int_safe            => lemma_int_safe
          | correctPC_subperm_R => lemma_correctPC_subperm_R
          | subperm_not_E       => lemma_subperm_not_E
          | safe_to_execute     => lemma_safe_to_execute
          end.

    End LemDef.

    Section ForeignDef.
      Import ForeignNotations.

      Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
        SepContract Δ τ.

      Definition sep_contract_rM : SepContractFunX rM :=
        {{ asn_csafe_angelic (term_record capability
                                  [term_var "p";
                                   term_var "b";
                                   term_var "e";
                                   term_var "address"]) ∗
             term_val ty.perm R <=ₚ term_var "p" ∗
             asn_within_bounds (term_var "address") (term_var "b") (term_var "e") }}
          fn rM ["address" :: ty.addr] ty.memval
        {{ "rM_result", 𝒱(term_var "rM_result") }}
        with ["p" :: ty.perm; "b" :: ty.addr; "e" :: ty.addr].

      Definition sep_contract_wM : SepContractFunX wM :=
        {{ 𝒱(term_var "new_value")
           ∗ asn_csafe_angelic (term_record capability
                                  [term_var "p";
                                   term_var "b";
                                   term_var "e";
                                   term_var "address"])
           ∗ term_val ty.perm RW <=ₚ term_var "p"
           ∗ asn_within_bounds (term_var "address") (term_var "b") (term_var "e") }}
          fn wM ["address" :: ty.addr; "new_value" :: ty.memval] ty.unit
        {{ "wM_result", term_var "wM_result" = term_val ty.unit tt }}
        with ["p" :: ty.perm; "b" :: ty.addr; "e" :: ty.addr].

      Definition sep_contract_dI : SepContractFunX dI :=
        {{ ⊤ }} fn dI ["code" :: ty.int] ty.instr {{ "_", ⊤ }}.

      Definition CEnvEx : SepContractEnvEx :=
        fun Δ τ f =>
          match f with
          | rM => sep_contract_rM
          | wM => sep_contract_wM
          | dI => sep_contract_dI
          end.
    End ForeignDef.

  Lemma linted_cenvex :
    forall Δ τ (f : FunX Δ τ),
      Linted (CEnvEx f).
  Proof.
    intros ? ? []; try constructor.
  Qed.

End ContractDefKit.

End MinCapsSpecification.
