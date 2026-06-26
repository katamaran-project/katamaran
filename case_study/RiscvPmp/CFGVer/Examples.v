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
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.Verifier
     RiscvPmp.Machine
     RiscvPmp.Sig.
From Katamaran Require
     RiscvPmp.CFGVer.Verifier.

Import RiscvPmpProgram.
Import RiscvPmpBlockVerifExecutor.
Import Assembly.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

From iris.base_logic Require Import lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.
(* From Katamaran Require Import RiscvPmp.LoopVerification. *)

(* ======================================================================== *)
(* CFGVer/Examples.v                                                        *)
(*                                                                           *)
(* This is the main file for the CFGVer case study.  It has four parts:     *)
(*                                                                           *)
(*  1. WithAsnNotations (in Module Examples): contracts and programs.        *)
(*     Defines CFGVerifierContract, ValidCFGVerifierContract, gen_contract,  *)
(*     and all concrete program contracts (jmp_fwd, countdown, swap, etc.)  *)
(*                                                                           *)
(*  2. Pure infrastructure (after WithAsnNotations):                         *)
(*     Step relations (RiscVStep, RiscVNStepsWithExitCond, etc.),            *)
(*     the Iris loop predicate (myWP2_loop), and adequacy lemmas.            *)
(*                                                                           *)
(*  3. AdequacyTools section: connects the CFGVer VC checker to Iris.        *)
(*     Extracts ptsto_instrs from raw memory, proves sound_exec_cfg_addr_myWP2, *)
(*     sound_sblock_verification_condition_myWP2, etc.                       *)
(*                                                                           *)
(*  4. Wiring and end-to-end lemmas:                                         *)
(*     cfg_instrs_verified → cfg_instrs_safe → cfg_instrs_contract          *)
(*     → cfg_instrs_endToEnd / _strong / _with_memory                       *)
(*     Concrete programs: jmp_fwd_endToEnd_cfg, countdown_endToEnd, etc.    *)
(*                                                                           *)
(* Security property: constant-time noninterference.                         *)
(*   Two worlds (γ1, μ1) and (γ2, μ2) start with the same public registers  *)
(*   and the same program, but may differ on private data.  The end-to-end   *)
(*   lemmas conclude leakage_trace μ1' = leakage_trace μ2'.                  *)
(*                                                                           *)
(* Simplification opportunity:                                               *)
(*   Both worlds must start at init_addr = 0.  The hard-coded 0 shows up in *)
(*   ptsto_instrs (SyncVal bv.zero), instrsMemory, and ImplPre.  Generalising *)
(*   to an arbitrary start address would make cfg_instrs_endToEnd cleaner.   *)
(* ======================================================================== *)

Module Examples.
  Import RiscvPmpBlockVerifExecutor.
  Import Assembly.
  Import RiscvPmp.Sig.
  Import iris.proofmode.tactics.
  Local Notation "x + y" := (term_binop bop.bvadd x y) : exp_scope.
  Local Notation "x - y" := (term_binop bop.bvsub x y) : exp_scope.
  Local Notation "a <=ᵘ b" := (term_binop (bop.relop bop.bvule) a b) : exp_scope.
  Local Notation "a = b" := (term_binop (bop.relop bop.eq) a b) : exp_scope.
  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
  (* Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])). *)

  Definition X0 : RegIdx := bv.zero.
  Definition X1 : RegIdx := bv.one.
  Definition X2 : RegIdx := bv.of_nat 2.
  Definition X3 : RegIdx := bv.of_nat 3.
  Definition X4 : RegIdx := bv.of_nat 4.

  (* ======================================================================== *)
  (* WithAsnNotations: symbolic contracts and program definitions             *)
  (*                                                                          *)
  (* Everything in this section is a Katamaran-level (pre-Iris) definition.  *)
  (* After `End WithAsnNotations`, the infrastructure drops to the Rocq/Iris  *)
  (* level (RegStore, Memory, iProp).                                          *)
  (* ======================================================================== *)
  Section WithAsnNotations.
    Import asn.notations.

    (* minimal_pre asserts that we start executing at address 0 in Machine mode.
       We choose an arbitrary list for the pmp entries (pmp is not used in these
       examples). *)
    Definition minimal_pre {Σ} : Assertion Σ :=
      (* asn.exist "_" _ (nextpc ↦ term_var "_")
      ∗ *)cur_privilege ↦ term_val ty_privilege Machine
      (* ∗ asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero) ; *)
      (*                               (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)]) *) ∗
            asn.chunk (chunk_user inv_leakage [env])
    .

    Definition extend_to_minimal_pre {Σ} (P : Assertion Σ) : Assertion Σ :=
      P ∗ minimal_pre.

    (* CFG verifier contract: analog of BlockVerifierContract but for the CFG
       verifier, which requires an explicit exit condition and fuel bound.
       Uses Katamaran.RiscvPmp.CFGVer.Verifier.sblock_verification_condition.
       Postconditions are not exposed: SHeapSpec has no leakcheck, so the final
       heap state is unconstrained and any leftover resources are silently dropped. *)
    Definition CFG_VC_triple {Σ}
      (P  : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
      (instrs  : list AST)
      (ec : bv xlenbits -> bool)
      (fl : nat) :=
      Katamaran.RiscvPmp.CFGVer.Verifier.sblock_verification_condition (Σ := Σ)
        (extend_to_minimal_pre P) instrs ec fl
        (asn.formula (formula_bool (term_val ty.bool true))) wnil.

    Definition Valid_CFG_VC {Σ}
      (P  : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
      (instrs  : list AST)
      (ec : bv xlenbits -> bool)
      (fl : nat) :=
      safeE (postprocess (CFG_VC_triple P instrs ec fl)).

    (* CFGVerifierContract: the top-level contract bundle for CFGVer.
       Fields:
         cfg_precondition  — symbolic PRE assertion over Σ ▻ "a" (start PC)
         cfg_instrs        — the program as a list of decoded instructions
         cfg_exitCond      — the halting criterion (Boolean function on PC)
         cfg_fuel          — step bound for sexec_cfg_addr
       No postcondition field: SHeapSpec has no leakcheck, and any Iris
       resources left in the heap after the final step are silently dropped
       (affine Iris).  The only observable output is the leakage trace.
       Notation: {{ P }} instrs @cfg[ ec, fl ]                               *)
    Record CFGVerifierContract {Σ} :=
      MkCFGVerifierContract
      { cfg_precondition  : Assertion (Σ ▻ "a" ∷ ty_xlenbits)
      ; cfg_instrs        : list AST
      ; cfg_exitCond      : bv xlenbits -> bool
      ; cfg_fuel          : nat
      }.

    Definition cfg_map {Σ A} (c : @CFGVerifierContract Σ)
      (f : Assertion (Σ ▻ "a" ∷ ty_xlenbits) -> list AST ->
           (bv xlenbits -> bool) -> nat -> A) : A :=
      match c with
      | {| cfg_precondition := pre; cfg_instrs := i;
           cfg_exitCond := ec; cfg_fuel := fl |} => f pre i ec fl
      end.

    Definition ValidCFGVerifierContract {Σ} (c : @CFGVerifierContract Σ) : Prop :=
      cfg_map c Valid_CFG_VC.

    Definition DebugCFGVerifierContract {Σ} (c : @CFGVerifierContract Σ) : Prop :=
      cfg_map c (fun P i ec fl =>
        VerificationCondition (postprocess (CFG_VC_triple P i ec fl))).

    Local Notation "'{{' P '}}' i '@cfg[' ec ',' fl ']'" :=
      (@MkCFGVerifierContract [ctx] P%asn i ec fl)
      (at level 90).
    Local Notation "'{{' P '}}' i '@cfg[' ec ',' fl ']' 'with' logvars" :=
      (@MkCFGVerifierContract logvars P%asn i ec fl)
      (at level 90).

    Local Ltac solve_bv :=
      repeat match goal with
        | |- context[bv.add ?x (@bv.mk ?n 0 I)] =>
            fold (@bv.zero n)
        | |- context[bv.add ?x bv.zero] =>
            rewrite bv.add_zero_r
        end.

    Local Ltac solve_vc :=
      vm_compute; constructor; cbn; intros; repeat split; try solve_bv; auto.

    (* Definition with_regidx {Σ} (r : RegIdx) (P : Reg ty_xlenbits -> Assertion Σ) : Assertion Σ := *)
    (*   match reg_convert r with *)
    (*   | None     => ⊤ *)
    (*   | Some reg => P reg *)
    (*   end. *)

    (* Notation "r '↦ᵣ' v" := (with_regidx r (fun reg => asn.chunk (chunk_ptsreg reg v))) (at level 70) : asn_scope. *)
    Definition asn_regidx_pts {Σ} (r : RegIdx) (v : Term Σ ty_xlenbits) : Assertion Σ :=
      match reg_convert r with
      | None     => ⊤
      | Some reg => asn.chunk (chunk_ptsreg reg v)
      end.
    Arguments asn_regidx_pts : simpl never.

    Notation "r '↦ᵣ' v" := (asn_regidx_pts r v) (at level 70) : asn_scope.

    Ltac unfold_asn_regidx_pts :=
      match goal with
      | |- context[asn.interpret (asn_regidx_pts ?r ?v) ?ι] =>
          change (asn.interpret (asn_regidx_pts ?r ?v) ?ι) with
          (lptsreg r (inst_term v ι))
      end.
    Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70).

    Definition asn_init_pc {Σ} : Assertion (Σ ▻ "a" :: ty_xlenbits) :=
      term_var "a" = term_val ty_xlenbits bv.zero.

    Definition asn_pc_eq {Σ} (t : Term (Σ ▻ "a" :: ty_xlenbits) ty_xlenbits) : Assertion (Σ ▻ "a" :: ty_xlenbits) :=
      term_var "a" = t.

    Local Notation term_pc_val := (term_var "a").

    Definition asn_next_pc_eq {Σ} (t : Term (Σ ▻ "an" :: ty_xlenbits) ty_xlenbits) : Assertion (Σ ▻ "an" :: ty_xlenbits) :=
      term_var "an" = t.

    Import SymProp.notations.
    Import Erasure.notations.

    Definition pcOutOfInstrs_exitCond (instrs : list AST) : bv xlenbits -> bool :=
      fun v => bv.ugeb v (bv.of_N (4 * N.of_nat (length instrs))).

    (* ------------------------------------------------------------------ *)
    (* Contract generator                                                   *)
    (*                                                                      *)
    (* reg_spec: (register, is_public)                                      *)
    (*   is_public = true  → secLeak assertion added (register is SyncVal) *)
    (*                                                                      *)
    (* Memory specs are a TODO (no public/private memory in endToEnd yet). *)
    (* ------------------------------------------------------------------ *)

    Definition reg_spec : Type := RegIdx * bool.

    Definition gen_reg_asn {Σ} (s : reg_spec) : Assertion Σ :=
      let '(r, is_pub) := s in
      asn.exist "v" ty_xlenbits
        (if is_pub
         then r ↦ᵣ term_var "v" ∗ secLeakvar "v"
         else r ↦ᵣ term_var "v").

    Definition gen_pre {Σ} (specs : list reg_spec) : Assertion Σ :=
      List.fold_right (fun s acc => gen_reg_asn s ∗ acc) ⊤ specs.

    Definition gen_contract
        (specs : list reg_spec)
        (instrs : list AST)
        (ec : bv xlenbits -> bool)
        (fl : nat)
        : CFGVerifierContract :=
      @MkCFGVerifierContract [ctx] (asn_init_pc ∗ gen_pre specs) instrs ec fl.


    Definition mv_zero_ex : CFGVerifierContract :=
      {{ asn_init_pc ∗ ∃ "v", X1 ↦ᵣ term_var "v" }}
        [MV X1 X0]
      @cfg[ pcOutOfInstrs_exitCond [MV X1 X0] , 3 ].

    Example valid_mv_zero_ex : ValidCFGVerifierContract mv_zero_ex.
    Proof. vm_compute. solve_vc. Qed.

    Definition mv_same_reg_ex : CFGVerifierContract :=
      {{ asn_init_pc ∗ X1 ↦ᵣ term_var "x" }}
        [MV X1 X1]
      @cfg[ pcOutOfInstrs_exitCond [MV X1 X1] , 3 ]
      with ["x" :: ty_xlenbits].

    Example valid_mv_same_reg_ex : ValidCFGVerifierContract mv_same_reg_ex.
    Proof. vm_compute. solve_vc. Qed.

    Definition mv_ex : CFGVerifierContract :=
      {{ asn_init_pc ∗ X1 ↦ᵣ term_var "x" ∗ X2 ↦ᵣ term_var "y" }}
        [MV X1 X2]
      @cfg[ pcOutOfInstrs_exitCond [MV X1 X2] , 3 ]
      with ["x" :: ty_xlenbits; "y" :: ty_xlenbits].

    Example valid_mv_ex : ValidCFGVerifierContract mv_ex.
    Proof. vm_compute. solve_vc. Qed.

    Definition swap_cfg_contract : CFGVerifierContract :=
      {{ asn_init_pc ∗ X1 ↦ᵣ term_var "x" ∗ X2 ↦ᵣ term_var "y" ∗
           ∃ "v", X3 ↦ᵣ term_var "v" }}
        [MV X3 X2; MV X2 X1; MV X1 X3]
      @cfg[ pcOutOfInstrs_exitCond [MV X3 X2; MV X2 X1; MV X1 X3] , 5 ]
      with ["x" :: ty_xlenbits; "y" :: ty_xlenbits].

    Lemma valid_swap_cfg_contract : ValidCFGVerifierContract swap_cfg_contract.
    Proof. vm_compute. solve_vc. Qed.

    (* TODO: move into Spec.v *)
    Definition JAL (rd : RegIdx) (imm : bv 21) : AST :=
      RISCV_JAL imm rd.
    Definition NOP : AST := MV X0 X0.
    Definition LW (rd rs : RegIdx) (imm : bv 12) : AST :=
      LOAD imm rs rd false WORD.
    Definition SW (rs2 rs1 : RegIdx) (imm : bv 12) : AST :=
      STORE imm rs2 rs1 WORD.

    Definition true_offset : bv 13 := bv.of_N 8.

    Import TermNotations.

    (* TODO: would rather write jump_if_zero (true_offset : bv 13) ... *)
    (* Jumps to `true_offset` when the value of X1 is equal to zero. The
         default offset allows one instruction between this block and the true
         block. X1 must be a public register (secLeak). *)
    Definition jump_if_zero_cfg_contract : CFGVerifierContract :=
      {{ asn_init_pc ∗ X1 ↦ᵣ term_var "x1" ∗
           secLeakvar "x1" }}
        [BEQ X1 X0 true_offset]
      @cfg[ pcOutOfInstrs_exitCond [BEQ X1 X0 true_offset] , 3 ]
      with ["x1" :: ty_xlenbits].

    Lemma valid_jump_if_zero_cfg_contract :
      ValidCFGVerifierContract jump_if_zero_cfg_contract.
    Proof. vm_compute. solve_vc. Qed.

    (* Unconditional forward jump: jumps 8 bytes ahead (2 instruction widths).
       The CFG verifier handles this correctly by following the actual PC. *)
    Definition jmp_offset : bv 21 := bv.of_N 8.

    (* CFGVer verification of jmp_fwd: the CFG verifier follows the actual PC
       after each instruction, so it correctly handles the forward jump that
       BlockVer cannot. Exit condition: PC ≥ 8 (execution left the block). *)
    Definition jmp_fwd_exitCond : bv xlenbits -> bool :=
      fun v => bv.ugeb v (bv.of_N 8).

    Definition jmp_fwd_cfg_contract : CFGVerifierContract :=
      {{ asn_init_pc }}
        [JAL X0 jmp_offset; NOP]
      @cfg[ jmp_fwd_exitCond , 5 ].

    Lemma valid_jmp_fwd_cfg_contract : ValidCFGVerifierContract jmp_fwd_cfg_contract.
    Proof. vm_compute. solve_vc. Qed.

    (* gen_contract version: precondition is asn_init_pc ∗ ⊤ (no register specs) *)
    Definition jmp_fwd_cfg_contract_gen : CFGVerifierContract :=
      gen_contract [] [JAL X0 jmp_offset; NOP] jmp_fwd_exitCond 5.

    Lemma valid_jmp_fwd_cfg_contract_gen :
      ValidCFGVerifierContract jmp_fwd_cfg_contract_gen.
    Proof. vm_compute. solve_vc. Qed.

    (* -4 in 13-bit two's complement: branches jump back 4 bytes (one instruction) *)
    Definition back_offset : bv 13 := bv.of_N 8188.

    (* -1 in 12-bit two's complement: ADDI immediate for decrement *)
    Definition neg_one_12 : bv 12 := bv.of_N 4095.

    (* Countdown program: X1 starts at 2 and counts down to 0.
       addr 0: ADDI X1 X1 (-1)  -- decrement X1
       addr 4: BNE X1 X0 (-4)   -- if X1 != 0, jump back to addr 0
       addr 8: exit (exitCond satisfied)
       Concrete execution: X1=2→1, BNE taken; X1=1→0, BNE not taken; exit.
       Backward branch actually fires, demonstrating CFGVer handles loops. *)
    Definition countdown_exitCond : bv xlenbits -> bool :=
      fun v => bv.ugeb v (bv.of_N 8).

    Definition countdown_cfg_contract : CFGVerifierContract :=
      {{ asn_init_pc ∗ X1 ↦ᵣ term_val ty_xlenbits (bv.of_N 2) }}
        [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset]
      @cfg[ countdown_exitCond , 5 ].

    Lemma valid_countdown_cfg_contract :
      ValidCFGVerifierContract countdown_cfg_contract.
    Proof. vm_compute. solve_vc. Qed.

    Definition set_X2_to_42 : CFGVerifierContract :=
      {{ asn_init_pc ∗ ∃ "_", X2 ↦ᵣ term_var "_" }}
        [ADDI X2 X0 (bv.of_N 42)]
      @cfg[ pcOutOfInstrs_exitCond [ADDI X2 X0 (bv.of_N 42)] , 3 ].

    Lemma valid_set_X2_to_42 : ValidCFGVerifierContract set_X2_to_42.
    Proof. vm_compute. solve_vc. Qed.

    (* Memory countdown: 4 instructions + a data word at address 16.
       addr  0: LOAD  imm=16 rs1=X0 rd=X1  -- X1 := mem[X0+16] = mem[16]
       addr  4: ADDI  X1 X1 (-1)            -- X1 := X1 - 1
       addr  8: STORE imm=16 rs2=X1 rs1=X0  -- mem[16] := X1
       addr 12: BNE   X1 X0 (-12)           -- if X1 ≠ 0, jump back to addr 0
       Data:    mem[16] = 2 initially.
       Two iterations: 2→1 (branch), 1→0 (fall-through); exit at pc=16. *)
    Definition back_12_offset : bv 13 := bv.of_N 8180.

    Definition countdown_mem_exitCond : bv xlenbits -> bool :=
      fun v => bv.ugeb v (bv.of_N 16).

    Definition countdown_mem_instrs : list AST :=
      [ LOAD (bv.of_N 16) X0 X1 false WORD
      ; ADDI X1 X1 neg_one_12
      ; STORE (bv.of_N 16) X1 X0 WORD
      ; BNE X1 X0 back_12_offset ].

    Definition countdown_mem_cfg_contract : CFGVerifierContract :=
      {{ asn_init_pc ∗ (∃ "_", X1 ↦ᵣ term_var "_") ∗
         (term_val ty_xlenbits (bv.of_N 16) ↦ₘ
          term_val ty_xlenbits (bv.of_N 2)) }}
        countdown_mem_instrs
      @cfg[ countdown_mem_exitCond , 10 ].

    Lemma valid_countdown_mem_cfg_contract :
      ValidCFGVerifierContract countdown_mem_cfg_contract.
    Proof. vm_compute. solve_vc. Qed.

  End WithAsnNotations.

  (* Public registers for a spec list: registers whose is_pub flag is true.
     Defined outside WithAsnNotations to avoid notation-scope interference. *)
  (* ======================================================================== *)
  (* Public register and memory infrastructure (outside WithAsnNotations)     *)
  (*                                                                          *)
  (* After the symbolic contracts are defined, the infrastructure for the     *)
  (* binary noninterference proof lives at the Rocq/Iris level.               *)
  (*                                                                          *)
  (* Public registers: `declare_public_registers γ1 γ2 list` asserts that    *)
  (*   both worlds agree on every register in `list`.                         *)
  (*   `something_registers HpubReg` converts between interp_gprs_with_registers  *)
  (*   (all registers as NonSyncVal) and interp_gprs_with_public_registers    *)
  (*   (public as SyncVal, private as NonSyncVal).                            *)
  (*   This is the key step for applying gen_implpre in ImplPre proofs.       *)
  (*                                                                          *)
  (* gen_public_regs: extracts the `is_public = true` entries from a         *)
  (*   reg_spec list and converts RegIdx to the sigma-typed Reg.              *)
  (* ======================================================================== *)
  Definition gen_public_regs (specs : list reg_spec) : list {x : Ty & 𝑹𝑬𝑮 x} :=
    base.omap (fun (spec : reg_spec) =>
      let '(r, pub) := spec in
      if pub then option_map (@existT Ty 𝑹𝑬𝑮 ty_xlenbits) (reg_convert r)
      else None) specs.

  Import IrisInstanceBinary.
  Import RiscvPmpIrisInstance2.
  Import RiscvPmpSemantics.
  Import RiscvPmpIrisAdeqParams2.
  Import SmallStepNotations.
  Import IrisModelBinary.RiscvPmpIrisBase2.

  From iris.bi Require big_op.
  From iris.algebra Require big_op.
  From iris.program_logic Require weakestpre.
  Import iris.algebra.excl.
  Import iris.algebra.gmap.

  Definition asn_regs_ptsto_with_registers γ1 γ2 : Assertion ctx.nil :=
    asn_and_regs
      (fun r => asn.chunk (chunk_ptsreg r (term_relval _ (NonSyncVal (read_register γ1 r) (read_register γ2 r))))).

  Lemma gprs_with_registers_equiv `{sailGS2 Σ} γ1 γ2 :
      interp_gprs_with_registers γ1 γ2 ⊣⊢
        asn.interpret (asn_regs_ptsto_with_registers γ1 γ2) env.nil.
  Proof.
    unfold interp_gprs_with_registers.
    rewrite big_sepS_list_to_set; [|apply bv.finite.nodup_enum].
    cbn. iSplit.
    - iIntros "(_ & H)"; repeat iDestruct "H" as "($ & H)".
    - iIntros "H"; iSplitR; auto.
      repeat iDestruct "H" as "($ & H)"; iFrame.
  Qed.

    Definition mem_has_word (μ : Memory) (a : Val ty_word) (w : Val ty_word) : Prop :=
      exists v0 v1 v2 v3, List.map (memory_ram μ) (bv.seqBv a 4) = [v0; v1; v2; v3]%list /\ bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil))) = w.

    (* byte order correct? *)
    Definition mem_has_instr (μ : Memory) (a : Val ty_word) w (instr : AST) : Prop :=
      mem_has_word μ a w /\ pure_decode w = inr instr.

    Fixpoint mem_has_instrs (μ : Memory) (a : Val ty_word) ws (instrs : list AST) : Prop :=
      match ws , instrs with
      | cons w ws , cons inst instrs => mem_has_instr μ a w inst /\ mem_has_instrs μ (bv.add (bv.of_N 4) a) ws instrs
      | nil , nil => True
      | _ , _ => False
      end.

    (* Word extraction: assemble 4 consecutive bytes into a 32-bit word *)
    Definition get_word (μ : Memory) (a : Val ty_word) : Val ty_word :=
      bv.app (memory_ram μ a)
        (bv.app (memory_ram μ (bv.add bv.one a))
          (bv.app (memory_ram μ (bv.add (bv.of_N 2) a))
            (bv.app (memory_ram μ (bv.add (bv.of_N 3) a)) bv.nil))).

    (* mem_spec: a word address paired with a public/private flag *)
    Definition mem_spec : Type := Val ty_word * bool.

    (* declare_public_memory: the two worlds agree on the word value at
       every address listed as public *)
    Definition declare_public_memory (μ1 μ2 : Memory)
        (public_addrs : list (Val ty_word)) : Prop :=
      Forall (fun a => get_word μ1 a = get_word μ2 a) public_addrs.

    (* gen_public_addrs: filter a mem_spec list to keep only public addresses *)
    Definition gen_public_addrs (specs : list mem_spec) : list (Val ty_word) :=
      base.omap (fun s : mem_spec => let '(a, pub) := s in
        if pub then Some a else None) specs.

    Definition filter_AnnotInstr_AST (l : list AnnotInstr) := base.omap extract_AST l.

    Definition init_addr     : N := 0.

    (* ====================================================================== *)
    (* Execution step relations                                               *)
    (*                                                                        *)
    (* RiscVStep γ1 μ1 γ2 μ2: one outer loop iteration.                      *)
    (*   Defined as: ⟨γ1, μ1, [env], fun_step⟩ --->* ⟨γ2, μ2, [env], tt⟩  *)
    (*   i.e., fun_step runs to completion (fetch → decode → execute → nextpc) *)
    (*                                                                        *)
    (* RiscVStepN: same but with an explicit micro-step count (needed for     *)
    (*   matching the fuel parameter of step_fupdN_soundness_gen).            *)
    (*                                                                        *)
    (* RiscVStepsWithExitCond exitCond γ1 μ1 γ2 μ2:                          *)
    (*   Written ⟨γ1, μ1⟩ -(exitCond)->* ⟨γ2, μ2⟩.                         *)
    (*   Reflexive-transitive closure of RiscVStep, under the constraint that *)
    (*   exitCond does NOT hold at the PC of each intermediate state.         *)
    (*   The halting state (γ2, μ2) satisfies exitCond at its PC.             *)
    (*                                                                        *)
    (* RiscVNStepsWithExitCond: as above but with an outer step count n.      *)
    (*   n = number of outer loop iterations (not micro-steps).               *)
    (*                                                                        *)
    (* RiscVlistNStepsWithExitCond: internal variant where step counts are a  *)
    (*   list of micro-step counts (one per outer iteration).  Used by        *)
    (*   step_fupdN_soundness_gen which needs the sum list_sum_plus_one l.    *)
    (*   nsteps_to_lsteps converts NSteps to listNSteps.                      *)
    (*                                                                        *)
    (* RiscVNSteps / RiscVlistNSteps: unconditional (no exitCond) versions.   *)
    (* ====================================================================== *)
    Definition RiscVStep (γ1 : RegStore) (μ1 : Memory) :
      forall (γ2 : RegStore) (μ2 : Memory), Prop :=
      fun γ2 μ2 => ⟨ γ1, μ1, [env], fun_step ⟩ --->* ⟨ γ2, μ2, [env], stm_val ty.unit tt ⟩.

    Definition RiscVStepN (γ1 : RegStore) (μ1 : Memory) :
      forall (γ2 : RegStore) (μ2 : Memory) n, Prop :=
      fun γ2 μ2 n => ⟨ γ1, μ1, [env], fun_step ⟩ -{ n }-> ⟨ γ2, μ2, [env], stm_val ty.unit tt ⟩.

    Inductive RiscVStepsWithExitCond (exitCond : Val ty_xlenbits -> Prop) (γ1 : RegStore) (μ1 : Memory) : RegStore -> Memory -> Prop :=
    | riscVStepWithExitCond_refl : RiscVStepsWithExitCond exitCond γ1 μ1 γ1 μ1
    | riscVStepWithExitCond_trans {γ2 γ3 : RegStore} {μ2 μ3 : Memory} :
      ~ exitCond (read_register γ1 pc) ->
      RiscVStep γ1 μ1 γ2 μ2 ->
      RiscVStepsWithExitCond exitCond  γ2 μ2 γ3 μ3 ->
      RiscVStepsWithExitCond exitCond  γ1 μ1 γ3 μ3.
    Notation "⟨ γ1 , μ1 ⟩ -( exitCond )->* ⟨ γ2 , μ2 ⟩" := (@RiscVStepsWithExitCond exitCond γ1 μ1 γ2 μ2)
                                                             (at level 75, only parsing, right associativity).

    Inductive RiscVNStepsWithExitCond  (exitCond : Val ty_xlenbits -> Prop) (γ1 : RegStore) (μ1 : Memory) : RegStore -> Memory -> nat -> Prop :=
    | riscVNStepWithExitCond_refl : RiscVNStepsWithExitCond exitCond γ1 μ1 γ1 μ1 0
    | riscVNStepWithExitCond_trans {n} {γ2 γ3 : RegStore} {μ2 μ3 : Memory} :
      ~ exitCond (read_register γ1 pc) ->
      RiscVStep γ1 μ1 γ2 μ2 ->
      RiscVNStepsWithExitCond exitCond  γ2 μ2 γ3 μ3 n ->
      RiscVNStepsWithExitCond exitCond  γ1 μ1 γ3 μ3 (S n)
    .
    Notation "⟨ γ1 , μ1 ⟩ -( exitCond , n )->* ⟨ γ2 , μ2 ⟩" := (@RiscVNStepsWithExitCond exitCond γ1 μ1 γ2 μ2 n)
                                                             (at level 75, only parsing, right associativity).

    Inductive RiscVlistNStepsWithExitCond  (exitCond : Val ty_xlenbits -> Prop) (γ1 : RegStore) (μ1 : Memory) : RegStore -> Memory -> list nat -> Prop :=
    | riscVlistNStepWithExitCond_refl : RiscVlistNStepsWithExitCond exitCond γ1 μ1 γ1 μ1 []
    | riscVlistNStepWithExitCond_trans {n} {l} {γ2 γ3 : RegStore} {μ2 μ3 : Memory} :
      ~ exitCond (read_register γ1 pc) ->
      RiscVStepN γ1 μ1 γ2 μ2 n ->
      RiscVlistNStepsWithExitCond exitCond  γ2 μ2 γ3 μ3 l ->
      RiscVlistNStepsWithExitCond exitCond  γ1 μ1 γ3 μ3 (n :: l)
    .
    Notation "⟨ γ1 , μ1 ⟩ -l( exitCond , n )->* ⟨ γ2 , μ2 ⟩" := (@RiscVlistNStepsWithExitCond exitCond γ1 μ1 γ2 μ2 n)
                                                                 (at level 75, only parsing, right associativity).

    Inductive RiscVNSteps (γ1 : RegStore) (μ1 : Memory) : RegStore -> Memory -> nat -> Prop :=
    | riscVNSteps_refl : RiscVNSteps γ1 μ1 γ1 μ1 0
    | riscVNSteps_trans {n} {γ2 γ3 : RegStore} {μ2 μ3 : Memory} :
      RiscVStep γ1 μ1 γ2 μ2 ->
      RiscVNSteps  γ2 μ2 γ3 μ3 n ->
      RiscVNSteps  γ1 μ1 γ3 μ3 (S n)
    .
    Notation "⟨ γ1 , μ1 ⟩ -( n )->* ⟨ γ2 , μ2 ⟩" := (@RiscVNSteps γ1 μ1 γ2 μ2 n)
                                                                  (at level 75, only parsing, right associativity).

    Inductive RiscVlistNSteps (γ1 : RegStore) (μ1 : Memory) : RegStore -> Memory -> list nat -> Prop :=
    | riscVlistNSteps_refl : RiscVlistNSteps γ1 μ1 γ1 μ1 []
    | riscVlistNSteps_trans {n} {l} {γ2 γ3 : RegStore} {μ2 μ3 : Memory} :
      RiscVStepN γ1 μ1 γ2 μ2 n ->
      RiscVlistNSteps  γ2 μ2 γ3 μ3 l ->
      RiscVlistNSteps  γ1 μ1 γ3 μ3 (n :: l)
    .
    Notation "⟨ γ1 , μ1 ⟩ -l( l )->* ⟨ γ2 , μ2 ⟩" := (@RiscVlistNSteps γ1 μ1 γ2 μ2 l)
                                                      (at level 75, only parsing, right associativity).

    (* ====================================================================== *)
    (* myWP2_loop: the Iris binary weakest-precondition loop fixpoint         *)
    (*                                                                        *)
    (* myWp2 is an alias for iProp Σ (the type of binary WP propositions).   *)
    (*                                                                        *)
    (* myWP2_loop_fix ExitCond wp: the one-step unfolding of the loop.       *)
    (*   = ExitCond ∨ semWP2 fun_step fun_step                               *)
    (*       (λ v1 δ1 v2 δ2 => match v1, v2 with                             *)
    (*                          | inr _, inr _ => True                        *)
    (*                          | inl _, inl _ => ▷ wp                        *)
    (*                          | _, _ => False end)                          *)
    (*   Left disjunct: both worlds have already exited (ExitCond holds).    *)
    (*   Right disjunct: run one outer loop step and recurse.  The ▷ guard   *)
    (*   is the contractiveness witness for the Iris fixpoint.                *)
    (*   `inr` = stm_fail (abnormal termination), never occurs in practice.  *)
    (*   `inl` = stm_val (normal return), i.e., one outer step completed.    *)
    (*                                                                        *)
    (* myWP2_loop ExitCond = fixpoint (myWP2_loop_fix ExitCond)              *)
    (*   The fixpoint exists by myWP2_loop_fix_Contractive.                   *)
    (*                                                                        *)
    (* Key lemmas:                                                            *)
    (*   fixpoint_myWP2_loop_eq: myWP2_loop ≡ myWP2_loop_fix (myWP2_loop)   *)
    (*   exitCondImpliesMyWP2_loop: ExitCond ⊢ myWP2_loop ExitCond          *)
    (*                                                                        *)
    (* exitCond_WP2_loop ec := myWP2_loop (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜ec v⌝)  *)
    (*   This is the standard ExitCond for CFGVer programs.  The SyncVal     *)
    (*   ensures both worlds exit on the same PC value (which is critical     *)
    (*   for the leakage-trace argument).                                     *)
    (*                                                                        *)
    (* Difference from BlockVer.Verifier.WP2_loop:                           *)
    (*   WP2_loop is the PLAIN infinite loop (no ExitCond).  It is used by   *)
    (*   semTripleCFG and sound_exec_cfg_addr in Verifier.v.                  *)
    (*   myWP2_loop ExitCond is the CONDITIONAL loop defined here.            *)
    (*   The bridge is sound_exec_cfg_addr_myWP2 in AdequacyTools, which     *)
    (*   proves that cexec_cfg_addr implies myWP2_loop (not WP2_loop).        *)
    (* ====================================================================== *)
    Definition myWp2 `{sailGS2 Σ} :=
        iProp Σ.

    Definition myWP2_loop_fix `{sailGS2 Σ} (ExitCond : iProp Σ) (wp : myWp2) :
      myWp2 :=
      (ExitCond ∨
        semWP2 env.nil env.nil (FunDef step) (FunDef step)
          (fun v1 _ v2 _ =>
             match v1 , v2 with
             | inr _ , inr _ => True
             | inl v1 , inl v2 => ▷ wp
             | _ , _ => False
             end
          )%I)%I.
    (* 4 empty arguments, because the return valueas are unit and the CStoreVals are empty *)
  
  Global Instance myWP2_loop_fix_Contractive `{sailGS2 Σ} (ExitCond : iProp Σ) :
    Contractive (myWP2_loop_fix ExitCond).
  Proof.
    rewrite /myWP2_loop_fix /= => n wp wp' Hwp.
    do 7 (f_contractive || f_equiv).
    unfold myWp2 in *.
    destruct a1; auto.
    f_contractive. apply Hwp.
  Qed.

  Definition myWP2_loop `{sailGS2 Σ} (ExitCond : iProp Σ) : myWp2 :=
    fixpoint (myWP2_loop_fix ExitCond).

  Lemma fixpoint_myWP2_loop_fix_eq `{sailGS2 Σ} (ExitCond : iProp Σ) :
    fixpoint (myWP2_loop_fix ExitCond) ≡ myWP2_loop_fix ExitCond (myWP2_loop ExitCond).
  Proof. exact: (fixpoint_unfold (myWP2_loop_fix ExitCond)). Qed.

  Lemma fixpoint_myWP2_loop_eq `{sailGS2 Σ} (ExitCond : iProp Σ) :
    myWP2_loop ExitCond ≡ myWP2_loop_fix ExitCond (myWP2_loop ExitCond).
  Proof. unfold myWP2_loop. rewrite {1}fixpoint_myWP2_loop_fix_eq. unfold myWP2_loop. done.
  Qed.

  Lemma exitCondImpliesMyWP2_loop `{sailGS2 Σ} (ExitCond : iProp Σ) :
    ExitCond ⊢ myWP2_loop ExitCond.
  Proof.
    iIntros "EC". rewrite fixpoint_myWP2_loop_eq. unfold myWP2_loop_fix. iLeft. done.
  Qed.

  Definition pcOutOfInstrs (start : Val ty_word) (instrs : list AST) (pc : Val ty_xlenbits) : Prop :=
      bv.ult pc start \/ bv.uge pc (start + bv.of_N (4 * N.of_nat (length instrs))).

  Definition pcBehindInstrs (start : Val ty_word) (instrs : list AST) (pc : Val ty_xlenbits) : Prop :=
    pc  = (start + bv_instrsize * bv.of_nat (length instrs))%bv.

  Add Ring BitVector : (bv.ring_theory 32).
  Definition pcBehindInstrs_app (start : Val ty_word) (instr : AST) (instrs : list AST) (pc : Val ty_xlenbits) : pcBehindInstrs start (instr :: instrs) pc <-> pcBehindInstrs (start + bv_instrsize)%bv instrs pc.
  Proof.
    unfold pcBehindInstrs.
    split; intro H; rewrite H;
      cbn; rewrite bv.of_nat_S; ring.
  Qed.

    Import IrisModel.RiscvPmpIrisBase.

    Lemma reg2_change `{sailGS2 Σ} {γ1 γ2 γ1' γ2'} :
      own_regstore2 γ1 γ2 ∗ regs_inv2 γ1' γ2' ⊢
        ⌜ read_register γ1 pc = read_register γ1' pc /\ read_register γ2 pc = read_register γ2' pc ⌝.
    Proof.
      iIntros "(HownRegstore & Hinv)".
      unfold own_regstore2; cbn.
      iDestruct "HownRegstore" as "(Hpc & _)".
      iPoseProof (reg_valid2 with "Hinv Hpc") as "(%eq1 & %eq2)".
      cbn in *. rewrite eq1 eq2. done.
    Qed.

    Definition list_sum_plus_one (l : list nat) :=
      foldr (fun a b => a + 1 + b) 0 l.

    Lemma list_sum_plus_one_app : ∀ l1 l2 : list nat, list_sum_plus_one (l1 ++ l2) = list_sum_plus_one l1 + list_sum_plus_one l2.
    Proof.
      unfold list_sum_plus_one.
      induction l1.
      - auto.
      - cbn in *. intro l2. rewrite IHl1. induction l2.
        + lia.
        + cbn. lia.
    Qed.

    Definition memory_in_sync (μ1 μ2 : Memory) (la : list Addr) :=
      Forall (fun a => (memory_ram μ1) a = (memory_ram μ2) a) la.

    Lemma mem_sync_app μ1 μ2 a la1 :
      memory_in_sync μ1 μ2 (a :: la1) <-> (memory_ram μ1) a = (memory_ram μ2) a /\ memory_in_sync μ1 μ2 la1.
    Proof.
      unfold memory_in_sync.
      split.
      - intro H. by inversion H.
      - intros (h & H). by constructor.
    Qed.

        Lemma create_resources Σ {sG' : subG memΣ2 Σ} {sG'' : subG sailΣ2 Σ} (Hinv : invGS Σ) γ1 γ2 μ1 μ2 :
      ⊢ |==>
        ∃ regs1 regs2 memG, let sG := @SailGS2 Σ Hinv (SailRegGS2 (SailRegGS (@reg_pre_inG2_left _ (@subG_sailGpreS _ _)) regs1) (SailRegGS (@reg_pre_inG2_right _ (@subG_sailGpreS _ sG'')) regs2)) memG in
           mem_inv2 (@sailGS2_memGS Σ sG) μ1 μ2 ∗ mem_res2 μ1 μ2 ∗
             @regs_inv2 _ (@sailGS2_regGS2 Σ sG) γ1 γ2 ∗ @own_regstore2 _ sG γ1 γ2.
      Proof.
        iMod (own_alloc ((● RegStore_to_map γ1 ⋅ ◯ RegStore_to_map γ1 ) : regUR)) as (regs1) "[Hregsown1 Hregsinv1]".
    { apply auth_both_valid.
      intuition.
      apply RegStore_to_map_valid. }
    iMod (own_alloc ((● RegStore_to_map γ2 ⋅ ◯ RegStore_to_map γ2 ) : regUR)) as (regs2) "[Hregsown2 Hregsinv2]".
    { apply auth_both_valid.
      intuition.
      apply RegStore_to_map_valid. }
    pose proof (memΣ_GpreS2 (Σ := Σ) _) as mGS.
    iMod (mem_inv_init2 (gHP := mGS) μ1 μ2) as (memG) "[Hmem Rmem]".
    pose (sG := @SailGS2 Σ Hinv (SailRegGS2 (SailRegGS (@reg_pre_inG2_left _ (@subG_sailGpreS _ _)) regs1) (SailRegGS (@reg_pre_inG2_right _ (@subG_sailGpreS _ sG'')) regs2)) memG).
    iAssert (regs_inv2 γ1 γ2) with "[Hregsown1 Hregsown2]" as "Hregs".
    { iSplitL "Hregsown1";
      by iApply own_RegStore_to_regs_inv.
    }
    iAssert (own_regstore2 γ1 γ2) with "[Hregsinv1 Hregsinv2]" as "Rregs".
    { iApply RiscvPmpIrisInstance2.own_RegStore_to_map_reg_pointsTos.
      apply finite.NoDup_enum.
      iSplitR "Hregsinv2"; iAssumption.
    }
    iModIntro. iExists regs1, regs2, memG. iFrame "Hmem Rmem Hregs Rregs".
      Qed.

  (*   Lemma adequacy_gen_RiscVNStepsExitCond l exitCond {γ11 γ12 γ21 γ22} {μ11 μ12 μ21 μ22} *)
  (*   (φ : Prop) : *)
  (*   ⟨ γ11, μ11 ⟩ -l( exitCond , l )->* ⟨ γ12, μ12 ⟩ -> *)
  (*   ⟨ γ21, μ21 ⟩ -l( exitCond , l )->* ⟨ γ22, μ22 ⟩ -> *)
  (*   (forall `{sailGS2 Σ}, *)
  (*       mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢ *)
  (*         |={⊤}=> myWP2_loop *)
  (*                   (∃ a, pc ↦ᵣ a ∗ *)
  (*                      ⌜ exitCond (ty.projLeft a) ∨ exitCond (ty.projRight a) ⌝) *)
  (*       ∗ (mem_inv2 _ μ12 μ22 ={⊤,∅}=∗ ⌜φ⌝) *)
  (*   )%I -> φ. *)
  (* Proof. *)
  (*   intros Heval1 Heval2 Hwp. *)
  (*   refine (uPred.pure_soundness _ *)
  (*             (step_fupdN_soundness_gen (Σ := sailΣ2) _ HasLc (list_sum_plus_one l) (list_sum_plus_one l) _)). *)
  (*   iIntros (Hinv) "Hcred'". *)
  (*   iMod (create_resources Hinv γ11 γ21 μ11 μ21) as (regs1 regs2 memG) "(Hmem & Rmem & Hregs & Rregs)". *)
  (*   pose (sG := @SailGS2 sailΣ2 Hinv (SailRegGS2 (SailRegGS (@reg_pre_inG2_left _ (@subG_sailGpreS _ _)) regs1) (SailRegGS (@reg_pre_inG2_right _ (@subG_sailGpreS _ _)) regs2)) memG). *)
  (*   specialize (Hwp _ sG). *)
  (*   iPoseProof (Hwp with "[$Rmem $Rregs]") as "Hwp2". *)
  (*   clear Hwp. *)
  (*   iStopProof. *)
  (*   revert Heval1 Heval2. *)
  (*   revert γ11 μ11 γ21 μ21. *)
  (*   induction l; iIntros (γ11 μ11 γ21 μ21 Heval1 Heval2) "(Hcred & Hmem & Hregs & Hwp2)". *)
  (*   - inversion Heval1. inversion Heval2. subst. *)
  (*     iMod "Hwp2" as "[_ Hcont]". *)
  (*     iMod ("Hcont" with "Hmem") as "%Hφ". *)
  (*     cbn. done. *)
  (*   - inversion Heval1 as [ | ? ? γ1 ? μ1 ? nEC1 Hstep1 Hevaln1]. clear Heval1. *)
  (*     inversion Heval2 as [ | ? ? γ2 ? μ2 ? nEC2 Hstep2 Hevaln2]. clear Heval2. subst. *)
  (*     specialize (IHl _ _ _ _ Hevaln1 Hevaln2). *)
  (*     rewrite fixpoint_myWP2_loop_eq. *)
  (*     unfold myWP2_loop_fix. *)
  (*     iMod "Hwp2" as "([H | Hwp2] & Hφ)". *)
  (*     + iDestruct "H" as (a') "(Hpc & %ECs)". *)
  (*       unfold reg_pointsTo2. *)
  (*       iPoseProof (reg_valid2 with "[$Hregs] [$Hpc]") as "(%eq1 & %eq2)". *)
  (*       rewrite eq1 in nEC1. rewrite eq2 in nEC2. tauto. *)
  (*     + iPoseProof (semWP2_preservation Hstep1 Hstep2 with "[$Hmem $Hregs]") as "Hwp". *)
  (*       iSpecialize ("Hwp" with "Hwp2"). *)
  (*       iMod "Hwp". *)
  (*       change (list_sum_plus_one (a :: l)) with (a + 1 + list_sum_plus_one l). *)
  (*       iAssert (|={∅}▷=>^a |={∅}=>  |={∅}▷=> |={∅}▷=>^(list_sum_plus_one l) ⌜φ⌝)%I with "[-]" as "H"; last first. *)
  (*       { do 2 rewrite step_fupdN_add. destruct a. done. by iApply step_fupdN_S_fupd. } *)
  (*       iApply (step_fupdN_wand with "Hwp"). *)
  (*       iIntros ">(Hmem & Hregs & Hwp)". *)
  (*       rewrite semWP2_val. *)
  (*       iMod "Hwp" as "Hwp". *)
  (*       rewrite (into_sep_lc_add (a + 1) (list_sum_plus_one l)). *)
  (*       rewrite (into_sep_lc_add a 1). *)
  (*       iDestruct "Hcred" as "[[Hcreda Hcred1] Hcredl]". *)
  (*       iMod (lc_fupd_elim_later with "Hcred1 Hwp") as "Hwp". *)
  (*       now iMod (IHl with "[$Hmem $Hcredl $Hregs $Hwp $Hφ]") as "IHl". *)
  (* Qed. *)

  From Equations Require Import Equations.

  Lemma nsteps_to_lsteps {γ γ' : RegStore} {μ μ' : Memory} ExitCond n :
    ⟨ γ, μ ⟩ -( ExitCond , n )->* ⟨ γ', μ' ⟩ ->
    ∃ l, length l = n ∧
           ⟨ γ, μ ⟩ -l( ExitCond , l )->* ⟨ γ', μ' ⟩.
  Proof.
    revert γ μ.
    induction n.
    - intros γ μ nsteps. exists []. inversion nsteps. split; auto. constructor.
    - intros γ μ nsteps. dependent elimination nsteps.
      destruct (IHn γ2 μ2 r0) as [l Hl].
      destruct (steps_to_nsteps r) as [n Hn].
      exists (n :: l).
      destruct Hl as [Hlen Hl].
      cbn. split.
      + by rewrite Hlen.
      + econstructor; eauto.
  Qed.

    (* Lemma semWP2_lockstep `{sailGS2 Σ} {s1 s2} *)
    (*   {γ1 μ1 δ1 γ1' μ1' n1} *)
    (*   {γ2 μ2 δ2 γ2' μ2' n2} *)
    (*   {Q} *)
    (*   (Hsteps1 : NSteps γ1 μ1 δ1 s1 γ1' μ1' [env] (stm_val ty.unit ()) n1) *)
    (*   (Hsteps2 : NSteps γ2 μ2 δ2 s2 γ2' μ2' [env] (stm_val ty.unit ()) n2) : *)
    (*   mem_inv2 _ μ1 μ2 ∗ *)
    (*     regs_inv2 γ1 γ2 ∗ *)
    (*     semWP2 δ1 δ2 s1 s2 Q ⊢ *)
    (*     |={⊤,∅}=> |={∅}▷=>^n1 ⌜n1 = n2⌝. *)
    (* Proof. *)
    (*   revert n2 s1 s2 γ1 γ1' δ1 μ1 μ1' γ2 γ2' δ2 μ2 μ2' Hsteps1 Hsteps2 Q. *)
    (*   induction n1. *)
    (*   - intros n2 s1 s2 γ1 γ1' δ1 μ1 μ1' γ2 γ2' δ2 μ2 μ2' Hsteps1 Hsteps2 Q. *)
    (*     iIntros "(Hmem & Hregs & Hwp)". *)
    (*     inversion Hsteps1. subst. *)
    (*     inversion Hsteps2; subst; auto. *)
    (*     + cbn. iApply fupd_mask_intro; first set_solver. iIntros "Hclose". by iFrame. *)
    (*     + rewrite semWP2_unfold. cbn. *)
    (*       destruct s2; cbn; iMod "Hwp"; auto. *)
    (*       all: inversion H0. *)
    (*   - intros n2 s1 s2 γ1 γ1' δ1 μ1 μ1' γ2 γ2' δ2 μ2 μ2' Hsteps1 Hsteps2 Q. *)
    (*     iIntros "(Hmem & Hregs & Hwp)". *)
    (*     inversion Hsteps1. subst. inversion Hsteps2; subst. *)
    (*     { rewrite semWP2_unfold. cbn. *)
    (*       destruct s1; cbn; iMod "Hwp"; auto. *)
    (*       all: inversion H1. *)
    (*     } *)
    (*     iPoseProof (semWP2_step H1 H0 with "[$Hmem $Hregs $Hwp]") as "Hwp". *)
    (*     iMod "Hwp". iModIntro. *)
    (*     replace (S n1) with (1 + n1); auto. *)
    (*     rewrite step_fupdN_add. *)
    (*     iMod "Hwp". do 2 iModIntro. iMod "Hwp". iMod "Hwp" as "(Hregs & Hmem & Hwp)". *)
    (*     replace (1 + n1) with (S n1); auto. *)
    (*     specialize (IHn1 n s0 s3 γ0 γ1' δ0 μ0 μ1' γ3 γ2' δ3 μ3 μ2' H6 H2 Q). *)
    (*     iMod (IHn1 with "[$Hmem $Hregs $Hwp]") as "IH". *)
    (*     iModIntro. iApply (step_fupdN_mono with "IH"). *)
    (*     iStartProof. *)
    (*     by iIntros "<-". *)
    (* Qed. *)

    (* semWP2_preservation': two-sided step preservation for myWP2_loop.
       Given NSteps for world 1 and Steps for world 2 (both to stm_val tt),
       and given mem_inv2 + regs_inv2 (resource invariants) and a semWP2
       hypothesis, yields: after n later-steps, we have the new resource
       invariants and the continued semWP2.
       NOTE: Both worlds' execution traces are given as input here (two-sided).
       The one-sided variant (semWP2_preservation_fwd') derives world-2's trace
       existentially using can_step.  This two-sided version is used in the
       proved adequacy_gen_RiscVNStepsExitCond. *)
    Lemma semWP2_preservation' `{sailGS2 Σ} n {s11 s21} {γ11 γ12 γ21 γ22} {μ11 μ12 μ21 μ22}
    {δ11 δ21}
    {Q}  :
    NSteps γ11 μ11 δ11 s11 γ12 μ12 [env] (stm_val ty.unit ()) n ->
      Steps γ21 μ21 δ21 s21 γ22 μ22 [env] (stm_val ty.unit ()) ->
    mem_inv2 _ μ11 μ21 ∗ regs_inv2 γ11 γ21 -∗
      semWP2 δ11 δ21 s11 s21 Q
    ={⊤,∅}=∗ |={∅}▷=>^(n) |={∅,⊤}=>
            mem_inv2 _ μ12 μ22 ∗ regs_inv2 γ12 γ22 ∗
              semWP2 [env] [env] (stm_val ty.unit ()) (stm_val ty.unit ()) Q.
  Proof.
    revert s11 s21 μ11 μ21 γ11 γ21 μ12 μ22 γ12 γ22 δ11 δ21 Q.
    induction n as [|n IH]=> s11 s21 μ11 μ21 γ11 γ21 μ12 μ22 γ12 γ22 δ11 δ21 Q /=.
    { intros steps1 steps2.
      inversion steps1. inversion steps2; subst; iIntros "(Hmem & Hregs)"; iIntros "Hwp".
      - iFrame.
        by iApply fupd_mask_subseteq.
      - rewrite {1}semWP2_unfold. cbn. 
        destruct s21; cbn; iMod "Hwp"; auto.
        + iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iMod "Hclose".
          inversion H4.
        + inversion H4.
    }
    iIntros (steps1 steps2) "(Hmem & Hregs)".
    iIntros " Hwp".
    inversion steps1 as [ | ? γ1 ? μ1 ? ? ? ? ? Hstep1 Hevaln1]. subst.
    inversion steps2; subst.
    { rewrite {1}semWP2_unfold. cbn. 
      destruct s11; cbn; iMod "Hwp"; auto.
      all: inversion Hstep1.
    }
    iPoseProof (semWP2_step Hstep1 H0 with "[$Hmem $Hregs $Hwp]") as "Hwp".
    iMod "Hwp". iModIntro. iMod "Hwp". do 2 iModIntro. do 2 iMod "Hwp".
    iDestruct "Hwp" as "(Hregs & Hmem & Hwp)".
    specialize (IH _ _ _ _ _ _ _ _ _ _ _ _ Q Hevaln1 H1).
    by iApply (IH with "[$Hmem $Hregs]").
  Qed.

  (* Termination-sensitive variant of semWP2_preservation':                   *)
  (* derives world-2's Steps existentially via can_step, rather than          *)
  (* requiring them as an input hypothesis.                                   *)
  (*                                                                          *)
  (* PC SYNCHRONISATION NOTE                                                  *)
  (*                                                                          *)
  (* The lemma carries pc_sync (γ11.pc = γ21.pc) as a Coq hypothesis and    *)
  (* returns the preserved pc_sync (γ12.pc = γ22.pc) as a pure conjunct in  *)
  (* the conclusion.  This lets adequacy_gen_RiscVNStepsExitCond_strong      *)
  (* thread the invariant step-by-step without needing pc_step_sync as an    *)
  (* external obligation on callers.                                          *)
  (*                                                                          *)
  (* ALTERNATIVE DESIGN — Iris invariant for PC sync                         *)
  (*                                                                          *)
  (* Instead of threading pc_sync through every step, we could maintain an   *)
  (* Iris invariant analogous to interp_inv_constant_time:                   *)
  (*                                                                          *)
  (*   Definition pc_sync_inv_ns := nroot .@ "pc_sync".                      *)
  (*   Definition interp_inv_pc_sync `{sailGS2 Σ} : iProp Σ :=               *)
  (*     inv pc_sync_inv_ns (∃ v : bv xlenbits, reg_pointsTo2 pc (SyncVal v)).*)
  (*                                                                          *)
  (* This says: throughout execution the two-world ghost PC is always         *)
  (* SyncVal v for some v.  Combined with reg_valid2, this gives              *)
  (* read_register γ1 pc = read_register γ2 pc at any point.                 *)
  (*                                                                          *)
  (* The invariant is strictly weaker than interp_inv_constant_time: PC sync *)
  (* is implied by leakage sync (LeakPc records the fetch address at every   *)
  (* step, so equal leakage traces imply equal PC sequences).  But relying   *)
  (* on the leakage invariant here would be architecturally backwards — the  *)
  (* leakage invariant is something we are trying to prove, not a tool to    *)
  (* prove it with.  The dedicated PC-sync invariant is independent of the   *)
  (* leakage model, so it would survive a leakage model change.              *)
  (*                                                                          *)
  (* Why we did NOT use this invariant approach:                              *)
  (* reg_pointsTo2 pc (SyncVal v) is currently held inside regs_inv2, which  *)
  (* is defined as regs_inv γ1 ∗ regs_inv γ2.  To store it inside an inv,   *)
  (* regs_inv2 would need to be redefined to exclude pc, splitting it into   *)
  (* regs_inv2_no_pc ∗ inv (∃ v, reg_pointsTo2 pc (SyncVal v)).  That is    *)
  (* invasive — it touches every proof that destructures regs_inv2.          *)
  (*                                                                          *)
  (* The alternative (a new auth/frag ghost algebra for PC, mirroring how    *)
  (* traceG supports tr_auth/tr_frag for the leakage invariant) would be     *)
  (* fully principled but requires new ghost infrastructure.                 *)
  (*                                                                          *)
  (* Threading pc_sync through the Coq induction (current approach) is       *)
  (* equivalent to the invariant approach in information content.  We chose  *)
  (* it as the simpler option until the regs_inv2 split or a new ghost type  *)
  (* is deemed worth the effort.                                              *)
  Lemma semWP2_preservation_fwd' `{sailGS2 Σ} n {s11 s21}
      {γ11 γ12 γ21} {μ11 μ12 μ21} {δ11 δ21} {Q}
      (Hpc : RiscvPmpProgram.read_register γ11 pc =
             RiscvPmpProgram.read_register γ21 pc) :
      NSteps γ11 μ11 δ11 s11 γ12 μ12 [env] (stm_val ty.unit ()) n ->
      mem_inv2 _ μ11 μ21 ∗ regs_inv2 γ11 γ21 -∗
        semWP2 δ11 δ21 s11 s21 Q
      ={⊤,∅}=∗ |={∅}▷=>^(n) |={∅,⊤}=>
        ∃ (γ22 : RegStore) (μ22 : Memory) (s22 : Stm [ctx] ty.unit),
          ⌜Steps γ21 μ21 δ21 s21 γ22 μ22 [env] s22⌝ ∗
          ⌜stm_to_val s22 ≠ None⌝ ∗
          ⌜RiscvPmpProgram.read_register γ12 pc =
           RiscvPmpProgram.read_register γ22 pc⌝ ∗
          mem_inv2 _ μ12 μ22 ∗ regs_inv2 γ12 γ22 ∗
          semWP2 [env] [env] (stm_val ty.unit ()) s22 Q.
  (* The conclusion quantifies over the terminal statement s22 for world 2
     (which may be stm_val or stm_fail for fun_step semantics).  The Q in
     the adequacy proof rules out stm_fail by its specific shape.
     The pc_sync conjunct is proved from the lock-step semantics: both worlds
     start at the same PC and execute the same instruction, so their PCs
     advance identically.
     - n=0 case: γ12=γ11 and γ22=γ21, so pc_sync is Hpc itself.
     - S n case: use can_step for world 2 (non-terminal by lock-step), apply
       semWP2_step, derive pc_sync_mid from one-step PC preservation,
       recurse via IH. *)
  Proof.
  Admitted.

  (* ======================================================================== *)
  (* Two-sided adequacy: adequacy_gen_RiscVNStepsExitCond                     *)
  (*                                                                          *)
  (* Given:                                                                   *)
  (*   Heval1 : ⟨γ11, μ11⟩ -(exitCond, n)->* ⟨γ12, μ12⟩  (world 1)         *)
  (*   Heval2 : ⟨γ21, μ21⟩ -(exitCond, n)->* ⟨γ22, μ22⟩  (world 2)         *)
  (*   Hwp : ∀ Σ, mem_res2 ∗ own_regstore2 ⊢ |={⊤}=>                         *)
  (*           myWP2_loop (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜exitCond v⌝)              *)
  (*         ∗ (mem_inv2 μ12 μ22 ={⊤,∅}=∗ ⌜φ⌝)                              *)
  (* Concludes: φ                                                              *)
  (*                                                                          *)
  (* Proof strategy:                                                          *)
  (*   - Convert Heval1 to list form (nsteps_to_lsteps → l1, Hl1, Heval1)   *)
  (*   - Create ghost resources (create_resources) and instantiate Hwp        *)
  (*   - iStopProof; induct on l1                                             *)
  (*   - Base case: n=0, apply Hcont to get ⌜φ⌝                             *)
  (*   - Inductive case:                                                      *)
  (*       rewrite fixpoint_myWP2_loop_eq; unfold myWP2_loop_fix             *)
  (*       + ExitCond branch: contradiction (exitCond fires but nEC1 says no) *)
  (*       + semWP2 branch: use semWP2_preservation' (both worlds' traces);  *)
  (*         apply IH after consuming lc credit                               *)
  (*   This is the PROVED version (uses both Heval1 and Heval2).             *)
  (*   The one-sided variant is adequacy_gen_RiscVNStepsExitCond_strong.     *)
  (* ======================================================================== *)
      Lemma adequacy_gen_RiscVNStepsExitCond n exitCond {γ11 γ12 γ21 γ22} {μ11 μ12 μ21 μ22}
    (φ : Prop) :
    ⟨ γ11, μ11 ⟩ -( exitCond , n )->* ⟨ γ12, μ12 ⟩ ->
    ⟨ γ21, μ21 ⟩ -( exitCond , n )->* ⟨ γ22, μ22 ⟩ ->
    (forall `{sailGS2 Σ},
        mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢
          |={⊤}=> myWP2_loop (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜exitCond v⌝)
        ∗ (mem_inv2 _ μ12 μ22 ={⊤,∅}=∗ ⌜φ⌝)
    )%I -> φ.
  Proof.
    intros Heval1 Heval2 Hwp.
    apply nsteps_to_lsteps in Heval1.
    destruct Heval1 as (l1 & Hl1 & Heval1).
    refine (uPred.pure_soundness _
              (step_fupdN_soundness_gen (Σ := sailΣ2) _ HasLc (list_sum_plus_one l1) (list_sum_plus_one l1) _)).
    iIntros (Hinv) "Hcred'".
    iMod (create_resources Hinv γ11 γ21 μ11 μ21) as (regs1 regs2 memG) "(Hmem & Rmem & Hregs & Rregs)".
    pose (sG := @SailGS2 sailΣ2 Hinv (SailRegGS2 (SailRegGS (@reg_pre_inG2_left _ (@subG_sailGpreS _ _)) regs1) (SailRegGS (@reg_pre_inG2_right _ (@subG_sailGpreS _ _)) regs2)) memG).
    specialize (Hwp _ sG).
    iPoseProof (Hwp with "[$Rmem $Rregs]") as "Hwp2".
    clear Hwp.
    iStopProof.
    revert Heval1 Heval2.
    revert γ11 μ11 γ21 μ21 n Hl1.
    induction l1; iIntros (γ11 μ11 γ21 μ21 n Hl1 Heval1 Heval2) "(Hcred & Hmem & Hregs & Hwp2)".
    - inversion Heval1. cbn in Hl1. subst.
      inversion Heval2. subst.
      iMod "Hwp2" as "[_ Hcont]".
      iMod ("Hcont" with "Hmem") as "%Hφ".
      cbn. done.
    - inversion Heval1 as [ | ? ? γ1 ? μ1 ? nEC1 Hstep1 Hevaln1]. clear Heval1. subst.
      inversion Heval2. subst. clear Heval2.
      rename H1 into Hstep2. rename H4 into Hevaln2. rename H0 into nEC2.
      specialize (IHl1 _ _ _ _ _ eq_refl Hevaln1 Hevaln2).
      rewrite fixpoint_myWP2_loop_eq.
      unfold myWP2_loop_fix.
      iMod "Hwp2" as "([H | Hwp2] & Hφ)".
      + iDestruct "H" as (v) "(Hpc & %Hec)".
        unfold reg_pointsTo2.
        iPoseProof (reg_valid2 with "[$Hregs] [$Hpc]") as "(%eq1 & _)".
        rewrite eq1 in nEC1. tauto.
      + iPoseProof (semWP2_preservation' Hstep1 Hstep2 with "[$Hmem $Hregs]") as "Hwp".
        iSpecialize ("Hwp" with "Hwp2").
        iMod "Hwp".
        change (list_sum_plus_one (a :: l1)) with (a + 1 + list_sum_plus_one l1).
        iAssert (|={∅}▷=>^a |={∅}=>  |={∅}▷=> |={∅}▷=>^(list_sum_plus_one l1) ⌜φ⌝)%I with "[-]" as "H"; last first.
        { do 2 rewrite step_fupdN_add. destruct a. done. by iApply step_fupdN_S_fupd. }
        iApply (step_fupdN_wand with "Hwp").
        iIntros ">(Hmem & Hregs & Hwp)".
        rewrite semWP2_val.
        iMod "Hwp" as "Hwp".
        rewrite (into_sep_lc_add (a + 1) (list_sum_plus_one l1)).
        rewrite (into_sep_lc_add a 1).
        iDestruct "Hcred" as "[[Hcreda Hcred1] Hcredl]".
        iMod (lc_fupd_elim_later with "Hcred1 Hwp") as "Hwp".
        now iMod (IHl1 with "[$Hmem $Hcredl $Hregs $Hwp $Hφ]") as "IHl".
  Qed.

  (* ======================================================================== *)
  (* One-sided adequacy: adequacy_gen_RiscVNStepsExitCond_strong  [ADMITTED] *)
  (*                                                                          *)
  (* UNLIKE adequacy_gen_RiscVNStepsExitCond, this takes ONLY world-1's      *)
  (* execution trace.  It derives world-2's trace and the conclusion          *)
  (* existentially.  This is the STRONG (termination-sensitive) variant.      *)
  (*                                                                          *)
  (* PC-synchronisation is threaded via semWP2_preservation_fwd' rather than *)
  (* requiring pc_step_sync as an external hypothesis.  The updated           *)
  (* semWP2_preservation_fwd' returns                                         *)
  (*   ⌜read_register γ12 pc = read_register γ22 pc⌝                         *)
  (* as a pure conjunct; the inductive case extracts it and passes it to the  *)
  (* IH as pc_sync_next.                                                       *)
  (*                                                                          *)
  (* ============================= PROOF PLAN ============================== *)
  (*                                                                          *)
  (* The proof mirrors adequacy_gen_RiscVNStepsExitCond with these changes:  *)
  (*                                                                          *)
  (* PREAMBLE (identical to non-strong):                                      *)
  (*   intros Heval1 Hwp.                                                    *)
  (*   apply nsteps_to_lsteps in Heval1.                                     *)
  (*   destruct Heval1 as (l1 & Hl1 & Heval1).                               *)
  (*   refine (uPred.pure_soundness _                                         *)
  (*     (step_fupdN_soundness_gen (Σ := sailΣ2) _ HasLc                    *)
  (*        (list_sum_plus_one l1) (list_sum_plus_one l1) _)).                *)
  (*   iIntros (Hinv) "Hcred'".                                              *)
  (*   iMod (create_resources Hinv γ11 γ21 μ11 μ21)                          *)
  (*     as (regs1 regs2 memG) "(Hmem & Rmem & Hregs & Rregs)".              *)
  (*   pose sG := ...  (* same as non-strong *)                               *)
  (*   specialize (Hwp _ sG).                                                *)
  (*   iPoseProof (Hwp with "[$Rmem $Rregs]") as "Hwp2".                     *)
  (*   clear Hwp.                                                             *)
  (*   iStopProof.                                                            *)
  (*   revert Heval1.                                                         *)
  (*   revert γ11 μ11 γ21 μ21 n Hl1 pc_init_sync.                           *)
  (*   induction l1;                                                          *)
  (*     iIntros (γ11 μ11 γ21 μ21 n Hl1 pc_sync Heval1)                     *)
  (*             "(Hcred & Hmem & Hregs & Hwp2)".                            *)
  (*                                                                          *)
  (* BASE CASE (l1 = []):                                                    *)
  (*   - inversion Heval1. cbn in Hl1. subst.                                *)
  (*     iMod "Hwp2" as "[_ Hcont]".                                         *)
  (*     (* Key difference: Hcont takes ∀ γ22 μ22 *)                        *)
  (*     iMod ("Hcont" $! γ21 μ21 with "Hmem") as "%Hφ".                    *)
  (*     cbn. iPureIntro.                                                     *)
  (*     exact ⟨γ21, μ21, riscVNStepWithExitCond_refl, Hφ⟩.                 *)
  (*                                                                          *)
  (* INDUCTIVE CASE (l1 = a :: l1):                                          *)
  (*   - inversion Heval1 ... (* extract γ1mid, μ1mid, nEC1, Hstep1 *)      *)
  (*     (* Derive nEC2 from pc_sync: exitCond fires on world-1 pc,         *)
  (*        so by pc_sync it fires on world-2 pc too. *)                    *)
  (*     have nEC2 : ¬ exitCond (read_register γ21 pc).                     *)
  (*     { intro Hex. apply nEC1. rewrite pc_sync. exact Hex. }             *)
  (*     specialize (IHl1 _ _ _ _ _ eq_refl).                                *)
  (*     rewrite fixpoint_myWP2_loop_eq. unfold myWP2_loop_fix.             *)
  (*     iMod "Hwp2" as "([H | Hwp2] & Hφ)".                                *)
  (*     + (* ExitCond branch: contradiction via pc_sync *)                  *)
  (*       iDestruct "H" as (v) "(Hpc & %Hec)".                             *)
  (*       unfold reg_pointsTo2.                                             *)
  (*       iPoseProof (reg_valid2 with "[$Hregs] [$Hpc]") as "(%eq1 & _)". *)
  (*       rewrite eq1 in nEC1. tauto.                                       *)
  (*     + (* semWP2 branch: use semWP2_preservation_fwd' with pc_sync *)    *)
  (*       iPoseProof (semWP2_preservation_fwd' pc_sync Hstep1               *)
  (*         with "[$Hmem $Hregs]") as "Hwp_pres".                           *)
  (*       iSpecialize ("Hwp_pres" with "Hwp2").                             *)
  (*       iMod "Hwp_pres".                                                  *)
  (*       (* fuel arithmetic: a + 1 + list_sum_plus_one l1 *)               *)
  (*       iApply (step_fupdN_wand with "Hwp_pres").                         *)
  (*       iIntros ">(%γ22mid & %μ22mid & %s22mid & %Hsteps &                *)
  (*                   %Hval & %pc_sync_next & Hmem_new & Hregs_new &        *)
  (*                   Hwp_new)".                                             *)
  (*       (* pc_sync_next from semWP2_preservation_fwd' output *)            *)
  (*       (* Case-analyze s22mid: stm_val or stm_fail *)                   *)
  (*       destruct (stm_to_val s22mid) as [v22|] eqn:Ev22.                 *)
  (*       2: { contradiction. } (* Hval : stm_to_val s22mid ≠ None *)      *)
  (*       destruct (stm_to_val_Some_cases Ev22)                             *)
  (*         as [(v' & Hs22 & Hv22) | (m & Hs22 & Hv22)].                   *)
  (*       * (* Success: s22mid = stm_val ty.unit v' *)                      *)
  (*         subst s22mid. subst v22. destruct v'.                           *)
  (*         rewrite semWP2_val. iMod "Hwp_new" as "Hwp_new".               *)
  (*         specialize (IHl1 γ1mid μ1mid γ22mid μ22mid (length l1) eq_refl *)
  (*                       pc_sync_next Hevaln1).                            *)
  (*         (* credit management: split lc for a + 1 + |l1| *)             *)
  (*         rewrite (into_sep_lc_add (a + 1) (list_sum_plus_one l1)).       *)
  (*         rewrite (into_sep_lc_add a 1).                                  *)
  (*         iDestruct "Hcred" as "[[Hcreda Hcred1] Hcredl]".               *)
  (*         iMod (lc_fupd_elim_later with "Hcred1 Hwp_new") as "Hwp_new".  *)
  (*         iMod (IHl1 with "[$Hmem_new $Hcredl $Hregs_new $Hwp_new $Hφ]") *)
  (*           as "IHl".                                                      *)
  (*         iApply (step_fupdN_wand with "IHl").                            *)
  (*         iModIntro. iApply step_fupd_intro; first set_solver. iModIntro. *)
  (*         iIntros "%HIH".                                                  *)
  (*         destruct HIH as (γ2_final & μ2_final & Hsteps_rest & Hphi).    *)
  (*         iPureIntro.                                                      *)
  (*         exact ⟨γ2_final, μ2_final,                                      *)
  (*                riscVNStepWithExitCond_trans nEC2 Hsteps Hsteps_rest,    *)
  (*                Hphi⟩.                                                   *)
  (*       * (* Failure: stm_fail — contradiction via semWP2_unfold *)       *)
  (*         subst s22mid. subst v22.                                         *)
  (*         iEval (rewrite semWP2_unfold; cbn) in "Hwp_new".               *)
  (*         iMod "Hwp_new" as "[]".                                         *)
  (* Qed.                                                                    *)
  (*                                                                          *)
  (* KEY INGREDIENTS:                                                         *)
  (*   semWP2_preservation_fwd' — existential world-2 step + pc_sync output  *)
  (*   stm_to_val_Some_cases (theories/Iris/Resources.v) — case-analyze stm  *)
  (*   nsteps_to_steps (theories/Iris/BinaryAdequacy.v) — NSteps → Steps     *)
  (*   riscVNStepWithExitCond_trans (line ~621) — prepend one step            *)
  (*   semWP2_val — unfolds semWP2 on (stm_val, stm_val)                     *)
  (*   semWP2_unfold + cbn — reveals False for stm_fail                      *)
  (*   lc_fupd_elim_later / into_sep_lc_add — credit management              *)
  (*   step_fupdN_wand — map inside step-fupdN modality                      *)
  (* ======================================================================== *)
  Lemma adequacy_gen_RiscVNStepsExitCond_strong
      n exitCond {γ11 γ12 γ21} {μ11 μ12 μ21}
      (pc_init_sync : RiscvPmpProgram.read_register γ11 pc =
                      RiscvPmpProgram.read_register γ21 pc)
      (φ : RegStore -> Memory -> Prop) :
      ⟨γ11, μ11⟩ -(exitCond, n)->* ⟨γ12, μ12⟩ ->
      (forall `{sailGS2 Σ},
          mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢
            |={⊤}=> myWP2_loop (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜exitCond v⌝)
            ∗ (∀ γ22 μ22, mem_inv2 _ μ12 μ22 ={⊤,∅}=∗ ⌜φ γ22 μ22⌝)
      )%I ->
      ∃ γ22 μ22,
        ⟨γ21, μ21⟩ -(exitCond, n)->* ⟨γ22, μ22⟩ ∧
        φ γ22 μ22.
  Proof.
    intros Heval1 Hwp.
    apply nsteps_to_lsteps in Heval1.
    destruct Heval1 as (l1 & Hl1 & Heval1).
    refine (uPred.pure_soundness _
              (step_fupdN_soundness_gen (Σ := sailΣ2) _ HasLc
                 (list_sum_plus_one l1) (list_sum_plus_one l1) _)).
    iIntros (Hinv) "Hcred'".
    iMod (create_resources Hinv γ11 γ21 μ11 μ21)
      as (regs1 regs2 memG) "(Hmem & Rmem & Hregs & Rregs)".
    pose (sG := @SailGS2 sailΣ2 Hinv
      (SailRegGS2
         (SailRegGS (@reg_pre_inG2_left _ (@subG_sailGpreS _ _)) regs1)
         (SailRegGS (@reg_pre_inG2_right _ (@subG_sailGpreS _ _)) regs2))
      memG).
    specialize (Hwp _ sG).
    iPoseProof (Hwp with "[$Rmem $Rregs]") as "Hwp2".
    clear Hwp.
    iStopProof.
    revert Heval1.
    revert γ11 μ11 γ21 μ21 n Hl1 pc_init_sync.
    induction l1 as [| a l1 IHl1];
      iIntros (γ11 μ11 γ21 μ21 n Hl1 pc_sync Heval1)
              "(Hcred & Hmem & Hregs & Hwp2)".
    - (* Base case: n = 0, both worlds already at exit *)
      inversion Heval1. cbn in Hl1. subst.
      iMod "Hwp2" as "[_ Hcont]".
      iMod ("Hcont" $! γ21 μ21 with "Hmem") as "%Hφ".
      cbn. iPureIntro.
      exists γ21, μ21. split; [apply riscVNStepWithExitCond_refl | exact Hφ].
    - (* Inductive case: one more outer-loop step *)
      inversion Heval1 as [| ? ? γ1mid ? μ1mid ? nEC1 Hstep1 Hevaln1].
      clear Heval1. subst.
      have nEC2 : ¬ exitCond (read_register γ21 pc).
      { intro Hex. apply nEC1. rewrite pc_sync. exact Hex. }
      rewrite fixpoint_myWP2_loop_eq. unfold myWP2_loop_fix.
      iMod "Hwp2" as "([H | Hwp2] & Hφ)".
      + (* ExitCond branch: contradiction *)
        iDestruct "H" as (v) "(Hpc & %Hec)".
        unfold reg_pointsTo2.
        iPoseProof (reg_valid2 with "[$Hregs] [$Hpc]") as "(%eq1 & _)".
        rewrite eq1 in nEC1. tauto.
      + (* semWP2 branch: derive world-2's step existentially *)
        iPoseProof (semWP2_preservation_fwd' pc_sync Hstep1
          with "[$Hmem $Hregs]") as "Hwp_pres".
        iSpecialize ("Hwp_pres" with "Hwp2").
        iMod "Hwp_pres".
        change (list_sum_plus_one (a :: l1)) with (a + 1 + list_sum_plus_one l1).
        iAssert (|={∅}▷=>^a |={∅}=> |={∅}▷=>
                 |={∅}▷=>^(list_sum_plus_one l1)
                 ⌜∃ γ22 μ22,
                    ⟨γ21, μ21⟩ -(exitCond, S (length l1))->* ⟨γ22, μ22⟩
                    ∧ φ γ22 μ22⌝)%I
          with "[-]" as "H"; last first.
        { do 2 rewrite step_fupdN_add. destruct a. done.
          by iApply step_fupdN_S_fupd. }
        iApply (step_fupdN_wand with "Hwp_pres").
        iIntros ">(%γ22mid & %μ22mid & %s22mid & %Hsteps &
                    %Hval & %pc_sync_next & Hmem_new & Hregs_new & Hwp_new)".
        destruct (stm_to_val s22mid) as [v22|] eqn:Ev22.
        2: { contradiction. }
        destruct (stm_to_val_Some_cases Ev22)
          as [(v' & Hs22 & Hv22) | (m & Hs22 & Hv22)].
        * (* Success: s22mid = stm_val ty.unit v' *)
          subst s22mid. subst v22. destruct v'.
          (* pc_sync_next from semWP2_preservation_fwd' output — no pc_step_sync needed *)
          rewrite semWP2_val. iMod "Hwp_new" as "Hwp_new".
          specialize (IHl1 γ1mid μ1mid γ22mid μ22mid (length l1) eq_refl
                        pc_sync_next Hevaln1).
          rewrite (into_sep_lc_add (a + 1) (list_sum_plus_one l1)).
          rewrite (into_sep_lc_add a 1).
          iDestruct "Hcred" as "[[Hcreda Hcred1] Hcredl]".
          iMod (lc_fupd_elim_later with "Hcred1 Hwp_new") as "Hwp_new".
          iMod (IHl1 with "[$Hmem_new $Hcredl $Hregs_new $Hwp_new $Hφ]") as "IHl"; auto.
          iApply (step_fupdN_wand with "IHl").
          iModIntro. Search "step" fupd. iApply step_fupd_intro; first set_solver.
          iModIntro.
          iIntros "%HIH".
          destruct HIH as (γ2_final & μ2_final & Hsteps_rest & Hphi).
          iPureIntro.
          exact (ex_intro _ γ2_final (ex_intro _ μ2_final
                   (conj (riscVNStepWithExitCond_trans nEC2 Hsteps Hsteps_rest)
                         Hphi))).
        * (* Failure: stm_fail — contradiction *)
          subst s22mid. subst v22.
          iEval (rewrite semWP2_unfold; cbn) in "Hwp_new".
          iMod "Hwp_new" as "[]".
  Qed.

  Lemma constant_time_from_mem_res2_only_leak `{sailGS2 Σ} `{memGS2 Σ} {μ1 μ2 E} :
    leakage_trace μ1 = leakage_trace μ2 -> mem_res2_only_leak μ1 μ2 ⊢ |={E}=> interp_inv_constant_time.
  Proof.
    iIntros (eq_leak) "Hmem".
    unfold interp_inv_constant_time.
    iApply (inv_alloc constant_time_inv_ns E (∃ t : LeakageTrace, trace.tr_frag trace.trace_name t ∗ trace.tr_frag trace.trace_name t) with "[Hmem]").
    iModIntro.
    unfold mem_res2_only_leak, IrisInstance.RiscvPmpIrisAdeqParameters.mem_res_only_leak.
    rewrite eq_leak.
    iFrame.
  Qed.

(* ======================================================================== *)
(* AdequacyTools: Iris-level machinery connecting VC soundness to myWP2_loop *)
(*                                                                           *)
(* This section bridges the gap between:                                     *)
(*   - The symbolic VC checker output (safeE (postprocess ...))              *)
(*   - The Iris loop predicate myWP2_loop                                   *)
(*                                                                           *)
(* Key definitions / lemmas in order:                                        *)
(*                                                                           *)
(*  regPstsTo_sync_is_nonsync: NonSyncVal v v ≡ SyncVal v for registers.    *)
(*    Used in cfg_instrs_verified when both worlds have the same init PC.    *)
(*                                                                           *)
(*  ptstomem_sync_is_nonsync: analogous for memory cells.                   *)
(*    Used in something_memory for public memory cells.                      *)
(*                                                                           *)
(*  intro_ptsto_instr / intro_ptsto_instrs:                                  *)
(*    Build ptsto_instrs from two-world raw byte ownership.                   *)
(*    The `SyncVal bv.zero` base address is hard-coded here (init_addr = 0). *)
(*                                                                           *)
(*  instrsMemory:                                                            *)
(*    Extract ptsto_instrs from mem_res2_without_leak (raw memory model).   *)
(*    Takes mem_has_instrs for both worlds (encoding = memory bytes match).  *)
(*                                                                           *)
(*  instrsAndDataMemory:                                                     *)
(*    Same as instrsMemory but also extracts interp_mem_with_memory for the  *)
(*    data region immediately following the instruction region.              *)
(*    (PROVED in commit 04a634c8.)                                           *)
(*                                                                           *)
(*  exitCond_WP2_loop: the standard ExitCond for CFGVer programs.           *)
(*    = myWP2_loop (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜exitCond v⌝)                   *)
(*    SyncVal v is critical: both worlds have the same PC at exit, so the   *)
(*    leakage-trace invariant can be closed uniformly.                       *)
(*                                                                           *)
(*  sound_exec_cfg_addr_myWP2:                                              *)
(*    The key bridge: given cexec_cfg_addr succeeds (Prop-level), the Iris  *)
(*    precondition implies myWP2_loop ExitCondIprop.                         *)
(*    Proof: induction on fuel; exit branch applies exitCondImpliesMyWP2_loop;*)
(*    execute branch uses ptsto_instrs_nth + sound_exec_instruction + IH.   *)
(*                                                                           *)
(*  sound_cexec_triple_addr_myWP2:                                          *)
(*    Wraps sound_exec_cfg_addr_myWP2 with the produce_sound step that       *)
(*    converts the precondition assertion to the heap form.                  *)
(*                                                                           *)
(*  sound_sblock_verification_condition_myWP2:                              *)
(*    TOP-LEVEL BRIDGE. Given safeE (postprocess VC), produces myWP2_loop.  *)
(*    Connects ValidCFGVerifierContract → myWP2_loop (∃ v, pc ↦ᵣ SyncVal v  *)
(*    ∗ ⌜exitCond v⌝) after consuming the precondition from the Iris state. *)
(*    This is called by cfg_instrs_verified / cfg_instrs_safe.              *)
(* ======================================================================== *)
Section AdequacyTools.

  Context {Σ} {GS : sailGS2 Σ}.
  Lemma regPstsTo_sync_is_nonsync `{sailGS2 Σ} σ r (v : Val σ) : r ↦ᵣ NonSyncVal v v ⊣⊢ r ↦ᵣ SyncVal v.
  Proof.
    unfold reg_pointsTo2. auto.
  Qed.

  Lemma interp_pstsTo_sync_is_nonsync `{sailGS2 Σ} r v : interp_ptsto r (NonSyncVal v v) ∗-∗ interp_ptsto r (SyncVal v).
  Proof.
    unfold interp_ptsto. auto.
  Qed.

  (* Word-level analog of regPstsTo_sync_is_nonsync *)
  Lemma ptstomem_sync_is_nonsync `{sailGS2 Σ} (a w : Val ty_word) :
    interp_ptstomem (width := 4) (SyncVal a) (NonSyncVal w w) ⊣⊢
    interp_ptstomem (width := 4) (SyncVal a) (SyncVal w).
  Proof. unfold interp_ptstomem. auto. Qed.

  Lemma intro_ptstomem_word `{sailGS2 Σ} v0 v1 v2 v3 (a : Val ty_word) :
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) (bv.of_Z (0 + bv.unsigned a)) (DfracOwn 1) v0 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) (bv.of_Z (1 + bv.unsigned a)) (DfracOwn 1) v1 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) (bv.of_Z (2 + bv.unsigned a)) (DfracOwn 1) v2 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) (bv.of_Z (3 + bv.unsigned a)) (DfracOwn 1) v3 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) (bv.of_Z (0 + bv.unsigned a)) (DfracOwn 1) v0 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) (bv.of_Z (1 + bv.unsigned a)) (DfracOwn 1) v1 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) (bv.of_Z (2 + bv.unsigned a)) (DfracOwn 1) v2 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) (bv.of_Z (3 + bv.unsigned a)) (DfracOwn 1) v3⊢
      interp_ptstomem (width := 4) (SyncVal a) (SyncVal (bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil))))).
  Proof.
    iIntros "(Hmem1a & Hmem1a1 & Hmem1a2 & Hmem1a3 & Hmem2a & Hmem2a1 & Hmem2a2 & Hmem2a3)".
    unfold interp_ptstomem. unfold IrisInstance.RiscvPmpIrisInstance.interp_ptstomem.
    rewrite ?bv.appView_app.
    replace (@bv.of_Z xlenbits (0 + bv.unsigned a)%Z) with a by now rewrite bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (1 + bv.unsigned a)%Z) with (bv.add bv.one a) by now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (2 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one a)).
    replace (@bv.of_Z xlenbits (3 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one (bv.add bv.one a))).
    cbn.
    unfold IrisInstance.RiscvPmpIrisInstance.interp_ptsto.
    iFrame.
    rewrite ?bv.add_assoc.
    change (bv.add _ bv.one) with (@bv.of_Z xlenbits 3).
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    rewrite ?bv.add_assoc.
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
  Qed.

  Lemma intro_ptstomem_word_nonsync `{sailGS2 Σ}
      v0l v1l v2l v3l v0r v1r v2r v3r (a : Val ty_word) :
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (0 + bv.unsigned a)) (DfracOwn 1) v0l ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (1 + bv.unsigned a)) (DfracOwn 1) v1l ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (2 + bv.unsigned a)) (DfracOwn 1) v2l ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (3 + bv.unsigned a)) (DfracOwn 1) v3l ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (0 + bv.unsigned a)) (DfracOwn 1) v0r ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (1 + bv.unsigned a)) (DfracOwn 1) v1r ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (2 + bv.unsigned a)) (DfracOwn 1) v2r ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (3 + bv.unsigned a)) (DfracOwn 1) v3r ⊢
    interp_ptstomem (width := 4) (SyncVal a)
      (NonSyncVal (bv.app v0l (bv.app v1l (bv.app v2l (bv.app v3l bv.nil))))
                  (bv.app v0r (bv.app v1r (bv.app v2r (bv.app v3r bv.nil))))).
  Proof.
    iIntros "(Hl0 & Hl1 & Hl2 & Hl3 & Hr0 & Hr1 & Hr2 & Hr3)".
    unfold interp_ptstomem. unfold IrisInstance.RiscvPmpIrisInstance.interp_ptstomem.
    rewrite ?bv.appView_app.
    replace (@bv.of_Z xlenbits (0 + bv.unsigned a)%Z) with a
      by now rewrite bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (1 + bv.unsigned a)%Z) with (bv.add bv.one a)
      by now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (2 + bv.unsigned a)%Z) with
      (bv.add bv.one (bv.add bv.one a)).
    replace (@bv.of_Z xlenbits (3 + bv.unsigned a)%Z) with
      (bv.add bv.one (bv.add bv.one (bv.add bv.one a))).
    cbn.
    unfold IrisInstance.RiscvPmpIrisInstance.interp_ptsto.
    iFrame "Hl0 Hl1 Hl2 Hl3 Hr0 Hr1 Hr2 Hr3".
    rewrite ?bv.add_assoc.
    change (bv.add _ bv.one) with (@bv.of_Z xlenbits 3).
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    rewrite ?bv.add_assoc.
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
  Qed.

  Lemma intro_ptstomem_word2 `{sailGS2 Σ} {μ1 μ2 : Memory} {a : Val ty_word} {v : Val ty_word} :
    mem_has_word μ1 a v ->
    mem_has_word μ2 a v ->
    ([∗ list] a' ∈ bv.seqBv a 4,
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ1 a')) ∗
      ([∗ list] a' ∈ bv.seqBv a 4,
        @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ2 a'))
      ⊢ interp_ptstomem (SyncVal a) (SyncVal v).
  Proof.
    iIntros (Hmhw1 Hmhw2) "[Hmem1 Hmem2]".
    destruct Hmhw1 as (v01 & v11 & v21 & v31 & Heqμ1 & Heqv1).
    destruct Hmhw2 as (v02 & v12 & v22 & v32 & Heqμ2 & Heqv2).
    unfold bv.seqBv, seqZ. change (seq 0 ?x) with [0;1;2;3].
    cbn -[bv.add interp_ptstomem word].
    iDestruct "Hmem1" as "(Hmem1a & Hmem1a1 & Hmem1a2 & Hmem1a3 & _)".
    iDestruct "Hmem2" as "(Hmem2a & Hmem2a1 & Hmem2a2 & Hmem2a3 & _)".
    rewrite <- Heqv1 in Heqv2.
    do 4 (apply bv.app_inj in Heqv2; destruct Heqv2 as [? Heqv2]). subst.
    rewrite <- Heqμ1 in Heqμ2.
    inversion Heqμ1; inversion Heqμ2.
    rewrite H5 H6 H7 H8.
    now iApply (intro_ptstomem_word with "[$Hmem1a $Hmem1a1 $Hmem1a2 $Hmem1a3 $Hmem2a $Hmem2a1 $Hmem2a2 $Hmem2a3]").
  Qed.

  Lemma intro_ptstomem_word2_nonsync `{sailGS2 Σ} {μ1 μ2 : Memory}
      {a : Val ty_word} {w1 w2 : Val ty_word} :
    mem_has_word μ1 a w1 →
    mem_has_word μ2 a w2 →
    ([∗ list] a' ∈ bv.seqBv a 4,
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) a'
        (DfracOwn 1) (memory_ram μ1 a')) ∗
    ([∗ list] a' ∈ bv.seqBv a 4,
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) a'
        (DfracOwn 1) (memory_ram μ2 a'))
    ⊢ interp_ptstomem (width := 4) (SyncVal a) (NonSyncVal w1 w2).
  Proof.
    iIntros (Hmhw1 Hmhw2) "[Hmem1 Hmem2]".
    destruct Hmhw1 as (v01 & v11 & v21 & v31 & Heqμ1 & Heqv1).
    destruct Hmhw2 as (v02 & v12 & v22 & v32 & Heqμ2 & Heqv2).
    unfold bv.seqBv, seqZ. change (seq 0 ?x) with [0;1;2;3].
    cbn -[bv.add interp_ptstomem word].
    iDestruct "Hmem1" as "(Hmem1a & Hmem1a1 & Hmem1a2 & Hmem1a3 & _)".
    iDestruct "Hmem2" as "(Hmem2a & Hmem2a1 & Hmem2a2 & Hmem2a3 & _)".
    inversion Heqμ1. subst v01 v11 v21 v31.
    inversion Heqμ2. subst v02 v12 v22 v32.
    rewrite <- Heqv1, <- Heqv2.
    iApply (intro_ptstomem_word_nonsync with
      "[$Hmem1a $Hmem1a1 $Hmem1a2 $Hmem1a3 $Hmem2a $Hmem2a1 $Hmem2a2 $Hmem2a3]").
  Qed.

  Lemma intro_ptsto_instr `{sailGS2 Σ} {μ1 μ2 : Memory} {a : Val ty_word} w {instr : AST} :
    mem_has_instr μ1 a w instr ->
    mem_has_instr μ2 a w instr ->   
    ([∗ list] a' ∈ bv.seqBv a 4,
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ1 a')) ∗
      ([∗ list] a' ∈ bv.seqBv a 4,
        @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ2 a'))
      ⊢ interp_ptsto_instr (SyncVal a) (SyncVal instr).
  Proof.
    iIntros ((Hmhw1 & Heq1) (Hmhw2 & Heq2)) "[Hmem1 Hmem2]".
    iExists (SyncVal w).
    iSplitL.
    { iApply (intro_ptstomem_word2 Hmhw1 Hmhw2). iFrame. }
    cbn. by rewrite Heq1.
  Qed.

  Lemma intro_ptsto_instrs `{sailGS2 Σ} {μ1 μ2 : Memory} {a : Val ty_word} ws {instrs : list AST} :
    (4 * N.of_nat (length instrs) + bv.bin a < lenAddr)%N  ->
      mem_has_instrs μ1 a ws instrs ->
      mem_has_instrs μ2 a ws instrs ->
      ([∗ list] a' ∈ bv.seqBv a (4 * N.of_nat (length instrs)),
        @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ1 a')) ∗
        ([∗ list] a' ∈ bv.seqBv a (4 * N.of_nat (length instrs)),
          @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ2 a'))
        ⊢ ptsto_instrs (SyncVal a) instrs.
  Proof.
    assert (word > 0) by now compute; Lia.lia.
    iIntros (Hrep Hmeminstrs1 Hmeminstrs2) "[Hmem1 Hmem2]".
    iInduction instrs as [|instr instrs] "IH" forall (a ws Hrep Hmeminstrs1 Hmeminstrs2).
    - done.
    - rewrite Nat2N.inj_succ in Hrep.
      fold (length instrs) in Hrep.
      replace (4 * N.of_nat (length (instr :: instrs)))%N with (4 + 4 * N.of_nat (length instrs))%N by (cbn; lia).
      rewrite bv.seqBv_app; try (cbn -[N.of_nat N.mul] in *; Lia.lia).
      rewrite big_opL_app.
      destruct ws.
      { inversion Hmeminstrs1; inversion Hmeminstrs2. }
      destruct Hmeminstrs1 as [Hinstr1 Hmeminstrs1].
      destruct Hmeminstrs2 as [Hinstr2 Hmeminstrs2].
      iDestruct "Hmem1" as "[Hmem1a Hmem1a4]".
      iDestruct "Hmem2" as "[Hmem2a Hmem2a4]".
      iSplitL "Hmem1a Hmem2a".
      + iApply (intro_ptsto_instr with "[$Hmem1a $Hmem2a]"); eauto.
      + cbn. rewrite (@bv.add_comm _ a bv_instrsize).
        replace minAddr with init_addr; auto.
        iApply ("IH" with "[%] [% //] [% //] [$Hmem1a4] [$Hmem2a4]").
        * rewrite bv.bin_add_small;
          cbn -[N.mul] in *.
          now Lia.lia.
          unfold lenAddr in Hrep. lia.
  Qed.

  Lemma instrsMemory `{sailGS2 Σ} {μ1 μ2 : Memory} ws instrs :
    (4 * N.of_nat (length instrs) < lenAddr)%N ->
    mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
    mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
    @mem_res2_without_leak _ sailGS2_memGS μ1 μ2 ⊢ |={⊤}=>
      ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs.
  Proof.
    iIntros (Hrep Hinit1 Hinit2) "Hmem".
    unfold mem_res2_without_leak, IrisInstance.RiscvPmpIrisAdeqParameters.mem_res_without_leak.
    replace liveAddrs with
      (bv.seqBv (n := 32) (bv.of_N minAddr) (4 * N.of_nat (length instrs)) ++
         bv.seqBv (n := 32) (bv.of_N minAddr + bv.of_N (4 * N.of_nat (length instrs))) (lenAddr - 4 * N.of_nat (length instrs))).
    2: { rewrite <- bv.seqBv_app. apply f_equal. lia. }
    iDestruct "Hmem" as "[[[Hinit1 Hrest1] Htr1] [[Hinit2 Hrest2] Htr2]]".
    iApply (intro_ptsto_instrs (μ1 := μ1) (μ2 := μ2)); eauto.
    { unfold init_addr. cbn. lia. }
    iFrame. auto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Public memory Iris predicates                                       *)
  (* ------------------------------------------------------------------ *)

  (* All data specs as NonSyncVal regardless of public flag.
     Used as the intermediate form produced by extracting raw bytes. *)
  Definition interp_mem_with_memory `{sailGS2 Σ}
      (μ1 μ2 : Memory) (specs : list mem_spec) : iProp Σ :=
    [∗ list] spec ∈ specs,
      let '(a, _) := spec in
      interp_ptstomem (width := 4) (SyncVal a)
        (NonSyncVal (get_word μ1 a) (get_word μ2 a)).

  (* Public specs use SyncVal (words must agree); private specs use NonSyncVal *)
  Definition interp_mem_with_public_memory `{sailGS2 Σ}
      (μ1 μ2 : Memory) (specs : list mem_spec) : iProp Σ :=
    [∗ list] spec ∈ specs,
      let '(a, pub) := (spec : mem_spec) in
      if pub
      then interp_ptstomem (width := 4) (SyncVal a) (SyncVal (get_word μ1 a))
      else interp_ptstomem (width := 4) (SyncVal a)
             (NonSyncVal (get_word μ1 a) (get_word μ2 a)).

  (* get_word always witnesses mem_has_word (the four bytes at a..a+3 assemble
     to exactly get_word μ a).  Proof requires unfolding bv.seqBv arithmetic. *)
  Lemma get_word_is_mem_has_word (μ : Memory) (a : Val ty_word) :
    mem_has_word μ a (get_word μ a).
  Proof.
    exists (memory_ram μ a), (memory_ram μ (bv.add bv.one a)),
           (memory_ram μ (bv.add (bv.of_N 2) a)), (memory_ram μ (bv.add (bv.of_N 3) a)).
    split; [| unfold get_word; reflexivity].
    enough (bv.seqBv a 4 = [a; bv.add bv.one a; bv.add (bv.of_N 2) a; bv.add (bv.of_N 3) a])
      as Hseq by now rewrite Hseq.
    unfold bv.seqBv, seqZ.
    change (Z.to_nat (Z.of_N 4)) with 4%nat.
    cbn [seq fmap list_fmap List.map].
    repeat f_equal.
    all: rewrite <- bv.of_Z_add, bv.of_Z_unsigned.
    - apply bv.add_zero_l.
    - change (1%nat : Z) with (Z.of_N 1). now rewrite bv.of_Z_N.
    - change (2%nat : Z) with (Z.of_N 2). now rewrite bv.of_Z_N.
    - change (3%nat : Z) with (Z.of_N 3). now rewrite bv.of_Z_N.
  Qed.

  (* Assembles interp_mem_with_memory from raw byte ownership, by induction
     over the spec list.  Direct analog of intro_ptsto_instrs for data memory. *)
  Lemma intro_mem_with_memory `{sailGS2 Σ} {μ1 μ2 : Memory} (a : bv word)
      (specs : list mem_spec) :
    (∀ i spec, specs !! i = Some spec →
      spec.1 = bv.add a (bv.of_N (4 * N.of_nat i))) →
    ([∗ list] a' ∈ bv.seqBv a (4 * N.of_nat (length specs)),
      @pointsto _ _ _ _ _
        (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) a'
        (DfracOwn 1) (memory_ram μ1 a')) ∗
    ([∗ list] a' ∈ bv.seqBv a (4 * N.of_nat (length specs)),
      @pointsto _ _ _ _ _
        (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) a'
        (DfracOwn 1) (memory_ram μ2 a'))
    ⊢ interp_mem_with_memory μ1 μ2 specs.
  Proof.
    iIntros (Haddrs) "[H1 H2]".
    iInduction specs as [| spec specs] "IH" forall (a Haddrs).
    { done. }
    destruct spec as [a_s pub].
    assert (Hlen : (4 * N.of_nat (length ((a_s, pub) :: specs)) =
                   4 + 4 * N.of_nat (length specs))%N).
    { cbn [length]. rewrite Nat2N.inj_succ. rewrite N.mul_succ_r. apply N.add_comm. }
    rewrite Hlen.
    rewrite (bv.seqBv_app (n := 32) a 4).
    rewrite !big_opL_app.
    iDestruct "H1" as "[H1h H1t]".
    iDestruct "H2" as "[H2h H2t]".
    cbn [interp_mem_with_memory big_opL].
    iSplitL "H1h H2h".
    { have Ha_s := Haddrs 0 (a_s, pub) eq_refl.
      cbn in Ha_s. rewrite bv.add_zero_r in Ha_s. subst a_s.
      iApply (intro_ptstomem_word2_nonsync (get_word_is_mem_has_word μ1 a)
                                            (get_word_is_mem_has_word μ2 a)).
      iFrame. }
    iApply ("IH" $! (a + bv.of_N 4)%bv with "[%] H1t H2t").
    intros i spec Hlook.
    pose proof (Haddrs (S i) spec Hlook) as Hsi.
    assert (H4 : (4 * N.of_nat (S i) = 4 + 4 * N.of_nat i)%N).
    { rewrite Nat2N.inj_succ. rewrite N.mul_succ_r. apply N.add_comm. }
    rewrite H4 in Hsi. rewrite <- bv.of_N_add in Hsi. rewrite bv.add_assoc in Hsi.
    exact Hsi.
  Qed.

  (* Extract both instruction memory AND data memory from mem_res2_without_leak.
     Data words must occupy the 4*|data_specs| bytes immediately following
     the instruction region (contiguous layout: instructions at [0, 4*n),
     data at [4*n, 4*n + 4*m)).

     The result is the "all-NonSyncVal" form interp_mem_with_memory.
     Use something_memory (outside AdequacyTools) to convert to the
     interp_mem_with_public_memory form.

     Uses intro_mem_with_memory (proved by induction over data_specs) for
     the data region, after a two-way bv.seqBv_app split. *)
  Lemma instrsAndDataMemory `{sailGS2 Σ} {μ1 μ2 : Memory} ws_instrs data_specs instrs :
    (4 * N.of_nat (length instrs) +
     4 * N.of_nat (length data_specs) < lenAddr)%N →
    mem_has_instrs μ1 (bv.of_N init_addr) ws_instrs instrs →
    mem_has_instrs μ2 (bv.of_N init_addr) ws_instrs instrs →
    (* data words are at init_addr + 4*|instrs|, init_addr + 4*|instrs| + 4, … *)
    (∀ i spec, data_specs !! i = Some spec →
      spec.1 = bv.of_N (init_addr + 4 * N.of_nat (length instrs)
                         + 4 * N.of_nat i)) →
    @mem_res2_without_leak _ sailGS2_memGS μ1 μ2 ⊢ |={⊤}=>
      ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs ∗
      interp_mem_with_memory μ1 μ2 data_specs.
  Proof.
    iIntros (Hlen HMem1 HMem2 HDataAddrs) "Hmem".
    unfold mem_res2_without_leak,
      IrisInstance.RiscvPmpIrisAdeqParameters.mem_res_without_leak.
    replace liveAddrs with
      (bv.seqBv (n := 32) (bv.of_N minAddr) (4 * N.of_nat (length instrs)) ++
         bv.seqBv (n := 32) (bv.of_N minAddr + bv.of_N (4 * N.of_nat (length instrs)))
                   (lenAddr - 4 * N.of_nat (length instrs))).
    2: { rewrite <- bv.seqBv_app. apply f_equal. lia. }
    iDestruct "Hmem" as "[[[Hinst1 Hrest1] Htr1] [[Hinst2 Hrest2] Htr2]]".
    iModIntro.
    iSplitL "Hinst1 Hinst2".
    - iApply (intro_ptsto_instrs (μ1 := μ1) (μ2 := μ2)); eauto.
      { unfold init_addr. cbn. lia. }
      iFrame.
    - have Hrep3 : (lenAddr - 4 * N.of_nat (length instrs) =
                     4 * N.of_nat (length data_specs) +
                     (lenAddr - 4 * N.of_nat (length instrs) -
                      4 * N.of_nat (length data_specs)))%N by lia.
      rewrite Hrep3.
      rewrite (bv.seqBv_app (n := 32)
                 (bv.of_N minAddr + bv.of_N (4 * N.of_nat (length instrs)))
                 (4 * N.of_nat (length data_specs))).
      rewrite !big_opL_app.
      iDestruct "Hrest1" as "[Hdata1 _]".
      iDestruct "Hrest2" as "[Hdata2 _]".
      iApply (intro_mem_with_memory
        (a := (bv.of_N minAddr + bv.of_N (4 * N.of_nat (length instrs)))%bv)).
      { intros i spec Hlook.
        have HDA := HDataAddrs i spec Hlook. rewrite HDA.
        unfold minAddr, init_addr. rewrite !bv.of_N_add. f_equal. }
      iFrame "Hdata1 Hdata2".
  Qed.

  (* Definition pcOutOfInstrs_WP2_loop `{sailGS2 Σ} instrs := *)
  (*   myWP2_loop *)
  (*   (∃ γ0 γ3 : RegStore, own_regstore2 γ0 γ3 ∗ *)
  (*                          ⌜pcOutOfInstrs (bv.of_N init_addr) instrs (read_register γ0 pc) *)
  (*                        ∨ pcOutOfInstrs (bv.of_N init_addr) instrs (read_register γ3 pc)⌝)%I. *)

  Definition pcOutOfInstrs_WP2_loop `{sailGS2 Σ} instrs :=
    myWP2_loop
      (∃ a, pc ↦ᵣ a ∗
                             ⌜pcOutOfInstrs (bv.of_N init_addr) instrs (ty.projLeft a)
                           ∨ pcOutOfInstrs (bv.of_N init_addr) instrs (ty.projRight a)⌝)%I.

  Definition exitCond_WP2_loop `{sailGS2 Σ} (exitCond : bv xlenbits -> bool) : iProp Σ :=
    myWP2_loop (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜exitCond v⌝)%I.

  Definition pcBehindInstrs_WP2_loop `{sailGS2 Σ} start instrs :=
    myWP2_loop
      (∃ γ0 γ3 : RegStore, own_regstore2 γ0 γ3 ∗
                             ⌜pcBehindInstrs start instrs (read_register γ0 pc)
                           ∨ pcBehindInstrs start instrs (read_register γ3 pc)⌝)%I.

    Import iris.base_logic.lib.iprop iris.proofmode.tactics.
    Import RiscvPmpIrisInstanceWithContracts.
    Import ProgramLogic.
    Import CHeapSpec CHeapSpec.notations.



    Lemma sound_exec_cfg_addr_myWP2
        {b exitCond fuel} (apc : RelVal ty_xlenbits)
        (ExitCondIprop : iProp Σ) Φ (h : SCHeap) :
      Katamaran.RiscvPmp.CFGVer.Verifier.cexec_cfg_addr b exitCond fuel apc Φ h →
      interpret_scheap h ∗ pc ↦ᵣ apc ∗ (∃ v, nextpc ↦ᵣ v) ∗
        Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs (SyncVal bv.zero) b ⊢
      (∀ an,
         ⌜match an with SyncVal v => exitCond v = true | NonSyncVal _ _ => False end⌝ ∗
         pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗
           Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs (SyncVal bv.zero) b ∗
         (∃ h', interpret_scheap h' ∧ ⌜Φ an h'⌝) -∗ ExitCondIprop) -∗
      myWP2_loop ExitCondIprop.
    Proof.
      revert apc h.
      induction fuel as [|n' IH]; intros apc h Hexec.
      - cbn [Katamaran.RiscvPmp.CFGVer.Verifier.cexec_cfg_addr CHeapSpec.error] in Hexec.
        contradiction.
      - destruct apc as [v|v1 v2].
        + cbn [Katamaran.RiscvPmp.CFGVer.Verifier.cexec_cfg_addr ty.RVToOption
               CHeapSpec.angelic_binary] in Hexec.
          destruct Hexec as [Hexit | Hexec].
          * destruct (exitCond v) eqn:Hexit_eq.
            -- cbn [CHeapSpec.pure] in Hexit.
               iIntros "(Hh & Hpc & Hnpc & Hinstrs) Hk".
               iApply exitCondImpliesMyWP2_loop.
               iApply ("Hk" $! (SyncVal v)).
               iSplit. { iPureIntro. exact Hexit_eq. }
               iFrame. iPureIntro. exact Hexit.
            -- cbn [CHeapSpec.error] in Hexit. contradiction.
          * destruct (Katamaran.RiscvPmp.CFGVer.Verifier.instrAligned v) eqn:Hmod.
            -- set (k := N.to_nat (bv.bin v) / bytes_per_instr) in *.
               destruct (List.nth_error b k) as [i|] eqn:Hnth.
               ++ unfold bind, CHeapSpec.bind in Hexec.
                  iIntros "(Hh & Hpc & Hnpc & Hinstrs) Hk".
                  unfold Katamaran.RiscvPmp.CFGVer.Verifier.instrAligned in Hmod.
                  apply Nat.eqb_eq in Hmod.
                  have Haddr : bv.add bv.zero (bv.of_N (N.of_nat (k * bytes_per_instr))) = v.
                  { have Hdiv : k * bytes_per_instr = N.to_nat (bv.bin v).
                    { have Hdm := Nat.div_mod (N.to_nat (bv.bin v)) bytes_per_instr.
                      unfold k, bytes_per_instr in *. lia. }
                    rewrite Hdiv. rewrite N2Nat.id. rewrite bv.of_N_bin.
                    rewrite bv.add_zero_l. reflexivity. }
                  iPoseProof (Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs_nth b k bv.zero Hnth
                    with "Hinstrs") as "[Hinstr Hframe]".
                  iEval (rewrite Haddr) in "Hinstr".
                  iEval (rewrite Haddr) in "Hframe".
                  rewrite {1}fixpoint_myWP2_loop_eq. unfold myWP2_loop_fix. iRight.
                  iApply (semWP2_mono with "[Hh Hnpc Hpc Hinstr]").
                  { iApply (Katamaran.RiscvPmp.CFGVer.Verifier.sound_exec_instruction Hexec). iFrame. }
                  iIntros ([v1|m1] δ1 [v2|m2] δ2); cbn.
                  2-3: iIntros "(%δ' & _ & HF)"; auto.
                  2: iIntros "_"; done.
                  iIntros "(%δ' & eqδ' & %rv & eqrv & ([%an (Hnpc' & Hpc' & (%h' & Hh' & %Hcfg & _))] & Hinstr' & _))".
                  iPoseProof ("Hframe" with "Hinstr'") as "Hinstrs'".
                  iModIntro.
                  iRevert "Hk".
                  iApply (IH an h' Hcfg).
                  iFrame "Hh' Hpc' Hinstrs'". iExists an. iExact "Hnpc'".
               ++ cbn [CHeapSpec.error] in Hexec. contradiction.
            -- cbn [CHeapSpec.error] in Hexec. contradiction.
        + cbn [Katamaran.RiscvPmp.CFGVer.Verifier.cexec_cfg_addr ty.RVToOption
               CHeapSpec.error] in Hexec.
          contradiction.
    Qed.

    Lemma sound_cexec_triple_addr_myWP2 {Γ : LCtx} {pre post b exitCond fuel}
        (ι : Valuation Γ) (ExitCondIprop : iProp Σ) :
      Katamaran.RiscvPmp.CFGVer.Verifier.cexec_triple_addr pre b exitCond fuel post (λ _ _, True) [] →
      ⊢ ∀ a : RelVal ty_xlenbits,
        asn.interpret pre ι.["a"∷ty_xlenbits ↦ a] ∗ ⌜secLeak a⌝ ∗
        pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗
        Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs (SyncVal bv.zero) b -∗
        (∀ an,
           ⌜match an with SyncVal v => exitCond v = true | NonSyncVal _ _ => False end⌝ ∗
           pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗
           Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs (SyncVal bv.zero) b -∗ ExitCondIprop) -∗
        myWP2_loop ExitCondIprop.
    Proof.
      cbv [Katamaran.RiscvPmp.CFGVer.Verifier.cexec_triple_addr bind demonic_ctx demonic
           CPureSpec.demonic lift_purespec].
      iIntros (Htrip a) "(Hpre & %HsLa & Hpc & Hnpc & Hinstrs) Hk".
      rewrite CPureSpec.wp_demonic_ctx in Htrip.
      specialize (Htrip ι a).
      apply produce_sound in Htrip.
      iPoseProof (Htrip with "[$] Hpre") as "(%h2 & [Hh2 %Hexec])". clear Htrip.
      iApply (sound_exec_cfg_addr_myWP2 a ExitCondIprop _ _ Hexec
        with "[$Hpc $Hnpc $Hinstrs $Hh2]").
      iIntros (an) "(%Hexit & Hpc & Hnpc & Hinstrs & _)".
      iApply ("Hk" $! an).
      iSplit. { iPureIntro. exact Hexit. }
      iFrame.
    Qed.

    Lemma sound_sblock_verification_condition_myWP2 {Γ pre post b exitCond fuel}
        (Hverif : safeE (postprocess (
            Katamaran.RiscvPmp.CFGVer.Verifier.sblock_verification_condition
              pre b exitCond fuel post wnil)))
        (ι : Valuation Γ) (ExitCond : iProp Σ) :
      ⊢ ∀ a : RelVal ty_xlenbits,
          asn.interpret pre (ι.["a"∷ty_xlenbits ↦ a]) ∗ ⌜secLeak a⌝ ∗
          pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗
          Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs (SyncVal bv.zero) b -∗
          (∀ an,
             ⌜match an with
               | SyncVal v => exitCond v = true
               | NonSyncVal _ _ => False
               end⌝ ∗
             pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗
             Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs (SyncVal bv.zero) b -∗
             ExitCond) -∗
          myWP2_loop ExitCond.
    Proof.
      apply (sound_cexec_triple_addr_myWP2 (post := post) (fuel := fuel) ι ExitCond).
      apply (safeE_safe env.nil), postprocess_sound in Hverif.
      apply LogicalSoundness.psafe_safe in Hverif; [|done].
      revert Hverif.
      apply Katamaran.RiscvPmp.CFGVer.Verifier.rexec_triple_addr.
      - easy. - easy. - easy. - constructor.
    Qed.

End AdequacyTools.

  (* ======================================================================== *)
  (* Iris-level verification chain                                             *)
  (*                                                                          *)
  (* cfg_instrs_pre instrs γ1 γ2:                                             *)
  (*   The Iris precondition for running the program in both worlds.          *)
  (*   = own_regstore2 γ1 γ2 ∗ ptsto_instrs 0 instrs ∗ interp_inv_constant_time *)
  (*   This says: we own both register stores and the instruction memory,     *)
  (*   and the constant-time invariant holds (leakage traces start equal).    *)
  (*                                                                          *)
  (* cfg_instrs_contract exitCond instrs γ1 γ2:                               *)
  (*   = cfg_instrs_pre -∗ exitCond_WP2_loop exitCond                        *)
  (*   The Iris statement: given preconditions, the loop terminates with      *)
  (*   exitCond firing on a SyncVal PC.                                       *)
  (*                                                                          *)
  (* Proof chain:                                                             *)
  (*   ValidCFGVerifierContract block                                         *)
  (*         ↓  [cfg_instrs_verified]                                        *)
  (*   ⊢ cfg_instrs_contract exitCond instrs γ1 γ2                           *)
  (*         ↓  [cfg_instrs_safe: uses interp_gprs_with_registers]           *)
  (*   interp_gprs_with_registers γ1 γ2 ∗ ... ⊢ exitCond_WP2_loop           *)
  (*         ↓  [cfg_instrs_endToEnd: adequacy + memory boilerplate]         *)
  (*   leakage_trace μ1' = leakage_trace μ2'                                  *)
  (*                                                                          *)
  (* cfg_instrs_verified vs cfg_instrs_safe:                                  *)
  (*   - cfg_instrs_verified: ImplPre is in the form used inside the proof   *)
  (*     of cfg_instrs_endToEnd (using interp_gprs_with_registers).          *)
  (*   - cfg_instrs_safe: ImplPre uses interp_gprs_with_public_registers      *)
  (*     (public entries as SyncVal), which is the PUBLIC-REGISTER-AWARE form.*)
  (*     Callers of cfg_instrs_endToEnd use this directly via HpubReg.       *)
  (*                                                                          *)
  (* Simplification opportunity:                                              *)
  (*   cfg_instrs_verified could be merged into cfg_instrs_safe (they differ *)
  (*   only in the register ownership form) by noting that both sides of      *)
  (*   something_registers commute.  Currently separate for clarity.          *)
  (* ======================================================================== *)
  Definition cfg_instrs_pre `{sailGS2 Σ} instrs γ1 γ2 : iProp Σ :=
    own_regstore2 γ1 γ2 ∗
      Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs
        (SyncVal (bv.of_N init_addr)) instrs ∗
      interp_inv_constant_time.

  Definition cfg_instrs_contract `{sailGS2 Σ} exitCond instrs γ1 γ2 :=
    (cfg_instrs_pre instrs γ1 γ2 -∗ exitCond_WP2_loop exitCond)%I.

  Lemma cfg_instrs_verified `{sailGS2 Σ} instrs' exitCond γ1 γ2 R (ι : Valuation R)
    (block : @CFGVerifierContract R)
    (valid_block : ValidCFGVerifierContract block)
    (blockInstrs : cfg_instrs block = instrs')
    (blockExitCond : cfg_exitCond block = exitCond)
    (ImplPre : interp_gprs_with_registers γ1 γ2 ∗
               cur_privilege ↦ᵣ ty.SyncVal Machine ∗
               interp_inv_constant_time -∗
               asn.interpret (extend_to_minimal_pre (cfg_precondition block))
                 ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⊢ cfg_instrs_contract exitCond instrs' γ1 γ2.
  Proof.
    iIntros (γ1curpriv γ2curpriv γ1pc γ2pc) "Hpre".
    iDestruct "Hpre" as "(Hregs & Hinstrs & #Hinv)".
    cbn.
    iDestruct "Hregs" as "(Hpc & Hnpc & Hstatus & Htvec & Hcause & Hepc & Hpriv & Hregs)".
    rewrite γ1curpriv γ1pc γ2curpriv γ2pc.
    rewrite !regPstsTo_sync_is_nonsync.
    unfold cfg_instrs_contract, exitCond_WP2_loop.
    destruct block.
    cbn in valid_block, blockInstrs, blockExitCond, ImplPre.
    subst cfg_instrs0 cfg_exitCond0.
    unfold Valid_CFG_VC, CFG_VC_triple in valid_block.
    iApply (sound_sblock_verification_condition_myWP2 valid_block ι _
              $! (SyncVal (bv.of_N init_addr))
              with "[Hpc Hnpc Hstatus Htvec Hcause Hepc Hpriv Hregs Hinstrs]").
    - iSplitL "Hpriv Hregs".
      + iApply ImplPre. iFrame "Hinv Hpriv".
        rewrite gprs_with_registers_equiv. cbn.
        repeat (iDestruct "Hregs" as "($ & Hregs)").
      + iSplit. { done. }
        iFrame.
    - iIntros (an) "(%Hexit & Hpc & Hnpc & Hinstrs)".
      destruct an as [v | v1 v2].
      + cbn in Hexit. iExists v. iFrame "Hpc". iPureIntro. rewrite Hexit. exact I.
      + contradiction.
  Qed.

  Lemma cfg_instrs_safe `{sailGS2 Σ} instrs' exitCond γ1 γ2 {R} {ι : Valuation R}
    (block : @CFGVerifierContract R)
    (valid_block : ValidCFGVerifierContract block)
    (blockInstrs : cfg_instrs block = instrs')
    (blockExitCond : cfg_exitCond block = exitCond)
    (ImplPre : interp_gprs_with_registers γ1 γ2 ∗
               cur_privilege ↦ᵣ ty.SyncVal Machine ∗
               interp_inv_constant_time -∗
               asn.interpret (extend_to_minimal_pre (cfg_precondition block))
                 ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⊢ own_regstore2 γ1 γ2 ∗
      Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs
        (SyncVal (bv.of_N init_addr)) instrs' ∗
      interp_inv_constant_time
    -∗ exitCond_WP2_loop exitCond.
  Proof.
    iIntros (γ1curpriv γ2curpriv γ1pc γ2pc) "H".
    iApply cfg_instrs_verified; eauto.
  Qed.

  Lemma cfg_instrs_verified_with_mem `{sailGS2 Σ} instrs' exitCond γ1 γ2
    {R} {ι : Valuation R}
    (data_specs : list mem_spec) (μ1 μ2 : Memory)
    (block : @CFGVerifierContract R)
    (valid_block : ValidCFGVerifierContract block)
    (blockInstrs : cfg_instrs block = instrs')
    (blockExitCond : cfg_exitCond block = exitCond)
    (ImplPre : interp_gprs_with_registers γ1 γ2 ∗
               interp_mem_with_public_memory μ1 μ2 data_specs ∗
               cur_privilege ↦ᵣ ty.SyncVal Machine ∗
               interp_inv_constant_time -∗
               asn.interpret (extend_to_minimal_pre (cfg_precondition block))
                 ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⊢ own_regstore2 γ1 γ2 ∗
      Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs
        (SyncVal (bv.of_N init_addr)) instrs' ∗
      interp_mem_with_public_memory μ1 μ2 data_specs ∗
      interp_inv_constant_time
    -∗ exitCond_WP2_loop exitCond.
  Proof.
    iIntros (γ1curpriv γ2curpriv γ1pc γ2pc) "Hpre".
    iDestruct "Hpre" as "(Hregs & Hinstrs & Hmem & #Hinv)".
    cbn.
    iDestruct "Hregs" as
      "(Hpc & Hnpc & Hstatus & Htvec & Hcause & Hepc & Hpriv & Hregs)".
    rewrite γ1curpriv γ1pc γ2curpriv γ2pc.
    rewrite !regPstsTo_sync_is_nonsync.
    unfold exitCond_WP2_loop.
    destruct block.
    cbn in valid_block, blockInstrs, blockExitCond, ImplPre.
    subst cfg_instrs0 cfg_exitCond0.
    unfold Valid_CFG_VC, CFG_VC_triple in valid_block.
    iApply (sound_sblock_verification_condition_myWP2 valid_block ι _
              $! (SyncVal (bv.of_N init_addr))
              with "[Hpc Hnpc Hstatus Htvec Hcause Hepc Hpriv Hregs Hinstrs Hmem]").
    - iSplitL "Hpriv Hregs Hmem".
      + iApply ImplPre. iFrame "Hinv Hpriv Hmem".
        rewrite gprs_with_registers_equiv. cbn.
        repeat (iDestruct "Hregs" as "($ & Hregs)").
      + iSplit. { done. }
        iFrame.
    - iIntros (an) "(%Hexit & Hpc & Hnpc & Hinstrs)".
      destruct an as [v | v1 v2].
      + cbn in Hexit. iExists v. iFrame "Hpc". iPureIntro. rewrite Hexit. exact I.
      + contradiction.
  Qed.

  Lemma cfg_instrs_safe_with_mem `{sailGS2 Σ} instrs' exitCond γ1 γ2
    {R} {ι : Valuation R}
    (data_specs : list mem_spec) (μ1 μ2 : Memory)
    (block : @CFGVerifierContract R)
    (valid_block : ValidCFGVerifierContract block)
    (blockInstrs : cfg_instrs block = instrs')
    (blockExitCond : cfg_exitCond block = exitCond)
    (ImplPre : interp_gprs_with_registers γ1 γ2 ∗
               interp_mem_with_public_memory μ1 μ2 data_specs ∗
               cur_privilege ↦ᵣ ty.SyncVal Machine ∗
               interp_inv_constant_time -∗
               asn.interpret (extend_to_minimal_pre (cfg_precondition block))
                 ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⊢ own_regstore2 γ1 γ2 ∗
      Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs
        (SyncVal (bv.of_N init_addr)) instrs' ∗
      interp_mem_with_public_memory μ1 μ2 data_specs ∗
      interp_inv_constant_time
    -∗ exitCond_WP2_loop exitCond.
  Proof.
    iIntros (γ1curpriv γ2curpriv γ1pc γ2pc) "H".
    iApply cfg_instrs_verified_with_mem; eauto.
  Qed.

    (* declare_public_registers γ1 γ2 list: both worlds agree on every
       register in `list`.  The list elements are sigma-typed: ⟨τ, r⟩ means
       register r of type τ.  Built from gen_public_regs for gen_contract.
       Proved by `constructor` for the empty list (not `Forall_nil _` — that
       is an iff lemma in stdpp, not a constructor). *)
    Definition declare_public_registers γ1 γ2 (public_registers : list {x : Ty & Reg x}) :=
      Forall
        (fun x => match x with
                  |existT x0 r => read_register γ1 r = read_register γ2 r
                  end)
        public_registers
    .

    Lemma something_registers `{sailGS2 Σ} {γ1 γ2} {public_registers : list {x : Ty & Reg x}}
      (HpubReg : declare_public_registers γ1 γ2 public_registers)
      : interp_gprs_with_registers γ1 γ2 ⊣⊢ interp_gprs_with_public_registers γ1 γ2 public_registers.
    Proof.
      unfold interp_gprs_with_public_registers, interp_gprs_with_registers, interp_ptsreg_with_public_registers, interp_ptsreg_with_registers.
      iSplit;
        iApply big_sepS_mono;
        intros x Hx;
        destruct (reg_convert x); auto.
    Qed.

  (* ------------------------------------------------------------------ *)
  (* Public memory equivalence: analogous to something_registers         *)
  (* ------------------------------------------------------------------ *)

  (* When declare_public_memory holds, the all-NonSyncVal representation
     interp_mem_with_memory is equivalent to interp_mem_with_public_memory.
     Proof: walk the spec list; for public entries use ptstomem_sync_is_nonsync
     (worlds agree by HpubMem so NonSyncVal w w = SyncVal w). *)
  Lemma something_memory `{sailGS2 Σ} μ1 μ2 (specs : list mem_spec)
      (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs specs)) :
    interp_mem_with_memory μ1 μ2 specs ⊣⊢
    interp_mem_with_public_memory μ1 μ2 specs.
  Proof.
    unfold interp_mem_with_memory, interp_mem_with_public_memory.
    iApply big_sepL_proper.
    intros k [a pub] Hspec.
    destruct pub; [|done].
    rewrite <- ptstomem_sync_is_nonsync.
    (* Need: get_word μ1 a = get_word μ2 a, i.e., a ∈ gen_public_addrs specs *)
    assert (Heq : get_word μ1 a = get_word μ2 a).
    { unfold declare_public_memory in HpubMem.
      rewrite Forall_forall in HpubMem.
      apply HpubMem.
      unfold gen_public_addrs.
      apply elem_of_list_omap.
      exists (a, true). split; [|done].
      now apply elem_of_list_lookup_2 with k. }
    rewrite Heq. done.
  Qed.

  (* Helper lemmas for declare_public_memory, analogous to the register ones *)
  Lemma declare_pub_mem_head_true a rest μ1 μ2 :
    declare_public_memory μ1 μ2 (gen_public_addrs ((a, true) :: rest)) →
    get_word μ1 a = get_word μ2 a.
  Proof.
    unfold declare_public_memory, gen_public_addrs. cbn.
    rewrite Forall_cons. tauto.
  Qed.

  Lemma declare_pub_mem_tail a pub rest μ1 μ2 :
    declare_public_memory μ1 μ2 (gen_public_addrs ((a, pub) :: rest)) →
    declare_public_memory μ1 μ2 (gen_public_addrs rest).
  Proof.
    unfold declare_public_memory, gen_public_addrs. cbn.
    destruct pub; cbn; [rewrite Forall_cons; tauto | done].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* gen_implpre: once-and-for-all ImplPre for gen_contract              *)
  (* (placed here: needs declare_public_registers + regPstsTo_sync)     *)
  (* ------------------------------------------------------------------ *)

  Lemma gen_reg_asn_of_ptsreg `{sailGS2 Σ}
      (r : RegIdx) (pub : bool) (γ1 γ2 : RegStore)
      (ι : Valuation ([ctx] ▻ "a"∷ty_xlenbits))
      (Heq : pub = true →
             ∀ x, reg_convert r = Some x →
               read_register γ1 x = read_register γ2 x) :
    interp_ptsreg_with_registers r γ1 γ2 ⊢
    asn.interpret (gen_reg_asn (r, pub)) ι.
  Proof.
    unfold interp_ptsreg_with_registers, gen_reg_asn.
    destruct (reg_convert r) as [x|] eqn:Hrc.
    - destruct pub.
      + specialize (Heq eq_refl x eq_refl) as Hval.
        rewrite <- Hval.
        unfold reg_pointsTo21.
        rewrite regPstsTo_sync_is_nonsync.
        iIntros "Hr".
        iExists (SyncVal (read_register γ1 x)).
        unfold asn_regidx_pts. rewrite Hrc. cbn. iFrame. done.
      + iIntros "Hr".
        iExists (NonSyncVal (read_register γ1 x) (read_register γ2 x)).
        unfold asn_regidx_pts. rewrite Hrc. cbn. iExact "Hr".
    - iIntros "_". iExists (SyncVal bv.zero).
      unfold asn_regidx_pts. rewrite Hrc.
      destruct pub; cbn; done.
  Qed.

  Lemma declare_pub_head_true r x rest γ1 γ2 :
    reg_convert r = Some x →
    declare_public_registers γ1 γ2 (gen_public_regs ((r, true) :: rest)) →
    read_register γ1 x = read_register γ2 x.
  Proof.
    intros Hrc Hpub.
    unfold declare_public_registers, gen_public_regs in Hpub.
    cbn in Hpub. rewrite Hrc in Hpub. cbn in Hpub.
    rewrite Forall_cons in Hpub. exact (proj1 Hpub).
  Qed.

  Lemma declare_pub_tail r pub rest γ1 γ2 :
    declare_public_registers γ1 γ2 (gen_public_regs ((r, pub) :: rest)) →
    declare_public_registers γ1 γ2 (gen_public_regs rest).
  Proof.
    intros Hpub.
    unfold declare_public_registers, gen_public_regs in Hpub |-*.
    cbn in Hpub |-*.
    destruct pub.
    - destruct (reg_convert r); cbn in Hpub |-*;
        [rewrite Forall_cons in Hpub; exact (proj2 Hpub) | exact Hpub].
    - exact Hpub.
  Qed.

  Lemma gen_implpre_inner `{sailGS2 Σ}
      (specs : list reg_spec) (γ1 γ2 : RegStore)
      (ι : Valuation ([ctx] ▻ "a"∷ty_xlenbits))
      (HpubReg : declare_public_registers γ1 γ2 (gen_public_regs specs))
      (HND : NoDup (map fst specs))
      (S : gset RegIdx)
      (HS : ∀ s, s ∈ specs → s.1 ∈ S) :
    ([∗ set] r ∈ S, interp_ptsreg_with_registers r γ1 γ2) ⊢
    asn.interpret (gen_pre specs) ι.
  Proof.
    iInduction specs as [|[r pub] rest] "IH"
        forall (HpubReg HND S HS).
    - simpl. iIntros "_". done.
    - simpl gen_pre. simpl asn.interpret.
      rewrite NoDup_cons in HND. destruct HND as [Hnotin HND].
      iIntros "H".
      iDestruct (big_sepS_delete with "H") as "[Hr Hrest]".
      { apply HS. apply elem_of_cons. left. done. }
      iSplitL "Hr".
      + iApply gen_reg_asn_of_ptsreg; [|iExact "Hr"].
        intros Hpub x Hrc. subst pub.
        by eapply declare_pub_head_true.
      + iApply ("IH" $! (declare_pub_tail r pub rest HpubReg)
                  HND (S ∖ {[r]}) with "[] [Hrest]").
        * iPureIntro.
          intros s Hs.
          rewrite elem_of_difference.
          split.
          -- apply HS. rewrite elem_of_cons. by right.
          -- rewrite elem_of_list_In in Hs.
             apply (in_map fst) in Hs.
             rewrite <- elem_of_list_In in Hs.
             intro Hcontr. rewrite elem_of_singleton in Hcontr.
             rewrite Hcontr in Hs. by apply Hnotin in Hs.
        * cbn. iFrame.
  Qed.

  Lemma gen_implpre `{sailGS2 Σ}
      (specs : list reg_spec) (γ1 γ2 : RegStore)
      (ι : Valuation ([ctx] ▻ "a"∷ty_xlenbits))
      (HpubReg : declare_public_registers γ1 γ2 (gen_public_regs specs))
      (HND : NoDup (map fst specs)) :
    interp_gprs_with_public_registers γ1 γ2 (gen_public_regs specs) ⊢
    asn.interpret (gen_pre specs) ι.
  Proof.
    rewrite <- (something_registers HpubReg).
    unfold interp_gprs_with_registers.
    apply gen_implpre_inner; [exact HpubReg | exact HND |].
    intros s _. unfold reg_file.
    apply elem_of_list_to_set, bv.finite.elem_of_enum.
  Qed.

  (* ======================================================================== *)
  (* cfg_instrs_endToEnd: the generic two-sided end-to-end lemma              *)
  (*                                                                          *)
  (* This is the main API for deriving the noninterference property from a    *)
  (* CFGVerifierContract.  Callers only need to supply ImplPre (the proof    *)
  (* that the Iris register ownership implies the contract precondition).     *)
  (*                                                                          *)
  (* Parameters:                                                              *)
  (*   HpubReg    : declare_public_registers γ1 γ2 public_registers          *)
  (*   block      : CFGVerifierContract (the contract)                        *)
  (*   valid_block: ValidCFGVerifierContract block (VC is true)               *)
  (*   ImplPre    : interp_gprs_with_public_registers ∗ cur_privilege ∗ inv  *)
  (*                  ⊢ asn.interpret (extend_to_minimal_pre pre) ι[a ↦ 0]  *)
  (*   Steps from both worlds (Heval1, Heval2)                               *)
  (*   Initial equal leakage (Htrace)                                         *)
  (*                                                                          *)
  (* Conclusion: leakage_trace μ1' = leakage_trace μ2'                        *)
  (*                                                                          *)
  (* Internal proof structure:                                                *)
  (*   apply (adequacy_gen_RiscVNStepsExitCond steps1 steps2)                *)
  (*   iMod (instrsMemory ...) to extract ptsto_instrs                       *)
  (*   iApply (cfg_instrs_safe γ1 γ2 block) — uses ImplPre                  *)
  (*   Close leakage-trace goal via trace_full_frag_eq                        *)
  (*                                                                          *)
  (* Call pattern (use @ to bypass Set Implicit Arguments):                   *)
  (*   eapply (@cfg_instrs_endToEnd γ1 γ2 γ1' γ2' μ1 μ2 μ1' μ2'            *)
  (*     instrs exitCond n ws [ctx] [env] public_registers HpubReg block     *)
  (*     valid_block eq_refl eq_refl).                                        *)
  (*   all: try eauto.  (* before bullet goals, handles routine subgoals *)  *)
  (*                                                                          *)
  (* Potential simplification: the proof body of cfg_instrs_endToEnd_strong  *)
  (* is nearly identical; a refactored helper lemma could deduplicate them.  *)
  (*                                                                          *)
  (* Future work: generalise from init_addr = 0 to arbitrary start address.  *)
  (* ======================================================================== *)
    Lemma cfg_instrs_endToEnd {γ1 γ2 γ1' γ2' : RegStore} {μ1 μ2 μ1' μ2' : Memory}
      instrs' exitCond n ws {R} {ι : Valuation R}
      public_registers
      (HpubReg : declare_public_registers γ1 γ2 public_registers)
      (block : @CFGVerifierContract R)
      (valid_block : ValidCFGVerifierContract block)
      (blockInstrs : cfg_instrs block = instrs')
      (blockExitCond : cfg_exitCond block = exitCond)
      (ImplPre : forall `{sailGS2 Σ},
          interp_gprs_with_public_registers γ1 γ2 public_registers ∗
          cur_privilege ↦ᵣ ty.SyncVal Machine ∗
          interp_inv_constant_time -∗
          asn.interpret (extend_to_minimal_pre (cfg_precondition block))
            ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
      (4 * N.of_nat (length instrs') < lenAddr)%N ->
      mem_has_instrs μ1 (bv.of_N init_addr) ws instrs' ->
      mem_has_instrs μ2 (bv.of_N init_addr) ws instrs' ->
      RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
      RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
      RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
      RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
      ⟨ γ1, μ1 ⟩ -(exitCond, n)->* ⟨ γ1', μ1' ⟩ ->
      ⟨ γ2, μ2 ⟩ -(exitCond, n)->* ⟨ γ2', μ2' ⟩ ->
      leakage_trace μ1 = leakage_trace μ2 ->
      leakage_trace μ1' = leakage_trace μ2'.
    Proof.
      intros Hleninstrs μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc
        steps1 steps2 Htrace.
      apply (adequacy_gen_RiscVNStepsExitCond (μ21 := μ2) (γ21 := γ2)
        _ steps1 steps2).
      iIntros (Σ' H').
      iIntros "(Hmem & H')".
      iPoseProof (mem_res2_split_leak with "Hmem") as "(Hmem & Hleak)".
      iPoseProof (constant_time_from_mem_res2_only_leak with "Hleak")
        as "Hinv"; auto.
      iMod "Hinv" as "#Hinv".
      iMod (instrsMemory with "Hmem") as "H"; eauto.
      iSplitR "".
      - iApply (cfg_instrs_safe γ1 γ2 block).
        all: eauto.
        iIntros "(Hregs & Hpriv & #Hinv')".
        iApply ImplPre.
        iFrame "∗ #".
        by iFrame "∗ #".
      - iModIntro.
        iIntros "Rmem".
        iInv "Hinv" as "Hleak".
        iPoseProof (mem_inv2_split_leak with "Rmem") as "(Rmem & [Htr1 Htr2])".
        unfold mem_inv_only_leak.
        iMod "Hleak".
        iDestruct "Hleak" as "[%t [Hfrag1 Hfrag2]]".
        iDestruct (trace.trace_full_frag_eq with "Htr1 Hfrag1") as "->".
        iDestruct (trace.trace_full_frag_eq with "Htr2 Hfrag2") as "->".
        iModIntro. iFrame.
        iApply fupd_mask_intro; first set_solver.
        now iIntros "_".
    Qed.

  (* ======================================================================== *)
  (* cfg_instrs_endToEnd_strong: the one-sided end-to-end lemma  [ADMITTED]  *)
  (*                                                                          *)
  (* Same as cfg_instrs_endToEnd but takes ONLY world-1's execution trace.   *)
  (* Conclusion: ∃ γ2' μ2', ⟨γ2, μ2⟩ -(exitCond, n)->* ⟨γ2', μ2'⟩         *)
  (*              ∧ leakage_trace μ1' = leakage_trace μ2'                    *)
  (*                                                                          *)
  (* pc_init_sync (eq_trans γ1pc (eq_sym γ2pc)) is derived from the          *)
  (* hypotheses that both worlds start at bv.of_N init_addr.  No external    *)
  (* pc_step_sync is needed — PC-sync is threaded through                    *)
  (* semWP2_preservation_fwd' at each step.                                   *)
  (*                                                                          *)
  (* Proof body is complete modulo adequacy_gen_RiscVNStepsExitCond_strong.  *)
  (* ======================================================================== *)
  (* Termination-sensitive variant: only world-1's execution is given as
     input; world-2's execution and the leakage conclusion are derived. *)
    Lemma cfg_instrs_endToEnd_strong
        {γ1 γ2 γ1' : RegStore} {μ1 μ2 μ1' : Memory}
        instrs' exitCond n ws {R} {ι : Valuation R}
        public_registers
        (HpubReg : declare_public_registers γ1 γ2 public_registers)
        (block : @CFGVerifierContract R)
        (valid_block : ValidCFGVerifierContract block)
        (blockInstrs : cfg_instrs block = instrs')
        (blockExitCond : cfg_exitCond block = exitCond)
        (ImplPre : forall `{sailGS2 Σ},
            interp_gprs_with_public_registers γ1 γ2 public_registers ∗
            cur_privilege ↦ᵣ ty.SyncVal Machine ∗
            interp_inv_constant_time -∗
            asn.interpret (extend_to_minimal_pre (cfg_precondition block))
              ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
        (4 * N.of_nat (length instrs') < lenAddr)%N ->
        mem_has_instrs μ1 (bv.of_N init_addr) ws instrs' ->
        mem_has_instrs μ2 (bv.of_N init_addr) ws instrs' ->
        RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
        RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
        RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
        RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
        ⟨γ1, μ1⟩ -(exitCond, n)->* ⟨γ1', μ1'⟩ ->
        leakage_trace μ1 = leakage_trace μ2 ->
        ∃ γ2' μ2',
          ⟨γ2, μ2⟩ -(exitCond, n)->* ⟨γ2', μ2'⟩ ∧
          leakage_trace μ1' = leakage_trace μ2'.
    Proof.
      intros Hleninstrs μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc
        steps1 Htrace.
      apply (@adequacy_gen_RiscVNStepsExitCond_strong
        n exitCond γ1 γ1' γ2 μ1 μ1' μ2
        (eq_trans γ1pc (eq_sym γ2pc))
        (fun _ μ2' => leakage_trace μ1' = leakage_trace μ2')
        steps1).
      iIntros (Σ' H').
      iIntros "(Hmem & H')".
      iPoseProof (mem_res2_split_leak with "Hmem") as "(Hmem & Hleak)".
      iPoseProof (constant_time_from_mem_res2_only_leak with "Hleak")
        as "Hinv"; auto.
      iMod "Hinv" as "#Hinv".
      iMod (instrsMemory with "Hmem") as "H"; eauto.
      iSplitR "".
      - iApply (cfg_instrs_safe γ1 γ2 block).
        all: eauto.
        iIntros "(Hregs & Hpriv & #Hinv')".
        iApply ImplPre.
        iFrame "∗ #".
        by iFrame "∗ #".
      - iModIntro.
        iIntros (γ22 μ22) "Rmem".
        iInv "Hinv" as "Hleak".
        iPoseProof (mem_inv2_split_leak with "Rmem") as "(Rmem & [Htr1 Htr2])".
        unfold mem_inv_only_leak.
        iMod "Hleak".
        iDestruct "Hleak" as "[%t [Hfrag1 Hfrag2]]".
        iDestruct (trace.trace_full_frag_eq with "Htr1 Hfrag1") as "->".
        iDestruct (trace.trace_full_frag_eq with "Htr2 Hfrag2") as "->".
        iModIntro. iFrame.
        iApply fupd_mask_intro; first set_solver.
        now iIntros "_".
    Qed.

  (* ------------------------------------------------------------------ *)
  (* cfg_instrs_endToEnd_with_memory                                     *)
  (* Like cfg_instrs_endToEnd, but also passes data memory ownership     *)
  (* to ImplPre via interp_mem_with_public_memory.                       *)
  (* data_specs describes the data words at init_addr + 4*|instrs| + …  *)
  (* (contiguous layout immediately after the instruction region).       *)
  (* ------------------------------------------------------------------ *)
    Lemma cfg_instrs_endToEnd_with_memory
        {γ1 γ2 γ1' γ2' : RegStore} {μ1 μ2 μ1' μ2' : Memory}
        instrs' exitCond n ws_instrs {R} {ι : Valuation R}
        public_registers
        (HpubReg : declare_public_registers γ1 γ2 public_registers)
        data_specs
        (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs data_specs))
        (block : @CFGVerifierContract R)
        (valid_block : ValidCFGVerifierContract block)
        (blockInstrs : cfg_instrs block = instrs')
        (blockExitCond : cfg_exitCond block = exitCond)
        (HDataAddrs : ∀ i spec, data_specs !! i = Some spec →
            spec.1 = bv.of_N (init_addr + 4 * N.of_nat (length instrs')
                               + 4 * N.of_nat i))
        (ImplPre : forall `{sailGS2 Σ},
            interp_gprs_with_public_registers γ1 γ2 public_registers ∗
            interp_mem_with_public_memory μ1 μ2 data_specs ∗
            cur_privilege ↦ᵣ ty.SyncVal Machine ∗
            interp_inv_constant_time -∗
            asn.interpret (extend_to_minimal_pre (cfg_precondition block))
              ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
        (4 * N.of_nat (length instrs') +
         4 * N.of_nat (length data_specs) < lenAddr)%N →
        mem_has_instrs μ1 (bv.of_N init_addr) ws_instrs instrs' →
        mem_has_instrs μ2 (bv.of_N init_addr) ws_instrs instrs' →
        RiscvPmpProgram.read_register γ1 cur_privilege = Machine →
        RiscvPmpProgram.read_register γ2 cur_privilege = Machine →
        RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr →
        RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr →
        ⟨ γ1, μ1 ⟩ -(exitCond, n)->* ⟨ γ1', μ1' ⟩ →
        ⟨ γ2, μ2 ⟩ -(exitCond, n)->* ⟨ γ2', μ2' ⟩ →
        leakage_trace μ1 = leakage_trace μ2 →
        leakage_trace μ1' = leakage_trace μ2'.
    Proof.
      intros Hlen μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc
        steps1 steps2 Htrace.
      apply (adequacy_gen_RiscVNStepsExitCond (μ21 := μ2) (γ21 := γ2)
        _ steps1 steps2).
      iIntros (Σ' H').
      iIntros "(Hmem & H')".
      iPoseProof (mem_res2_split_leak with "Hmem") as "(Hmem & Hleak)".
      iPoseProof (constant_time_from_mem_res2_only_leak with "Hleak")
        as "Hinv"; auto.
      iMod "Hinv" as "#Hinv".
      (* Extract instruction + data memory from raw byte ownership *)
      iMod (instrsAndDataMemory ws_instrs data_specs instrs' with "Hmem") as "[H Hmemdata]";
        [exact Hlen | exact μinit1 | exact μinit2 | exact HDataAddrs |].
      (* Convert all-NonSyncVal to public form *)
      rewrite (something_memory data_specs HpubMem).
      iSplitR "".
      - iApply (cfg_instrs_safe_with_mem γ1 γ2 data_specs μ1 μ2 block).
        all: eauto.
        iIntros "(Hregs & Hmem & Hpriv & #Hinv')".
        iApply ImplPre.
        rewrite <- (something_registers HpubReg).
        iFrame "Hmem ∗ #".
        by iFrame "∗ #".
      - iModIntro.
        iIntros "Rmem".
        iInv "Hinv" as "Hleak".
        iPoseProof (mem_inv2_split_leak with "Rmem") as "(Rmem & [Htr1 Htr2])".
        unfold mem_inv_only_leak.
        iMod "Hleak".
        iDestruct "Hleak" as "[%t [Hfrag1 Hfrag2]]".
        iDestruct (trace.trace_full_frag_eq with "Htr1 Hfrag1") as "->".
        iDestruct (trace.trace_full_frag_eq with "Htr2 Hfrag2") as "->".
        iModIntro. iFrame.
        iApply fupd_mask_intro; first set_solver.
        now iIntros "_".
    Qed.

  (* ------------------------------------------------------------------ *)
  (* cfg_instrs_endToEnd_with_memory_strong                              *)
  (* One-sided (termination-sensitive) variant of                        *)
  (* cfg_instrs_endToEnd_with_memory.  Takes ONLY world-1's execution    *)
  (* trace; concludes ∃ γ2' μ2', ⟨γ2,μ2⟩ -(exitCond,n)->* ⟨γ2',μ2'⟩  *)
  (*   ∧ leakage_trace μ1' = leakage_trace μ2'.                         *)
  (* ------------------------------------------------------------------ *)
    Lemma cfg_instrs_endToEnd_with_memory_strong
        {γ1 γ2 γ1' : RegStore} {μ1 μ2 μ1' : Memory}
        instrs' exitCond n ws_instrs {R} {ι : Valuation R}
        public_registers
        (HpubReg : declare_public_registers γ1 γ2 public_registers)
        data_specs
        (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs data_specs))
        (block : @CFGVerifierContract R)
        (valid_block : ValidCFGVerifierContract block)
        (blockInstrs : cfg_instrs block = instrs')
        (blockExitCond : cfg_exitCond block = exitCond)
        (HDataAddrs : ∀ i spec, data_specs !! i = Some spec →
            spec.1 = bv.of_N (init_addr + 4 * N.of_nat (length instrs')
                               + 4 * N.of_nat i))
        (ImplPre : forall `{sailGS2 Σ},
            interp_gprs_with_public_registers γ1 γ2 public_registers ∗
            interp_mem_with_public_memory μ1 μ2 data_specs ∗
            cur_privilege ↦ᵣ ty.SyncVal Machine ∗
            interp_inv_constant_time -∗
            asn.interpret (extend_to_minimal_pre (cfg_precondition block))
              ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
        (4 * N.of_nat (length instrs') +
         4 * N.of_nat (length data_specs) < lenAddr)%N →
        mem_has_instrs μ1 (bv.of_N init_addr) ws_instrs instrs' →
        mem_has_instrs μ2 (bv.of_N init_addr) ws_instrs instrs' →
        RiscvPmpProgram.read_register γ1 cur_privilege = Machine →
        RiscvPmpProgram.read_register γ2 cur_privilege = Machine →
        RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr →
        RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr →
        ⟨ γ1, μ1 ⟩ -(exitCond, n)->* ⟨ γ1', μ1' ⟩ →
        leakage_trace μ1 = leakage_trace μ2 →
        ∃ γ2' μ2',
          ⟨ γ2, μ2 ⟩ -(exitCond, n)->* ⟨ γ2', μ2' ⟩ ∧
          leakage_trace μ1' = leakage_trace μ2'.
    Proof.
      intros Hlen μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc
        steps1 Htrace.
      apply (@adequacy_gen_RiscVNStepsExitCond_strong
        n exitCond γ1 γ1' γ2 μ1 μ1' μ2
        (eq_trans γ1pc (eq_sym γ2pc))
        (fun _ μ2' => leakage_trace μ1' = leakage_trace μ2')
        steps1).
      iIntros (Σ' H').
      iIntros "(Hmem & H')".
      iPoseProof (mem_res2_split_leak with "Hmem") as "(Hmem & Hleak)".
      iPoseProof (constant_time_from_mem_res2_only_leak with "Hleak")
        as "Hinv"; auto.
      iMod "Hinv" as "#Hinv".
      (* Extract instruction + data memory from raw byte ownership *)
      iMod (instrsAndDataMemory ws_instrs data_specs instrs' with "Hmem") as "[H Hmemdata]";
        [exact Hlen | exact μinit1 | exact μinit2 | exact HDataAddrs |].
      (* Convert all-NonSyncVal to public form *)
      rewrite (something_memory data_specs HpubMem).
      iSplitR "".
      - iApply (cfg_instrs_safe_with_mem γ1 γ2 data_specs μ1 μ2 block).
        all: eauto.
        iIntros "(Hregs & Hmem & Hpriv & #Hinv')".
        iApply ImplPre.
        rewrite <- (something_registers HpubReg).
        iFrame "Hmem ∗ #".
        by iFrame "∗ #".
      - iModIntro.
        iIntros (γ22 μ22) "Rmem".
        iInv "Hinv" as "Hleak".
        iPoseProof (mem_inv2_split_leak with "Rmem") as "(Rmem & [Htr1 Htr2])".
        unfold mem_inv_only_leak.
        iMod "Hleak".
        iDestruct "Hleak" as "[%t [Hfrag1 Hfrag2]]".
        iDestruct (trace.trace_full_frag_eq with "Htr1 Hfrag1") as "->".
        iDestruct (trace.trace_full_frag_eq with "Htr2 Hfrag2") as "->".
        iModIntro. iFrame.
        iApply fupd_mask_intro; first set_solver.
        now iIntros "_".
    Qed.

  Lemma swap_endToEnd {γ1 γ2 γ1' : RegStore} {μ1 μ2 μ1' : Memory} n ws :
    let instrs := [MV X3 X2; MV X2 X1; MV X1 X3] in
    mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
    mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
    RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
    ⟨ γ1, μ1 ⟩ -(pcOutOfInstrs_exitCond instrs, n)->* ⟨ γ1', μ1' ⟩ ->
    leakage_trace μ1 = leakage_trace μ2 ->
    ∃ γ2' μ2',
      ⟨ γ2, μ2 ⟩ -(pcOutOfInstrs_exitCond instrs, n)->* ⟨ γ2', μ2' ⟩ ∧
      leakage_trace μ1' = leakage_trace μ2'.
  Proof.
    intros instrs μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc steps1 Htrace.
    assert (HpubReg : declare_public_registers γ1 γ2 []) by constructor.
    assert (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs [])) by constructor.
    eapply (@cfg_instrs_endToEnd_with_memory_strong γ1 γ2 γ1' μ1 μ2 μ1'
      instrs (pcOutOfInstrs_exitCond instrs) n ws
      ["x"::ty_xlenbits; "y"::ty_xlenbits]
      [env].["x"::ty_xlenbits ↦
        NonSyncVal (read_register γ1 x1) (read_register γ2 x1)].["y"::ty_xlenbits ↦
        NonSyncVal (read_register γ1 x2) (read_register γ2 x2)]
      [] HpubReg [] HpubMem swap_cfg_contract valid_swap_cfg_contract eq_refl eq_refl).
    all: try eauto.
    - intros i spec H. inversion H.
    - intros Σ H.
      iIntros "(Hregs & Hmem & Hpriv & #Hinv)". iClear "Hmem".
      cbn.
      iFrame "Hpriv Hinv".
      rewrite <- (something_registers HpubReg).
      rewrite gprs_with_registers_equiv. cbn.
      repeat (iDestruct "Hregs" as "($ & Hregs)").
      auto.
    - cbn. by unfold lenAddr.
  Qed.

  Lemma jumpIfZero_endToEnd {γ1 γ2 γ1' : RegStore} {μ1 μ2 μ1' : Memory} n ws
    (HpubReg : declare_public_registers γ1 γ2 [existT ty_xlenbits x1]) :
    let instrs := [BEQ X1 X0 true_offset] in
    mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
    mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
    RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
    ⟨ γ1, μ1 ⟩ -(pcOutOfInstrs_exitCond instrs, n)->* ⟨ γ1', μ1' ⟩ ->
    leakage_trace μ1 = leakage_trace μ2 ->
    ∃ γ2' μ2',
      ⟨ γ2, μ2 ⟩ -(pcOutOfInstrs_exitCond instrs, n)->* ⟨ γ2', μ2' ⟩ ∧
      leakage_trace μ1' = leakage_trace μ2'.
  Proof.
    intros instrs μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc steps1 Htrace.
    assert (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs [])) by constructor.
    eapply (@cfg_instrs_endToEnd_with_memory_strong γ1 γ2 γ1' μ1 μ2 μ1'
      instrs (pcOutOfInstrs_exitCond instrs) n ws
      ["x1"::ty_xlenbits]
      [env].["x1"::ty_xlenbits ↦ SyncVal (read_register γ1 x1)]
      [existT ty_xlenbits x1] HpubReg [] HpubMem jump_if_zero_cfg_contract
      valid_jump_if_zero_cfg_contract eq_refl eq_refl).
    all: try eauto.
    - intros i spec H. inversion H.
    - intros Σ H.
      iIntros "(Hregs & Hmem & Hpriv & #Hinv)". iClear "Hmem".
      cbn.
      iFrame "Hpriv Hinv".
      assert (Hx1 : read_register γ1 x1 = read_register γ2 x1). {
        unfold declare_public_registers in HpubReg.
        rewrite Forall_singleton in HpubReg. exact HpubReg. }
      rewrite <- (something_registers HpubReg).
      rewrite gprs_with_registers_equiv. cbn.
      rewrite Hx1. rewrite regPstsTo_sync_is_nonsync.
      iDestruct "Hregs" as "($ & Hregs)".
      done.
    - cbn. by unfold lenAddr.
  Qed.

  Lemma jmp_fwd_safe_cfg `{sailGS2 Σ} γ1 γ2 :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
    RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
    ⊢ cfg_instrs_contract jmp_fwd_exitCond [JAL X0 jmp_offset; NOP] γ1 γ2.
  Proof.
    intros γ1curpriv γ2curpriv γ1pc γ2pc.
    unfold cfg_instrs_contract, cfg_instrs_pre, exitCond_WP2_loop.
    iIntros "(Hregs & Hinstrs & #Hinv)".
    cbn.
    iDestruct "Hregs" as
      "(Hpc & Hnpc & Hstatus & Htvec & Hcause & Hepc & Hpriv & Hregs)".
    rewrite γ1curpriv γ1pc γ2curpriv γ2pc.
    rewrite !regPstsTo_sync_is_nonsync.
    iApply (sound_sblock_verification_condition_myWP2 valid_jmp_fwd_cfg_contract [env] _
              $! (SyncVal (bv.of_N init_addr))
              with "[Hpc Hnpc Hstatus Htvec Hcause Hepc Hpriv Hregs Hinstrs]").
    - iSplitL "Hpriv".
      + cbn. iSplit. { iPureIntro. split; [reflexivity | trivial]. }
        iFrame "∗ #".
      + iFrame "Hpc". iSplitL "Hnpc". { iExists _. iExact "Hnpc". }
        iExact "Hinstrs".
    - iIntros (an) "(%Hexit & Hpc & Hnpc & Hinstrs & Hpost)".
      destruct an as [v | vl vr].
      + cbn in Hexit. iExists v. iFrame "Hpc". iPureIntro. rewrite Hexit. exact I.
      + contradiction.
  Qed.

  Lemma jmp_fwd_endToEnd_cfg {γ1 γ2 γ1' : RegStore} {μ1 μ2 μ1' : Memory} n ws
  (HpubReg : declare_public_registers γ1 γ2 [existT ty_xlenbits x1]) :
    let instrs := [JAL X0 jmp_offset; NOP] in
    mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
    mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
    RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
    ⟨ γ1, μ1 ⟩ -(jmp_fwd_exitCond, n)->* ⟨ γ1', μ1' ⟩ ->
    leakage_trace μ1 = leakage_trace μ2 ->
    ∃ γ2' μ2',
      ⟨ γ2, μ2 ⟩ -(jmp_fwd_exitCond, n)->* ⟨ γ2', μ2' ⟩ ∧
      leakage_trace μ1' = leakage_trace μ2'.
  Proof.
    intros instrs μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc steps1 Htrace.
    assert (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs [])) by constructor.
    eapply (@cfg_instrs_endToEnd_with_memory_strong γ1 γ2 γ1' μ1 μ2 μ1'
      instrs jmp_fwd_exitCond n ws [ctx] [env]
      [existT ty_xlenbits x1] HpubReg [] HpubMem jmp_fwd_cfg_contract
      valid_jmp_fwd_cfg_contract eq_refl eq_refl).
    all: try eauto.
    - intros i spec H. inversion H.
    - intros Σ H.
      cbn.
      iIntros "(Hregs & Hmem & Hpriv & #Hinv)". iClear "Hmem".
      iSplitL "".
      + iPureIntro. split; [reflexivity | done].
      + iFrame "∗ #".
    - cbn. by unfold lenAddr.
  Qed.

  Lemma jmp_fwd_endToEnd_cfg_gen {γ1 γ2 γ1' : RegStore} {μ1 μ2 μ1' : Memory} n ws :
    let instrs := [JAL X0 jmp_offset; NOP] in
    mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
    mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
    RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
    ⟨ γ1, μ1 ⟩ -(jmp_fwd_exitCond, n)->* ⟨ γ1', μ1' ⟩ ->
    leakage_trace μ1 = leakage_trace μ2 ->
    ∃ γ2' μ2',
      ⟨ γ2, μ2 ⟩ -(jmp_fwd_exitCond, n)->* ⟨ γ2', μ2' ⟩ ∧
      leakage_trace μ1' = leakage_trace μ2'.
  Proof.
    intros instrs μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc steps1 Htrace.
    assert (HpubReg : declare_public_registers γ1 γ2 []) by constructor.
    assert (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs [])) by constructor.
    eapply (@cfg_instrs_endToEnd_with_memory_strong γ1 γ2 γ1' μ1 μ2 μ1'
      instrs jmp_fwd_exitCond n ws [ctx] [env]
      [] HpubReg [] HpubMem jmp_fwd_cfg_contract_gen
      valid_jmp_fwd_cfg_contract_gen eq_refl eq_refl).
    all: try eauto.
    - intros i spec H. inversion H.
    - intros Σ H.
      iIntros "(Hregs & Hmem & Hpriv & #Hinv)". iClear "Hmem".
      cbn. iFrame "∗ #".
      iSplit; (iSplit; [iPureIntro | done]).
      all: vm_compute; done.
    - cbn. by unfold lenAddr.
  Qed.
  
  Lemma countdown_endToEnd {γ1 γ2 γ1' : RegStore}
      {μ1 μ2 μ1' : Memory} n ws
      (HpubReg : declare_public_registers γ1 γ2 [existT ty_xlenbits x1])
      (Hx1_1 : RiscvPmpProgram.read_register γ1 x1 = bv.of_N 2)
      (Hx1_2 : RiscvPmpProgram.read_register γ2 x1 = bv.of_N 2) :
    let instrs := [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset] in
    mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
    mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
    RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
    ⟨ γ1, μ1 ⟩ -(countdown_exitCond, n)->* ⟨ γ1', μ1' ⟩ ->
    leakage_trace μ1 = leakage_trace μ2 ->
    ∃ γ2' μ2',
      ⟨ γ2, μ2 ⟩ -(countdown_exitCond, n)->* ⟨ γ2', μ2' ⟩ ∧
      leakage_trace μ1' = leakage_trace μ2'.
  Proof.
    intros instrs μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc steps1 Htrace.
    assert (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs [])) by constructor.
    eapply (@cfg_instrs_endToEnd_with_memory_strong γ1 γ2 γ1' μ1 μ2 μ1'
      instrs countdown_exitCond n ws [ctx] [env]
      [existT ty_xlenbits x1] HpubReg [] HpubMem countdown_cfg_contract
      valid_countdown_cfg_contract eq_refl eq_refl).
    all: try eauto.
    - intros i spec H. inversion H.
    - intros Σ H.
      iIntros "(Hregs & Hmem & Hpriv & #Hinv)". iClear "Hmem".
      cbn.
      iFrame "Hpriv Hinv".
      assert (Hx1_eq : read_register γ1 x1 = read_register γ2 x1) by congruence.
      rewrite <- (something_registers HpubReg).
      rewrite gprs_with_registers_equiv. cbn.
      rewrite Hx1_eq. rewrite regPstsTo_sync_is_nonsync. rewrite Hx1_2.
      iDestruct "Hregs" as "($ & Hregs)".
      iSplit; [iPureIntro | done].
      vm_compute. done.
    - cbn. by unfold lenAddr.
  Qed.

  Lemma countdown_mem_endToEnd {γ1 γ2 γ1' : RegStore}
      {μ1 μ2 μ1' : Memory} n ws_instrs
      (Hmem1 : get_word μ1 (bv.of_N 16) = bv.of_N 2)
      (Hmem2 : get_word μ2 (bv.of_N 16) = bv.of_N 2) :
    let instrs := countdown_mem_instrs in
    mem_has_instrs μ1 (bv.of_N init_addr) ws_instrs instrs ->
    mem_has_instrs μ2 (bv.of_N init_addr) ws_instrs instrs ->
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
    RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
    ⟨ γ1, μ1 ⟩ -(countdown_mem_exitCond, n)->* ⟨ γ1', μ1' ⟩ ->
    leakage_trace μ1 = leakage_trace μ2 ->
    ∃ γ2' μ2',
      ⟨ γ2, μ2 ⟩ -(countdown_mem_exitCond, n)->* ⟨ γ2', μ2' ⟩ ∧
      leakage_trace μ1' = leakage_trace μ2'.
  Proof.
    intros instrs μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc steps1 Htrace.
    assert (HpubReg : declare_public_registers γ1 γ2 []) by constructor.
    assert (HpubMem : declare_public_memory μ1 μ2
        (gen_public_addrs [(bv.of_N 16, true)])).
    { unfold declare_public_memory, gen_public_addrs. cbn.
      constructor. rewrite Hmem1 Hmem2. reflexivity. constructor. }
    eapply (@cfg_instrs_endToEnd_with_memory_strong γ1 γ2 γ1' μ1 μ2 μ1'
      countdown_mem_instrs countdown_mem_exitCond n ws_instrs
      [ctx] [env]
      [] HpubReg
      [(bv.of_N 16, true)] HpubMem
      countdown_mem_cfg_contract valid_countdown_mem_cfg_contract
      eq_refl eq_refl).
    all: try eauto.
    - intros i spec Hlook.
      destruct i; cbn in Hlook; [inversion Hlook; subst | inversion Hlook].
      vm_compute. done.
    - intros Σ H.
      iIntros "(Hregs & Hmemdata & Hpriv & #Hinv)".
      cbn.
      iFrame "Hpriv Hinv".
      rewrite Hmem1.
      iDestruct "Hmemdata" as "[Hmem _]".
      rewrite <- (something_registers HpubReg).
      rewrite gprs_with_registers_equiv. cbn.
      iDestruct "Hregs" as "(Hx1 & _)".
      iSplitL "".
      { iSplit; [iPureIntro | done]. vm_compute. done. }
      iSplitL "Hx1".
      { iExists _. iExact "Hx1". }
      iExact "Hmem".
    - cbn. by unfold lenAddr.
  Qed.

End Examples.

