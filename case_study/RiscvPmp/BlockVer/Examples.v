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

    (* minimal_post asserts ownership of the cur_privilege CSR,
       but do not care in which mode we end up. *)
    Definition minimal_post {Σ} : Assertion Σ :=
      (* asn.exist "_" _ (nextpc ↦ term_var "_")
      ∗ *) cur_privilege ↦ term_val ty_privilege Machine
      (* ∗ asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero) ; *)
      (*                               (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)]) *)
    .

    Definition extend_to_minimal_pre {Σ} (P : Assertion Σ) : Assertion Σ :=
      P ∗ minimal_pre.

    Definition extend_to_minimal_post {Σ} (Q : Assertion Σ) : Assertion Σ :=
      Q ∗ minimal_post.

    Definition VC_triple {Σ} (P : Assertion (Σ ▻ "a" :: ty_xlenbits)) (i : list AST) (Q : Assertion (Σ ▻ "a" :: ty_xlenbits ▻ "an" :: ty_xlenbits)) :=
      sblock_verification_condition (extend_to_minimal_pre P) i (extend_to_minimal_post Q) wnil.

    Definition Valid_VC {Σ} (P : Assertion (Σ ▻ "a" :: ty_xlenbits)) (i : list AST) (Q : Assertion (Σ ▻ "a" :: ty_xlenbits ▻ "an" :: ty_xlenbits)) :=
      safeE (postprocess (VC_triple P i Q)).

    Definition Debug_VC {Σ} (P : Assertion (Σ ▻ "a" :: ty_xlenbits)) (i : list AST) (Q : Assertion (Σ ▻ "a" :: ty_xlenbits ▻ "an" :: ty_xlenbits)) :=
      VerificationCondition (postprocess (VC_triple P i Q)).

    Record BlockVerifierContract {Σ} :=
      MkBlockVerifierContract
      { precondition  : Assertion (Σ ▻ "a" :: ty_xlenbits)
      ; instrs        : list AST
      ; postcondition : Assertion (Σ ▻ "a" :: ty_xlenbits ▻ "an" :: ty_xlenbits)
      }.

    Definition map {Σ A} (c : @BlockVerifierContract Σ)
      (f : Assertion (Σ ▻ "a" :: ty_xlenbits) -> list AST -> Assertion (Σ ▻ "a" :: ty_xlenbits ▻ "an" :: ty_xlenbits) -> A)
      : A :=
      match c with
      | {| precondition := pre; instrs := i; postcondition := post |} =>
          f pre i post
      end.

    Definition ValidBlockVerifierContract {Σ} (c : @BlockVerifierContract Σ) : Prop :=
      map c Valid_VC.

    Definition DebugBlockVerifierContract {Σ} (c : @BlockVerifierContract Σ) : Prop :=
      map c Debug_VC.

    Local Notation "'{{' P '}}' i '{{' Q '}}'" := (@MkBlockVerifierContract [ctx] P%asn i Q%asn)
        (at level 90, format "'[v' '{{'  P  '}}' '/'  i '/' '{{'  Q  '}}' ']'").
    Local Notation "'{{' P '}}' i '{{' Q '}}' 'with' logvars" := (@MkBlockVerifierContract logvars P%asn i Q%asn)
        (at level 90, format "'[v' '{{'  P  '}}' '/'  i '/' '{{'  Q  '}}' '/' 'with'  logvars ']'").

    Local Ltac solve_bv :=
      repeat match goal with
        | |- context[bv.add ?x (@bv.mk ?n 0 I)] =>
            fold (@bv.zero n)
        | |- context[bv.add ?x bv.zero] =>
            rewrite bv.add_zero_r
        end.

    Local Ltac solve_vc :=
      vm_compute; constructor; cbn; intros; repeat split; try solve_bv; auto.

    Definition with_regidx {Σ} (r : RegIdx) (P : Reg ty_xlenbits -> Assertion Σ) : Assertion Σ :=
      match reg_convert r with
      | None     => ⊤
      | Some reg => P reg
      end.

    Notation "r '↦ᵣ' v" := (with_regidx r (fun reg => asn.chunk (chunk_ptsreg reg v))) (at level 70) : asn_scope.
    Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70).

    Definition asn_init_pc {Σ} : Assertion (Σ ▻ "a" :: ty_xlenbits) :=
      term_var "a" = term_val ty_xlenbits bv.zero.

    Definition asn_pc_eq {Σ} (t : Term (Σ ▻ "a" :: ty_xlenbits) ty_xlenbits) : Assertion (Σ ▻ "a" :: ty_xlenbits) :=
      term_var "a" = t.

    Local Notation term_pc_val := (term_var "a").

    Definition asn_next_pc_eq {Σ} (t : Term (Σ ▻ "an" :: ty_xlenbits) ty_xlenbits) : Assertion (Σ ▻ "an" :: ty_xlenbits) :=
      term_var "an" = t.

    Definition mv_zero_ex : BlockVerifierContract :=
      {{ asn_init_pc ∗ ∃ "v", X1 ↦ᵣ term_var "v" }}
        [MV X1 X0]
      {{ X1 ↦ᵣ term_val ty_xlenbits bv.zero }}.

    Import SymProp.notations.
    Import Erasure.notations.

    Example valid_mv_zero_ex : ValidBlockVerifierContract mv_zero_ex.
    Proof. vm_compute. solve_vc. Qed.

    Definition mv_same_reg_ex : BlockVerifierContract :=
      {{ asn_init_pc ∗ X1 ↦ᵣ term_var "x" }} [MV X1 X1] {{ X1 ↦ᵣ term_var "x" }}
      with ["x" :: ty_xlenbits].

    Example valid_mv_same_reg_ex : ValidBlockVerifierContract mv_same_reg_ex.
    Proof. solve_vc. Qed.

    Definition mv_ex : BlockVerifierContract :=
      {{ asn_init_pc ∗ X1 ↦ᵣ term_var "x" ∗ X2 ↦ᵣ term_var "y" }}
        [MV X1 X2]
      {{ X1 ↦ᵣ term_var "y" ∗ X2 ↦ᵣ term_var "y" }}
      with ["x" :: ty_xlenbits; "y" :: ty_xlenbits].

    Example valid_mv_ex : ValidBlockVerifierContract mv_ex.
    Proof. solve_vc. Qed.

    (* swap_two registers using a third, temporary, register (X3) *)
    Definition swap_ex : BlockVerifierContract :=
      {{ asn_init_pc ∗ X1 ↦ᵣ term_var "x" ∗ X2 ↦ᵣ term_var "y" ∗ ∃ "v", X3 ↦ᵣ term_var "v" }}
        [ MV X3 X2
        ; MV X2 X1
        ; MV X1 X3
        ]
      {{ X1 ↦ᵣ term_var "y" ∗ X2 ↦ᵣ term_var "x" ∗ ∃ "v", X3 ↦ᵣ term_var "v" }}
      with ["x" :: ty_xlenbits; "y" :: ty_xlenbits].

    Example valid_swap_ex : ValidBlockVerifierContract swap_ex.
    Proof. solve_vc. Qed.

    (* TODO: move into Spec.v *)
    Definition JAL (rd : RegIdx) (imm : bv 21) : AST :=
      RISCV_JAL imm rd.
    Definition LW (rd rs : RegIdx) (imm : bv 12) : AST :=
      LOAD imm rs rd false WORD.
    Definition SW (rs2 rs1 : RegIdx) (imm : bv 12) : AST :=
      STORE imm rs2 rs1 WORD.

    Definition true_offset : bv 13 := bv.of_N 8.

    Import TermNotations.

    (* TODO: would rather write jump_if_zero (true_offset : bv 13) ... *)
    (* Jumps to `true_offset` when the value of X1 is equal to zero. The
         default offset allows one instruction between this block and the true
         block. *)
    Definition jump_if_zero : BlockVerifierContract :=
      {{ asn_init_pc ∗ X1 ↦ᵣ term_var "x1" ∗ asn.formula (formula_secLeak (term_var "x1")) }}
        [ BEQ X1 X0 true_offset ]
        {{ if: term_var "x1" ?= term_val ty_xlenbits bv.zero
           then asn_next_pc_eq (term_pc_val +ᵇ term_val ty_xlenbits (bv.zext true_offset))
           else asn_next_pc_eq (term_pc_val +ᵇ term_val ty_xlenbits (bv.of_N 4)) }}
      with ["x1" :: ty_xlenbits].

    (* TODO: would rather write ∀ true_offset, ... but verification then explodes *)
    Lemma valid_jump_if_zero : ValidBlockVerifierContract jump_if_zero.
    Proof. vm_compute. solve_vc. Qed.

    (* Sets the contents of register X2 to value 42. The contract reflects
         this, we require ownership of X2, and after executing we know that
         the PC will be pointing to the next instructions and X2 will contain
         42. *)
    Definition set_X2_to_42 : BlockVerifierContract :=
      {{ asn_init_pc ∗ ∃ "_", X2 ↦ᵣ term_var "_" }}
        [ ADDI X2 X0 (bv.of_N 42) ]
      {{ asn_next_pc_eq (term_pc_val +ᵇ term_val ty_xlenbits (bv.of_N 4))
         ∗ X2 ↦ᵣ term_val ty_xlenbits (bv.of_N 42) }}.

    Lemma valid_set_X2_to_42 : ValidBlockVerifierContract set_X2_to_42.
    Proof. solve_vc. Qed.

  End WithAsnNotations.

  Definition extract_pre_from_contract {Σ} (c : BlockVerifierContract)
    : Assertion (Σ ▻ "a" ∷ ty_xlenbits) :=
    map c (fun P _ _ => extend_to_minimal_pre P).

  Definition extract_post_from_contract {Σ} (c : BlockVerifierContract)
    : Assertion (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits) :=
    map c (fun _ _ Q => extend_to_minimal_post Q).

  Definition extract_instrs_from_contract {Σ} (c : @BlockVerifierContract Σ) : list AST :=
    map c (fun _ i _ => i).

  Section WithSailResources.
      Import IrisModelBinary.RiscvPmpIrisBase2.
      Import IrisInstanceBinary.RiscvPmpIrisInstance2.
      Import RiscvPmpIrisInstanceWithContracts.

      Context `{sailGS Σ} `{sailGS2 Σ}.

      Definition ptsto_instrs_from_contract {Γ} (c : @BlockVerifierContract Γ) (a : RelVal ty_xlenbits) : iProp Σ :=
        ptsto_instrs a (extract_instrs_from_contract c).

      Definition jump_if_zero_pre (x1 : RelVal ty_xlenbits) : iProp Σ :=
        asn.interpret (extract_pre_from_contract jump_if_zero)
          [env].["x1"∷ty_xlenbits ↦ x1].["a"∷ty_xlenbits ↦ (SyncVal bv.zero)]
        ∗ reg_pointsTo2 pc (SyncVal bv.zero) ∗ (∃ npc, reg_pointsTo2 nextpc npc)
        ∗ ptsto_instrs_from_contract jump_if_zero (SyncVal bv.zero).

      Definition jump_if_zero_post (x1 : RelVal ty_xlenbits) : iProp Σ :=
        ∃ (an : RelVal ty_xlenbits),
          reg_pointsTo2 pc an ∗ (∃ npc, reg_pointsTo2 nextpc npc)
          ∗ ptsto_instrs_from_contract jump_if_zero (SyncVal bv.zero)
          ∗ asn.interpret (extract_post_from_contract jump_if_zero)
          [env].["x1"∷ty_xlenbits ↦ x1].["a"∷ty_xlenbits ↦ (SyncVal bv.zero)].["an"∷ty_xlenbits ↦ an].

      Definition iris_contract (pre post : iProp Σ) : iProp Σ :=
        pre -∗ (post -∗ WP2_loop) -∗ WP2_loop.

      Definition jump_if_zero_contract : iProp Σ := ∀ x1,
          iris_contract (jump_if_zero_pre x1) (jump_if_zero_post x1).

      Lemma jump_if_zero_verified :
        ⊢ jump_if_zero_contract.
      Proof.
        iIntros (x1) "Hpre Hk".
        iApply (sound_sblock_verification_condition valid_jump_if_zero
                  [env].["x1"∷ty_xlenbits ↦ x1] $! (SyncVal bv.zero) with "[Hpre] [Hk]").
        unfold jump_if_zero_pre, extract_pre_from_contract, jump_if_zero. cbn.
        iDestruct "Hpre" as "((((A1 & _) & A1' & (A1'' & _)) & A2 & A3) & B & C & D & E)".
        iFrame.
        iIntros (an) "H".
        iApply "Hk".
        by iExists an.
      Qed.

      
      Definition set_X2_to_42_pre (instrs_loc : RelVal ty_xlenbits) : iProp Σ :=
        asn.interpret (extract_pre_from_contract set_X2_to_42)
          [env].["a"∷ty_xlenbits ↦ instrs_loc]
        ∗ reg_pointsTo2 pc instrs_loc ∗ (∃ npc, reg_pointsTo2 nextpc npc)
        ∗ ptsto_instrs_from_contract set_X2_to_42 instrs_loc
        ∗ ⌜ secLeak instrs_loc ⌝.

      Definition set_X2_to_42_post (instrs_loc : RelVal ty_xlenbits) : iProp Σ :=
        ∃ (an : RelVal ty_xlenbits),
          reg_pointsTo2 pc an ∗ (∃ npc, reg_pointsTo2 nextpc npc)
          ∗ ptsto_instrs_from_contract set_X2_to_42 instrs_loc
          ∗ asn.interpret (extract_post_from_contract set_X2_to_42)
              [env].["a"∷ty_xlenbits ↦ instrs_loc].["an"∷ty_xlenbits ↦ an].

      Definition set_X2_to_42_contract (instrs_loc : RelVal ty_xlenbits) : iProp Σ :=
        iris_contract (set_X2_to_42_pre instrs_loc) (set_X2_to_42_post instrs_loc).

      Lemma set_X2_to_42_verified : ∀ instrs_loc,
          ⊢ set_X2_to_42_contract instrs_loc.
      Proof.
        iIntros (instrs_loc) "Hpre Hk".
        iApply (sound_sblock_verification_condition valid_set_X2_to_42
                  [env] $! instrs_loc with "[Hpre] [Hk]").
        iDestruct "Hpre" as "(A & B & C & D & E)".
        unfold extract_pre_from_contract, set_X2_to_42. cbn.
        iFrame.
        iIntros (an) "H".
        iApply "Hk".
        by iExists an.
      Qed.
  End WithSailResources.

  Import IrisInstanceBinary.
  Import RiscvPmpIrisInstance2.
  Import RiscvPmpSemantics.
  Import RiscvPmpIrisAdeqParams2.
  Import SmallStepNotations.
  Import IrisModelBinary.RiscvPmpIrisBase2.

  From iris.bi Require big_op.
  From iris.algebra Require big_op.
  From iris.program_logic Require weakestpre.

    Definition mem_has_word (μ : Memory) (a : Val ty_word) (w : Val ty_word) : Prop :=
      exists v0 v1 v2 v3, List.map (memory_ram μ) (bv.seqBv a 4) = [v0; v1; v2; v3]%list /\ bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil))) = w.

    (* byte order correct? *)
    Definition mem_has_instr (μ : Memory) (a : Val ty_word) (instr : AST) : Prop :=
      exists w, mem_has_word μ a w /\ pure_decode w = inr instr.

    Fixpoint mem_has_instrs (μ : Memory) (a : Val ty_word) (instrs : list AST) : Prop :=
      match instrs with
      | cons inst instrs => mem_has_instr μ a inst /\ mem_has_instrs μ (bv.add (bv.of_N 4) a) instrs
      | nil => True
      end.

    Definition filter_AnnotInstr_AST (l : list AnnotInstr) := base.omap extract_AST l.

    Definition init_addr     : N := 0.

    Locate "↦ᵣ".
    Locate reg_pointsTo2.

      Lemma mvZero_endToEnd {γ1 γ2 γ1' γ2' : RegStore} {μ1 μ2 μ1' μ2' : Memory}
        {δ1 δ2 δ1' δ2' : CStoreVal [ctx]} {s' : Stm [ctx] ty.unit} (is_mmio : bool) :
        mem_has_instrs μ1 (bv.of_N init_addr) [MV X1 X0] ->
        mem_has_instrs μ2 (bv.of_N init_addr) [MV X1 X0] ->
        read_register γ1 cur_privilege = Machine ->
        read_register γ2 cur_privilege = Machine ->
        (* read_register γ pmp0cfg = default_pmpcfg_ent -> *)
        (* read_register γ pmpaddr0 = bv.zero -> *)
        (* read_register γ pmp1cfg = default_pmpcfg_ent -> *)
        (* read_register γ pmpaddr1 = bv.zero -> *)
        read_register γ1 pc = (bv.of_N init_addr) ->
        read_register γ2 pc = (bv.of_N init_addr) ->
        ⟨ γ1, μ1, δ1, fun_loop ⟩ --->* ⟨ γ1', μ1', δ1', s' ⟩ ->
        ⟨ γ2, μ2, δ2, fun_loop ⟩ --->* ⟨ γ2', μ2', δ2', s' ⟩ ->
        leakage_trace μ1 = leakage_trace μ2 ->
        leakage_trace μ1' = leakage_trace μ2'      (* The initial demands hold over the final state *).
      Proof.
        intros μ1init μ2init γ1curpriv γ2curpriv γ1pc γ2pc steps1 steps2 eq_leak.
        refine (adequacy_gen (μ21 := μ2) (γ21 := γ2) (δ21 := δ2) (Q := fun _ _ _ _ _ _ => True%I) fun_loop _ steps1 _).
        iIntros (Σ' H).
        cbn.
        iIntros "(Hmem & Hpc & Hnpc & Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & H')".
        rewrite γ1curpriv γ1pc γ2curpriv γ2pc.
        iModIntro.
        iSplitR "".
        - destruct (env.view δ1); env.destroy δ2.
          
          iApply (femtokernel_init_safe is_mmio with "[-]").

          Local Opaque ptsto_instrs. (* Avoid spinning because code is unfolded *)
          iFrame "∗ #". rewrite Model.RiscvPmpModel2.gprs_equiv. cbn.
          now repeat iDestruct "H'" as "($ & H')".
        - iIntros "Hmem".
          (* Prove that this predicate follows from the invariants in both cases *)
          destruct (negb is_mmio).
          + iInv "Hfortytwo" as ">Hptsto" "_".
            iDestruct (interp_ptstomem_valid with "Hmem Hptsto") as "$".
            iApply fupd_mask_intro; first set_solver.
            now iIntros "_".
          + iInv "Hfortytwo" as (t) ">[Hfrag %Hpred]" "_".
            iDestruct "Hmem" as "(%memmap & Hinv & %link & Htr)".
            iDestruct (trace.trace_full_frag_eq with "Htr Hfrag") as "->".
            iApply fupd_mask_intro; first set_solver.
            now iIntros "_".

End Examples.
