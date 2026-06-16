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
      {{ asn_next_pc_eq (term_val (ty.bvec _) (bv.of_nat 12)) ∗
           X1 ↦ᵣ term_var "y" ∗ X2 ↦ᵣ term_var "x" ∗ ∃ "v", X3 ↦ᵣ term_var "v" }}
      with ["x" :: ty_xlenbits; "y" :: ty_xlenbits].

    Example valid_swap_ex : ValidBlockVerifierContract swap_ex.
    Proof. solve_vc. Qed.

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

    (* Unconditional forward jump: jumps 8 bytes ahead (2 instruction widths).
       The block verifier cannot handle this because sexec_block_addr requires
       ainstr = apc at each step, i.e. control flow must be linear. *)
    Definition jmp_offset : bv 21 := bv.of_N 8.

    Definition jmp_fwd : BlockVerifierContract :=
      {{ asn_init_pc }}
        [ JAL X0 jmp_offset ; NOP ]
      {{ asn_next_pc_eq (term_pc_val +ᵇ term_val ty_xlenbits (bv.zext jmp_offset)) }}.

    (* This proof fails: after vm_compute, solve_vc leaves two unprovable goals:
       (1) ty.valToRelVal [bv 0x8] = SyncVal ([bv 0x0] + [bv 0x4])%bv
           — the ainstr = apc check: JAL jumps to 0x8 but sexec_block_addr
             expects the next instruction at ainstr = 0x4 (linear advance).
       (2) ty.valToRelVal [bv 0xc] = SyncVal ([bv 0x0] + [bv 0x8])%bv
           — the verifier then executes NOP as if at 0x4, landing at 0xc,
             which disagrees with the postcondition an = 0x0 + 0x8 = 0x8.
       The fix requires sexec_cfg_addr: follow the actual PC after each
       instruction instead of advancing ainstr linearly. *)
    Lemma valid_jmp_fwd : ValidBlockVerifierContract jmp_fwd.
    Proof. vm_compute. solve_vc. Admitted.

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
  Import iris.algebra.excl.
  Import iris.algebra.gmap.

  Search Assertion.

  Definition asn_regs_ptsto_with_registers {Σ} γ1 γ2 : Assertion Σ :=
    asn_and_regs
      (fun r => asn.chunk (chunk_ptsreg r (term_relval _ (NonSyncVal (read_register γ1 r) (read_register γ2 r))))).

  Lemma gprs_with_registers_equiv `{sailGS2 Σ} γ1 γ2 : ∀ {Σ} (ι : Valuation Σ),
      interp_gprs_with_registers γ1 γ2 ⊣⊢
        asn.interpret (asn_regs_ptsto_with_registers γ1 γ2) ι.
  Proof.
    iIntros. unfold interp_gprs_with_registers.
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

    Definition filter_AnnotInstr_AST (l : list AnnotInstr) := base.omap extract_AST l.

    Definition init_addr     : N := 0.

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
    done.
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

    Lemma semWP2_preservation' `{sailGS2 Σ} n {s11 s21} {γ11 γ12 γ21 γ22} {μ11 μ12 μ21 μ22}
    {δ11 δ21}
    {Q}  :
    NSteps γ11 μ11 δ11 s11 γ12 μ12 [env] (stm_val ty.unit ()) n ->
      Steps γ21 μ21 δ21 s21 γ22 μ22 [env] (stm_val ty.unit ()) ->
    mem_inv2 _ μ11 μ21 ∗ regs_inv2 γ11 γ21 -∗
      semWP2 δ11 δ21 s11 s21 Q
    ={⊤,∅}=∗ |={∅}▷=>^(n) |={∅,⊤}=> mem_inv2 _ μ12 μ22 ∗ regs_inv2 γ12 γ22 ∗
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

      Lemma adequacy_gen_RiscVNStepsExitCond n exitCond {γ11 γ12 γ21 γ22} {μ11 μ12 μ21 μ22}
    (φ : Prop) :
    ⟨ γ11, μ11 ⟩ -( exitCond , n )->* ⟨ γ12, μ12 ⟩ ->
    ⟨ γ21, μ21 ⟩ -( exitCond , n )->* ⟨ γ22, μ22 ⟩ ->
    (forall `{sailGS2 Σ},
        mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢
          |={⊤}=> myWP2_loop
                    (∃ a, pc ↦ᵣ a ∗
                       ⌜ exitCond (ty.projLeft a) ∨ exitCond (ty.projRight a) ⌝)
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
      + iDestruct "H" as (a') "(Hpc & %ECs)".
        unfold reg_pointsTo2.
        iPoseProof (reg_valid2 with "[$Hregs] [$Hpc]") as "(%eq1 & %eq2)".
        rewrite eq1 in nEC1. rewrite eq2 in nEC2. tauto.
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

  Definition pcBehindInstrs_WP2_loop `{sailGS2 Σ} start instrs :=
    myWP2_loop
      (∃ γ0 γ3 : RegStore, own_regstore2 γ0 γ3 ∗
                             ⌜pcBehindInstrs start instrs (read_register γ0 pc)
                           ∨ pcBehindInstrs start instrs (read_register γ3 pc)⌝)%I.

  (* TODO: This is not instruction agnostic anymore *)
  Definition swap_init_pre `{sailGS2 Σ} v1 v2 : iProp Σ :=
    let instrs :=  [ MV X3 X2; MV X2 X1; MV X1 X3] in
    (∃ rv, mstatus ↦ᵣ rv) ∗
      (∃ rv, mtvec ↦ᵣ rv) ∗
      (∃ rv, mcause ↦ᵣ rv) ∗
      (∃ rv, mepc ↦ᵣ rv) ∗
      cur_privilege ↦ᵣ SyncVal Machine ∗
      (pc ↦ᵣ SyncVal (bv.of_N init_addr)) ∗
      (∃ v, nextpc ↦ᵣ v) ∗
      ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs ∗
      x1 ↦ᵣ v1 ∗
      x2 ↦ᵣ v2 ∗
      (∃ v, x3 ↦ᵣ v) ∗
      interp_inv_constant_time
  .

    Definition swap_init_contract `{sailGS2 Σ} v1 v2 : iProp Σ :=
      swap_init_pre v1 v2 -∗
                             pcOutOfInstrs_WP2_loop [ MV X3 X2; MV X2 X1; MV X1 X3].

    Import BlockVer.Verifier.
    Import iris.base_logic.lib.iprop iris.proofmode.tactics.
    Import RiscvPmpIrisInstanceWithContracts.
    Import ProgramLogic.
    Import RiscvPmpBlockVerifShalExecutor.CStoreSpec (evalStoreSpec).
    Import CHeapSpec CHeapSpec.notations.

    Definition exec_instructions_prologue (a : RelVal ty_xlenbits) (l : list AST) : iProp Σ :=
      pc ↦ᵣ a ∗
      ptsto_instrs a l ∗
      (∃ v, nextpc ↦ᵣ v) ∗
      ⌜ secLeak a ⌝
    .

    Definition exec_instructions_epilogue (a an : RelVal ty_xlenbits) (l : list AST) : iProp Σ :=
      pc ↦ᵣ an ∗
      ptsto_instrs a l ∗
      (∃ v, nextpc ↦ᵣ v) ∗
       ⌜ secLeak a ⌝
    .

    Fixpoint step_n (instrs : list AST) (ainstr apc : RelVal ty_xlenbits) (POST : RelVal ty_xlenbits -> iProp Σ) : iProp Σ :=
      match instrs with
      | nil   => POST apc
      | cons i instrs => ⌜ainstr = apc⌝
                ∗ (asn.interpret (exec_instruction_prologue i) [env].["a"∷ty_xlenbits ↦ ainstr]  -∗
                   semWP2 [env] [env] fun_step fun_step
                     (λ v1 δ1 v2 δ2,
                       match v1 , v2 with
                       | inl v1 , inl v2 => ∃ na, asn.interpret (exec_instruction_epilogue i) [env].["a"∷ty_xlenbits ↦ ainstr].["an"∷ty_xlenbits ↦ na] ∗
                                                                                                                                 step_n instrs (ty.liftUnOp (σ1 := ty.bvec _) (σ2 := ty.bvec _) (fun a => bv.add a bv_instrsize) ainstr) na POST
                     | inl _ , inr _ => False
                     | inr _ , inl _ => False
                     | inr _ , inr _ => True
                      end)%I)
      end.

    Lemma step_n_mono {instrs : list AST} {a apc : RelVal ty_xlenbits} {POST1 POST2 : RelVal ty_xlenbits -> iProp Σ} :
      step_n instrs a apc POST1 -∗
      (∀ an, POST1 an -∗ POST2 an) -∗
      step_n instrs a apc POST2.
    Proof.
      revert a apc.
      iInduction instrs as [|instr instrs]; iIntros (a apc) "H HPOSTS".
      - cbn. now iApply "HPOSTS".
      - cbn. iDestruct "H" as "(<- & H)". iSplitR; first auto.
        iIntros "Hpro". iSpecialize ("H" with "Hpro").
        iApply (semWP2_mono with "H").
        iIntros ([] ? [] ?); auto.
        iIntros "H". iDestruct "H" as "(%na & $ & H)".
        iApply ("IHinstrs" with "H HPOSTS").
    Qed.

    Definition stepTriple (l : list AST) (a apc : RelVal ty_xlenbits)
      (PRE : RelVal ty_xlenbits -> iProp Σ) (POST : RelVal ty_xlenbits -> RelVal ty_xlenbits -> iProp Σ) : iProp Σ :=
      PRE a -∗
        step_n l a apc (POST a).

    Definition semTripleOneInstrStep (PRE : RelVal ty_xlenbits -> iProp Σ) (instr : AST) (POST : RelVal ty_xlenbits -> RelVal ty_xlenbits -> iProp Σ) (a : RelVal ty_xlenbits) : iProp Σ :=
      stepTriple [instr] a a PRE POST.

    Definition semTripleBlock (PRE : RelVal ty_xlenbits -> iProp Σ) (a : RelVal ty_xlenbits) (instrs : list AST) (POST : RelVal ty_xlenbits -> RelVal ty_xlenbits -> iProp Σ) : iProp Σ :=
      stepTriple instrs a a PRE POST.

    Lemma sound_exec_instruction {instr} a Φ (h : SCHeap) :
      cexec_instruction instr a Φ h ->
      ⊢ semTripleOneInstrStep (λ a, interpret_scheap h) instr
        (λ a an, ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ an h'⌝) a.
    Proof.
      cbv [cexec_instruction exec_instruction_prologue bind produce demonic
             produce_chunk lift_purespec CPureSpec.produce_chunk CPureSpec.pure
             CPureSpec.demonic RiscvPmpBlockVerifShalExecutor.CStoreSpec.evalStoreSpec].
      cbn - [consume].
      iIntros (Hverif) "Hheap". iSplitR; first auto.
      iIntros "(Hpc & Hinstr & [%npc Hnpc] & [%Hsla _])". cbn -[consume] in *.
      specialize (Hverif npc). apply sound_cexec in Hverif; auto.
      iApply (semWP2_mono with "[-]").
      iApply (sound_stm foreignSemBlockVerif lemSemBlockVerif Hverif with "[] [$]").
      - iIntros (n R) "!>". iApply contractsSound.
      - iIntros ([v1|m1] ? [v2|m2] ?); last done.
        2-3: iIntros "(%δ & _ & %HF)"; contradiction.
        iIntros "(%δ & [%HδL %HδR] & %rv & [%HrvL %HrvR] & %h1 & Hh1 & %Htrip)". clear Hverif.
        destruct Htrip as [an Htrip].
        iPoseProof (consume_sound _ _ Htrip with "Hh1")
          as "[(Hpc & Hinstr & Han) (%h2 & Hh2 & %HΦ)]".
        iExists an. iFrame "Hpc Hinstr Han".
        iExists h2. by iFrame.
    Qed.

    Lemma sound_exec_block_addr {instrs ainstr apc} Φ (h : SCHeap) :
      cexec_block_addr instrs ainstr apc Φ h ->
      ⊢ (stepTriple instrs ainstr apc (λ a, interpret_scheap h)
           (λ a an, ∃ h', interpret_scheap h' ∧ ⌜Φ an h'⌝))%I.
    Proof.
      revert ainstr apc Φ h.
      iInduction instrs as [|instr instrs]; cbn; iIntros (ainstr apc Φ h);
        cbv [bind assert_formula lift_purespec CPureSpec.assert_formula
               CPureSpec.assert_pathcondition pure CPureSpec.pure].
      - iIntros (HΦ) "Hh". iFrame "Hh". done.
      - iIntros ([-> Hverif%sound_exec_instruction]).
        unfold semTripleOneInstrStep in Hverif.
        iIntros "Hh". iSplitR; first auto.
        iIntros "(Hpc & Hinstr & Hnpc)".
        iPoseProof (Hverif with "[$]") as "(_ & H)".
        cbn. iSpecialize ("H" with "[$]").
        iApply (semWP2_mono with "H").
        iIntros ([] ? [] ?); auto.
        iIntros "(%an & Hepi & %h' & Hh' & %Hexec)".
        iFrame "Hepi".
        destruct instrs. cbn.
        + iExists h'. now iFrame "Hh'".
        + remember Hexec as Hexec'.
          cbn in Hexec'.
          cbv [bind assert_formula lift_purespec CPureSpec.assert_formula
                 CPureSpec.assert_pathcondition pure CPureSpec.pure] in Hexec'.
          destruct Hexec' as [<- Hexec']. clear HeqHexec' Hexec'.
          iSpecialize ("IHinstrs" $! _ _ _ _ Hexec with "[$]").
          iApply (step_n_mono with "IHinstrs"). auto.
    Qed.

    Lemma sound_cexec_triple_addr {Γ : LCtx} {pre post instrs} {ι : Valuation Γ} {a : RelVal ty_xlenbits} :
      cexec_triple_addr pre instrs post (fun _ _ => True) []%list ->
      ⊢ semTripleBlock (λ a : RelVal ty_xlenbits, asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])) a instrs
          (λ a na : RelVal ty_xlenbits, asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      cbv [cexec_triple_addr bind demonic_ctx demonic CPureSpec.demonic lift_purespec].
      iIntros (Htrip). unfold semTripleBlock, stepTriple.
      rewrite CPureSpec.wp_demonic_ctx in Htrip.
      specialize (Htrip ι a). apply produce_sound in Htrip.
      destruct instrs as [|instr instrs].
      - iIntros "Hpre".
        iPoseProof (Htrip with "[$] Hpre") as "(%h2 & [Hh2 %Hexec])". clear Htrip.
        apply sound_exec_block_addr in Hexec.
        iPoseProof (Hexec with "[$]") as "H". clear Hexec.
        iDestruct "H" as "(%h' & Hh' & %Hconsume)".
        apply consume_sound in Hconsume.
        iDestruct (Hconsume with "Hh'") as "($ & _)".
      - iIntros "Hpre".
        iPoseProof (Htrip with "[$] Hpre") as "(%h2 & [Hh2 %Hexec])". clear Htrip.
        apply sound_exec_block_addr in Hexec.
        iPoseProof (Hexec with "[$]") as "H". clear Hexec.
        iApply (step_n_mono with "H").
        iIntros (an) "(%h' & Hh' & %Hconsume)".
        apply consume_sound in Hconsume.
        iDestruct (Hconsume with "Hh'") as "($ & _)".
    Qed.

    Lemma sound_cblock_verification_condition {Γ pre post a instrs} :
      cblock_verification_condition pre instrs post ->
      forall ι : Valuation Γ,
      ⊢ semTripleBlock (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]))
          a instrs
          (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      intros Hverif ι.
      now apply sound_cexec_triple_addr.
    Qed.

    Lemma sound_sblock_verification_condition {Γ pre post a instrs} :
      safeE (postprocess (sblock_verification_condition pre instrs post wnil)) ->
      forall ι : Valuation Γ,
      ⊢ semTripleBlock (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]))
          a instrs
          (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      intros Hverif ι.
      apply sound_cexec_triple_addr.
      apply (safeE_safe env.nil), postprocess_sound in Hverif.
      apply LogicalSoundness.psafe_safe in Hverif; [|done].
      revert Hverif.
      apply rexec_triple_addr.
      - easy.
      - easy.
      - easy.
      - constructor.
    Qed.

    Lemma WP2_loop_semTriple : ∀ PRE POST,
      PRE -∗
      semTriple [env] PRE fun_step POST -∗
      (∀ v1 δ1, POST v1 δ1 -∗ WP2_loop) -∗
      WP2_loop.
    Proof.
      iIntros (PRE POST) "HPRE Htrip Hk".
      unfold semTriple.
      iSpecialize ("Htrip" with "HPRE").
      unfold WP2_loop at 2.
      cbn [FunDef]. unfold fun_loop.
      iApply semWP2_seq.
      iApply semWP2_call_inline.
      iApply (semWP2_mono with "Htrip").
      iIntros ([] ? [] ?) "(%δ & [_ _] & H)"; auto.
      + iDestruct "H" as "(%rv & [_ _] & H)".
        iSpecialize ("Hk" with "H").
        now iApply semWP2_call_inline.
      + cbn. by rewrite <- semWP2_fail.
    Qed.

    Lemma myWP2_loop_semTriple : ∀ PRE POST ExitCond,
        PRE -∗
        semTriple [env] PRE fun_step POST -∗
        (∀ v1 δ1, POST v1 δ1 -∗ myWP2_loop ExitCond) -∗
        myWP2_loop ExitCond.
    Proof.
      iIntros (PRE POST ExitCond) "HPRE Htrip Hk".
      unfold semTriple.
      iSpecialize ("Htrip" with "HPRE").
      rewrite {2}fixpoint_myWP2_loop_eq.
      unfold myWP2_loop_fix.
      iRight.
      iApply (semWP2_mono with "Htrip").
      iIntros ([] ? [] ?) "(%δ & [_ _] & H)"; auto.
      + iDestruct "H" as "(%rv & [_ _] & H)".
        iSpecialize ("Hk" with "H").
        done.
    Qed.

    Lemma WP2_loop_semTripleBlock : ∀ PRE a instrs POST,
      (exec_instructions_prologue a instrs) -∗
      (PRE a) -∗
      semTripleBlock PRE a instrs POST -∗
      (∀ an, POST a an ∗ exec_instructions_epilogue a an instrs -∗ WP2_loop) -∗
      WP2_loop.
    Proof.
      iIntros (PRE a instrs).
      iRevert (PRE a).
      iInduction instrs as [|instr instrs] "IH";
        iIntros (PRE a POST) "Hpro HPRE Htrip Hk".
      - cbn. iSpecialize ("Htrip" with "HPRE").
        iApply ("Hk" with "[$Htrip $Hpro]").
      - cbn. iDestruct ("Htrip" with "HPRE") as "(_ & Htrip)".
        iDestruct "Hpro" as "(Hpc & Hinstrs & Hnpc & %Hsla)"; cbn.
        iDestruct "Hinstrs" as "(Hinstr & Hinstrs)".
        iSpecialize ("Htrip" with "[Hpc Hinstr Hnpc]").
        { by iFrame. }
        unfold WP2_loop at 4.
        cbn [FunDef]. unfold fun_loop.
        iApply semWP2_seq.
        iApply semWP2_call_inline. simpl.
        iApply (semWP2_mono with "Htrip").
        iIntros ([] ? [] ?) "H"; auto.
        iDestruct "H" as "(%na & (Hpc & Hinstr & Hnpc & [_ _] & [%Hslna _]) & Htrip)".
        iApply semWP2_call_inline.
        destruct instrs.
        + cbn. iApply ("Hk" with "[$Htrip Hpc Hinstr Hnpc]"). by iFrame.
        + cbn. iDestruct "Htrip" as "(<- & Htrip)".
          iApply ("IH" $! (λ _, True)%I _ (λ a' an, ⌜a' = ty.liftUnOp (σ1 := ty.bvec _) (σ2 := ty.bvec _) (fun a => bv.add a bv_instrsize) a⌝ ∗ POST a an)%I with "[$Hpc $Hinstrs $Hnpc] [] [Htrip]");
            auto.
          { iIntros "_". iSplitR; first auto. iIntros "H".
            iSpecialize ("Htrip" with "H"). iApply (semWP2_mono with "Htrip").
            iIntros ([] ? [] ?); auto.
            iIntros "(%na & Hepi & H)". iExists na. iFrame "Hepi".
            iApply (step_n_mono with "H").
            iIntros (an) "$"; auto. }
          iIntros (an) "([-> HPOST] & Hpc & Hinstrs & Hnpc & Hsla_plus)".
          iApply ("Hk" with "[$HPOST Hpc Hnpc Hinstr Hinstrs Hsla_plus]").
          unfold exec_instructions_epilogue.
          iFrame "Hpc Hnpc".
          cbn.
          iFrame "Hinstr Hinstrs".
          done.
        + rewrite <- semWP2_fail. done.
    Qed.

    Lemma myWP2_loop_semTripleBlock : ∀ PRE a instrs POST ExitCond,
        (exec_instructions_prologue a instrs) -∗
        (PRE a) -∗
        semTripleBlock PRE a instrs POST -∗
        (∀ an, POST a an ∗ exec_instructions_epilogue a an instrs -∗ myWP2_loop ExitCond) -∗
        myWP2_loop ExitCond.
    Proof.
      iIntros (PRE a instrs).
      iRevert (PRE a).
      iInduction instrs as [|instr instrs] "IH";
        iIntros (PRE a POST ExitCond) "Hpro HPRE Htrip Hk".
      - cbn. iSpecialize ("Htrip" with "HPRE").
        iApply ("Hk" with "[$Htrip $Hpro]").
      - cbn. iDestruct ("Htrip" with "HPRE") as "(_ & Htrip)".
        iDestruct "Hpro" as "(Hpc & Hinstrs & Hnpc & %Hsla)"; cbn.
        iDestruct "Hinstrs" as "(Hinstr & Hinstrs)".
        iSpecialize ("Htrip" with "[Hpc Hinstr Hnpc]").
        { by iFrame. }
        rewrite {2}fixpoint_myWP2_loop_eq. unfold myWP2_loop_fix.
        iRight.
        iApply (semWP2_mono with "Htrip").
        iIntros ([] ? [] ?) "H"; auto.
        iDestruct "H" as "(%na & (Hpc & Hinstr & Hnpc & [_ _] & [%Hslna _]) & Htrip)".
        destruct instrs.
        + cbn. iApply ("Hk" with "[$Htrip Hpc Hinstr Hnpc]"). by iFrame.
        + cbn. iDestruct "Htrip" as "(<- & Htrip)".
          iApply ("IH" $! (λ _, True)%I _ (λ a' an, ⌜a' = ty.liftUnOp (σ1 := ty.bvec _) (σ2 := ty.bvec _) (fun a => bv.add a bv_instrsize) a⌝ ∗ POST a an)%I with "[$Hpc $Hinstrs $Hnpc] [] [Htrip]");
            auto.
          { iIntros "_". iSplitR; first auto. iIntros "H".
            iSpecialize ("Htrip" with "H"). iApply (semWP2_mono with "Htrip").
            iIntros ([] ? [] ?); auto.
            iIntros "(%na & Hepi & H)". iExists na. iFrame "Hepi".
            iApply (step_n_mono with "H").
            iIntros (an) "$"; auto. }
          iModIntro.
          iIntros (an) "([-> HPOST] & Hpc & Hinstrs & Hnpc & Hsla_plus)".
          iApply ("Hk" with "[$HPOST Hpc Hnpc Hinstr Hinstrs Hsla_plus]").
          unfold exec_instructions_epilogue.
          iFrame "Hpc Hnpc".
          cbn.
          iFrame "Hinstr Hinstrs".
          done.
    Qed.

    Lemma swap_init_verified v1 v2 :
      ⊢ swap_init_contract v1 v2.
  Proof.
    iIntros "Hpre".
    iDestruct "Hpre" as "(Hstatus & Htvec & Hcause & Hepc & Hpriv & Hpc & Hnpc & Hinstrs & Hx1 & Hx2 & Hx3 & Hinv)".
    unfold pcOutOfInstrs_WP2_loop.
    iApply (myWP2_loop_semTripleBlock with "[$Hpc $Hinstrs $Hnpc] [Hpriv Hx1 Hx2 Hx3 Hinv] [] []").
    2: iApply (sound_sblock_verification_condition valid_swap_ex [env].["x"::ty_xlenbits ↦ v1].["y"::ty_xlenbits ↦ v2]).
    - cbn. iFrame.
      done.
    - cbn -[own_regstore2].
      iIntros (an) "((([-> H1] & (H2 & H2' & H2'')) & H3) & H4 & H5 & H6 & H7)".
      iApply exitCondImpliesMyWP2_loop.
      iFrame.
      iPureIntro.
      right. right. done.
  Qed.

End AdequacyTools.

  Lemma swap_safe `{sailGS2 Σ} v1 v2 :
    let instrs := [ MV X3 X2; MV X2 X1; MV X1 X3] in
    ⊢ (∃ rv, mstatus ↦ᵣ rv) ∗
      (∃ rv, mtvec ↦ᵣ rv) ∗
      (∃ rv, mcause ↦ᵣ rv) ∗
      (∃ rv, mepc ↦ᵣ rv) ∗
      cur_privilege ↦ᵣ SyncVal Machine ∗
      (pc ↦ᵣ SyncVal (bv.of_N init_addr)) ∗
      (∃ v, nextpc ↦ᵣ v) ∗
      ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs ∗
      x1 ↦ᵣ v1 ∗
      x2 ↦ᵣ v2 ∗
      (∃ v, x3 ↦ᵣ v) ∗
      interp_inv_constant_time
    -∗
       pcOutOfInstrs_WP2_loop instrs.
  Proof.
    iIntros (instrs) "H".
    iApply (swap_init_verified with "[-]"); auto.
  Qed.

  Lemma swap_endToEnd {γ1 γ2 γ1' γ2' : RegStore} {μ1 μ2 μ1' μ2' : Memory}
    {δ1 δ2 δ1' δ2' : CStoreVal [ctx]} {s' : Stm [ctx] ty.unit} (is_mmio : bool) n ws :
    let instrs := [ MV X3 X2; MV X2 X1; MV X1 X3] in
    mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
    mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    (* read_register γ pmp0cfg = default_pmpcfg_ent -> *)
    (* read_register γ pmpaddr0 = bv.zero -> *)
    (* read_register γ pmp1cfg = default_pmpcfg_ent -> *)
    (* read_register γ pmpaddr1 = bv.zero -> *)
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⟨ γ1, μ1 ⟩ -( pcOutOfInstrs (bv.of_N init_addr) instrs , n )->* ⟨ γ1', μ1' ⟩ ->
    ⟨ γ2, μ2 ⟩ -( pcOutOfInstrs (bv.of_N init_addr) instrs , n )->* ⟨ γ2', μ2' ⟩ ->
    leakage_trace μ1 = leakage_trace μ2 ->
    leakage_trace μ1' = leakage_trace μ2'      (* The initial demands hold over the final state *).
  Proof.
        intros instrs μinit1 μinit2 γ1curpriv γ2curpriv (* γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 *) γ1pc γ2pc steps1 steps2 Htrace.
        apply (adequacy_gen_RiscVNStepsExitCond (μ21 := μ2) (γ21 := γ2) _ steps1 steps2).
        iIntros (Σ' H).
        iIntros "(Hmem & H')".
        iPoseProof (mem_res2_split_leak with "Hmem") as "(Hmem & Hleak)".
        iPoseProof (constant_time_from_mem_res2_only_leak with "Hleak") as "Hinv"; auto.
        iMod "Hinv" as "#Hinv".
        iMod (instrsMemory with "Hmem") as "H"; eauto.
        { (* TODO: Maybe do this in more generality *)
          cbn. by unfold lenAddr.
        }
        iSplitR "".
        - destruct (env.view δ1); env.destroy δ2.
          iApply swap_safe.
          cbn.
          rewrite γ1curpriv γ1pc γ2curpriv γ2pc.
          rewrite !regPstsTo_sync_is_nonsync.
          iFrame "∗ #".
          by repeat iDestruct "H'" as "($ & H')".
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

  Definition instrs_pre `{sailGS2 Σ} instrs γ1 γ2 : iProp Σ :=
    own_regstore2 γ1 γ2 ∗
      ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs ∗
      interp_inv_constant_time
  .

  Definition instrs_contract `{sailGS2 Σ} instrs γ1 γ2 :=
    (instrs_pre instrs γ1 γ2 -∗ pcOutOfInstrs_WP2_loop instrs)%I.


  Lemma instrs_verified `{sailGS2 Σ} instrs' γ1 γ2 R (ι : Valuation R)
    block
    (valid_block : ValidBlockVerifierContract block)
    (blockInstrs : instrs block = instrs')
    (ImplPre : interp_gprs_with_registers γ1 γ2 ∗
              cur_privilege ↦ᵣ ty.SyncVal Machine ∗
              interp_inv_constant_time -∗
                                          asn.interpret (extract_pre_from_contract block) ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)])
    (ImplPost : forall an, asn.interpret (extend_to_minimal_post (postcondition block)) ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)].["an"∷ty_xlenbits ↦ an] ∗ pc ↦ᵣ an -∗
          pc ↦ᵣ an ∗
            ⌜pcOutOfInstrs (bv.of_N init_addr) instrs' (ty.projLeft an)
              ∨ pcOutOfInstrs (bv.of_N init_addr) instrs' (ty.projRight an)⌝)
    :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⊢ instrs_contract instrs' γ1 γ2.
  Proof.
    iIntros (γ1curpriv γ2curpriv γ1pc γ2pc) "Hpre".
    iDestruct "Hpre" as "(Hregs & Hinstrs & #Hinv)".
    cbn.
    iDestruct "Hregs" as "(Hpc & Hnpc & Hstatus & Htvec & Hcause & Hepc & Hpriv & Hregs)".
    rewrite γ1curpriv γ1pc γ2curpriv γ2pc.
    rewrite !regPstsTo_sync_is_nonsync.
    unfold pcOutOfInstrs_WP2_loop.
    destruct block.
    iApply (myWP2_loop_semTripleBlock with "[$Hpc $Hinstrs $Hnpc] [Hpriv Hregs] [] []").
    Focus 2.
    cbn in *. rewrite blockInstrs in valid_block.
    iApply (sound_sblock_verification_condition valid_block).
    - cbn. iApply ImplPre. iFrame "Hinv Hpriv".
      rewrite gprs_with_registers_equiv.
      cbn.
      repeat (iDestruct "Hregs" as "($ & Hregs)").
    - cbn -[own_regstore2].
      iIntros (an) "((Hpost & Hpriv) & (Hpc & Hinstrs & Hnpc & %HsL))".
      iApply exitCondImpliesMyWP2_loop.
      iExists an.
      iApply ImplPost.
      iFrame.
      Unshelve. exact ctx.nil. exact env.nil.
  Qed.

  Lemma instrs_safe `{sailGS2 Σ} instrs' γ1 γ2 {R} {ι : Valuation R}
    block
    (valid_block : ValidBlockVerifierContract block)
    (blockInstrs : instrs block = instrs')
    (ImplPre : interp_gprs_with_registers γ1 γ2 ∗
                 cur_privilege ↦ᵣ ty.SyncVal Machine ∗
                 interp_inv_constant_time -∗
                                             asn.interpret (extract_pre_from_contract block) ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)])
    (ImplPost : forall an, asn.interpret (extend_to_minimal_post (postcondition block)) ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)].["an"∷ty_xlenbits ↦ an] ∗ pc ↦ᵣ an -∗
                                                                                                                                                                                    pc ↦ᵣ an ∗
                                                                                                                                                                                    ⌜pcOutOfInstrs (bv.of_N init_addr) instrs' (ty.projLeft an)
                           ∨ pcOutOfInstrs (bv.of_N init_addr) instrs' (ty.projRight an)⌝)
    :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⊢ own_regstore2 γ1 γ2 ∗
      ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs' ∗
      interp_inv_constant_time
    -∗
       pcOutOfInstrs_WP2_loop instrs'.
  Proof.
    iIntros (γ1curpriv γ2curpriv γ1pc γ2pc) "H".
    iApply instrs_verified; auto.
    all: auto.
  Qed.

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

    Lemma instrs_endToEnd {γ1 γ2 γ1' γ2' : RegStore} {μ1 μ2 μ1' μ2' : Memory}
      instrs' n ws {R} {ι : Valuation R}
      public_registers
      (HpubReg : declare_public_registers γ1 γ2 public_registers)
      {block : @BlockVerifierContract R}
      (valid_block : ValidBlockVerifierContract block)
      (blockInstrs : instrs block = instrs')
      (ImplPre : forall `{sailGS2 Σ}, interp_gprs_with_public_registers γ1 γ2 public_registers ∗
                                        cur_privilege ↦ᵣ ty.SyncVal Machine ∗
                                        interp_inv_constant_time
                                      -∗
                                                                    asn.interpret (extract_pre_from_contract block) ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)])
      (ImplPost : forall `{sailGS2 Σ}, forall an,
          asn.interpret (extend_to_minimal_post (postcondition block)) ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)].["an"∷ty_xlenbits ↦ an] ∗ pc ↦ᵣ an -∗
                                                                                                                                                               pc ↦ᵣ an ∗
                                                                                                                                                               ⌜pcOutOfInstrs (bv.of_N init_addr) instrs' (ty.projLeft an)
          ∨ pcOutOfInstrs (bv.of_N init_addr) instrs' (ty.projRight an)⌝)
      :
      (4 * N.of_nat (length instrs') < lenAddr)%N ->
      mem_has_instrs μ1 (bv.of_N init_addr) ws instrs' ->
      mem_has_instrs μ2 (bv.of_N init_addr) ws instrs' ->
      RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
      RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
      RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
      RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
      ⟨ γ1, μ1 ⟩ -( pcOutOfInstrs (bv.of_N init_addr) instrs' , n )->* ⟨ γ1', μ1' ⟩ ->
      ⟨ γ2, μ2 ⟩ -( pcOutOfInstrs (bv.of_N init_addr) instrs' , n )->* ⟨ γ2', μ2' ⟩ ->
      leakage_trace μ1 = leakage_trace μ2 ->
      leakage_trace μ1' = leakage_trace μ2'      (* The initial demands hold over the final state *).
    Proof.
      intros Hleninstrs μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc steps1 steps2 Htrace.
      apply (adequacy_gen_RiscVNStepsExitCond (μ21 := μ2) (γ21 := γ2) _ steps1 steps2).
      iIntros (Σ' H').
      iIntros "(Hmem & H')".
      iPoseProof (mem_res2_split_leak with "Hmem") as "(Hmem & Hleak)".
      iPoseProof (constant_time_from_mem_res2_only_leak with "Hleak") as "Hinv"; auto.
      iMod "Hinv" as "#Hinv".
      iMod (instrsMemory with "Hmem") as "H"; eauto.
      iSplitR "".
      - iApply (instrs_safe γ1 γ2 block).
        all: eauto.
        iIntros "(Hregs & Hpriv & #Hinv)".
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

    Lemma swap_endToEnd2 {γ1 γ2 γ1' γ2' : RegStore} {μ1 μ2 μ1' μ2' : Memory} n ws :
    let instrs := [ MV X3 X2; MV X2 X1; MV X1 X3] in
    mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
    mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    (* read_register γ pmp0cfg = default_pmpcfg_ent -> *)
    (* read_register γ pmpaddr0 = bv.zero -> *)
    (* read_register γ pmp1cfg = default_pmpcfg_ent -> *)
    (* read_register γ pmpaddr1 = bv.zero -> *)
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⟨ γ1, μ1 ⟩ -( pcOutOfInstrs (bv.of_N init_addr) instrs , n )->* ⟨ γ1', μ1' ⟩ ->
    ⟨ γ2, μ2 ⟩ -( pcOutOfInstrs (bv.of_N init_addr) instrs , n )->* ⟨ γ2', μ2' ⟩ ->
    leakage_trace μ1 = leakage_trace μ2 ->
    leakage_trace μ1' = leakage_trace μ2'      (* The initial demands hold over the final state *).
    Proof.
      assert (declare_public_registers γ1 γ2 []) as HpubReg.
      { by apply Forall_nil.  }
      apply (instrs_endToEnd
               (ι := [env].["x"::ty_xlenbits ↦
                              NonSyncVal (read_register γ1 x1) (read_register γ2 x1)].["y"::ty_xlenbits ↦ NonSyncVal (read_register γ1 x2) (read_register γ2 x2)]) _
               HpubReg valid_swap_ex); eauto.
      - intros. cbn. iIntros "(Hregs & Hpriv & Hinv)".
        iFrame.
        rewrite <- something_registers; auto.
        rewrite gprs_with_registers_equiv.
        cbn.
        repeat (iDestruct "Hregs" as "($ & Hregs)").
        auto.
      - intros. cbn. iIntros "((((-> & _) & L') & H & Hregs) & HpcL & HpcR)".
        iFrame. cbn.
        iPureIntro.
        right. right. done.
      - done.
        Unshelve. exact ctx.nil. exact env.nil.
    Qed.

    Lemma jumpIfZero_endToEnd {γ1 γ2 γ1' γ2' : RegStore} {μ1 μ2 μ1' μ2' : Memory} n ws
      (HpubReg : declare_public_registers γ1 γ2 [existT ty_xlenbits x1]) :
      let instrs := [ BEQ X1 X0 true_offset ] in
      mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
      mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
      RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
      RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
      (* read_register γ pmp0cfg = default_pmpcfg_ent -> *)
      (* read_register γ pmpaddr0 = bv.zero -> *)
      (* read_register γ pmp1cfg = default_pmpcfg_ent -> *)
      (* read_register γ pmpaddr1 = bv.zero -> *)
      RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
      RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
      ⟨ γ1, μ1 ⟩ -( pcOutOfInstrs (bv.of_N init_addr) instrs , n )->* ⟨ γ1', μ1' ⟩ ->
      ⟨ γ2, μ2 ⟩ -( pcOutOfInstrs (bv.of_N init_addr) instrs , n )->* ⟨ γ2', μ2' ⟩ ->
      leakage_trace μ1 = leakage_trace μ2 ->
      leakage_trace μ1' = leakage_trace μ2'      (* The initial demands hold over the final state *).
    Proof.
      eapply (instrs_endToEnd
               (ι := [env].["x1"::ty_xlenbits ↦
                              SyncVal (read_register γ1 x1)]) _
               HpubReg valid_jump_if_zero); eauto.
      - intros. cbn. iIntros "(Hregs & Hpriv & Hinv)".
        iFrame.
        rewrite <- something_registers; auto.
        rewrite gprs_with_registers_equiv.
        cbn.
        unfold declare_public_registers in HpubReg. rewrite Forall_singleton in HpubReg.
        rewrite HpubReg.
        iDestruct "Hregs" as "($ & Hregs)".
        auto.
      - intros. cbn.
        destruct (Classes.eq_dec (read_register γ1 x1) bv.zero) as [|] eqn:HisZero;
          rewrite HisZero; cbn;
        iIntros "(((-> & _) & J & I) & L)".
        + iFrame. iPureIntro. right. right. cbn.
          now rewrite <-bv.uleb_ule.
        + iFrame. iPureIntro. right. right. cbn.
          now rewrite <-bv.uleb_ule.
      - done.
        Unshelve. exact ctx.nil. exact env.nil.
    Qed.

End Examples.

