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
  Import iris.algebra.excl.
  Import iris.algebra.gmap.

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

    Definition RiscVStepsN (γ1 : RegStore) (μ1 : Memory) :
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
      RiscVStepsN γ1 μ1 γ2 μ2 n ->
      RiscVlistNStepsWithExitCond exitCond  γ2 μ2 γ3 μ3 l ->
      RiscVlistNStepsWithExitCond exitCond  γ1 μ1 γ3 μ3 (n :: l)
    .
    Notation "⟨ γ1 , μ1 ⟩ -l( exitCond , n )->* ⟨ γ2 , μ2 ⟩" := (@RiscVlistNStepsWithExitCond exitCond γ1 μ1 γ2 μ2 n)
                                                                 (at level 75, only parsing, right associativity).

    Definition myPost2 `{sailGS2 Σ} :=
      iProp Σ.

    Definition myWp2 `{sailGS2 Σ} :=
        myPost2 -d>
        iProp Σ.

    Definition myWP2_loop_fix `{sailGS2 Σ} (ExitCond : iProp Σ) (wp : myWp2) :
      myWp2 :=
      fun (POST : myPost2) =>
      (ExitCond ∨
        semWP2 env.nil env.nil (FunDef step) (FunDef step)
          (fun _ _ _ _ => ▷ wp POST)%I)%I.
    (* 4 empty arguments, because the return valueas are unit and the CStoreVals are empty *)
  
  Global Instance myWP2_loop_fix_Contractive `{sailGS2 Σ} (ExitCond : iProp Σ) :
    Contractive (myWP2_loop_fix ExitCond).
  Proof.
    rewrite /myWP2_loop_fix /= => n wp wp' Hwp Post.
    do 7 (f_contractive || f_equiv).
    unfold myWp2 in *.
    apply Hwp.
  Qed.

  Definition myWP2_loop `{sailGS2 Σ} (ExitCond : iProp Σ) : myWp2 :=
    fixpoint (myWP2_loop_fix ExitCond).

  Lemma fixpoint_myWP2_loop_fix_eq `{sailGS2 Σ} (ExitCond : iProp Σ) (POST : myPost2) :
    fixpoint (myWP2_loop_fix ExitCond) POST ≡ myWP2_loop_fix ExitCond (fixpoint (myWP2_loop_fix ExitCond)) POST.
  Proof. exact: (fixpoint_unfold (myWP2_loop_fix ExitCond) POST). Qed.

  Lemma fixpoint_myWP2_loop_eq `{sailGS2 Σ} (ExitCond : iProp Σ) (POST : myPost2) :
    myWP2_loop ExitCond POST ≡ myWP2_loop_fix ExitCond (myWP2_loop ExitCond) POST.
  Proof. by unfold myWP2_loop; rewrite fixpoint_myWP2_loop_fix_eq. Qed.

  Definition pcOutOfInstrs (start : Val ty_word) (instrs : list AST) (pc : Val ty_xlenbits) : Prop :=
      bv.ult pc start \/ bv.uge pc (start + bv.of_N (4 * N.of_nat (length instrs))).

    Import IrisModel.RiscvPmpIrisBase.

    Lemma reg2_change `{sailGS2 Σ} {γ1 γ2 γ1' γ2'} :
      own_regstore2 γ1 γ2 ∗ regs_inv2 γ1' γ2' ⊢
        ⌜ read_register γ1 pc = read_register γ1' pc /\ read_register γ2 pc = read_register γ2' pc ⌝.
    Proof.
      iIntros "(HownRegstore & Hinv)".
      unfold own_regstore2; cbn.
      iDestruct "HownRegstore" as "(Hpc & _)".
      Search regs_inv2.
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

    Lemma adequacy_gen_RiscVNStepsExitCond l exitCond {γ11 γ12 γ21 γ22} {μ11 μ12 μ21 μ22} {Q : forall `{sailGS2 Σ}, iProp Σ}
    (φ : Prop) :
    ⟨ γ11, μ11 ⟩ -l( exitCond , l )->* ⟨ γ12, μ12 ⟩ ->
    ⟨ γ21, μ21 ⟩ -l( exitCond , l )->* ⟨ γ22, μ22 ⟩ ->
    (forall `{sailGS2 Σ},
        mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢
          |={⊤}=> myWP2_loop
                    (∃ γ1 γ2, own_regstore2 γ1 γ2 ∗
                       ⌜ exitCond (read_register γ1 pc) ∨ exitCond (read_register γ2 pc) ⌝) Q
        ∗ (mem_inv2 _ μ12 μ22 ={⊤,∅}=∗ ⌜φ⌝)
    )%I -> φ.
  Proof.
    intros Heval1 Heval2 Hwp.
    refine (uPred.pure_soundness _
              (step_fupdN_soundness_gen (Σ := sailΣ2) _ HasLc (list_sum_plus_one l) (list_sum_plus_one l) _)).
    iIntros (Hinv) "Hcred'".
    iMod (own_alloc (A := regUR) ((● RegStore_to_map γ11 ⋅ ◯ RegStore_to_map γ11 ) : regUR)) as (regs1) "[Hregsown1 Hregsinv1]".
    { apply auth_both_valid.
      intuition.
      apply RegStore_to_map_valid. }
    iMod (own_alloc ((● RegStore_to_map γ21 ⋅ ◯ RegStore_to_map γ21 ) : regUR)) as (regs2) "[Hregsown2 Hregsinv2]".
    { apply auth_both_valid.
      intuition.
      apply RegStore_to_map_valid. }
    pose proof (memΣ_GpreS2 (Σ := sailΣ2) _) as mGS.
    iMod (mem_inv_init2 μ11 μ21) as (memG) "[Hmem Rmem]".
    pose (sG := @SailGS2 sailΣ2 Hinv (SailRegGS2 (SailRegGS (@reg_pre_inG2_left _ (@subG_sailGpreS _ _)) regs1) (SailRegGS (@reg_pre_inG2_right _ (@subG_sailGpreS _ _)) regs2)) memG).
    specialize (Hwp _ sG).
    iPoseProof (Hwp with "[$Rmem Hregsinv1 Hregsinv2]") as "Hwp2".
    { unfold own_regstore2.
      iApply RiscvPmpIrisInstance2.own_RegStore_to_map_reg_pointsTos.
      apply finite.NoDup_enum.
      iSplitR "Hregsinv2"; iAssumption.
    }
    iAssert (regs_inv2 γ11 γ21) with "[Hregsown1 Hregsown2]" as "Hregs".
    { iSplitL "Hregsown1";
      now iApply own_RegStore_to_regs_inv.
    }
    clear Hwp.
    iStopProof.
    revert Heval1 Heval2.
    revert γ11 μ11 γ21 μ21.
    induction l.
    - iIntros (γ11 μ11 γ21 μ21 Heval1 Heval2) "(Hcred & Hmem & Hwp2 & Hregs)".
      inversion Heval1. inversion Heval2. subst.
      iMod "Hwp2" as "[_ Hcont]".
      iMod ("Hcont" with "Hmem") as "%Hφ".
      cbn. done.
    - iIntros (γ11 μ11 γ21 μ21 Heval1 Heval2) "(Hcred & Hmem & Hwp2 & Hregs)".
      inversion Heval1 as [ | ? ? γ1 ? μ1 ? nEC1 Hstep1 Hevaln1]. clear Heval1.
      inversion Heval2 as [ | ? ? γ2 ? μ2 ? nEC2 Hstep2 Hevaln2]. clear Heval2. subst.
      specialize (IHl _ _ _ _ Hevaln1 Hevaln2).
      rewrite fixpoint_myWP2_loop_eq.
      unfold myWP2_loop_fix.
      iMod "Hwp2" as "([H | Hwp2] & Hφ)".
      + iDestruct "H" as (γ1' γ2') "(HownRegStore & %ECs)".        
        iPoseProof (reg2_change with "[$HownRegStore $Hregs]") as "(%eq1 & %eq2)".
        rewrite eq1 eq2 in ECs. tauto.
      + iPoseProof (semWP2_preservation Hstep1 Hstep2 with "[$Hmem $Hregs]") as "Hwp".
        iSpecialize ("Hwp" with "Hwp2").
        iMod "Hwp".
        change (list_sum_plus_one (a :: l)) with (a + 1 + list_sum_plus_one l).
        iAssert (|={∅}▷=>^a |={∅}=>  |={∅}▷=> |={∅}▷=>^(list_sum_plus_one l) ⌜φ⌝)%I with "[-]" as "H"; last first.
        { do 2 rewrite step_fupdN_add. destruct a. done. by iApply step_fupdN_S_fupd. }
        iApply (step_fupdN_wand with "Hwp").
        iIntros ">(Hmem & Hregs & Hwp)".
        rewrite semWP2_val.
        iMod "Hwp" as "Hwp".
        rewrite (into_sep_lc_add (a + 1) (list_sum_plus_one l)).
        rewrite (into_sep_lc_add a 1).
        iDestruct "Hcred" as "[[Hcreda Hcred1] Hcredl]".
        iMod (lc_fupd_elim_later with "Hcred1 Hwp") as "Hwp".
        now iMod (IHl with "[$Hmem $Hcredl $Hregs $Hwp $Hφ]") as "IHl".
    Unshelve. auto.
  Qed.


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

  Lemma mvZeroMemory `{sailGS2 Σ} {μ1 μ2 : Memory} ws instrs :
    (4 * N.of_nat (length instrs) < lenAddr)%N ->
    mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
    mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
    @mem_res2 _ sailGS2_memGS μ1 μ2 ⊢ |={⊤}=>
      ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs.
  Proof.
    iIntros (Hrep Hinit1 Hinit2) "Hmem".
    unfold mem_res2, IrisInstance.RiscvPmpIrisAdeqParameters.mem_res.
    replace liveAddrs with
      (bv.seqBv (n := 32) (bv.of_N minAddr) (4 * N.of_nat (length instrs)) ++
         bv.seqBv (n := 32) (bv.of_N minAddr + bv.of_N (4 * N.of_nat (length instrs))) (lenAddr - 4 * N.of_nat (length instrs))).
    2: { rewrite <- bv.seqBv_app. apply f_equal. lia. }
    iDestruct "Hmem" as "[[[Hinit1 Hrest1] [Htr1 Hltr1]] [[Hinit2 Hrest2] [Htr2 Hltr2]]]".
    iApply (intro_ptsto_instrs (μ1 := μ1) (μ2 := μ2)); eauto.
    { unfold init_addr. cbn. lia. }
    iFrame. auto.
  Qed.

  Definition pcOutOfInstrs_WP2_loop `{sailGS2 Σ} instrs :=
    myWP2_loop
    (∃ γ0 γ3 : RegStore, own_regstore2 γ0 γ3 ∗
                           ⌜pcOutOfInstrs (bv.of_N init_addr) instrs (read_register γ0 pc)
                         ∨ pcOutOfInstrs (bv.of_N init_addr) instrs (read_register γ3 pc)⌝)%I True%I.

  Definition instrs_init_pre `{sailGS2 Σ} instrs : iProp Σ :=
    (∃ rv, mstatus ↦ᵣ rv) ∗
      (∃ rv, mtvec ↦ᵣ rv) ∗
      (∃ rv, mcause ↦ᵣ rv) ∗
      (∃ rv, mepc ↦ᵣ rv) ∗
      cur_privilege ↦ᵣ SyncVal Machine ∗
      interp_gprs ∗
      (pc ↦ᵣ SyncVal (bv.of_N init_addr)) ∗
      (∃ v, nextpc ↦ᵣ v) ∗
      ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs.

  Definition instrs_init_post `{sailGS2 Σ} instrs : iProp Σ :=
    (∃ rv, mstatus ↦ᵣ rv) ∗
      (∃ rv, mtvec ↦ᵣ rv) ∗
      (∃ rv, mcause ↦ᵣ rv) ∗
      (∃ rv, mepc ↦ᵣ rv) ∗
      cur_privilege ↦ᵣ SyncVal Machine ∗
      interp_gprs ∗
      (∃ rv, pc ↦ᵣ rv) ∗
      (∃ v, nextpc ↦ᵣ v) ∗
      ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs.

    Definition instrs_init_contract `{sailGS2 Σ} instrs : iProp Σ :=
    instrs_init_pre instrs -∗
      (instrs_init_post instrs -∗ pcOutOfInstrs_WP2_loop instrs) -∗
         pcOutOfInstrs_WP2_loop instrs.

  (* Note: temporarily make instrs_init_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque instrs_init_pre.

  (* Lemma instrs_init_verified instrs : forall `{sailGS2 Σ}, ⊢ instrs_init_contract instrs. *)
  (* Proof. *)
  (*   iIntros (Σ sG) "Hpre Hk". *)
  (*   iApply (sound_sannotated_block_verification_condition RiscvPmpIrisInstanceWithContracts.lemSemBlockVerif sat__femtoinit [env] $! bv.zero with "[Hpre] [Hk]"). *)
  (*   - unfold femto_init_pre. cbn -[ptsto_instrs]. *)
  (*     iDestruct "Hpre" as "((Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp0cfg & Hpmp1cfg & Hpmpaddr0 & Hpmpaddr1) & Hpc & Hnpc & Hinit)". *)
  (*     rewrite Model.RiscvPmpModel2.gprs_equiv. *)
  (*     now iFrame "Hmstatus Hmtvec Hmcause Hmepc Hcurpriv Hgprs Hpmp0cfg Hpmp1cfg Hpc Hnpc Hinit Hpmpaddr0 Hpmpaddr1". *)
  (*   - iIntros (an) "(Hpc & Hnpc & Hhandler & [%eq _] & (Hmstatus & Hmtvec & Hmcause & Hmepc & Hcp & (Hgprs & (Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1))))". *)
  (*     iApply ("Hk" with "[Hpc $Hnpc $Hhandler $Hmstatus $Hmtvec $Hmcause $Hmepc $Hcp Hgprs $Hpmp0cfg $Hpmpaddr0 $Hpmp1cfg $Hpmpaddr1]"). *)
  (*     cbn in eq. subst. *)
  (*     rewrite Model.RiscvPmpModel2.gprs_equiv. *)
  (*     now iFrame. *)
  (* Qed. *)

  Lemma mvZero_init_safe `{sailGS2 Σ} :
    let instrs := [ MV X3 X2; MV X2 X1; MV X1 X3] in
    ⊢ (∃ rv, mstatus ↦ᵣ rv) ∗
      (∃ rv, mtvec ↦ᵣ rv) ∗
      (∃ rv, mcause ↦ᵣ rv) ∗
      (∃ rv, mepc ↦ᵣ rv) ∗
      cur_privilege ↦ᵣ SyncVal Machine ∗
      interp_gprs ∗
      (pc ↦ᵣ SyncVal (bv.of_N init_addr)) ∗
      (∃ v, nextpc ↦ᵣ v) ∗
      ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs
    -∗
       myWP2_loop
       (∃ γ0 γ3 : RegStore, own_regstore2 γ0 γ3 ∗
                              ⌜pcOutOfInstrs (bv.of_N init_addr) instrs (read_register γ0 pc)
                            ∨ pcOutOfInstrs (bv.of_N init_addr) instrs (read_register γ3 pc)⌝) True.
  Proof.
    iIntros (instrs) "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpc & Hnextpc & Hinit)".
    iApply (femto_init_verified with "[$Hmstatus $Hmtvec $Hmcause $Hmepc $Hcurpriv $Hgprs $Hpmp0cfg $Hpmpaddr0 $Hpmp1cfg $Hpmpaddr1 $Hpc $Hinit $Hnextpc]").
    iIntros "((Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1) & Hpc & Hnextpc & Hinit)".
    iAssert (interp_pmp_entries femto_pmpentries) with "[Hpmp0cfg Hpmpaddr0 Hpmp1cfg Hpmpaddr1]" as "Hpmpents".
    { unfold interp_pmp_entries; cbn; iFrame. }
    unfold WP_loop, semWP.
    iApply fupd_wp.
    iMod (femtokernel_manualStep2 with "[Hmstatus $Hmtvec $Hmcause $Hgprs $Hcurpriv $Hpmpents $Hfortytwo $Hpc $Hnextpc $Hhandler $Hadv $Hmepc ]") as "[%mpp Hlooppre]".
    {iDestruct "Hmstatus" as "[%mst Hmstatus]".
      destruct mst as [mpp].
      now iExists mpp.
    }
    iPoseProof (LoopVerification.valid_semTriple_loop with "Hlooppre") as "H".
    iModIntro. cbn. unfold semWP.
    iApply (wp_mono with "H"). auto.
  Qed.

  Lemma mvZero_endToEnd {γ1 γ2 γ1' γ2' : RegStore} {μ1 μ2 μ1' μ2' : Memory}
    {δ1 δ2 δ1' δ2' : CStoreVal [ctx]} {s' : Stm [ctx] ty.unit} (is_mmio : bool) l ws :
    let instrs := [ MV X3 X2; MV X2 X1; MV X1 X3] in
    mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
    mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
    read_register γ1 cur_privilege = Machine ->
    read_register γ2 cur_privilege = Machine ->
    (* read_register γ pmp0cfg = default_pmpcfg_ent -> *)
    (* read_register γ pmpaddr0 = bv.zero -> *)
    (* read_register γ pmp1cfg = default_pmpcfg_ent -> *)
    (* read_register γ pmpaddr1 = bv.zero -> *)
    read_register γ1 pc = (bv.of_N init_addr) ->
    read_register γ2 pc = (bv.of_N init_addr) ->
    ⟨ γ1, μ1 ⟩ -l( pcOutOfInstrs (bv.of_N init_addr) instrs , l )->* ⟨ γ1', μ1' ⟩ ->
    ⟨ γ2, μ2 ⟩ -l( pcOutOfInstrs (bv.of_N init_addr) instrs , l )->* ⟨ γ2', μ2' ⟩ ->
    leakage_trace μ1 = leakage_trace μ2 ->
    leakage_trace μ1' = leakage_trace μ2'      (* The initial demands hold over the final state *).
  Proof.
        intros instrs μinit1 μinit2 γ1curpriv γ2curpriv (* γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 *) γ1pc γ2pc steps1 steps2 Htrace.
        apply (adequacy_gen_RiscVNStepsExitCond (μ21 := μ2) (γ21 := γ2) (Q := fun _ _ => True%I) _ steps1 steps2).
        iIntros (Σ' H).
        unfold own_regstore2 at 1. cbn -[own_regstore2].
        iIntros "(Hmem & Hpc & Hnpc & Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & H')".
        rewrite γ1curpriv γ1pc γ2curpriv γ2pc.
        rewrite !regPstsTo_sync_is_nonsync.
        iMod (mvZeroMemory with "Hmem") as "H"; eauto.
        { (* TODO: Maybe do this in more generality *)
          cbn. by unfold lenAddr.
        }
        iModIntro.
        iSplitR "".
        - destruct (env.view δ1); env.destroy δ2.
          iClear "H'".
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
