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
From Katamaran Require Import RiscvPmp.LoopVerification.

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
  Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

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
      ∗ asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero) ;
                                    (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)]).

    (* minimal_post asserts ownership of the cur_privilege CSR,
       but do not care in which mode we end up. *)
    Definition minimal_post {Σ} : Assertion Σ :=
      (* asn.exist "_" _ (nextpc ↦ term_var "_")
      ∗ *) cur_privilege ↦ term_val ty_privilege Machine
      ∗ asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero) ;
                                    (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)]).

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
        | |- context[bv.add ?x (@BitvectorBase.bv.mk ?n 0 I)] =>
            fold (@bv.zero n)
        | |- context[bv.add ?x bv.zero] =>
            rewrite BitvectorBase.bv.add_zero_r
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

    Example valid_mv_zero_ex : ValidBlockVerifierContract mv_zero_ex.
    Proof. solve_vc. Qed.

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
      {{ asn_init_pc ∗ X1 ↦ᵣ term_var "x1" }}
        [ BEQ X1 X0 true_offset ]
        {{ if: term_var "x1" ?= term_val ty_xlenbits bv.zero
           then asn_next_pc_eq (term_pc_val +ᵇ term_val ty_xlenbits (bv.zext true_offset))
           else asn_next_pc_eq (term_pc_val +ᵇ term_val ty_xlenbits (bv.of_N 4)) }}
      with ["x1" :: ty_xlenbits].

    (* TODO: would rather write ∀ true_offset, ... but verification then explodes *)
    Lemma valid_jump_if_zero : ValidBlockVerifierContract jump_if_zero.
    Proof. solve_vc. Qed.

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
      Import IrisModel.RiscvPmpIrisBase.
      Import IrisInstance.RiscvPmpIrisInstance.
      Import RiscvPmpIrisInstanceWithContracts.

      Context `{sailGS Σ} `{sailGS2 Σ}.

      Definition ptsto_instrs_from_contract {Γ} (c : @BlockVerifierContract Γ) (a : Val ty_xlenbits) : iProp Σ :=
        ptsto_instrs a (extract_instrs_from_contract c).

      Definition jump_if_zero_pre (x1 : Val ty_xlenbits) : iProp Σ :=
        asn.interpret (extract_pre_from_contract jump_if_zero)
          [env].["x1"∷ty_xlenbits ↦ x1].["a"∷ty_xlenbits ↦ bv.zero]
        ∗ reg_pointsTo pc bv.zero ∗ (∃ npc, reg_pointsTo nextpc npc)
        ∗ ptsto_instrs_from_contract jump_if_zero bv.zero.

      Definition jump_if_zero_post (x1 : Val ty_xlenbits) : iProp Σ :=
        ∃ (an : Val ty_xlenbits),
          reg_pointsTo pc an ∗ (∃ npc, reg_pointsTo nextpc npc)
          ∗ ptsto_instrs_from_contract jump_if_zero bv.zero
          ∗ asn.interpret (extract_post_from_contract jump_if_zero)
          [env].["x1"∷ty_xlenbits ↦ x1].["a"∷ty_xlenbits ↦ bv.zero].["an"∷ty_xlenbits ↦ an].

      Definition iris_contract (pre post : iProp Σ) : iProp Σ :=
        pre -∗ (post -∗ WP_loop) -∗ WP_loop.

      Definition jump_if_zero_contract : iProp Σ := ∀ x1,
          iris_contract (jump_if_zero_pre x1) (jump_if_zero_post x1).

      Lemma jump_if_zero_verified :
        ⊢ jump_if_zero_contract.
      Proof.
        iIntros (x1) "Hpre Hk".
        iApply (sound_sblock_verification_condition valid_jump_if_zero
                  [env].["x1"∷ty_xlenbits ↦ x1] $! bv.zero with "Hpre [Hk]").
        iIntros (an) "H".
        iApply "Hk".
        by iExists an.
      Qed.

      Definition set_X2_to_42_pre (instrs_loc : Val ty_xlenbits) : iProp Σ :=
        asn.interpret (extract_pre_from_contract set_X2_to_42)
          [env].["a"∷ty_xlenbits ↦ instrs_loc]
        ∗ reg_pointsTo pc instrs_loc ∗ (∃ npc, reg_pointsTo nextpc npc)
        ∗ ptsto_instrs_from_contract set_X2_to_42 instrs_loc.

      Definition set_X2_to_42_post (instrs_loc : Val ty_xlenbits) : iProp Σ :=
        ∃ (an : Val ty_xlenbits),
          reg_pointsTo pc an ∗ (∃ npc, reg_pointsTo nextpc npc)
          ∗ ptsto_instrs_from_contract set_X2_to_42 instrs_loc
          ∗ asn.interpret (extract_post_from_contract set_X2_to_42)
              [env].["a"∷ty_xlenbits ↦ instrs_loc].["an"∷ty_xlenbits ↦ an].

      Definition set_X2_to_42_contract (instrs_loc : Val ty_xlenbits) : iProp Σ :=
        iris_contract (set_X2_to_42_pre instrs_loc) (set_X2_to_42_post instrs_loc).

      Lemma set_X2_to_42_verified : ∀ instrs_loc,
          ⊢ set_X2_to_42_contract instrs_loc.
      Proof.
        iIntros (instrs_loc) "Hpre Hk".
        iApply (sound_sblock_verification_condition valid_set_X2_to_42
                  [env] $! instrs_loc with "Hpre [Hk]").
        iIntros (an) "H".
        iApply "Hk".
        by iExists an.
      Qed.
  End WithSailResources.
End Examples.
