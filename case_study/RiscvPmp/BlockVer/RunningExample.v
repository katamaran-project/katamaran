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
     RiscvPmp.BlockVer.PartialVerifier
     RiscvPmp.BlockVer.TotalVerifier
     RiscvPmp.Machine
     RiscvPmp.Sig
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstanceBinary
     RiscvPmp.ModelBinary.

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
From Katamaran Require Import RiscvPmp.LoopVerificationBinary.

Module AsnNotations.
  Export asn.notations.
  Export TermNotations.
  Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).
  Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
End AsnNotations.

Section Utils.
  Definition Block : Set := list AST.

  Definition bytes_per_instr : nat := 4.

  Definition addr_after_block : Block -> N :=
    N.of_nat ∘ mult bytes_per_instr ∘ List.length.

  Definition AssertionWith (Σ : LCtx) := Assertion {| wctx := Σ; wco := []%ctx |}.

  Section WithAsnNotations.
    Import AsnNotations.

    Definition pmp_cfg : list PmpCheck.PmpEntryCfg :=
      [(default_pmpcfg_ent , bv.zero); (default_pmpcfg_ent , bv.zero)].

    (* TODO: port this into something shared so femto can reuse this (without needing to specify this kind of stuff once as a term, and once as a list! *)
    Definition pmp_cfg_to_term {Σ} : list PmpCheck.PmpEntryCfg -> list (Term Σ (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
      let term_cfg cfg := term_val ty_pmpcfg_ent cfg in
      let term_addr a  := term_val ty_xlenbits a in
      map (fun '(cfg , addr) => term_binop bop.pair (term_cfg cfg) (term_addr addr)).

    Definition term_pmp_cfg {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
      term_list (pmp_cfg_to_term pmp_cfg).
  End WithAsnNotations.
End Utils.

Section Code.
  Definition code : list AST :=
    [ MRET ].

  Definition adv_addr : N := addr_after_block code.
End Code.

Module UnaryCheck.
  (* UnaryCheck contains a unary version of the contracts. This is used as a
     sanity check to be confident that, when we split the binary verification
     into two unary ones, it should hold. *)

  Section WithAsnNotations.
    Import AsnNotations.

    (* TODO: in both pre and post, we are missing some regs (pc, npc) and
             ptsto_instrs chunks. *)
    Definition PRE : AssertionWith [ "a" :: ty_xlenbits ] :=
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N adv_addr) < term_val ty.int (Z.of_N maxAddr))%asn ∗
      (∃ "mpie", mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mpie"; term_val ty.bool false ]) ∗
      (∃ "mip", mip ↦ term_var "mip") ∗ (∃ "mie", mie ↦ term_var "mie") ∗
      (∃ "v", mtvec ↦ term_var "v") ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      mepc ↦ term_val ty_xlenbits (bv.of_N adv_addr) ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      asn_regs_ptsto ∗
      asn_pmp_entries term_pmp_cfg.

    Definition POST : AssertionWith ["a" :: ty_xlenbits; "an" :: ty_xlenbits] :=
      (term_var "an" = term_val ty_xlenbits (bv.of_N adv_addr))%asn ∗
      (∃ "v", mstatus ↦ term_var "v") ∗
      (∃ "mip", mip ↦ term_var "mip") ∗
      (∃ "mie", mie ↦ term_var "mie") ∗
      (∃ "v", mtvec ↦ term_var "v") ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (∃ "v", mepc ↦ term_var "v") ∗
      cur_privilege ↦ term_val ty_privilege User ∗
      asn_regs_ptsto ∗
      asn_pmp_entries term_pmp_cfg.
  End WithAsnNotations.

  Definition vc_code : 𝕊 ε :=
    postprocess (BlockVer.Verifier.sblock_verification_condition PRE code POST wnil).

  Lemma sat_code : safeE vc_code.
  Proof.
    vm_compute.
    constructor; cbn.
    intuition; bv_solve_Ltac.solveBvManual.
  Qed.

  (* At this point we can be sure that the unary version works. Obviously this
     is only a valid statement if the binary assertions are correctly defined. *)
End UnaryCheck.

Module RunningExample.
  Import TotalBlockVer.Verifier.
  (* First version of the running example is the bare minimum, just making sure
     that all the building blocks fit together. The example is a MRET instr,
     with the entire memory and all registers public (i.e., there are no secrets). *)

  (* Reuse the existing PRE and POST defined in UnaryCheck (doesn't specify
     which logic to use for the block verifier, so this should be fine). *)
  Definition PRE := UnaryCheck.PRE.
  Definition POST := UnaryCheck.POST.

  Section TotalVerif.
    Import IrisInstance.RiscvPmpIrisInstance.
    Import IrisModel.RiscvPmpIrisBase.

    Definition vc_code : 𝕊 ε :=
      (* We need the vm_compute here, otherwise Rocq will spin forever when we
         try to apply sat_code further down. *)
      Eval vm_compute in postprocess2 (sblock_verification_condition PRE code POST wnil).

    Lemma sat_code : TotalBlockVer.Verifier.safeE vc_code.
    Proof.
      constructor; cbn.
      intuition; bv_solve_Ltac.solveBvManual.
    Qed.

    Definition iPRE `{sailGS Σ} (a : Val ty_xlenbits) : iProp Σ :=
      asn.interpret PRE [env].["a" :: ty_xlenbits ↦ a].

    Definition iPOST `{sailGS Σ} (a an : Val ty_xlenbits) : iProp Σ :=
      asn.interpret POST [env].["a" :: ty_xlenbits ↦ a].["an" :: ty_xlenbits ↦ an].

    Definition contract_step `{sailGS Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock iPRE a code iPOST.

    Section WithIris.
      Import iris.program_logic.weakestpre.
      Import iris.proofmode.tactics.

      Lemma contract_step_verified : ∀ `{sailGS Σ} (a : Val ty_xlenbits), ⊢ contract_step a.
      Proof.
        unfold contract_step.
        iIntros (Σ sg a).
        iApply sound_sblock_verification_condition.
        apply sat_code.
      Qed.

    End WithIris.
  End TotalVerif.

  Section WithIris.
    Import iris.program_logic.weakestpre.
    Import iris.proofmode.tactics.
    Import RiscvPmpIrisBase2.
    Import RiscvPmpIrisInstance2.

    #[local] Notation "a '↦ᵣ' t" := (reg_pointsTo2 a t t).

    Definition iPRE2 `{sailGS2 Σ} (a : Val ty_xlenbits) : iProp Σ :=
      asn.interpret PRE [env].["a" :: ty_xlenbits ↦ a].

    Definition iPOST2 `{sailGS2 Σ} (a an : Val ty_xlenbits) : iProp Σ :=
      asn.interpret POST [env].["a" :: ty_xlenbits ↦ a].["an" :: ty_xlenbits ↦ an].

    Import RiscvPmpIrisInstance2.

    Fixpoint ptsto_instrs2 `{sailGS2 Σ} (a : Val ty_word) (instrs : list AST) : iProp Σ :=
      match instrs with
      | cons inst insts => (interp_ptsto_instr a inst ∗ ptsto_instrs2 (bv.add a bv_instrsize) insts)%I
      | nil => True%I
      end.

    Definition semTripleBlock2 {Σ} `{sailGS2 Σ} (PRE : Val ty_xlenbits -> iProp Σ) (instrs : list AST) (POST : Val ty_xlenbits -> Val ty_xlenbits -> iProp Σ) : iProp Σ :=
      (∀ a,
         (PRE a ∗ pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs2 a instrs) -∗
         (∀ an, pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs2 a instrs ∗ POST a an -∗ WP2_loop) -∗
         WP2_loop)%I.
    #[global] Arguments semTripleBlock2 {_ _} PRE%_I instrs POST%_I.

    Definition contract_step2 `{sailGS2 Σ} : iProp Σ :=
      semTripleBlock2 iPRE2 code iPOST2.

    Section MoveToBinaryWeakestPre.
      Fixpoint semWP2_n `{sailGS2 Σ} {Γ τ} (n : nat)
        (δ1 : CStore Γ) (δ2 : CStore Γ) (s1 : Stm Γ τ) (s2 : Stm Γ τ)
        (POST : IVal τ -> CStore Γ -> IVal τ -> CStore Γ -> iProp Σ) : iProp Σ :=
        match n with
        | O => ∀ v1 δ1 v2 δ2, POST v1 δ1 v2 δ2
        | S n => semWP2 δ1 δ2 s1 s2 (λ v1 δ1' v2 δ2',
                     ⌜v1 = v2⌝ ∗ ⌜δ1' = δ2'⌝ ∗ semWP2_n n δ1 δ2 s1 s2 POST)%I
        end.

      Lemma semWP2_n_mono `{sailGS2 Σ} {Γ τ} (n : nat)
        (δ1 : CStore Γ) (δ2 : CStore Γ) (s1 : Stm Γ τ) (s2 : Stm Γ τ)
        (POST1 POST2 : IVal τ -> CStore Γ -> IVal τ -> CStore Γ -> iProp Σ) :
        semWP2_n n δ1 δ2 s1 s2 POST1 -∗
        (∀ v1 δ1 v2 δ2, POST1 v1 δ1 v2 δ2 -∗ POST2 v1 δ1 v2 δ2) -∗
        semWP2_n n δ1 δ2 s1 s2 POST2.
      Proof.
        revert δ1 δ2 POST1 POST2.
        iInduction n as [|n]; iIntros (δ1 δ2 POST1 POST2).
        - iIntros "POST1 HPOSTS".
          cbn. iIntros (v1 δ1' v2 δ2').
          now iApply "HPOSTS".
        - iIntros "Hwp HPOSTS".
          cbn.
          iApply (semWP2_mono with "Hwp").
          iIntros (v1 δ1' v2 δ2') "(<- & <- & H)"; auto.
          repeat iSplitR; auto.
          iApply ("IHn" with "H").
          iIntros (? ? ? ?) "H".
          now iApply "HPOSTS".
      Qed.

      Lemma semWP2_S_n_twp_seq {Σ} {sG : sailGS2 Σ} {Γ τ} (n : nat) {s1 : Stm Γ τ} {s2 : Stm Γ τ} :
        ⊢ ∀ Q δ1 δ2,
            @semTWP _ sailGS2_sailGS_left _ _ δ1 s1 (λ v1 δ1',
                @semTWP _ sailGS2_sailGS_right _ _ δ2 s2 (λ v2 δ2',
                    ⌜v1 = v2⌝ ∗ ⌜δ1' = δ2'⌝ ∗
                    semWP2_n n δ1 δ2 s1 s2 Q)) -∗
          semWP2_n (S n) δ1 δ2 s1 s2 Q.
      Proof.
        simpl. iIntros (Q δ1 δ2) "H".
        now iApply semWP2_focus_seq.
      Qed.

      Definition semTriple_n {Σ} `{sailGS2 Σ} {Γ τ} (n : nat) (δ : CStore Γ)
        (PRE : iProp Σ) (s : Stm Γ τ) (POST : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
        PRE -∗ semWP2_n n δ δ s s (λ v1 δ1 v2 δ2, match v1 with
                                                  | inl v1 => POST v1 δ1
                                                  | inr _ => True
                                                  end)%I.
      #[global] Arguments semTriple_n {Σ} {_} {Γ} {τ} n%nat δ PRE%_I s%_exp POST%_I.

    End MoveToBinaryWeakestPre.

    Lemma WP2_loop_split `{sg : sailGS2 Σ} : ∀ PRE POST,
      PRE -∗
      (semTriple [env] PRE fun_step POST ∗ (∀ v1 δ1, POST v1 δ1 -∗ WP2_loop)) -∗
      WP2_loop.
    Proof.
      iIntros (PRE POST) "HPRE (Htrip & Hk)".
      unfold semTriple.
      iSpecialize ("Htrip" with "HPRE").
      unfold WP2_loop at 2.
      cbn [FunDef]. unfold fun_loop.
      iApply semWP2_seq.
      iApply semWP2_call_inline.
      iApply (semWP2_mono with "Htrip").
      iIntros (v1 δ1 v2 δ2) "(-> & -> & H)".
      destruct v2 as [v|m].
      - iSpecialize ("Hk" with "H").
        now iApply semWP2_call_inline.
      - now iApply semWP2_fail.
    Qed.

    Lemma WP2_loop_split_n `{sg : sailGS2 Σ} : ∀ n POST,
      (semWP2_n n [env] [env] fun_step fun_step POST ∗ (∀ v1 δ1 v2 δ2, POST v1 δ1 v2 δ2 -∗ WP2_loop)) -∗
      WP2_loop.
    Proof.
      iLöb as "IH".
      iIntros ([] POST) "(Htrip & Hk)".
      - iApply ("Hk" with "[Htrip]").
        iSpecialize ("Htrip" $! (inl ()) [env] (inl ()) [env]).
        iExact "Htrip".
      - unfold WP2_loop at 4.
        cbn [FunDef]. unfold fun_loop.
        iApply semWP2_seq.
        iApply semWP2_call_inline_later. simpl. iModIntro.
        iApply (semWP2_mono with "Htrip").
        iIntros (? ? [] δ2) "(-> & -> & H)".
        + iApply semWP2_call_inline.
          destruct (env.view δ2).
          iApply ("IH" with "[$H $Hk]").
        + now iApply semWP2_fail.
    Qed.

    Lemma WP2_loop_split_n' `{sg : sailGS2 Σ} : ∀ n PRE POST,
      PRE -∗
      (semTriple_n n [env] PRE fun_step POST ∗ (∀ v1 δ1, POST v1 δ1 -∗ WP2_loop)) -∗
      WP2_loop.
    Proof.
      iLöb as "IH".
      iIntros (n).
      iInduction n as [|];
        iIntros (PRE POST) "HPre (Htrip & Hk)".
      - iSpecialize ("Htrip" with "HPre"). simpl.
        iApply ("Hk" with "[Htrip]").
        iSpecialize ("Htrip" $! (inl ()) [env] (inl ()) [env]).
        iExact "Htrip".
      - iSpecialize ("Htrip" with "HPre"). simpl.
        unfold WP2_loop at 6.
        cbn [FunDef]. unfold fun_loop.
        iApply semWP2_seq.
        iApply semWP2_call_inline_later. simpl. iModIntro.
        iApply (semWP2_mono with "Htrip").
        iIntros (? ? [] ?) "(-> & -> & H)".
        + admit.
        + now iApply semWP2_fail.
    Abort.

    Lemma contract_step2_verified : ∀ `{sailGS2 Σ}, ⊢ contract_step2.
    Proof.
      unfold contract_step2.
      iIntros (Σ sG a) "HPRE Hk".
      iApply (WP2_loop_split_n (length code)).
      iSplitR "Hk".
      - unfold code.
        iApply semWP2_S_n_twp_seq.
        admit.
      - iIntros (v1 δ1 v2 δ2) "H". iApply "Hk".
        iExact "H".
    Admitted.
  End WithIris.

End RunningExample.
