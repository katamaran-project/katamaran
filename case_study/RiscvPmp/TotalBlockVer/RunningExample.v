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
     RiscvPmp.TotalBlockVer.Spec
     RiscvPmp.TotalBlockVer.Verifier
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.Verifier
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

    Definition PRE : AssertionWith [ "a" :: ty_xlenbits ] :=
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N adv_addr) < term_val ty.int (Z.of_N maxAddr))%asn ∗
      mstatus ↦ term_val (ty.record rmstatus) {| MPP := User |} ∗
      (∃ "v", mtvec ↦ term_var "v") ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      mepc ↦ term_val ty_xlenbits (bv.of_N adv_addr) ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      asn_regs_ptsto ∗
      asn_pmp_entries term_pmp_cfg.

    Definition POST : AssertionWith ["a" :: ty_xlenbits; "an" :: ty_xlenbits] :=
      (term_var "an" = term_val ty_xlenbits (bv.of_N adv_addr))%asn ∗
      (∃ "v", mstatus ↦ term_var "v") ∗
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
  (* First version of the running example is the bare minimum, just making sure
     that all the building blocks fit together. The example is a MRET instr,
     with the entire memory and all registers public (i.e., there are no secrets). *)

  (* Reuse the existing PRE and POST defined in UnaryCheck (doesn't specify
     which logic to use for the block verifier, so this should be fine). *)
  Definition PRE := UnaryCheck.PRE.
  Definition POST := UnaryCheck.POST.

  Definition vc_code : 𝕊 ε :=
    postprocess (TotalBlockVer.Verifier.sblock_verification_condition PRE code POST wnil).

  Lemma sat_code : TotalBlockVer.Verifier.safeE vc_code.
  Proof.
    vm_compute.
    constructor; cbn.
    intuition; bv_solve_Ltac.solveBvManual.
  Qed.

  Section WithIris.
    Import iris.program_logic.weakestpre.
    Import iris.proofmode.tactics.
    Import RiscvPmpIrisBase2.
    Import RiscvPmpIrisInstance2.

    #[local] Notation "a '↦ᵣ' t" := (reg_pointsTo2 a t t).

    (* Ref: femto_handler_pre *)
    Definition iPRE `{sailGS2 Σ} : iProp Σ :=
      mstatus ↦ᵣ {| MPP := User |} ∗
      (∃ v, mtvec ↦ᵣ v) ∗
      (∃ v, mcause ↦ᵣ v) ∗
      mepc ↦ᵣ (bv.of_N adv_addr) ∗
      cur_privilege ↦ᵣ Machine ∗
      interp_gprs ∗
      interp_pmp_entries pmp_cfg.

    Definition iPOST `{sailGS2 Σ} : iProp Σ :=
      (∃ v, mstatus ↦ᵣ v) ∗
      (∃ v, mtvec ↦ᵣ v) ∗
      (∃ v, mcause ↦ᵣ v) ∗
      (∃ v, mepc ↦ᵣ v) ∗
      cur_privilege ↦ᵣ User ∗
      interp_gprs ∗
      interp_pmp_entries pmp_cfg.

    Import IrisInstance.RiscvPmpIrisInstance.
    Print WP2_loop.
    Definition contract `{sailGS2 Σ} : iProp Σ :=
      semTTriple [env] iPRE fun_step (λ _ _, iPOST).

    Definition contract `{sailGS2 Σ} : iProp Σ :=
      iPRE -∗
        (iPOST -∗ WP2_loop) -∗
          WP2_loop.

    Lemma contract_verified : ∀ `{sailGS2 Σ}, ⊢ contract.
    Proof.
      iIntros (Σ sG) "Hpre Hk".
      iDestruct "Hpre" as "((Hmstatus₁ & Hmstatus₂) & (%mtvec & Hmtvec₁ & Hmtvec₂)
                          & (%mcause & Hmcause₁ & Hmcause₂) & (Hmepc₁ & Hmepc₂)
                          & (Hcp₁ & Hcp₂) & Hgprs & Hpmp)".
      iPoseProof (RiscvPmpModel2.interp_pmpentries_dedup with "Hpmp") as "(Hpmp₁ & Hpmp₂)".
      iPoseProof (RiscvPmpModel2.interp_gprs_split with "Hgprs") as "(Hgprs₁ & Hgprs₂)".
      iApply semWP2_focus.

      
      iApply semWP2_anaglyph.
      iApply (semWP_mono with "[-]").
      - iApply (sound_sblock_verification_condition with "[-Hk Hmstatus₂ Hmtvec₂ Hmcause₂ Hmepc₂ Hcp₂ Hpmp₂ Hgprs₂] [Hk Hmstatus₂ Hmtvec₂ Hmcause₂ Hmepc₂ Hcp₂ Hpmp₂ Hgprs₂]").
        + apply UnaryCheck.sat_code.
        + cbn - [asn_regs_ptsto].
          iPoseProof (@Model.RiscvPmpModel2.gprs_equiv _ RiscvPmpModel2.sailGS2_sailGS_left with "Hgprs₁") as "Hgprs₁".
          iFrame "Hmstatus₁ Hmtvec₁ Hmcause₁ Hmepc₁ Hcp₁ Hpmp₁ Hgprs₁".
          admit (* TODO: missing some stuff in the pre and post above :) *).
        + cbn.
          iIntros (an) "(Hpc₁ & Hnpc₁ & Hhandler & H & Hmstatus₁ & Hmtvec₁ & Hmcause₁ & Hmepc₁ & Hcurpriv₁ & Hregs₁ & Hpmp₁)".
          unfold iPOST.
          iSpecialize ("Hk" with "[$Hmstatus]").
      -

  End WithIris.

End RunningExample.
