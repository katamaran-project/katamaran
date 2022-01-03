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

From RiscvPmp Require Import
     Machine
     Contracts.
From Katamaran Require Import
     Environment
     Program
     Specification
     Sep.Hoare
     Sep.Logic
     Semantics
     Iris.Model.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Set Implicit Arguments.

Module gh := iris.base_logic.lib.gen_heap.

Module RiscvPmpSemantics <: Semantics RiscvPmpBase RiscvPmpProgram :=
  MakeSemantics RiscvPmpBase RiscvPmpProgram.

Module RiscvPmpModel.
  Import RiscvPmpProgram.
  Import RiscvPmpSpecification.

  Include ProgramLogicOn RiscvPmpBase RiscvPmpSpecification.
  Include Iris RiscvPmpBase RiscvPmpSpecification RiscvPmpSemantics.

  Ltac destruct_syminstance ι :=
    repeat
      match type of ι with
      | Env _ (ctx.snoc _ (MkB ?s _)) =>
        let id := string_to_ident s in
        let fr := fresh id in
        destruct (env.snocView ι) as [ι fr];
        destruct_syminstance ι
      | Env _ ctx.nil => destruct (env.nilView ι)
      | _ => idtac
      end.

  Module RiscvPmpIrisHeapKit <: IrisHeapKit.

    Section WithIrisNotations.
      Import iris.bi.interface.
      Import iris.bi.big_op.
      Import iris.base_logic.lib.iprop.
      Import iris.base_logic.lib.gen_heap.

      Definition MemVal : Set := Word.

      Class mcMemG Σ := McMemG {
                            (* ghost variable for tracking state of registers *)
                            mc_ghG :> gh.gen_heapG Addr MemVal Σ;
                            mc_invNs : namespace
                          }.

      Definition memPreG : gFunctors -> Set := fun Σ => gh.gen_heapPreG Z MemVal Σ.
      Definition memG : gFunctors -> Set := mcMemG.
      Definition memΣ : gFunctors := gh.gen_heapΣ Addr MemVal.

      Definition memΣ_PreG : forall {Σ}, subG memΣ Σ -> memPreG Σ := fun {Σ} => gh.subG_gen_heapPreG (Σ := Σ) (L := Addr) (V := MemVal).

      Definition mem_inv : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
        fun {Σ} hG μ => (True)%I.

      Definition mem_res : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
        fun {Σ} hG μ => (True)%I.

      Lemma mem_inv_init : forall Σ (μ : Memory), memPreG Σ ->
                                                  ⊢ |==> ∃ memG : memG Σ, (mem_inv memG μ ∗ mem_res memG μ)%I.
      Admitted.

      Import Contracts.

      Definition interp_ptsreg `{sailRegG Σ} (r: RegIdx) (v : Z) : iProp Σ :=
        match r with
        | 1%Z => reg_pointsTo x1 v
        | 2%Z => reg_pointsTo x2 v
        | 3%Z => reg_pointsTo x3 v
        | _   => False
        end.

      Definition reg_file : gset RegIdx := list_to_set (seqZ 1 3).

      Lemma seqZ_list : seqZ 1 3 = [1;2;3]%Z.
      Proof.
        unfold seqZ; now cbv.
      Qed.

      Definition interp_gprs `{sailRegG Σ} : iProp Σ :=
        [∗ set] r ∈ reg_file, (∃ v, interp_ptsreg r v)%I.

      Definition luser_inst `{sailRegG Σ} `{invG Σ} (mG : memG Σ) (p : Predicate) : Env Val (𝑯_Ty p) -> iProp Σ :=
        match p return Env Val (𝑯_Ty p) -> iProp Σ with
        | pmp_entries  => fun ts => let entries_lst := env.head ts in
                                    match entries_lst with
                                    | (cfg0, addr0) :: [] =>
                                      (reg_pointsTo pmp0cfg cfg0 ∗
                                              reg_pointsTo pmpaddr0 addr0)%I
                                    | _ => False%I
                                    end
        | ptsreg       => fun ts => interp_ptsreg (env.head (env.tail ts)) (env.head ts)
        | gprs         => fun _  => interp_gprs
        end.

    Definition lduplicate_inst `{sailRegG Σ} `{invG Σ} (mG : memG Σ) :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst mG p ts) ⊢ (luser_inst mG p ts ∗ luser_inst mG p ts).
    Proof.
      iIntros (p ts hdup) "H".
      destruct p; inversion hdup;
      iDestruct "H" as "#H";
      auto.
    Qed.

    End WithIrisNotations.
  End RiscvPmpIrisHeapKit.

  Module Import RiscvPmpIrisInstance := IrisInstance RiscvPmpIrisHeapKit.

  Lemma foreignSem `{sg : sailG Σ} : ForeignSem (Σ := Σ).
  Proof.
    intros Γ τ Δ f es δ.
    destruct f; cbn.
  Admitted.

  Section Lemmas.
    Context `{sg : sailG Σ}.

    Lemma open_ptsreg_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_ptsreg.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      unfold RiscvPmpIrisHeapKit.interp_ptsreg.
      destruct rs; auto.
      repeat (destruct p; auto).
    Qed.

    Lemma close_ptsreg_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_ptsreg.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      destruct rs; cbn; iFrame; try (iIntros "[%H _]"; inversion H).
      repeat (destruct p;
              try (iIntros "[%H _]"; inversion H);
              try (iIntros; iAccu)).
    Qed.

    Lemma open_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      unfold RiscvPmpIrisHeapKit.interp_gprs, RiscvPmpIrisHeapKit.reg_file.
      rewrite big_sepS_list_to_set; [|apply NoDup_seqZ].
      rewrite RiscvPmpIrisHeapKit.seqZ_list; cbn.
      iIntros "[Hx1 [Hx2 [Hx3 _]]]".
      iSplitL "Hx1"; [iAssumption|].
      iSplitL "Hx2"; iAssumption.
    Qed.

    Lemma close_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      unfold RiscvPmpIrisHeapKit.interp_gprs, RiscvPmpIrisHeapKit.reg_file.
      iIntros "[Hx1 [Hx2 Hx3]]".
      iApply big_sepS_list_to_set; [apply NoDup_seqZ|].
      rewrite RiscvPmpIrisHeapKit.seqZ_list; cbn; iFrame.
    Qed.
  End Lemmas.

  Lemma lemSem `{sg : sailG Σ} : LemmaSem (Σ := Σ).
  Proof.
    intros Δ [];
      eauto using open_ptsreg_sound, close_ptsreg_sound, open_gprs_sound,
                  close_gprs_sound.
  Qed.
End RiscvPmpModel.
