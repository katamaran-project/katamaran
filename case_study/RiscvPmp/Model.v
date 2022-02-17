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
     Lists.List.
From RiscvPmp Require Import
     Machine
     Contracts.
From Katamaran Require Import
     Bitvector
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
From iris.proofmode Require Import string_ident tactics.

Set Implicit Arguments.
Import ListNotations.

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
    Variable maxAddr : nat.

    Section WithIrisNotations.
      Import iris.bi.interface.
      Import iris.bi.big_op.
      Import iris.base_logic.lib.iprop.
      Import iris.base_logic.lib.gen_heap.

      Definition MemVal : Set := Word.

      Class mcMemGS Σ :=
        McMemGS {
            (* ghost variable for tracking state of registers *)
            mc_ghGS :> gh.gen_heapGS Addr MemVal Σ;
            mc_invNs : namespace
          }.

      Definition memGpreS : gFunctors -> Set := fun Σ => gh.gen_heapGpreS Z MemVal Σ.
      Definition memGS : gFunctors -> Set := mcMemGS.
      Definition memΣ : gFunctors := gh.gen_heapΣ Addr MemVal.

      Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ :=
        fun {Σ} => gh.subG_gen_heapGpreS (Σ := Σ) (L := Addr) (V := MemVal).

      Definition mem_inv : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
        fun {Σ} mG μ => (True)%I.

      Definition mem_res : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
        fun {Σ} mG μ => (True)%I.

      Definition liveAddrs := seqZ 0 maxAddr.
      Definition initMemMap μ := (list_to_map (map (fun a => (a , μ a)) liveAddrs) : gmap Addr MemVal).

      Lemma initMemMap_works μ : map_Forall (λ (a : Addr) (v : MemVal), μ a = v) (initMemMap μ).
      Proof.
        unfold initMemMap.
        rewrite map_Forall_to_list.
        rewrite Forall_forall.
        intros (a , v).
        rewrite elem_of_map_to_list.
        intros el.
        apply elem_of_list_to_map_2 in el.
        apply elem_of_list_In in el.
        apply in_map_iff in el.
        by destruct el as (a' & <- & _).
      Qed.

      Lemma mem_inv_init : forall Σ (μ : Memory), memGpreS Σ ->
        ⊢ |==> ∃ mG : memGS Σ, (mem_inv mG μ ∗ mem_res mG μ)%I.
      Proof.
        iIntros (Σ μ gHP).
        iMod (gen_heap_init (gen_heapGpreS0 := gHP) (L := Addr) (V := MemVal)) as (gH) "[inv _]".
        Unshelve.
        iModIntro.
        iExists (McMemGS gH (nroot .@ "addr_inv")).
        unfold mem_inv, mem_res.
        done.
        apply initMemMap; auto.
      Qed.

      Import Contracts.

      Definition reg_file : gset (bv 2) :=
        list_to_set (finite.enum (bv 2)).

      Definition interp_ptsreg `{sailRegGS Σ} (r : RegIdx) (v : Z) : iProp Σ :=
        match reg_convert r with
        | Some x => reg_pointsTo x v
        | None => True
        end.

      Definition interp_gprs `{sailRegGS Σ} : iProp Σ :=
        [∗ set] r ∈ reg_file, (∃ v, interp_ptsreg r v)%I.

      Definition PmpEntryCfg : Set := Pmpcfg_ent * Xlenbits.

      Definition interp_pmp_entries `{sailRegGS Σ} (entries : list PmpEntryCfg) : iProp Σ :=
        match entries with
        | (cfg0, addr0) :: (cfg1, addr1) :: [] =>
            reg_pointsTo pmp0cfg cfg0 ∗
            reg_pointsTo pmpaddr0 addr0 ∗
            reg_pointsTo pmp1cfg cfg1 ∗
            reg_pointsTo pmpaddr1 addr1
        | _ => False
        end.

      Definition PmpAddrRange := option (Xlenbits * Xlenbits).

      Definition pmp_addr_range (cfg : Pmpcfg_ent) (hi lo : Xlenbits) : PmpAddrRange :=
        match A cfg with
        | OFF => None
        | TOR => Some (lo , hi)
        end.

      Definition pmp_match_addr (a : Addr) (rng : PmpAddrRange) : PmpAddrMatch :=
        match rng with
        | Some (lo, hi) =>
            if hi <? lo
            then PMP_NoMatch
            else if (a<? lo) || (hi <? a)
                 then PMP_NoMatch
                 else if (lo <=? a) && (a <=? hi)
                      then PMP_Match
                      else PMP_PartialMatch
        | None          => PMP_NoMatch
        end.

      (* Ignore execute perm for now *)
      Inductive Permission : Set :=
      | O
      | R
      | W
      | RW.

      Definition translate_perm_from_cfg (cfg : Pmpcfg_ent) : Permission :=
        match Base.R cfg, Base.W cfg with
        | false, false => O
        | true, false  => R
        | false, true  => W
        | true, true   => RW
        end.

      Definition pmp_permission (m : Privilege) (cfg : Pmpcfg_ent) : Permission :=
        let p := translate_perm_from_cfg cfg in
        match m, L cfg with
        | User,    _    => p
        | Machine, true => p (* only restrict Machine mode if PMP entry is locked *)
        | Machine, _    => RW
        end.

      Definition pmp_match_entry (a : Addr) (m : Privilege) (cfg : Pmpcfg_ent) (lo hi : Xlenbits) : PmpMatch * Permission :=
        let rng := pmp_addr_range cfg hi lo in
        match pmp_match_addr a rng with
        | PMP_NoMatch      => (PMP_Continue , O)
        | PMP_PartialMatch => (PMP_Fail, O)
        | PMP_Match        => (PMP_Success, pmp_permission m cfg)
        end.

      Fixpoint pmp_check (a : Addr) (entries : list PmpEntryCfg) (prev : Addr) (m : Privilege) : option Permission :=
        match entries with
        | [] => None
        | (cfg , addr) :: entries =>
            match pmp_match_entry a m cfg prev addr with
            | (PMP_Success , p) => Some p
            | (PMP_Fail, _)     => None
            | (PMP_Continue, _) => pmp_check a entries addr m
            end
        end.

      (* check_access is based on the pmpCheck algorithm, main difference
         is that we can define it less cumbersome because entries will contain
         the PMP entries in highest-priority order. *)
      Definition check_access (a : Addr) (entries : list PmpEntryCfg) (m : Privilege) : option Permission :=
        pmp_check a entries 0 m.

      (* TODO: add perm_access predicate *)
      (* pmp_addr_access(?entries, ?mode) 
         ∀ a ∈ Mem, p : Perm . check_access(a, entries, mode) = Some p -> 
                               ∃ w . a ↦ w ∗ perm_access(a, p) *)
      Definition interp_pmp_addr_access `{sailRegGS Σ} `{invGS Σ} {mG : memGS Σ} (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
        [∗ list] a ∈ liveAddrs,
          (⌜∃ p, check_access a entries m = Some p⌝ -∗
            (∃ w, mapsto (hG := mc_ghGS (mcMemGS := mG)) a (DfracOwn 1) w))%I.

      Definition luser_inst `{sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) (p : Predicate) : Env Val (𝑯_Ty p) -> iProp Σ :=
        match p return Env Val (𝑯_Ty p) -> iProp Σ with
        | pmp_entries     => fun ts => interp_pmp_entries (env.head ts)
        | pmp_addr_access => fun ts => interp_pmp_addr_access (mG := mG) (env.head (env.tail ts)) (env.head ts)
        | gprs            => fun _  => interp_gprs
        | ptsto           => fun _  => True%I (* TODO: interp_ptst *)
        end.

    Definition lduplicate_inst `{sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) :
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

  Lemma foreignSem `{sg : sailGS Σ} : ForeignSem (Σ := Σ).
  Proof.
    intros Γ τ Δ f es δ.
    destruct f; cbn.
  Admitted.

  Section Lemmas.
    Context `{sg : sailGS Σ}.

    Lemma open_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      unfold RiscvPmpIrisHeapKit.interp_gprs, RiscvPmpIrisHeapKit.reg_file.
      rewrite big_sepS_list_to_set; [|apply finite.NoDup_enum]; cbn.
      iIntros "[_ [Hx1 [Hx2 [Hx3 _]]]]". iFrame.
    Qed.

    Lemma close_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      unfold RiscvPmpIrisHeapKit.interp_gprs, RiscvPmpIrisHeapKit.reg_file.
      iIntros "[Hx1 [Hx2 Hx3]]".
      iApply big_sepS_list_to_set; [apply finite.NoDup_enum|].
      cbn; iFrame. eauto using 0%Z.
    Qed.
  End Lemmas.

  Lemma lemSem `{sg : sailGS Σ} : LemmaSem (Σ := Σ).
  Proof.
    intros Δ [];
      eauto using open_gprs_sound, close_gprs_sound.
  Qed.
End RiscvPmpModel.
