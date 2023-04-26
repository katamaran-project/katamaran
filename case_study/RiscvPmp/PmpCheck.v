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
     Lists.List.
From Katamaran Require Import
     Bitvector
     RiscvPmp.Base.
From iris.proofmode Require Import
     tactics.

Import ListNotations.
Import bv.notations.

Ltac bv_comp :=
  repeat match goal with
    | H: (?a <ᵘ? ?b) = true |- _ =>
        rewrite bv.ultb_ult in H
    | H: (?a <ᵘ? ?b) = false |- _ =>
        rewrite bv.ultb_uge in H
    | H: (?a <=ᵘ? ?b) = true |- _ =>
        rewrite bv.uleb_ule in H
    | H: (?a <=ᵘ? ?b) = false |- _ =>
        rewrite bv.uleb_ugt in H
    | H: (?P || ?Q)%bool = true |- _ =>
        apply Bool.orb_true_iff in H as [?|?]
    end.

Ltac bv_comp_bool :=
  repeat match goal with
    | H: ?a <ᵘ ?b |- _ =>
        rewrite ? (proj2 (bv.ultb_ult _ _) H)
                ? (proj2 (bv.uleb_ugt _ _) H);
        clear H
    | H: ?a <=ᵘ ?b |- _ =>
        rewrite ? (proj2 (bv.uleb_ule _ _) H)
                ? (proj2 (bv.ultb_uge _ _) H);
        clear H
    | H: ?a <=ᵘ ?b /\ _ |- _ =>
        destruct H
    | H: ?a <ᵘ ?b /\ _ |- _ =>
        destruct H
    end.

Section Implementation.
  Definition PmpEntryCfg : Set := Pmpcfg_ent * Xlenbits.
  Definition PmpAddrRange := option (Xlenbits * Xlenbits).

  Definition pmp_addr_range (cfg : Pmpcfg_ent) (pmpaddr prev_pmpaddr : Xlenbits) : PmpAddrRange :=
    match A cfg with
    | OFF => None
    | TOR => Some (prev_pmpaddr , pmpaddr)
    | NA4 => Some (pmpaddr , bv.add pmpaddr (bv.of_nat 4))
    end.

  Definition pmp_match_addr (a : Xlenbits) (width : Xlenbits) (rng : PmpAddrRange) : PmpAddrMatch :=
    match rng with
    | Some (lo, hi) =>
        if hi <ᵘ? lo
        then PMP_NoMatch
        else if ((a + width <=ᵘ? lo)%bv || (hi <=ᵘ? a))%bool
             then PMP_NoMatch
             else if ((lo <=ᵘ? a) && (a + width <=ᵘ? hi)%bv)%bool
                  then PMP_Match
                  else PMP_PartialMatch
    | None          => PMP_NoMatch
    end.

  Definition pmp_match_entry (a width : Xlenbits) (m : Privilege) (cfg : Pmpcfg_ent) (lo hi : Xlenbits) : PmpMatch :=
    let rng := pmp_addr_range cfg hi lo in
    match pmp_match_addr a width rng with
    | PMP_NoMatch      => PMP_Continue
    | PMP_PartialMatch => PMP_Fail
    | PMP_Match        => PMP_Success
    end.

  Equations(noeqns) decide_access_pmp_perm (a : AccessType) (p : PmpCfgPerm) : bool :=
  | Read      | PmpR   := true;
  | Read      | PmpRW  := true;
  | Read      | PmpRX  := true;
  | Write     | PmpW   := true;
  | Write     | PmpRW  := true;
  | Write     | PmpWX  := true;
  | ReadWrite | PmpRW  := true;
  | Execute   | PmpX   := true;
  | Execute   | PmpRX  := true;
  | Execute   | PmpWX  := true;
  | _         | PmpRWX := true;
  | _         | _      := false.

  Definition pmp_get_RWX (cfg : Pmpcfg_ent) (p : Privilege) : PmpCfgPerm :=
    match cfg with
    | {| L := L; A := _; X := X; W := W; R := R |} =>
        match L, p with
        | false, Machine => PmpRWX
        | _,     _       =>
            match X, W, R with
            | false, false, true  => PmpR
            | false, true,  false => PmpW
            | false, true,  true  => PmpRW
            | true,  false, false => PmpX
            | true,  false, true  => PmpRX
            | true,  true,  false => PmpWX
            | true,  true,  true  => PmpRWX
            | _,     _,     _     => PmpO
            end
        end
    end.

  Definition pmp_get_perms (cfg : Pmpcfg_ent) (p : Privilege) : PmpCfgPerm :=
    match p with
    | Machine =>
        if L cfg
        then pmp_get_RWX cfg p
        else PmpRWX
    | User =>
        pmp_get_RWX cfg p
    end.

  Fixpoint pmp_check_rec (a width lo : Xlenbits) (entries : list PmpEntryCfg) (p : Privilege) (acc : AccessType) : bool :=
    match entries with
    | (cfg , hi) :: entries =>
        match pmp_match_entry a width p cfg lo hi with
        | PMP_Success  => decide_access_pmp_perm acc (pmp_get_perms cfg p)
        | PMP_Fail     => false
        | PMP_Continue => pmp_check_rec a width hi entries p acc
        end
    | [] =>
        match p with
        | Machine => true
        | _       => false
        end
    end%list.

  Definition pmp_check_aux (a width lo : Xlenbits) (entries : list PmpEntryCfg) (p : Privilege) (acc : AccessType) : bool :=
    pmp_check_rec a width lo entries p acc.

  Definition pmp_check (a width : Xlenbits) (entries : list PmpEntryCfg) (p : Privilege) (acc : AccessType) : bool :=
    pmp_check_aux a width bv.zero entries p acc.
End Implementation.

Section AddrMatchType.
  Lemma addr_match_type_neq_off_cases :
    ∀ a, a ≠ OFF -> a = TOR ∨ a = NA4.
  Proof. destruct a; firstorder. Qed.

  Lemma addr_match_type_TOR_neq_OFF :
    ∀ a, a = TOR -> a ≠ OFF.
  Proof. destruct a; firstorder. Qed.

  Lemma addr_match_type_NA4_neq_OFF :
    ∀ a, a = NA4 -> a ≠ OFF.
  Proof. destruct a; firstorder. Qed.

  Lemma addr_match_type_neq_OFF :
    ∀ a, a = TOR \/ a = NA4 -> a ≠ OFF.
  Proof. destruct a; firstorder. Qed.
End AddrMatchType.

Section PmpAddrRange.
  Lemma pmp_addr_range_None_1 : ∀ cfg hi lo,
      pmp_addr_range cfg hi lo = None ->
      A cfg = OFF.
  Proof.
    intros.
    unfold pmp_addr_range in H.
    destruct (A cfg); auto; discriminate.
  Qed.

  Lemma pmp_addr_range_None_2 : ∀ cfg hi lo,
      A cfg = OFF ->
      pmp_addr_range cfg hi lo = None.
  Proof. intros; unfold pmp_addr_range; now rewrite H. Qed.

  Lemma pmp_addr_range_None : ∀ cfg hi lo,
      pmp_addr_range cfg hi lo = None <->
      A cfg = OFF.
  Proof.
    intros; split.
    - apply pmp_addr_range_None_1.
    - apply pmp_addr_range_None_2.
  Qed.

  Lemma pmp_addr_range_Some_1 : ∀ cfg hi lo p,
      pmp_addr_range cfg hi lo = Some p ->
      (A cfg = TOR /\ p = (lo , hi))
      \/ (A cfg = NA4 /\ p = (hi , hi + (bv.of_nat 4))).
  Proof.
    intros.
    unfold pmp_addr_range in H.
    destruct (A cfg); auto; inversion H; intuition.
  Qed.

  Lemma pmp_addr_range_Some_2 : ∀ cfg hi lo p,
      (A cfg = TOR /\ p = (lo , hi))
      \/ (A cfg = NA4 /\ p = (hi , hi + (bv.of_nat 4))) ->
      pmp_addr_range cfg hi lo = Some p.
  Proof.
    unfold pmp_addr_range;
      intros ? ? ? ? [[-> Hp]|[-> Hp]];
      subst;
      intuition.
  Qed.

  Lemma pmp_addr_range_Some : ∀ cfg hi lo p,
      pmp_addr_range cfg hi lo = Some p <->
      (A cfg = TOR /\ p = (lo , hi)) \/ (A cfg = NA4 /\ p = (hi , hi + bv.of_nat 4)).
  Proof.
    intros; split.
    - apply pmp_addr_range_Some_1.
    - apply pmp_addr_range_Some_2.
  Qed.

  Lemma pmp_addr_range_Some_1' : ∀ cfg pmpaddr prev_pmpaddr p,
      pmp_addr_range cfg pmpaddr prev_pmpaddr = Some p ->
      A cfg ≠ OFF.
  Proof.
    unfold pmp_addr_range;
      intros cfg ? ? ?;
      destruct (A cfg) eqn:?;
      simpl in *;
      try discriminate.
  Qed.

  Lemma pmp_addr_range_Some_2' : ∀ cfg pmpaddr prev_pmpaddr,
      A cfg ≠ OFF ->
      ∃ p, pmp_addr_range cfg pmpaddr prev_pmpaddr = Some p.
  Proof.
    unfold pmp_addr_range;
      intros cfg ? ? [H|H]%addr_match_type_neq_off_cases;
      eexists; rewrite H; auto.
  Qed.

  Lemma pmp_addr_range_Some_TOR : ∀ cfg pmpaddr prev_pmpaddr,
      A cfg = TOR ->
      pmp_addr_range cfg pmpaddr prev_pmpaddr = Some (prev_pmpaddr , pmpaddr).
  Proof. unfold pmp_addr_range; intros ? ? ? ->; auto. Qed.

  Lemma pmp_addr_range_Some_NA4 : ∀ cfg pmpaddr prev_pmpaddr,
      A cfg = NA4 ->
      pmp_addr_range cfg pmpaddr prev_pmpaddr = Some (pmpaddr , pmpaddr + (bv.of_nat 4)).
  Proof. unfold pmp_addr_range; intros ? ? ? ->; auto. Qed.
End PmpAddrRange.

Section PmpMatchAddr.
  Lemma pmp_match_addr_match_conditions_1 : forall (paddr w lo hi : Xlenbits),
      pmp_match_addr paddr w (Some (lo , hi)) = PMP_Match ->
      lo <=ᵘ hi ∧ lo <ᵘ (paddr + w)%bv ∧ lo <=ᵘ paddr
      ∧ paddr <ᵘ hi ∧ (paddr + w)%bv <=ᵘ hi.
  Proof.
    unfold pmp_match_addr.
    intros paddr w lo hi H.
    destruct (hi <ᵘ? lo) eqn:Ehilo; try discriminate H.
    destruct ((paddr + w)%bv <=ᵘ? lo) eqn:Epwlo; first easy.
    destruct (hi <=ᵘ? paddr) eqn:Ehip; first easy.
    simpl in H.
    destruct (lo <=ᵘ? paddr) eqn:Elop; last easy.
    destruct ((paddr + w)%bv <=ᵘ? hi) eqn:Epwhi; last easy.
    rewrite bv.ultb_antisym in Ehilo.
    apply Bool.negb_false_iff in Ehilo.
    now bv_comp.
  Qed.

  Lemma pmp_match_addr_match_conditions_2 : forall paddr w lo hi,
      lo <=ᵘ hi ∧ lo <ᵘ (paddr + w)%bv ∧ lo <=ᵘ paddr
      ∧ paddr <ᵘ hi ∧ (paddr + w)%bv <=ᵘ hi ->
      pmp_match_addr paddr w (Some (lo , hi)) = PMP_Match.
  Proof.
    intros ? ? ? ? (? & ? & ? & ? & ?);
      unfold pmp_match_addr; now bv_comp_bool.
  Qed.

  Lemma pmp_match_addr_match : forall (paddr w lo hi : Xlenbits),
      pmp_match_addr paddr w (Some (lo , hi)) = PMP_Match <->
      lo <=ᵘ hi ∧ lo <ᵘ (paddr + w)%bv ∧ lo <=ᵘ paddr
      ∧ paddr <ᵘ hi ∧ (paddr + w)%bv <=ᵘ hi.
    Proof.
      intros; split.
      - apply pmp_match_addr_match_conditions_1.
      - apply pmp_match_addr_match_conditions_2.
    Qed.

  Lemma pmp_match_addr_nomatch_conditions : forall paddr w lo hi,
      hi <ᵘ lo ->
      pmp_match_addr paddr w (Some (lo , hi)) = PMP_NoMatch.
  Proof. intros; unfold pmp_match_addr; now bv_comp_bool. Qed.

  Lemma pmp_match_addr_nomatch_conditions_1 : forall paddr w lo hi,
      (paddr + w)%bv <=ᵘ lo ->
      pmp_match_addr paddr w (Some (lo , hi)) = PMP_NoMatch.
  Proof. intros; unfold pmp_match_addr; destruct (hi <ᵘ? lo); now bv_comp_bool. Qed.

  Lemma pmp_match_addr_nomatch_conditions_2 : forall paddr w lo hi,
      hi <=ᵘ paddr ->
      pmp_match_addr paddr w (Some (lo , hi)) = PMP_NoMatch.
  Proof.
    intros.
    unfold pmp_match_addr.
    destruct (hi <ᵘ? lo) eqn:Ehilo; auto; bv_comp_bool.
    now rewrite Bool.orb_true_r.
  Qed.

  Lemma pmp_match_addr_none: forall paddr w,
      pmp_match_addr paddr w None = PMP_NoMatch.
  Proof. auto. Qed.

  Lemma pmp_match_addr_nomatch_1 : forall paddr w rng,
      pmp_match_addr paddr w rng = PMP_NoMatch ->
      rng = None ∨
        (∀ lo hi, rng = Some (lo , hi) ->
                  (hi <ᵘ lo
                   ∨ (paddr + w)%bv <=ᵘ lo
                   ∨ hi <=ᵘ paddr)).
  Proof.
    intros paddr w [[lo hi]|]; auto.
    intros H.
    right; intros l h Heq; inversion Heq; subst.
    unfold pmp_match_addr in H.
    destruct (h <ᵘ? l) eqn:?; bv_comp; auto.
    destruct ((paddr + w)%bv <=ᵘ? l) eqn:?; bv_comp; simpl in H; auto.
    destruct (h <=ᵘ? paddr) eqn:?; bv_comp; auto.
    destruct (l <=ᵘ? paddr) eqn:?; destruct ((paddr + w)%bv <=ᵘ? h) eqn:?;
      inversion H.
  Qed.

  Lemma pmp_match_addr_nomatch_2 : forall paddr w rng,
      (rng = None ∨
         (∀ lo hi, rng = Some (lo , hi) ->
                   (hi <ᵘ lo
                    ∨ (paddr + w)%bv <=ᵘ lo
                    ∨ hi <=ᵘ paddr))) ->
      pmp_match_addr paddr w rng = PMP_NoMatch.
  Proof.
    intros paddr w [[lo hi]|]; auto.
    intros [|H]; first discriminate.
    specialize (H lo hi eq_refl).
    destruct H as [|[|]].
    now apply pmp_match_addr_nomatch_conditions.
    now apply pmp_match_addr_nomatch_conditions_1.
    now apply pmp_match_addr_nomatch_conditions_2.
  Qed.

  Lemma pmp_match_addr_nomatch : forall paddr w rng,
      pmp_match_addr paddr w rng = PMP_NoMatch <->
        rng = None ∨
          (∀ lo hi, rng = Some (lo , hi) ->
                    (hi <ᵘ lo
                     ∨ (paddr + w)%bv <=ᵘ lo
                     ∨ hi <=ᵘ paddr)).
  Proof.
    intros; split.
    - apply pmp_match_addr_nomatch_1.
    - apply pmp_match_addr_nomatch_2.
  Qed.
End PmpMatchAddr.

Section PmpMatchEntry.
  Lemma pmp_match_entry_PMP_Continue : ∀ a width m cfg prev_pmpaddr pmpaddr rng,
      pmp_addr_range cfg pmpaddr prev_pmpaddr = rng ->
      pmp_match_entry a width m cfg prev_pmpaddr pmpaddr = PMP_Continue ->
      A cfg = OFF
      ∨ (A cfg ≠ OFF ∧
         (∃ lo hi, (rng = Some (lo , hi) /\
                      (hi <ᵘ lo
                       ∨ (lo <=ᵘ hi ∧ (a + width)%bv <=ᵘ lo)
                       ∨ (lo <=ᵘ hi ∧ lo <ᵘ (a + width)%bv ∧ hi <=ᵘ a))))).
  Proof.
    unfold pmp_match_entry; intros.
    destruct (pmp_addr_range _ _ _) eqn:Hrng.
    - right.
      destruct p as [lo hi].
      destruct (pmp_match_addr _ _ _) eqn:Hmatch;
        try discriminate.
      apply pmp_match_addr_nomatch in Hmatch.
      apply pmp_addr_range_Some_1' in Hrng.
      split; auto.
      exists lo, hi; split; auto.
      destruct Hmatch as [|Hmatch];
        try discriminate.
      specialize (Hmatch lo hi eq_refl).
      destruct Hmatch as [|[|]].
      + now left.
      + destruct (hi <ᵘ? lo) eqn:?; bv_comp; auto.
      + destruct (hi <ᵘ? lo) eqn:?;
          destruct ((a + width)%bv <=ᵘ? lo) eqn:?;
          bv_comp; auto.
    - apply pmp_addr_range_None in Hrng.
      now left.
  Qed.

  Lemma pmp_match_entry_cfg_OFF_PMP_Continue : ∀ a width m cfg lo hi,
      A cfg = OFF ->
      pmp_match_entry a width m cfg lo hi = PMP_Continue.
  Proof.
    intros; unfold pmp_match_entry.
    now rewrite (proj2 (pmp_addr_range_None _ _ _) H).
  Qed.

  Lemma pmp_match_entry_cfg_ON_PMP_Continue : ∀ a width m cfg prev_pmpaddr pmpaddr lo hi,
      pmp_addr_range cfg pmpaddr prev_pmpaddr = Some (lo , hi) ->
      (A cfg ≠ OFF ∧
         (hi <ᵘ lo
          ∨ (lo <=ᵘ hi ∧ (a + width)%bv <=ᵘ lo)
          ∨ (lo <=ᵘ hi ∧ lo <ᵘ (a + width)%bv ∧ hi <=ᵘ a))) ->
      pmp_match_entry a width m cfg prev_pmpaddr pmpaddr = PMP_Continue.
  Proof.
    intros ? ? ? ? ? ? ? ? Hrng H; unfold pmp_match_entry.
    destruct H as [HA H].
    rewrite Hrng.
    cbn.
    destruct H as [|[[]|[? []]]];
      now bv_comp_bool.
  Qed.

  Lemma pmp_match_entry_PMP_Success_1 : ∀ a width m cfg prev_pmpaddr pmpaddr lo hi,
      pmp_addr_range cfg pmpaddr prev_pmpaddr = Some (lo , hi) ->
      pmp_match_entry a width m cfg prev_pmpaddr pmpaddr = PMP_Success ->
      A cfg ≠ OFF
      ∧ lo <=ᵘ hi ∧ lo <ᵘ (a + width)%bv ∧ lo <=ᵘ a
      ∧ a <ᵘ hi ∧ (a + width)%bv <=ᵘ hi.
  Proof.
    unfold pmp_match_entry; intros ? ? ? ? ? ? ? ? Hrng H.
    rewrite Hrng in H.
    destruct (pmp_match_addr _ _ _) eqn:Ha;
      try discriminate.
    apply pmp_match_addr_match in Ha.
    apply pmp_addr_range_Some_1' in Hrng.
    auto.
  Qed.

  Lemma pmp_match_entry_PMP_Success_2 : ∀ a width m cfg prev_pmpaddr pmpaddr lo hi,
      pmp_addr_range cfg pmpaddr prev_pmpaddr = Some (lo , hi) ->
      A cfg ≠ OFF
      ∧ lo <=ᵘ hi ∧ lo <ᵘ (a + width)%bv ∧ lo <=ᵘ a
      ∧ a <ᵘ hi ∧ (a + width)%bv <=ᵘ hi ->
      pmp_match_entry a width m cfg prev_pmpaddr pmpaddr = PMP_Success.
  Proof.
    intros ? ? ? ? ? ? ? ? Hrng H; unfold pmp_match_entry.
    destruct H as (HA & H).
    rewrite Hrng.
    rewrite (proj2 (pmp_match_addr_match _ _ _ _) H).
    auto.
  Qed.

  Lemma pmp_match_entry_PMP_Success : ∀ a width m cfg prev_pmpaddr pmpaddr lo hi,
      pmp_addr_range cfg pmpaddr prev_pmpaddr = Some (lo , hi) ->
      (pmp_match_entry a width m cfg prev_pmpaddr pmpaddr = PMP_Success <->
       A cfg ≠ OFF
       ∧ lo <=ᵘ hi ∧ lo <ᵘ (a + width)%bv ∧ lo <=ᵘ a
       ∧ a <ᵘ hi ∧ (a + width)%bv <=ᵘ hi).
  Proof.
    intros ? ? ? ? ? ? ? ? H; split; revert H.
    - apply pmp_match_entry_PMP_Success_1.
    - apply pmp_match_entry_PMP_Success_2.
  Qed.
End PmpMatchEntry.
