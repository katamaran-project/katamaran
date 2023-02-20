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
     Strings.String.
From Katamaran Require Import
     Signature
     Notations
     Symbolic.Solver
     RiscvPmp.Base.
From Equations Require Import
     Equations.
From iris.proofmode Require Import string_ident tactics.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import bv.notations.
Import option.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Inductive PurePredicate : Set :=
| pmp_access
| pmp_check_perms
| pmp_check_rwx
| sub_perm
| access_pmp_perm
| within_cfg
| not_within_cfg
| prev_addr
| in_entries
.

Inductive Predicate : Set :=
| pmp_entries
| pmp_addr_access
| pmp_addr_access_without (bytes : nat)
| gprs
| ptsto
| ptstomem_readonly (bytes : nat)
| encodes_instr
| ptstomem (bytes : nat)
| ptstoinstr
.

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
    end.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

Module Export RiscvPmpSignature <: Signature RiscvPmpBase.

  Section PredicateKit.
    Definition 𝑷 := PurePredicate.
    Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
      match p with
      | pmp_access      => [ty_xlenbits; ty_xlenbits; ty.list ty_pmpentry; ty_privilege; ty_access_type]
      | pmp_check_perms => [ty_pmpcfg_ent; ty_access_type; ty_privilege]
      | pmp_check_rwx   => [ty_pmpcfg_ent; ty_access_type]
      | sub_perm        => [ty_access_type; ty_access_type]
      | access_pmp_perm => [ty_access_type; ty_pmpcfgperm]
      | within_cfg      => [ty_xlenbits; ty_pmpcfg_ent; ty_xlenbits; ty_xlenbits]
      | not_within_cfg  => [ty_xlenbits; ty.list ty_pmpentry]
      | prev_addr       => [ty_pmpcfgidx; ty.list ty_pmpentry; ty_xlenbits]
      | in_entries      => [ty_pmpcfgidx; ty_pmpentry; ty.list ty_pmpentry]
      end.

    Definition PmpEntryCfg : Set := Pmpcfg_ent * Xlenbits.
    Definition PmpAddrRange := option (Xlenbits * Xlenbits).

    Example default_pmpcfg_ent : Pmpcfg_ent :=
      {| L := false; A := OFF; X := false; W := false; R := false |}.

    Example default_pmpentries : list (Pmpcfg_ent * Xlenbits) :=
      [(default_pmpcfg_ent, bv.zero);
       (default_pmpcfg_ent, bv.zero)
      ].

    Definition pmp_check_RWX (cfg : Val ty_pmpcfg_ent) (acc : Val ty_access_type) : bool :=
      match cfg with
      | {| L := _; A := _; X := X; W := W; R := R |} =>
          match acc with
          | Read      => R
          | Write     => W
          | ReadWrite => R && W
          | Execute   => X
          end
      end.

    Definition pmp_get_RWX (cfg : Val ty_pmpcfg_ent) (p : Val ty_privilege) : Val ty_pmpcfgperm :=
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

    Definition decide_pmp_check_perms (cfg : Val ty_pmpcfg_ent) (acc : Val ty_access_type) (p : Val ty_privilege) : bool :=
      match p with
      | Machine =>
          if L cfg
          then pmp_check_RWX cfg acc
          else true
      | User =>
          pmp_check_RWX cfg acc
      end.

    Definition pmp_get_perms (cfg : Val ty_pmpcfg_ent) (p : Val ty_privilege) : Val ty_pmpcfgperm :=
      match p with
      | Machine =>
          if L cfg
          then pmp_get_RWX cfg p
          else PmpRWX
      | User =>
          pmp_get_RWX cfg p
      end.

    Definition pmp_addr_range (cfg : Pmpcfg_ent) (hi lo : Xlenbits) : PmpAddrRange :=
      match A cfg with
      | OFF => None
      | TOR => Some (lo , hi)
      end.

    Definition pmp_match_addr (a : Val ty_xlenbits) (width : Val ty_xlenbits) (rng : PmpAddrRange) : Val ty_pmpaddrmatch :=
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

    Lemma pmp_match_addr_match_conditions_1 : forall (paddr w lo hi : Val ty_xlenbits),
        pmp_match_addr paddr w (Some (lo , hi)) = PMP_Match ->
        lo <=ᵘ hi /\ lo <ᵘ (paddr + w)%bv /\ lo <=ᵘ paddr /\ paddr <ᵘ hi /\ (paddr + w)%bv <=ᵘ hi.
    Proof.
      unfold pmp_match_addr.
      intros paddr w lo hi H.
      destruct (hi <ᵘ? lo) eqn:Ehilo; try discriminate H.
      destruct ((paddr + w)%bv <=ᵘ? lo) eqn:Epwlo; first done.
      destruct (hi <=ᵘ? paddr) eqn:Ehip; first done.
      simpl in H.
      destruct (lo <=ᵘ? paddr) eqn:Elop; last done.
      destruct ((paddr + w)%bv <=ᵘ? hi) eqn:Epwhi; last done.
      rewrite bv.ultb_antisym in Ehilo.
      apply negb_false_iff in Ehilo.
      now bv_comp.
    Qed.

    Lemma pmp_match_addr_match_conditions_2 : forall paddr w lo hi,
        lo <=ᵘ hi ->
        lo <ᵘ (paddr + w)%bv ->
        lo <=ᵘ paddr ->
        paddr <ᵘ hi ->
        (paddr + w)%bv <=ᵘ hi ->
        pmp_match_addr paddr w (Some (lo , hi)) = PMP_Match.
    Proof.
      intros paddr w lo hi Hlohi Hlopw Hlop Hphi Hpwhi.
      unfold pmp_match_addr.
      replace (hi <ᵘ? lo) with false
        by (symmetry; now rewrite bv.ultb_antisym negb_false_iff bv.uleb_ule).
      replace ((paddr + w)%bv <=ᵘ? lo) with false by (symmetry; now rewrite bv.uleb_ugt).
      replace (hi <=ᵘ? paddr) with false by (symmetry; now rewrite bv.uleb_ugt).
      replace (lo <=ᵘ? paddr) with true by (symmetry; now rewrite bv.uleb_ule).
      now replace ((paddr + w)%bv <=ᵘ? hi) with true by (symmetry; now rewrite bv.uleb_ule).
    Qed.

    Lemma pmp_match_addr_nomatch_conditions : forall paddr w lo hi,
        hi <ᵘ lo ->
        pmp_match_addr paddr w (Some (lo , hi)) = PMP_NoMatch.
    Proof.
      intros.
      unfold pmp_match_addr.
      rewrite <- bv.ultb_ult in H.
      now rewrite H.
    Qed.

    Lemma pmp_match_addr_nomatch_conditions_1 : forall paddr w lo hi,
        (paddr + w)%bv <=ᵘ lo ->
        pmp_match_addr paddr w (Some (lo , hi)) = PMP_NoMatch.
    Proof.
      intros.
      unfold pmp_match_addr.
      destruct (hi <ᵘ? lo) eqn:Ehilo; auto.
      apply bv.uleb_ule in H.
      now rewrite H.
    Qed.

    Lemma pmp_match_addr_nomatch_conditions_2 : forall paddr w lo hi,
        hi <=ᵘ paddr ->
        pmp_match_addr paddr w (Some (lo , hi)) = PMP_NoMatch.
    Proof.
      intros.
      unfold pmp_match_addr.
      destruct (hi <ᵘ? lo) eqn:Ehilo; auto.
      apply bv.uleb_ule in H.
      rewrite H.
      now rewrite Bool.orb_true_r.
    Qed.

    Lemma pmp_match_addr_none: forall paddr w,
        pmp_match_addr paddr w None = PMP_NoMatch.
    Proof. auto. Qed.

    Lemma pmp_match_addr_nomatch_1 : forall paddr w rng,
        pmp_match_addr paddr w rng = PMP_NoMatch ->
        rng = None \/
        (∀ lo hi, rng = Some (lo , hi) ->
         (hi <ᵘ lo \/ (paddr + w)%bv <=ᵘ lo \/ hi <=ᵘ paddr)).
    Proof.
      intros paddr w [[lo hi]|]; auto.
      intros H.
      right; intros l h Heq; inversion Heq; subst.
      unfold pmp_match_addr in H.
      destruct (h <ᵘ? l) eqn:?; auto.
      left; now bv_comp.
      destruct ((paddr + w)%bv <=ᵘ? l) eqn:?.
      right; left; now bv_comp.
      destruct (h <=ᵘ? paddr) eqn:?.
      right; right; now bv_comp.
      simpl in H.
      destruct (l <=ᵘ? paddr) eqn:?; destruct ((paddr + w)%bv <=ᵘ? h) eqn:?; inversion H.
    Qed.

    Lemma pmp_match_addr_nomatch_2 : forall paddr w rng,
        (rng = None \/
           (∀ lo hi, rng = Some (lo , hi) ->
            (hi <ᵘ lo \/ (paddr + w)%bv <=ᵘ lo \/ hi <=ᵘ paddr))) ->
        pmp_match_addr paddr w rng = PMP_NoMatch.
    Proof.
      intros paddr w [[lo hi]|]; auto.
      intros [H|H].
      inversion H.
      assert (Heq: Some (lo , hi) = Some (lo , hi)) by auto.
      destruct (H lo hi Heq) as [Hs|[Hs|Hs]]; revert Hs.
      apply pmp_match_addr_nomatch_conditions.
      apply pmp_match_addr_nomatch_conditions_1.
      apply pmp_match_addr_nomatch_conditions_2.
    Qed.

    Definition pmp_match_entry (a : Val ty_xlenbits) (width : Val ty_xlenbits) (m : Val ty_privilege) (cfg : Val ty_pmpcfg_ent) (lo hi : Val ty_xlenbits) : Val ty_pmpmatch :=
      let rng := pmp_addr_range cfg hi lo in
      match pmp_match_addr a width rng with
      | PMP_NoMatch      => PMP_Continue
      | PMP_PartialMatch => PMP_Fail
      | PMP_Match        => PMP_Success
      end.

    Section UnrolledPmpCheck.
      Definition unrolled_pmp_check (a : Val ty_xlenbits) (width : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (prev : Val ty_xlenbits) (m : Val ty_privilege) : (bool * option (Val ty_pmpcfgperm)) :=
        match entries with
        | (cfg0 , addr0) :: (cfg1 , addr1) :: [] =>
            match pmp_match_entry a width m cfg0 prev addr0 with
            | PMP_Success  => (true, Some (pmp_get_perms cfg0 m))
            | PMP_Fail     => (false, None)
            | PMP_Continue => 
                match pmp_match_entry a width m cfg1 addr0 addr1 with
                | PMP_Success  => (true, Some (pmp_get_perms cfg1 m))
                | PMP_Fail     => (false, None)
                | PMP_Continue => 
                    match m with
                    | Machine => (true, None)
                    | User    => (false, None)
                    end
                end
            end
        | _ => 
            match m with
            | Machine => (true, None)
            | User    => (false, None)
            end
        end%list.
    End UnrolledPmpCheck.

    Fixpoint split_entries_aux (n : nat) (es : Val (ty.list ty_pmpentry)) : option (list (Val ty_pmpcfg_ent) * list (Val ty_xlenbits)) :=
      match n, es with
      | O   , []                 => Some ([] , [])
      | S n , (cfg , addr) :: es =>
          '(cfgs , addrs) <- split_entries_aux n es ;;
          Some (cfg :: cfgs , addr :: addrs)
      | _   , _                  => None
      end%list.

    Definition split_entries (n : nat) (es : Val (ty.list ty_pmpentry)) : option (list (Val ty_pmpcfg_ent) * list (Val ty_xlenbits)) :=
      '(cfgs , addrs) <- split_entries_aux n es ;;
      Some (cfgs , bv.zero :: addrs)%list.

    Equations(noeqns) decide_access_pmp_perm (a : Val ty_access_type) (p : Val ty_pmpcfgperm) : bool :=
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

    Definition Pmp_check_perms (cfg : Val ty_pmpcfg_ent) (acc : Val ty_access_type) (p : Val ty_privilege) : Prop :=
      decide_pmp_check_perms cfg acc p = true.

    Section PresplitPmpCheck.
      Fixpoint presplit_pmp_check (a width : Val ty_xlenbits) (bounds : list (Val ty_xlenbits)) (cfgs : list (Val ty_pmpcfg_ent)) (p : Val ty_privilege) (acc : Val ty_access_type) : bool :=
        match bounds, cfgs with
        | _, []  => match p with
                    | Machine => true
                    | User    => false
                    end
        | [], _  => false
        | [_], _ => false
        | lo :: hi :: bounds, cfg :: cfgs =>
            match pmp_match_entry a width p cfg lo hi with
            | PMP_Success  => decide_access_pmp_perm acc (pmp_get_perms cfg p)
            | PMP_Fail     => false
            | PMP_Continue => presplit_pmp_check a width (hi :: bounds) cfgs p acc
            end
        end%list.

      Fixpoint presplit_pmp_check_vc (a width : Val ty_xlenbits) (bounds : list (Val ty_xlenbits)) (cfgs : list (Val ty_pmpcfg_ent)) (p : Val ty_privilege) (acc : Val ty_access_type) : Prop :=
        match bounds, cfgs with
        | _, []  => p = Machine
        | [], _  => True
        | [_], _ => True
        | lo :: hi :: bounds, cfg :: cfgs =>
            ((* PMP_NoMatch *)
              (A cfg = OFF
               ∨ (A cfg ≠ OFF ∧
                    (hi <ᵘ lo
                     ∨ (lo <=ᵘ hi ∧ (a + width)%bv <=ᵘ lo)
                     ∨ (lo <=ᵘ hi ∧ lo <ᵘ (a + width)%bv ∧ hi <=ᵘ a))))
              ∧ presplit_pmp_check_vc a width (hi :: bounds) cfgs p acc)
            ∨
              ((* PMP_Match *)
                A cfg ≠ OFF
                ∧ lo <=ᵘ hi
                ∧ lo <ᵘ (a + width)%bv
                ∧ a <ᵘ hi
                ∧ lo <=ᵘ a
                ∧ (a + width)%bv <=ᵘ hi
                ∧ Pmp_check_perms cfg acc p)
        end%list.
    End PresplitPmpCheck.

    Section GeneralizedPmpCheck.
      (* TODO: - remove other definitions eventually
               - introduce the nat parameter again to control recursion (necessary for the user solver one, can't recurse over a term list?)
               - ideally we would reuse the vcgen here and add a pass over it to translate the generated VC into a formula *)
      Fixpoint pmp_check_aux (a width : Val ty_xlenbits) (lo : Val ty_xlenbits) (entries : list (Val ty_pmpentry)) (p : Val ty_privilege) (acc : Val ty_access_type) : bool :=
        match entries with
        | (cfg , hi) :: entries =>
            match pmp_match_entry a width p cfg lo hi with
            | PMP_Success  => decide_access_pmp_perm acc (pmp_get_perms cfg p)
            | PMP_Fail     => false
            | PMP_Continue => pmp_check_aux a width hi entries p acc
            end
        | [] =>
            match p with
            | Machine => true
            | _       => false
            end
        end%list.

      Definition pmp_check (a width : Val ty_xlenbits) (lo : Val ty_xlenbits) (entries : list (Val ty_pmpentry)) (p : Val ty_privilege) (acc : Val ty_access_type) : bool :=
        pmp_check_aux a width lo entries p acc.

      Fixpoint pmp_check_vc_aux (a width : Val ty_xlenbits) (lo : Val ty_xlenbits) (entries : list (Val ty_pmpentry)) (p : Val ty_privilege) (acc : Val ty_access_type) : Prop :=
        match entries with
        | (cfg , hi) :: entries =>
            ((* PMP_NoMatch *)
              (A cfg = OFF
               ∨ (A cfg ≠ OFF ∧
                    (hi <ᵘ lo
                     ∨ (lo <=ᵘ hi ∧ (a + width)%bv <=ᵘ lo)
                     ∨ (lo <=ᵘ hi ∧ lo <ᵘ (a + width)%bv ∧ hi <=ᵘ a))))
              ∧ pmp_check_vc_aux a width hi entries p acc)
            ∨
              ((* PMP_Match *)
                A cfg ≠ OFF
                ∧ lo <=ᵘ hi
                ∧ lo <ᵘ (a + width)%bv
                ∧ a <ᵘ hi
                ∧ lo <=ᵘ a
                ∧ (a + width)%bv <=ᵘ hi
                ∧ Pmp_check_perms cfg acc p)
        | [] => p = Machine
        end%list.

      Definition pmp_check_vc (a width : Val ty_xlenbits) (lo : Val ty_xlenbits) (entries : list (Val ty_pmpentry)) (p : Val ty_privilege) (acc : Val ty_access_type) : Prop :=
        pmp_check_vc_aux a width lo entries p acc.

      Lemma pmp_check_inversion_1 (a width : Val ty_xlenbits) (lo : Val ty_xlenbits) (entries : list (Val ty_pmpentry)) (p : Val ty_privilege) (acc : Val ty_access_type) :
        pmp_check a width lo entries p acc = true ->
        pmp_check_vc a width lo entries p acc.
      Proof.
        generalize dependent lo.
        induction entries.
        - cbn; intros; destruct p; auto; discriminate.
        - simpl.
          destruct a0 as [cfg0 addr0].
          unfold pmp_match_entry.
          intros lo.
          unfold pmp_addr_range.
          destruct (pmp_match_addr a width _) eqn:?;
            destruct (A _) eqn:?;
            intros H;
            try discriminate.
          + apply pmp_match_addr_nomatch_1 in Heqv.
            destruct Heqv; try discriminate; auto.
          + apply pmp_match_addr_nomatch_1 in Heqv.
            destruct Heqv; try discriminate; auto.
            specialize (H0 lo addr0 eq_refl).
            destruct H0 as [|[|]].
            left; split; auto.
            left; split; auto.
            right; split; auto.
            admit. (* TODO: seems like pmp_match_addr_nomatch_1 loses information *)
            admit.
          + right.
            apply pmp_match_addr_match_conditions_1 in Heqv as (? & ? & ? & ? & ?).
            repeat split; auto.
            admit. (* TODO: remember already writing a lemma that converts Pmp_check_perms... Not accesible here, so need to move it up! *)
      Admitted.
    End GeneralizedPmpCheck.

    Definition decide_pmp_access (a : Val ty_xlenbits) (width : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) (acc : Val ty_access_type) : bool :=
      let result :=
        '(cfgs , addrs) <- split_entries NumPmpEntries entries ;;
        Some (pmp_check a width addrs cfgs m acc)
      in match result with
         | Some b => b
         | None   => false
         end.

    Definition Pmp_access (a : Val ty_xlenbits) (width : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) (acc : Val ty_access_type) : Prop :=
      decide_pmp_access a width entries m acc = true.

    Lemma pmp_check_inversion_1 (a width : Val ty_xlenbits) (bounds : list (Val ty_xlenbits)) (cfgs : list (Val ty_pmpcfg_ent)) (p : Val ty_privilege) (acc : Val ty_access_type) :
      pmp_check a width bounds cfgs p acc = true ->
      pmp_check_vc a width bounds cfgs p acc.
    Proof.
      generalize dependent bounds.
      induction cfgs.
      - destruct bounds; auto.
        simpl; destruct p; auto; discriminate.
        simpl; destruct bounds; destruct p; auto; discriminate.
      - induction bounds.
        + simpl; intros; discriminate.
        +

    Section Old_pmp_check.
      Fixpoint pmp_check' (a : Val ty_xlenbits) (width : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (prev : Val ty_xlenbits) (m : Val ty_privilege) : (bool * option (Val ty_pmpcfgperm)) :=
        match entries with
        | [] => match m with
                | Machine => (true, None)
                | User    => (false, None)
                end
        | (cfg , addr) :: entries =>
            match pmp_match_entry a width m cfg prev addr with
            | PMP_Success  => (true, Some (pmp_get_perms cfg m))
            | PMP_Fail     => (false, None)
            | PMP_Continue => pmp_check' a width entries addr m
            end
        end%list.
    End Old_pmp_check.

    Equations(noeqns) access_type_eqb (a1 a2 : Val ty_access_type) : bool :=
    | Read      | Read      := true;
    | Write     | Write     := true;
    | ReadWrite | ReadWrite := true;
    | Execute   | Execute   := true;
    | _         | _         := false.

    Equations(noeqns) decide_sub_perm (a1 a2 : Val ty_access_type) : bool :=
    | Read      | Read      := true;
    | Write     | Write     := true;
    | Execute   | Execute   := true;
    | ReadWrite | ReadWrite := true;
    | Read      | Execute   := true;
    | Read      | ReadWrite := true;
    | Write     | ReadWrite := true;
    | _         | _         := false.

    Lemma decide_sub_perm_refl (a1 a2 : Val ty_access_type) :
      a1 = a2 -> decide_sub_perm a1 a2 = true.
    Proof.
      intros ->; destruct a2; auto.
    Qed.

    Definition Sub_perm (a1 a2 : Val ty_access_type) : Prop :=
      decide_sub_perm a1 a2 = true.

    Definition Access_pmp_perm (a : Val ty_access_type) (p : Val ty_pmpcfgperm) : Prop :=
      decide_access_pmp_perm a p = true.

    Definition Pmp_check_rwx (cfg : Val ty_pmpcfg_ent) (acc : Val ty_access_type) : Prop :=
      pmp_check_RWX cfg acc = true.

    Equations PmpAddrMatchType_eqb (a1 a2 : PmpAddrMatchType) : bool :=
    | OFF | OFF := true;
    | TOR | TOR := true;
    | _   | _   := false.

    Definition pmpcfg_ent_eqb (c1 c2 : Pmpcfg_ent) : bool :=
      match c1, c2 with
      | {| L := L1; A := A1; X := X1; W := W1; R := R1 |},
        {| L := L2; A := A2; X := X2; W := W2; R := R2 |} =>
          (Bool.eqb L1 L2) && (PmpAddrMatchType_eqb A1 A2) && (Bool.eqb X1 X2)
          && (Bool.eqb W1 W2) && (Bool.eqb R1 R2)
      end.

    Definition decide_in_entries (idx : Val ty_pmpcfgidx) (e : Val ty_pmpentry) (es : Val (ty.list ty_pmpentry)) : bool :=
      match es with
      | cfg0 :: cfg1 :: [] =>
          let (c, a) := e in
          let (c', a') := match idx with
                          | PMP0CFG => cfg0
                          | PMP1CFG => cfg1
                          end in
          (pmpcfg_ent_eqb c c' && (bv.eqb a a'))%bool
      | _ => false
      end%list.

    Definition In_entries (idx : Val ty_pmpcfgidx) (e : Val ty_pmpentry) (es : Val (ty.list ty_pmpentry)) : Prop :=
      decide_in_entries idx e es = true.

    Definition decide_prev_addr (cfg : Val ty_pmpcfgidx) (entries : Val (ty.list ty_pmpentry)) (prev : Val ty_xlenbits) : bool :=
      match entries with
      | (c0 , a0) :: (c1 , a1) :: [] =>
          match cfg with
          | PMP0CFG => bv.eqb prev [bv 0]
          | PMP1CFG => bv.eqb prev a0
          end
      | _ => false
      end%list.

    Definition Prev_addr (cfg : Val ty_pmpcfgidx) (entries : Val (ty.list ty_pmpentry)) (prev : Val ty_xlenbits) : Prop :=
      decide_prev_addr cfg entries prev = true.

    Definition decide_within_cfg (paddr : Val ty_xlenbits) (cfg : Val ty_pmpcfg_ent) (prev_addr addr : Val ty_xlenbits) : bool :=
      match A cfg with
      | OFF => false
      | TOR => (prev_addr <=ᵘ? paddr) && (paddr <ᵘ? addr)
      end.

    Definition Within_cfg (paddr : Val ty_xlenbits) (cfg : Val ty_pmpcfg_ent) (prev_addr addr : Val ty_xlenbits) : Prop :=
      decide_within_cfg paddr cfg prev_addr addr = true.

    Definition decide_not_within_cfg (paddr : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) : bool :=
      match entries with
      | (c0 , a0) :: (c1 , a1) :: [] =>
          (((PmpAddrMatchType_eqb (A c0) OFF) && (PmpAddrMatchType_eqb (A c1) OFF))
          || (([bv 0] <=ᵘ? paddr) && (a0 <=ᵘ? paddr) && (a1 <=ᵘ? paddr)))%bool
      | _ => false
      end%list.

    Definition Not_within_cfg (paddr : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) : Prop :=
      decide_not_within_cfg paddr entries = true.

    Definition is_pmp_cfg_unlocked (cfg : Val ty_pmpcfg_ent) : bool :=
      negb (L cfg).

    Lemma is_pmp_cfg_unlocked_bool : forall (cfg : Val ty_pmpcfg_ent),
        is_pmp_cfg_unlocked cfg = true <->
        L cfg = false.
    Proof. intros [[]]; split; auto. Qed.

    Definition Pmp_cfg_unlocked (cfg : Val ty_pmpcfg_ent) : Prop :=
      is_pmp_cfg_unlocked cfg = true.

    Lemma Pmp_cfg_unlocked_bool : forall (cfg : Val ty_pmpcfg_ent),
        Pmp_cfg_unlocked cfg <->
        L cfg = false.
    Proof. unfold Pmp_cfg_unlocked; apply is_pmp_cfg_unlocked_bool. Qed.

    Definition Pmp_entry_unlocked (ent : Val ty_pmpentry) : Prop :=
      Pmp_cfg_unlocked (fst ent).
    Global Arguments Pmp_entry_unlocked !ent.

    Lemma Pmp_check_perms_Access_pmp_perm : forall cfg acc p,
        Pmp_check_perms cfg acc p <-> Access_pmp_perm acc (pmp_get_perms cfg p).
    Proof. by intros [[] ? [] [] []] [] []. Qed.

    Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
      match p with
      | pmp_access      => Pmp_access
      | pmp_check_perms => Pmp_check_perms
      | pmp_check_rwx   => Pmp_check_rwx
      | sub_perm        => Sub_perm
      | access_pmp_perm => Access_pmp_perm
      | within_cfg      => Within_cfg
      | not_within_cfg  => Not_within_cfg
      | prev_addr       => Prev_addr
      | in_entries      => In_entries
      end.

    Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

    Definition 𝑯 := Predicate.
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | pmp_entries                   => [ty.list ty_pmpentry]
      | pmp_addr_access               => [ty.list ty_pmpentry; ty_privilege]
      | pmp_addr_access_without bytes => [ty_xlenbits; ty.list ty_pmpentry; ty_privilege]
      | gprs                          => ctx.nil
      | ptsto                         => [ty_xlenbits; ty_byte]
      | ptstomem_readonly width       => [ty_xlenbits; ty.bvec (width * byte)]
      | encodes_instr                 => [ty_word; ty_ast]
      | ptstomem width                => [ty_xlenbits; ty.bvec (width * byte)]
      | ptstoinstr                    => [ty_xlenbits; ty_ast]
      end.

    Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
      is_duplicable p :=
        match p with
        | pmp_entries                => false
        | pmp_addr_access            => false
        | pmp_addr_access_without  _ => false
        | gprs                       => false
        | ptsto                      => false
        | ptstomem_readonly width    => true
        | encodes_instr              => true
        | ptstomem _                 => false
        | ptstoinstr                 => false
        end
      }.
    Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

    Local Arguments Some {_} &.

    (* TODO: look up precise predicates again, check if below makes sense *)
    Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
      match p with
      | ptsto                     => Some (MkPrecise [ty_xlenbits] [ty_byte] eq_refl)
      | ptstomem_readonly width   => Some (MkPrecise [ty_xlenbits] [ty.bvec (width * byte)] eq_refl)
      | pmp_entries               => Some (MkPrecise ε [ty.list ty_pmpentry] eq_refl)
      | pmp_addr_access           => Some (MkPrecise ε [ty.list ty_pmpentry; ty_privilege] eq_refl)
      | pmp_addr_access_without _ => Some (MkPrecise [ty_xlenbits] [ty.list ty_pmpentry; ty_privilege] eq_refl)
      | ptstomem width            => Some (MkPrecise [ty_xlenbits] [ty.bvec (width * byte)] eq_refl)
      | ptstoinstr                => Some (MkPrecise [ty_xlenbits] [ty_ast] eq_refl)
      | encodes_instr             => Some (MkPrecise [ty_word] [ty_ast] eq_refl)
      | _                         => None
      end.

  End PredicateKit.

  Include PredicateMixin RiscvPmpBase.
  Include SignatureMixin RiscvPmpBase.

  Section ContractDefKit.

    Import asn.notations.

    Local Notation "e1 '=?' e2" := (term_binop (bop.relop bop.eq) e1 e2).

    Definition z_term {Σ} : Z -> Term Σ ty.int := term_val ty.int.

    Definition sep_contract_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
      ctx.map (fun '(x::σ) => x::σ) Δ ▻▻ Σ.

    Definition create_localstore (Δ : PCtx) (Σ : LCtx) : SStore Δ (sep_contract_logvars Δ Σ) :=
      (env.tabulate (fun '(x::σ) xIn =>
                       @term_var
                         (sep_contract_logvars Δ Σ)
                         x
                         σ
                         (ctx.in_cat_left Σ (ctx.in_map (fun '(y::τ) => y::τ) xIn)))).

    Definition asn_with_reg {Σ} (r : Term Σ ty.int) (asn : Reg ty_xlenbits -> Assertion Σ) (asn_default : Assertion Σ) : Assertion Σ :=
      if: r =? z_term 1
      then asn x1
      else
        if: r =? z_term 2
        then asn x2
        else
          if: r =? z_term 3
          then asn x3
          else asn_default.

    Definition asn_and_regs {Σ} (f : Reg ty_xlenbits -> Assertion Σ) : Assertion Σ :=
      f x1 ∗ f x2 ∗ f x3 ∗ f x4 ∗ f x5 ∗ f x6 ∗ f x7.

    Definition asn_regs_ptsto {Σ} : Assertion Σ :=
      asn_and_regs
        (fun r => asn.exist "w" _ (r ↦ term_var "w")).

    Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

    (* TODO: abstract away the concrete type, look into unions for that *)
    (* TODO: length of list should be 16, no duplicates *)
    Definition term_pmp_entries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfgidx ty_pmpaddridx)) :=
      term_list
        (cons (term_val ty_pmpcfgidx PMP0CFG ,ₜ term_val ty_pmpaddridx PMPADDR0)
              (cons (term_val ty_pmpcfgidx PMP1CFG ,ₜ term_val ty_pmpaddridx PMPADDR1) nil)).

  End ContractDefKit.

  Import asn.notations.

  Module notations.
    (* TODO: better notation needed *)
    Notation "a '↦mem' b bs" := (asn.chunk (chunk_user (ptstomem b) [a; bs])) (at level 70).
    Notation "a '↦ₘ' t" := (asn.chunk (chunk_user ptsto [a; t])) (at level 70).
    Notation "p '⊑' q" := (asn.formula (formula_user sub_perm [p;q])) (at level 70).

    Notation asn_bool t := (asn.formula (formula_bool t)).
    Notation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
    Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

    (* TODO: check if I can reproduce the issue with angelic stuff, I think it was checked_mem_read, with the correct postcondition *)
    (* Notation asn_pmp_entries_angelic l := (asn.chunk_angelic (chunk_user pmp_entries [l])). *)
    Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
    Notation asn_pmp_addr_access_without a width l m := (asn.chunk (chunk_user (pmp_addr_access_without width) [a; l; m])).
    Notation asn_gprs := (asn.chunk (chunk_user gprs env.nil)).
    Notation asn_within_cfg a cfg prev_addr addr := (asn.formula (formula_user within_cfg [a; cfg; prev_addr; addr])).
    Notation asn_not_within_cfg a es := (asn.formula (formula_user not_within_cfg [a; es])).
    Notation asn_prev_addr cfg es prev := (asn.formula (formula_user prev_addr [cfg; es; prev])).
    Notation asn_in_entries idx e es := (asn.formula (formula_user in_entries [idx; e; es])).
    Notation asn_pmp_access addr width es m p := (asn.formula (formula_user pmp_access [addr;width;es;m;p])).
    Notation asn_pmp_check_perms cfg acc p := (asn.formula (formula_user pmp_check_perms [cfg;acc;p])).
    Notation asn_pmp_check_rwx cfg acc := (asn.formula (formula_user pmp_check_rwx [cfg;acc])).
    Notation asn_expand_pmpcfg_ent cfg := (asn.match_record rpmpcfg_ent cfg
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil "L" "L") "A" "A") "X" "X") "W" "W") "R" "R")
      (asn.formula (formula_bool (term_val ty.bool true)))).
  End notations.
End RiscvPmpSignature.

Module RiscvPmpSolverKit <: SolverKit RiscvPmpBase RiscvPmpSignature.
  #[local] Arguments Some {_} _%ctx.

  Definition simplify_sub_perm {Σ} (a1 a2 : Term Σ ty_access_type) : option (PathCondition Σ) :=
    match term_get_val a1 , term_get_val a2 with
    | Some a1 , Some a2 => if decide_sub_perm a1 a2 then Some ctx.nil else None
    | _       , _       => Some [formula_user sub_perm [a1;a2]]
    end%ctx.

  Definition simplify_access_pmp_perm {Σ} (a : Term Σ ty_access_type) (p : Term Σ ty_pmpcfgperm) : option (PathCondition Σ) :=
    match term_get_val a , term_get_val p with
    | Some a , Some p => if decide_access_pmp_perm a p then Some ctx.nil else None
    | _      , _      => Some [formula_user access_pmp_perm [a;p]]
    end%ctx.

  (* TODO: move up *)
  Local Notation "P ∨ Q" := (formula_or P Q). 
  Local Notation "P ∧ Q" := (formula_and P Q). 

  Definition is_off {Σ} (A : Term Σ ty_pmpaddrmatchtype) : Formula Σ :=
    formula_relop bop.eq A (term_val ty_pmpaddrmatchtype OFF).

  Definition is_on {Σ} (A : Term Σ ty_pmpaddrmatchtype) : Formula Σ :=
    formula_relop bop.neq A (term_val ty_pmpaddrmatchtype OFF).

  Definition is_machine_mode {Σ} (p : Term Σ ty_privilege) : Formula Σ :=
    formula_relop bop.eq (term_val ty_privilege Machine) p.

  Fixpoint simplify_pmpcheck {Σ} (a width : Term Σ ty_xlenbits) (bounds : list (Term Σ ty_xlenbits)) (cfgs : list (NamedEnv (Term Σ) (recordf_ty rpmpcfg_ent))) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : Formula Σ :=
  match bounds, cfgs with
  | _, []                       => is_machine_mode p
  | [],  _                      => formula_true
  | [_], _                      => formula_true
  | lo :: hi :: bounds, cfg :: cfgs =>
      ((* PMP_NoMatch *)
        (is_off cfg.[??"A"]
         ∨ (is_on cfg.[??"A"] ∧
              (formula_relop bop.bvult hi lo
              ∨ (formula_relop bop.bvule lo hi ∧ formula_relop bop.bvule (term_binop bop.bvadd a width) lo)
              ∨ (formula_relop bop.bvule lo hi ∧ formula_relop bop.bvult lo (term_binop bop.bvadd a width) ∧ formula_relop bop.bvule hi a))))
         ∧ simplify_pmpcheck a width (hi :: bounds) cfgs p acc)
      ∨
      ((* PMP_Match *)
        is_on cfg.[??"A"]
      ∧ formula_relop bop.bvule lo hi
      ∧ formula_relop bop.bvult lo (term_binop bop.bvadd a width)
      ∧ formula_relop bop.bvult a hi
      ∧ formula_relop bop.bvule lo a
      ∧ formula_relop bop.bvule (term_binop bop.bvadd a width) hi
      ∧ formula_user pmp_check_perms [term_record rpmpcfg_ent [cfg.[??"L"];cfg.[??"A"];cfg.[??"X"];cfg.[??"W"];cfg.[??"R"]]; acc; p])
  end%list.

  Definition get_inl {A B} (v : option (A + B)) : option A :=
    match v with
    | Some (inl x) => Some x
    | _            => None
    end.

  Definition get_inr {A B} (v : option (A + B)) : option B :=
    match v with
    | Some (inr x) => Some x
    | _            => None
    end.

  (* NOTE: can't just recurse over es, Coq can't determine it will ever terminate (not sure how to fix this, don't think we can do something as "measure (length es)"), that's why the parameter n is added for the nr of pmp entries of the machine *)
  Fixpoint split_entries_aux {Σ} (n : nat) (es : Term Σ (ty.list ty_pmpentry)) : option (list (NamedEnv (Term Σ) (recordf_ty rpmpcfg_ent)) * list (Term Σ ty_xlenbits)) :=
    match n, term_get_list es with
    | O   , Some (inr tt)         => Some ([] , [])
    | S n , Some (inl (pmp , es)) =>
        '(cfg , addr) <- term_get_pair pmp ;;
        cfg' <- term_get_record cfg ;;
        '(cfgs , addrs) <- split_entries_aux n es ;;
        Some (cfg' :: cfgs , addr :: addrs)
    | _   , _                     => None
    end%list.

  Definition split_entries {Σ} (n : nat) (es : Term Σ (ty.list ty_pmpentry)) : option (list (NamedEnv (Term Σ) (recordf_ty rpmpcfg_ent)) * list (Term Σ ty_xlenbits)) :=
    '(cfgs , addrs) <- split_entries_aux n es ;;
    Some (cfgs , cons (term_val ty_xlenbits bv.zero) addrs).

  Definition simplify_pmp_access {Σ} (paddr : Term Σ ty_xlenbits) (width : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (PathCondition Σ) :=
    let pmp_access_fml := formula_user pmp_access [paddr; width; es; p; acc] in
    match term_get_val paddr , term_get_val width , term_get_val es , term_get_val p , term_get_val acc with
    | Some paddr , Some width , Some entries , Some p , Some acc =>
        if decide_pmp_access paddr width entries p acc
        then Some []
        else None
    | _, _ , _ , _, _ =>  
        let result := '(cfgs , addrs) <- split_entries NumPmpEntries es ;;
                      Some [simplify_pmpcheck paddr width addrs cfgs p acc] in
        match result with
        | Some v => Some v
        | None   => Some [pmp_access_fml]
        end
    end.

  (* TODO: User predicates can be simplified smarter *)
  Definition simplify_pmp_check_rwx {Σ} (cfg : Term Σ ty_pmpcfg_ent) (acc : Term Σ ty_access_type) : option (PathCondition Σ) :=
    match term_get_record cfg, term_get_val acc with
    | Some cfg' , Some acc' =>
        match acc' with
        | Read      => match term_get_val cfg'.[??"R"] with
                       | Some true  => Some []
                       | Some false => None
                       | None       => Some [formula_user pmp_check_rwx [cfg; acc]]
                       end
        | Write     => match term_get_val cfg'.[??"W"] with
                       | Some true  => Some []
                       | Some false => None
                       | None       => Some [formula_user pmp_check_rwx [cfg;acc]]
                       end
        | ReadWrite => match term_get_val cfg'.[??"R"], term_get_val cfg'.[??"W"] with
                       | Some b1 , Some b2 => if andb b1 b2 then Some ctx.nil else None
                       | _       , _       => Some [formula_user pmp_check_rwx [cfg;acc]]
                       end
        | Execute   => match term_get_val cfg'.[??"X"] with
                       | Some true  => Some []
                       | Some false => None
                       | None       => Some [formula_user pmp_check_rwx [cfg;acc]]
                       end
        end
    | _        , _        => Some [formula_user pmp_check_rwx [cfg;acc]]
    end%ctx.

  Definition simplify_pmp_check_perms {Σ} (cfg : Term Σ ty_pmpcfg_ent) (acc : Term Σ ty_access_type) (p : Term Σ ty_privilege) : option (PathCondition Σ) :=
    match term_get_record cfg, term_get_val p with
    | Some cfg' , Some Machine => match term_get_val cfg'.[??"L"] with
                                  | Some true  => Some [formula_user pmp_check_rwx [cfg;acc]]
                                  | Some false => Some []
                                  | None       => Some [formula_user pmp_check_perms [cfg;acc;p]]
                                  end
    | Some cfg' , Some User    => Some [formula_user pmp_check_rwx [cfg;acc]]
    | _         , _            => Some [formula_user pmp_check_perms [cfg;acc;p]]
    end%ctx.

  Definition simplify_within_cfg {Σ} (paddr : Term Σ ty_xlenbits) (cfg : Term Σ ty_pmpcfg_ent) (prev_addr addr : Term Σ ty_xlenbits) : option (PathCondition Σ) :=
    match term_get_val paddr, term_get_val cfg, term_get_val prev_addr, term_get_val addr with
    | Some paddr, Some cfg, Some a , Some a' => if decide_within_cfg paddr cfg a a' then Some [] else None
    | _         , _       , _      , _       =>
        Some [formula_user within_cfg [paddr; cfg; prev_addr; addr]]
    end%ctx.

  Definition simplify_prev_addr {Σ} (cfg : Term Σ ty_pmpcfgidx) (entries : Term Σ (ty.list ty_pmpentry)) (prev : Term Σ ty_xlenbits) : option (PathCondition Σ) :=
    match term_get_val cfg, term_get_val entries, term_get_val prev with
    | Some cfg, Some entries, Some prev => if decide_prev_addr cfg entries prev then Some [] else None
    | _       , _           , _         => Some [formula_user prev_addr [cfg; entries; prev]]
    end%ctx.

  Import DList.

  Equations(noeqns) simplify_user [Σ] (p : 𝑷) : Env (Term Σ) (𝑷_Ty p) -> option (PathCondition Σ) :=
  | pmp_access               | [ paddr; width; entries; priv; perm ] => simplify_pmp_access paddr width entries priv perm
  | pmp_check_perms          | [ cfg; acc; priv ]             => simplify_pmp_check_perms cfg acc priv
  | pmp_check_rwx            | [ cfg; acc ]                   => simplify_pmp_check_rwx cfg acc
  | sub_perm                 | [ a1; a2 ]                     => simplify_sub_perm a1 a2
  | access_pmp_perm          | [ a; p ]                       => simplify_access_pmp_perm a p
  | within_cfg               | [ paddr; cfg; prevaddr; addr]  => simplify_within_cfg paddr cfg prevaddr addr
  | not_within_cfg           | [ paddr; entries ]             => Some [formula_user not_within_cfg [paddr; entries]]%ctx
  | prev_addr                | [ cfg; entries; prev ]         => simplify_prev_addr cfg entries prev
  | in_entries               | [ cfg; entries; prev ]         => Some [formula_user in_entries [cfg; entries; prev]]%ctx.

  Import Entailment.

  Local Ltac lsolve :=
    repeat
      lazymatch goal with
      | |- Some _             ⊣⊢ Some _             => apply @proper_some
      | |- ctx.snoc ctx.nil _ ⊣⊢ ctx.snoc ctx.nil _ => apply proper_snoc; [easy|]
      | |- None               ⊣⊢ Some _             => apply @unsatisfiable_none_some
      | |- [ctx]              ⊣⊢ _                  => apply nil_l_valid
      | |- Unsatisfiable (ctx.snoc ctx.nil _)       => apply unsatisfiable_snoc_r
      | |- match @term_get_val ?Σ ?σ ?v with _ => _ end ⊣⊢ _ =>
          destruct (@term_get_val_spec Σ σ v); subst; try progress cbn
      | |- match @term_get_list ?Σ ?σ ?v with _ =>_ end ⊣⊢ _ =>
          destruct (@term_get_list_spec Σ σ v) as [[] ?|]; subst; try progress cbn
      | |- match @term_get_pair ?Σ ?σ₁ ?σ₂ ?v with _ =>_ end ⊣⊢ _ =>
          destruct (@term_get_pair_spec Σ σ₁ σ₂ v); subst; try progress cbn
      | |- match @term_get_record ?r ?Σ ?v with _ =>_ end ⊣⊢ _ =>
          destruct (@term_get_record_spec Σ r v); subst; try progress cbn
      | H: ?fst * ?snd |- _ =>
          destruct H; subst; try progress cbn
      | u: () |- _ =>
          destruct u; try progress cbn
      end; try easy; auto.

  Lemma simplify_sub_perm_spec {Σ} (a1 a2 : Term Σ ty_access_type) :
    simplify_sub_perm a1 a2 ⊣⊢ Some [formula_user sub_perm [a1; a2]].
  Proof.
    unfold simplify_sub_perm. lsolve.
    intros ι; cbn. unfold Sub_perm.
    now destruct decide_sub_perm.
  Qed.

  Lemma simplify_access_pmp_perm_spec {Σ} (acc : Term Σ ty_access_type) (p : Term Σ ty_pmpcfgperm) :
    simplify_access_pmp_perm acc p ⊣⊢ Some [formula_user access_pmp_perm [acc; p]].
  Proof.
    unfold simplify_access_pmp_perm. lsolve.
    intros ι; cbn. unfold Access_pmp_perm.
    now destruct decide_access_pmp_perm.
  Qed.

  Lemma addr_match_type_neq_off_cases :
    ∀ a, a ≠ OFF -> a = TOR.
  Proof. by destruct a. Qed.

  Local Ltac process_inst ι :=
    repeat match goal with
      | a: NamedEnv ?t (recordf_ty ?r) |- _ =>
          simpl in a; env.destroy a
      | H: ∀ ι : Valuation ?Σ, ?P |- _ =>
          specialize (H ι)
      end.

  Opaque NumPmpEntries.
  Lemma simplify_pmp_access_spec {Σ} (paddr : Term Σ ty_xlenbits)
    (width : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry))
    (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) :
    simplify_pmp_access paddr width es p acc ⊣⊢ Some [formula_user pmp_access [paddr; width; es; p; acc]].
  Proof.
    unfold simplify_pmp_access. lsolve.
    - intros ι; cbn. unfold Pmp_access, decide_pmp_access.
      induction (RiscvPmpSignature.split_entries NumPmpEntries a1).
      + destruct a4; simpl.
        admit. (* TODO: provable *)
      + lsolve.
    (* - *) (* env.destroy a1; induction a1; lsolve. *)
      (* env.destroy a1; destruct a1; [easy|]. *)
      (* env.destroy a1; destruct a1; [|easy]. *)
      (* cbn; destruct v as [[] ?]; destruct v0 as [[] ?]; lsolve. *)
      (* cbn. *)
      (* intros ι; cbn; *)
      (*   unfold Pmp_access, decide_pmp_access, check_pmp_access, *)
      (*   pmp_check, pmp_match_entry, pmp_match_addr, pmp_addr_range; *)
      (*   process_inst ι. *)
      (* split; intros Hpmp. *)
      (* + repeat match goal with *)
      (*          | H: inst ?ι ?v = ?x |- _ => *)
      (*              cbn in H; rewrite H *)
      (*          | H: ?x = inst ?ι ?v |- _ => *)
      (*              symmetry in H *)
      (*          | H: ?P ∧ ?q |- _ => *)
      (*              destruct H *)
      (*          | H: ?P ∨ ?q |- _ => *)
      (*              destruct H *)
      (*          | H: ?x = OFF |- _ => *)
      (*              rewrite !H; clear H *)
      (*          | H: ?x ≠ OFF |- _ => *)
      (*              apply addr_match_type_neq_off_cases in H; rewrite H *)
      (*          | H: Pmp_check_perms _ _ _ |- _ => *)
      (*              apply Pmp_check_perms_Access_pmp_perm in H; unfold Access_pmp_perm in H *)
      (*          end; *)
      (*     subst; *)
      (*     try progress cbn; *)
      (*     bv_comp_bool; *)
      (*     simpl; *)
      (*     auto. *)
      (* + destruct Hpmp as [_ Hpmp]; simpl in Hpmp. *)
      (*   destruct A, A0; *)
      (*     repeat match goal with *)
      (*       | H: context[match inst ?v ?ι with | _ => _ end] |- _ => *)
      (*           let E := fresh "E" in *)
      (*           destruct (inst v ι) eqn:E; rewrite ?E in H *)
      (*       | H: context[if ?a <ᵘ? ?b then _ else _] |- _ => *)
      (*           let E := fresh "E" in *)
      (*           destruct (a <ᵘ? b) eqn:E; rewrite ?E in H *)
      (*       | H: context[if ?a <=ᵘ? ?b then _ else _] |- _ => *)
      (*           let E := fresh "E" in *)
      (*           destruct (a <=ᵘ? b) eqn:E; rewrite ?E in H *)
      (*       | H: context[if false && _ then _ else _] |- _ => *)
      (*           rewrite andb_false_l in H *)
      (*       | H: context[if true && _ then _ else _] |- _ => *)
      (*           rewrite andb_true_l in H *)
      (*       | H: context[if ?a && ?b then _ else _] |- _ => *)
      (*           let E := fresh "E" in *)
      (*           destruct (a) eqn:E; rewrite ?E in H *)
      (*       | H: context[if true || _ then _ else _] |- _ => *)
      (*           rewrite orb_true_l in H *)
      (*       | H: context[if false || _ then _ else _] |- _ => *)
      (*           rewrite orb_false_l in H *)
      (*       | H: context[if ?a || ?b then _ else _] |- _ => *)
      (*           let E := fresh "E" in *)
      (*           destruct (a) eqn:E; rewrite ?E in H *)
      (*       end; *)
      (*     try discriminate; *)
      (*     bv_comp; *)
      (*     rewrite ?Pmp_check_perms_Access_pmp_perm; *)
      (*     repeat split; *)
      (*     auto 11. *)
    (* - intros ι; cbn;
        unfold Pmp_access, decide_pmp_access, check_pmp_access,
        pmp_check, pmp_match_entry, pmp_match_addr, pmp_addr_range;
        process_inst ι.
      split; intros Hpmp.
      + repeat match goal with
             | H: inst ?ι ?v = ?x |- _ =>
                 cbn in H; rewrite H
             | H: ?x = inst ?ι ?v |- _ =>
                 symmetry in H
             | H: ?P ∧ ?q |- _ =>
                 destruct H
             | H: ?P ∨ ?q |- _ =>
                 destruct H
             | H: ?x = OFF |- _ =>
                 rewrite !H; clear H
             | H: ?x ≠ OFF |- _ =>
                 apply addr_match_type_neq_off_cases in H; rewrite H
             end;
        subst;
        try progress cbn;
        bv_comp_bool;
        simpl;
        try apply Pmp_check_perms_Access_pmp_perm;
        auto.
      + repeat match goal with
             | H: inst ?ι ?v = ?x |- _ =>
                 cbn in H; rewrite H in Hpmp; simpl in Hpmp
             | H: ?x = inst ?ι ?v |- _ =>
                 symmetry in H
             | H: ?P ∧ ?q |- _ =>
                 destruct H
             | H: ?P ∨ ?q |- _ =>
                 destruct H
             | H: ?x ≠ OFF |- _ =>
                 apply addr_match_type_neq_off_cases in H; rewrite H
             end;
        subst;
        try progress cbn.
        repeat match goal with
               | H: context[match inst ?v ?ι with | _ => _ end] |- _ =>
                   let E := fresh "E" in
                   destruct (inst v ι) eqn:E; rewrite ?E in H
               | H: context[if ?a <ᵘ? ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a <ᵘ? b) eqn:E; rewrite ?E in H
               | H: context[if ?a <=ᵘ? ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a <=ᵘ? b) eqn:E; rewrite ?E in H
               | H: context[if false && _ then _ else _] |- _ =>
                   rewrite andb_false_l in H
               | H: context[if true && _ then _ else _] |- _ =>
                   rewrite andb_true_l in H
               | H: context[if ?a && ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a) eqn:E; rewrite ?E in H
               | H: context[if true || _ then _ else _] |- _ =>
                   rewrite orb_true_l in H
               | H: context[if false || _ then _ else _] |- _ =>
                   rewrite orb_false_l in H
               | H: context[if ?a || ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a) eqn:E; rewrite ?E in H
               end;
          try discriminate;
          bv_comp;
          rewrite ?Pmp_check_perms_Access_pmp_perm;
          repeat split;
          auto 11.
    - intros ι; cbn;
        unfold Pmp_access, decide_pmp_access, check_pmp_access,
        pmp_check, pmp_match_entry, pmp_match_addr, pmp_addr_range;
        process_inst ι.
      split; intros Hpmp.
      + repeat match goal with
             | H: inst ?ι ?v = ?x |- _ =>
                 cbn in H; rewrite H
             | H: ?x = inst ?ι ?v |- _ =>
                 symmetry in H
             | H: ?P ∧ ?q |- _ =>
                 destruct H
             | H: ?P ∨ ?q |- _ =>
                 destruct H
             | H: ?x = OFF |- _ =>
                 rewrite !H; clear H
             | H: ?x ≠ OFF |- _ =>
                 apply addr_match_type_neq_off_cases in H; rewrite H
             end;
        subst;
        try progress cbn;
        bv_comp_bool;
        simpl;
        try apply Pmp_check_perms_Access_pmp_perm;
        auto.
      + repeat match goal with
             | H: inst ?ι ?v = ?x |- _ =>
                 cbn in H; rewrite H in Hpmp; simpl in Hpmp
             | H: ?x = inst ?ι ?v |- _ =>
                 symmetry in H
             | H: ?P ∧ ?q |- _ =>
                 destruct H
             | H: ?P ∨ ?q |- _ =>
                 destruct H
             | H: ?x ≠ OFF |- _ =>
                 apply addr_match_type_neq_off_cases in H; rewrite H
             end;
        subst;
        try progress cbn.
        repeat match goal with
               | H: context[match inst ?v ?ι with | _ => _ end] |- _ =>
                   let E := fresh "E" in
                   destruct (inst v ι) eqn:E; rewrite ?E in H
               | H: context[if ?a <ᵘ? ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a <ᵘ? b) eqn:E; rewrite ?E in H
               | H: context[if ?a <=ᵘ? ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a <=ᵘ? b) eqn:E; rewrite ?E in H
               | H: context[if false && _ then _ else _] |- _ =>
                   rewrite andb_false_l in H
               | H: context[if true && _ then _ else _] |- _ =>
                   rewrite andb_true_l in H
               | H: context[if ?a && ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a) eqn:E; rewrite ?E in H
               | H: context[if true || _ then _ else _] |- _ =>
                   rewrite orb_true_l in H
               | H: context[if false || _ then _ else _] |- _ =>
                   rewrite orb_false_l in H
               | H: context[if ?a || ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a) eqn:E; rewrite ?E in H
               end;
          try discriminate;
          bv_comp;
          rewrite ?Pmp_check_perms_Access_pmp_perm;
          repeat split;
          auto 11.
    - intros ι; cbn;
        unfold Pmp_access, decide_pmp_access, check_pmp_access,
        pmp_check, pmp_match_entry, pmp_match_addr, pmp_addr_range;
        process_inst ι.
      split; intros Hpmp.
      + repeat match goal with
             | H: inst ?ι ?v = ?x |- _ =>
                 cbn in H; rewrite H
             | H: ?x = inst ?ι ?v |- _ =>
                 symmetry in H
             | H: ?P ∧ ?q |- _ =>
                 destruct H
             | H: ?P ∨ ?q |- _ =>
                 destruct H
             | H: ?x = OFF |- _ =>
                 rewrite !H; clear H
             | H: ?x ≠ OFF |- _ =>
                 apply addr_match_type_neq_off_cases in H; rewrite H
             end;
        subst;
        try progress cbn;
        bv_comp_bool;
        simpl;
        try apply Pmp_check_perms_Access_pmp_perm;
        auto.
      + repeat match goal with
             | H: inst ?ι ?v = ?x |- _ =>
                 cbn in H; rewrite H in Hpmp; simpl in Hpmp
             | H: ?x = inst ?ι ?v |- _ =>
                 symmetry in H
             | H: ?P ∧ ?q |- _ =>
                 destruct H
             | H: ?P ∨ ?q |- _ =>
                 destruct H
             | H: ?x ≠ OFF |- _ =>
                 apply addr_match_type_neq_off_cases in H; rewrite H
             end;
        subst;
        try progress cbn.
        repeat match goal with
               | H: context[match inst ?v ?ι with | _ => _ end] |- _ =>
                   let E := fresh "E" in
                   destruct (inst v ι) eqn:E; rewrite ?E in H
               | H: context[if ?a <ᵘ? ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a <ᵘ? b) eqn:E; rewrite ?E in H
               | H: context[if ?a <=ᵘ? ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a <=ᵘ? b) eqn:E; rewrite ?E in H
               | H: context[if false && _ then _ else _] |- _ =>
                   rewrite andb_false_l in H
               | H: context[if true && _ then _ else _] |- _ =>
                   rewrite andb_true_l in H
               | H: context[if ?a && ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a) eqn:E; rewrite ?E in H
               | H: context[if true || _ then _ else _] |- _ =>
                   rewrite orb_true_l in H
               | H: context[if false || _ then _ else _] |- _ =>
                   rewrite orb_false_l in H
               | H: context[if ?a || ?b then _ else _] |- _ =>
                   let E := fresh "E" in
                   destruct (a) eqn:E; rewrite ?E in H
               end;
          try discriminate;
          bv_comp;
          rewrite ?Pmp_check_perms_Access_pmp_perm;
          repeat split;
          auto 11.
  Qed. *)
  Admitted.

  #[local] Arguments Pmp_check_rwx !cfg !acc /.
  Lemma simplify_pmp_check_rwx_spec {Σ} (cfg : Term Σ ty_pmpcfg_ent) (acc : Term Σ ty_access_type) :
    simplify_pmp_check_rwx cfg acc ⊣⊢ Some [formula_user pmp_check_rwx [cfg; acc]].
  Proof.
    unfold simplify_pmp_check_rwx.
    destruct (term_get_record_spec cfg); [|lsolve].
    cbn in a; env.destroy a; cbn in *; lsolve.
    destruct a; lsolve.
    - destruct a; lsolve; intro; cbn; now rewrite H.
    - destruct a; lsolve; intro; cbn; now rewrite H.
    - destruct (a && a0)%bool eqn:Heq; lsolve; intro; cbn; rewrite H; cbn; intuition.
      now rewrite Heq in H0.
    - destruct a; lsolve; intro; cbn; now rewrite H.
  Qed.

  Lemma simplify_pmp_check_perms_spec {Σ} (cfg : Term Σ ty_pmpcfg_ent)
    (acc : Term Σ ty_access_type) (p : Term Σ ty_privilege) :
    simplify_pmp_check_perms cfg acc p ⊣⊢ Some [formula_user pmp_check_perms [cfg; acc; p]].
  Proof.
    unfold simplify_pmp_check_perms.
    destruct (term_get_record_spec cfg); [|lsolve].
    cbn in a; env.destroy a; cbn in *; lsolve.
    destruct a; lsolve.
    destruct a; lsolve; intros ι; cbn; now rewrite H.
  Qed.

  Lemma simplify_within_cfg_spec {Σ} (paddr : Term Σ ty_xlenbits)
    (cfg : Term Σ ty_pmpcfg_ent) (prevaddr addr : Term Σ ty_xlenbits) :
    simplify_within_cfg paddr cfg prevaddr addr ⊣⊢ Some [formula_user within_cfg [paddr; cfg; prevaddr; addr]].
  Proof.
    unfold simplify_within_cfg. lsolve.
    intros ι; cbn. unfold Within_cfg.
    now destruct decide_within_cfg.
  Qed.

  Lemma simplify_prev_addr_spec {Σ} (cfg : Term Σ ty_pmpcfgidx)
    (entries : Term Σ (ty.list ty_pmpentry)) (prev : Term Σ ty_xlenbits) :
    simplify_prev_addr cfg entries prev ⊣⊢ Some [formula_user prev_addr [cfg; entries; prev]].
  Proof.
    unfold simplify_prev_addr. lsolve.
    intros ι; cbn. unfold Prev_addr.
    now destruct decide_prev_addr.
  Qed.

  Lemma simplify_user_spec : SolverUserOnlySpec simplify_user.
  Proof.
    intros Σ p ts.
    destruct p; cbv in ts; env.destroy ts; cbn.
    - simple apply simplify_pmp_access_spec.
    - simple apply simplify_pmp_check_perms_spec.
    - simple apply simplify_pmp_check_rwx_spec.
    - simple apply simplify_sub_perm_spec.
    - simple apply simplify_access_pmp_perm_spec.
    - simple apply simplify_within_cfg_spec.
    - reflexivity.
    - simple apply simplify_prev_addr_spec.
    - reflexivity.
  Qed.

  Definition solver : Solver :=
    solveruseronly_to_solver simplify_user.

  Lemma solver_spec : SolverSpec solver.
  Proof.
    apply solveruseronly_to_solver_spec, simplify_user_spec.
  Qed.

End RiscvPmpSolverKit.
Module RiscvPmpSolver := MakeSolver RiscvPmpBase RiscvPmpSignature RiscvPmpSolverKit.
