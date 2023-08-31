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
     Classes.EquivDec
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
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(* bv_comp is a tactic that converts boolean comparison operators into props. *)
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

(* PurePredicate defines the pure predicates for this case. *)
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

(* Predicate defines the spatial predicates for this case. *)
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
    (* 𝑷_Ty gives the parameter types for the pure predicates. *)
    Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
      match p with
      | pmp_access               => [ty_xlenbits; ty_xlenbits; ty.list ty_pmpentry; ty_privilege; ty_access_type]
      | pmp_check_perms          => [ty_pmpcfg_ent; ty_access_type; ty_privilege]
      | pmp_check_rwx            => [ty_pmpcfg_ent; ty_access_type]
      | sub_perm                 => [ty_access_type; ty_access_type]
      | access_pmp_perm          => [ty_access_type; ty_pmpcfgperm]
      | within_cfg               => [ty_xlenbits; ty_pmpcfg_ent; ty_xlenbits; ty_xlenbits]
      | not_within_cfg           => [ty_xlenbits; ty.list ty_pmpentry]
      | prev_addr                => [ty_pmpcfgidx; ty.list ty_pmpentry; ty_xlenbits]
      | in_entries               => [ty_pmpcfgidx; ty_pmpentry; ty.list ty_pmpentry]
      end.

    (* PmpEntryCfg is an alias for a pmp entry, which consists of the config
       (Pmpcfg_ent) and the address. *)
    Definition PmpEntryCfg : Set := Pmpcfg_ent * Xlenbits.
    (* PmpAddrRange is the range for a pmp entry, this can be None if the pmp
       entry addr match type is OFF. *)
    Definition PmpAddrRange := option (Xlenbits * Xlenbits).

    (* default_pmpcfg_ent defines the default config for a pmp entry, which is
       unlocked and OFF. These configurations give full permission to Machine
       mode and deny all access to User mode. *)
    Example default_pmpcfg_ent : Pmpcfg_ent :=
      {| L := false; A := OFF; X := false; W := false; R := false |}.

    (* default_pmpentries is the default list of pmp entries, where each
       entry has the default config and a zero address. *)
    Example default_pmpentries : list PmpEntryCfg :=
      [(default_pmpcfg_ent, bv.zero);
       (default_pmpcfg_ent, bv.zero)
      ].

    (* pmp_check_RWX decides if we the requested access type is allowed for
       the given pmp config. *)
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

    (* pmp_get_perms returns a PmpCfgperm depending on the fields of the pmp config
       and given privilege level. *)
    Definition pmp_get_perms (cfg : Val ty_pmpcfg_ent) (p : Val ty_privilege) : Val ty_pmpcfgperm :=
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

    (* decide_pmp_check_perms decides whether we can access pmp config cfg with
       the requested access type and privilege level. *)
    Definition decide_pmp_check_perms (cfg : Val ty_pmpcfg_ent) (acc : Val ty_access_type) (p : Val ty_privilege) : bool :=
      match p with
      | Machine =>
          if L cfg
          then pmp_check_RWX cfg acc
          else true
      | User =>
          pmp_check_RWX cfg acc
      end.

    (* pmp_addr_range returns the addr range based on the addr match type of the
       pmp config. *)
    Definition pmp_addr_range (cfg : Pmpcfg_ent) (hi lo : Xlenbits) : PmpAddrRange :=
      match A cfg with
      | OFF => None
      | TOR => Some (lo , hi)
      end.

    (* pmp_match_addr matches the given addr a and width against the range rng. *)
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

  Section PmpMatchAddrConditions.
    (* In this section we define lemmas that capture the conditions for the
       different outcomes fo the pmp_addr_match function. *)
    Lemma pmp_match_addr_match_conditions_1 : forall (paddr w lo hi : Val ty_xlenbits),
        bv.zero <ᵘ w ->
        pmp_match_addr paddr w (Some (lo , hi)) = PMP_Match ->
        lo <=ᵘ hi /\ lo <ᵘ (paddr + w)%bv /\ lo <=ᵘ paddr /\ paddr <ᵘ hi /\ (paddr + w)%bv <=ᵘ hi.
    Proof.
      unfold pmp_match_addr.
      intros paddr w lo hi Hw H.
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
        bv.zero <ᵘ w ->
        lo <=ᵘ hi ->
        lo <ᵘ (paddr + w)%bv ->
        lo <=ᵘ paddr ->
        paddr <ᵘ hi ->
        (paddr + w)%bv <=ᵘ hi ->
        pmp_match_addr paddr w (Some (lo , hi)) = PMP_Match.
    Proof.
      intros paddr w lo hi Hw Hlohi Hlopw Hlop Hphi Hpwhi.
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
  End PmpMatchAddrConditions.

    (* pmp_match_entry matches the given address, width and privilege against
       the given config and bounds of a pmp entry. *)
    Definition pmp_match_entry (a : Val ty_xlenbits) (width : Val ty_xlenbits) (m : Val ty_privilege) (cfg : Val ty_pmpcfg_ent) (lo hi : Val ty_xlenbits) : Val ty_pmpmatch :=
      let rng := pmp_addr_range cfg hi lo in
      match pmp_match_addr a width rng with
      | PMP_NoMatch      => PMP_Continue
      | PMP_PartialMatch => PMP_Fail
      | PMP_Match        => PMP_Success
      end.

    (* pmp_check is our spec implementation of the pmp check algorithm to be
       used in our predicates. *)
    Definition pmp_check (a : Val ty_xlenbits) (width : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (prev : Val ty_xlenbits) (m : Val ty_privilege) : (bool * option (Val ty_pmpcfgperm)) :=
      match entries with
      | (cfg0 , addr0) :: (cfg1 , addr1) :: [] =>
          match pmp_match_entry a width m cfg0 prev addr0 with
          | PMP_Success  => (true, Some (pmp_get_perms cfg0 m))
          | PMP_Fail     => (false, None)
          | PMP_Continue => 
              match pmp_match_entry a width m cfg1 addr0 addr1 with
              | PMP_Success  => (true, Some (pmp_get_perms cfg1 m))
              | PMP_Fail     => (false, None)
              | PMP_Continue => match m with
                                | Machine => (true, None)
                                | User    => (false, None)
                                end
              end
          end
      | _ => match m with
             | Machine => (true, None)
             | User    => (false, None)
             end
      end%list.

    (* check_pmp_access is based on the pmpCheck algorithm, main difference
       is that we can define it less cumbersome because entries will contain
       the PMP entries in highest-priority order. *)
    Definition check_pmp_access (a : Val ty_xlenbits) (width : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) : (bool * option (Val ty_pmpcfgperm)) :=
      pmp_check a width entries [bv 0] m.

    Definition access_type_eqb := @equiv_decb _ _ _ AccessType_eqdec.

    (* decide_sub_perm decides if a1 is a subpermission of a2. *)
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

    (* Sub_perm is the predicate implementation of decide_sub_perm. *)
    Definition Sub_perm (a1 a2 : Val ty_access_type) : Prop :=
      decide_sub_perm a1 a2 = true.

    (* decide_access_pmp_perm decides whether the access type is a subpermission
       of a pmp config permission. *)
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

    (* Access_pmp_perm is the predicate implementation of decide_access_pmp_perm. *)
    Definition Access_pmp_perm (a : Val ty_access_type) (p : Val ty_pmpcfgperm) : Prop :=
      decide_access_pmp_perm a p = true.

    (* decide_pmp_access is the decision procedure for the pmp check. From the
       pmp check we get whether we have a match and which permissions the
       matching pmp entry has. We then need to check if the requested access
       type is a subpermission of the pmp entry permissions. *)
    Definition decide_pmp_access (a : Val ty_xlenbits) (width : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) (acc : Val ty_access_type) : bool :=
      match check_pmp_access a width entries m with
      | (true, Some p) => decide_access_pmp_perm acc p
      | (true, None)     => true
      | (false, _)       => false
      end.

    (* Pmp_access is the predicate implementation of decide_pmp_access. *)
    Definition Pmp_access (a : Val ty_xlenbits) (width : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) (acc : Val ty_access_type) : Prop :=
      decide_pmp_access a width entries m acc = true.

    (* Pmp_check_perms is the predicate implementation of decide_pmp_check_perms. *)
    Definition Pmp_check_perms (cfg : Val ty_pmpcfg_ent) (acc : Val ty_access_type) (p : Val ty_privilege) : Prop :=
      decide_pmp_check_perms cfg acc p = true.

    (* Pmp_check_rwx is the predicate implementation of pmp_check_RWX. *)
    Definition Pmp_check_rwx (cfg : Val ty_pmpcfg_ent) (acc : Val ty_access_type) : Prop :=
      pmp_check_RWX cfg acc = true.

    Definition PmpAddrMatchType_eqb := @equiv_decb _ _ _ PmpAddrMatchType_eqdec.

    Definition pmpcfg_ent_eqb := @equiv_decb _ _ _ Pmpcfg_ent_eqdec.

    (* decide_in_entries decides whether the given pmp entry is in the list of
       pmp entries at the specified index. *)
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

    (* In_entries is the predicate implementation of decide_in_entries. *)
    Definition In_entries (idx : Val ty_pmpcfgidx) (e : Val ty_pmpentry) (es : Val (ty.list ty_pmpentry)) : Prop :=
      decide_in_entries idx e es = true.

    (* decide_prev_addr decides if the given prev address is the previous
       address of the given pmp config index in the entries list. *)
    Definition decide_prev_addr (cfg : Val ty_pmpcfgidx) (entries : Val (ty.list ty_pmpentry)) (prev : Val ty_xlenbits) : bool :=
      match entries with
      | (c0 , a0) :: (c1 , a1) :: [] =>
          match cfg with
          | PMP0CFG => bv.eqb prev [bv 0]
          | PMP1CFG => bv.eqb prev a0
          end
      | _ => false
      end%list.

    (* Prev_addr is the predicate implementation of decide_prev_addr. *)
    Definition Prev_addr (cfg : Val ty_pmpcfgidx) (entries : Val (ty.list ty_pmpentry)) (prev : Val ty_xlenbits) : Prop :=
      decide_prev_addr cfg entries prev = true.

    (* decide_within_cfg decides if the given physical adress is within the
       given bounds according to the addr match type of the pmp config. *)
    Definition decide_within_cfg (paddr : Val ty_xlenbits) (cfg : Val ty_pmpcfg_ent) (prev_addr addr : Val ty_xlenbits) : bool :=
      match A cfg with
      | OFF => false
      | TOR => (prev_addr <=ᵘ? paddr) && (paddr <ᵘ? addr)
      end.

    (* Within_cfg is the predicate implementation of decide_within_cfg. *)
    Definition Within_cfg (paddr : Val ty_xlenbits) (cfg : Val ty_pmpcfg_ent) (prev_addr addr : Val ty_xlenbits) : Prop :=
      decide_within_cfg paddr cfg prev_addr addr = true.

    (* decide_not_within_cfg checks whether the given paddr is within any pmp
       entry of the entries list. *)
    Definition decide_not_within_cfg (paddr : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) : bool :=
      match entries with
      | (c0 , a0) :: (c1 , a1) :: [] =>
          (((PmpAddrMatchType_eqb (A c0) OFF) && (PmpAddrMatchType_eqb (A c1) OFF))
          || (([bv 0] <=ᵘ? paddr) && (a0 <=ᵘ? paddr) && (a1 <=ᵘ? paddr)))%bool
      | _ => false
      end%list.

    (* Not_within_cfg is the predicate implementation of decide_not_within_cfg. *)
    Definition Not_within_cfg (paddr : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) : Prop :=
      decide_not_within_cfg paddr entries = true.

    Definition is_pmp_cfg_unlocked (cfg : Val ty_pmpcfg_ent) : bool :=
      negb (L cfg).

    Lemma is_pmp_cfg_unlocked_bool : forall (cfg : Val ty_pmpcfg_ent),
        is_pmp_cfg_unlocked cfg = true <->
        L cfg = false.
    Proof. intros [[]]; split; auto. Qed.

    (* Pmp_cfg_unlocked is a predicate that indicates whether the lock bit of a
       config is set or not. *)
    Definition Pmp_cfg_unlocked (cfg : Val ty_pmpcfg_ent) : Prop :=
      is_pmp_cfg_unlocked cfg = true.

    Lemma Pmp_cfg_unlocked_bool : forall (cfg : Val ty_pmpcfg_ent),
        Pmp_cfg_unlocked cfg <->
        L cfg = false.
    Proof. unfold Pmp_cfg_unlocked; apply is_pmp_cfg_unlocked_bool. Qed.

    (* Pmp_entry_unlocked is the Pmp_cfg_unlocked predicated lifted to pmp
       entries (a pair of a config and address). *)
    Definition Pmp_entry_unlocked (ent : Val ty_pmpentry) : Prop :=
      Pmp_cfg_unlocked (fst ent).
    Global Arguments Pmp_entry_unlocked !ent.

    (* 𝑷_inst couples the pure predicates to their implementation. *)
    Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
      match p with
      | pmp_access               => Pmp_access
      | pmp_check_perms          => Pmp_check_perms
      | pmp_check_rwx            => Pmp_check_rwx
      | sub_perm                 => Sub_perm
      | access_pmp_perm          => Access_pmp_perm
      | within_cfg               => Within_cfg
      | not_within_cfg           => Not_within_cfg
      | prev_addr                => Prev_addr
      | in_entries               => In_entries
      end.

    Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

    Definition 𝑯 := Predicate.
    (* 𝑯_Ty defines the parameter types of the spatial predicates. *)
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

    (* 𝑯_is_dup indicates which spatial predicates are duplicable. *)
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

    (* 𝑯_precise specifies which predicates are precise and what the input and
       output parameters of precise predicates are. *)
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

    (* z_term is shorthand for creating integer terms. *)
    Definition z_term {Σ} : Z -> Term Σ ty.int := term_val ty.int.

    (* sep_contract_logvars creates an LCtx representing the logical variables
       for the given Δ and Σ (function arguments and additional logical
       variables). *)
    Definition sep_contract_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
      ctx.map (fun '(x::σ) => x::σ) Δ ▻▻ Σ.

    (* create_localstore creates the localstore from the given program context
       and logical context. *)
    Definition create_localstore (Δ : PCtx) (Σ : LCtx) : SStore Δ (sep_contract_logvars Δ Σ) :=
      (env.tabulate (fun '(x::σ) xIn =>
                       @term_var
                         (sep_contract_logvars Δ Σ)
                         x
                         σ
                         (ctx.in_cat_left Σ (ctx.in_map (fun '(y::τ) => y::τ) xIn)))).

    (* asn_and_regs maps f over each GPR. *)
    Definition asn_and_regs {Σ} (f : Reg ty_xlenbits -> Assertion Σ) : Assertion Σ :=
      f x1 ∗ f x2 ∗ f x3 ∗ f x4 ∗ f x5 ∗ f x6 ∗ f x7 ∗ f x8 ∗ f x9 ∗
      f x10 ∗ f x11 ∗ f x12 ∗ f x13 ∗ f x14 ∗ f x15 ∗ f x16 ∗ f x17 ∗ f x18 ∗ f x19 ∗
      f x20 ∗ f x21 ∗ f x22 ∗ f x23 ∗ f x24 ∗ f x25 ∗ f x26 ∗ f x27 ∗ f x28 ∗ f x29 ∗
      f x30 ∗ f x31. 

    (* asn_regs_ptsto asserts ownership over all GPRs. *)
    Definition asn_regs_ptsto {Σ} : Assertion Σ :=
      asn_and_regs
        (fun r => asn.exist "w" _ (r ↦ term_var "w")).

    Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

    Definition term_pmp_entries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfgidx ty_pmpaddridx)) :=
      term_list
        (cons (term_val ty_pmpcfgidx PMP0CFG ,ₜ term_val ty_pmpaddridx PMPADDR0)
              (cons (term_val ty_pmpcfgidx PMP1CFG ,ₜ term_val ty_pmpaddridx PMPADDR1) nil)).

  End ContractDefKit.

  Import asn.notations.

  Module notations.
    Notation "a '↦mem' b bs" := (asn.chunk (chunk_user (ptstomem b) [a; bs])) (at level 70).
    Notation "a '↦ₘ' t" := (asn.chunk (chunk_user ptsto [a; t])) (at level 70).
    Notation "p '⊑' q" := (asn.formula (formula_user sub_perm [p;q])) (at level 70).

    Notation asn_bool t := (asn.formula (formula_bool t)).
    Notation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
    Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

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
  (* In the RiscvPmpSolverKit we start by defining simplification functions for
     the pure predicates. Most of these have a similar structure, if the term
     is a ground value, then we can just call the decision function of the
     predicate on it. If this function returns true, then the predicate holds
     and no other conditions need to be fullfilled. If the result is false,
     then the predicate cannot be satisfied and we return None to indicate this.
     To have a sound solver we also prove that our simplification functions
     are sound. *)
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

  Definition simplify_pmp_access {Σ} (paddr : Term Σ ty_xlenbits) (width : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (PathCondition Σ) :=
    match term_get_val paddr , term_get_val width , term_get_val es , term_get_val p with
    | Some paddr , Some width , Some entries , Some p =>
      match check_pmp_access paddr width entries p with
      | (true, Some typ) => simplify_access_pmp_perm acc (term_val ty_pmpcfgperm typ)
      | (true, None)     => Some []
      | (false, _)       => None
      end
    | _, _ , _ , _ => Some [formula_user pmp_access [paddr; width; es; p; acc]]
    end%ctx.

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

  (* simplify_user couples the predicates and their simplification function. *)
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

  Lemma simplify_pmp_access_spec {Σ} (paddr : Term Σ ty_xlenbits)
    (width : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry))
    (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) :
    simplify_pmp_access paddr width es p acc ⊣⊢ Some [formula_user pmp_access [paddr; width; es; p; acc]].
  Proof.
    unfold simplify_pmp_access. lsolve.
    - intros ι; cbn. unfold Pmp_access, decide_pmp_access.
      destruct check_pmp_access as [[] o]; [|easy].
      destruct o; [|easy].
      apply simplify_access_pmp_perm_spec.
  Qed.

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
