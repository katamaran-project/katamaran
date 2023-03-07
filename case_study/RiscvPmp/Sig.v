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
     RiscvPmp.Base
     RiscvPmp.PmpCheck.
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
| gen_pmp_access
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
      | gen_pmp_access  => [ty.int; ty_xlenbits; ty_xlenbits; ty_xlenbits; ty.list ty_pmpentry; ty_privilege; ty_access_type]
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

    Definition decide_pmp_check_perms (cfg : Val ty_pmpcfg_ent) (acc : Val ty_access_type) (p : Val ty_privilege) : bool :=
      match p with
      | Machine =>
          if L cfg
          then pmp_check_RWX cfg acc
          else true
      | User =>
          pmp_check_RWX cfg acc
      end.

    Definition Pmp_check_perms (cfg : Val ty_pmpcfg_ent) (acc : Val ty_access_type) (p : Val ty_privilege) : Prop :=
      decide_pmp_check_perms cfg acc p = true.

    Definition Access_pmp_perm (a : Val ty_access_type) (p : Val ty_pmpcfgperm) : Prop :=
      decide_access_pmp_perm a p = true.

    Lemma Pmp_check_perms_Access_pmp_perm : forall cfg acc p,
        Pmp_check_perms cfg acc p <-> Access_pmp_perm acc (pmp_get_perms cfg p).
    Proof. by intros [[] ? [] [] []] [] []. Qed.

    Definition Gen_Pmp_access (n : Val ty.int) (a width lo : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) (acc : Val ty_access_type) : Prop :=
      pmp_check_aux (Z.to_nat n) a width lo entries m acc = true.

    Definition Pmp_access (a : Val ty_xlenbits) (width : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) (acc : Val ty_access_type) : Prop :=
      Gen_Pmp_access (Z.of_nat NumPmpEntries) a width bv.zero entries m acc.

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

    Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
      match p with
      | gen_pmp_access  => Gen_Pmp_access
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

  #[local] Arguments Some {_} _%ctx.
  Local Notation "P ∨ Q" := (formula_or P Q). 
  Local Notation "P ∧ Q" := (formula_and P Q). 

  Definition is_off {Σ} (A : Term Σ ty_pmpaddrmatchtype) : Formula Σ :=
    formula_relop bop.eq A (term_val ty_pmpaddrmatchtype OFF).

  Definition is_on {Σ} (A : Term Σ ty_pmpaddrmatchtype) : Formula Σ :=
    formula_relop bop.neq A (term_val ty_pmpaddrmatchtype OFF).

  Definition is_machine_mode {Σ} (p : Term Σ ty_privilege) : Formula Σ :=
    formula_relop bop.eq (term_val ty_privilege Machine) p.

  Fixpoint simplify_pmpcheck {Σ} (n : nat) (a width lo : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (Formula Σ) :=
    match n, term_get_list es with
    | S n, Some (inl (pmp , es)) =>
        '(cfg , addr) <- term_get_pair pmp ;;
        cfg <- term_get_record cfg ;;
        fml <- simplify_pmpcheck n a width addr es p acc ;;
        Some (((* PMP_NoMatch *)
              (is_off cfg.[??"A"]
               ∨ (is_on cfg.[??"A"] ∧
                    (formula_relop bop.bvult addr lo
                     ∨ (formula_relop bop.bvule lo addr ∧ formula_relop bop.bvule (term_binop bop.bvadd a width) lo)
                     ∨ (formula_relop bop.bvule lo addr ∧ formula_relop bop.bvult lo (term_binop bop.bvadd a width) ∧ formula_relop bop.bvule addr a))))
              ∧ fml)
              ∨
                ((* PMP_Match *)
                  is_on cfg.[??"A"]
                  ∧ formula_relop bop.bvule lo addr
                  ∧ formula_relop bop.bvult lo (term_binop bop.bvadd a width)
                  ∧ formula_relop bop.bvult a addr
                  ∧ formula_relop bop.bvule lo a
                  ∧ formula_relop bop.bvule (term_binop bop.bvadd a width) addr
                  ∧ formula_user pmp_check_perms [term_record rpmpcfg_ent [cfg.[??"L"];cfg.[??"A"];cfg.[??"X"];cfg.[??"W"];cfg.[??"R"]]; acc; p]))
    | O, Some (inr tt) => Some (is_machine_mode p)
    | _, _             => None
    end%list.

  Definition pmp_check_fml_term_aux {Σ} (n : nat) (a width lo : Term Σ ty_xlenbits) (entries : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : Formula Σ :=
    let fml     := simplify_pmpcheck n a width lo entries p acc in
    match fml with
    | Some fml => fml
    | None     =>
        let term_n  := term_val ty.int (Z.of_nat n) in
        formula_user gen_pmp_access [term_n; a; width; lo; entries; p; acc]
    end.

  Definition pmp_check_fml_aux {Σ} (n : nat) (a width lo : Val ty_xlenbits) (entries : list (Val ty_pmpentry)) (p : Val ty_privilege) (acc : Val ty_access_type) : Formula Σ :=
    let a       := term_val ty_xlenbits a in
    let width   := term_val ty_xlenbits width in
    let lo      := term_val ty_xlenbits lo in
    let entries := term_val (ty.list ty_pmpentry) entries in
    let p       := term_val ty_privilege p in
    let acc     := term_val ty_access_type acc in
    pmp_check_fml_term_aux n a width lo entries p acc.

  Definition pmp_check_fml_prop_aux (n : nat) (a width lo : Val ty_xlenbits) (entries : list (Val ty_pmpentry)) (p : Val ty_privilege) (acc : Val ty_access_type) : Prop :=
    instprop (pmp_check_fml_aux n a width lo entries p acc) [env].

  Lemma cfg_record : ∀ cfg,
      {| L := L cfg; A := A cfg; X := X cfg; W := W cfg; R := R cfg |} = cfg.
  Proof. now intros []. Qed.

  Lemma pmp_addr_range_None : ∀ cfg hi lo,
      pmp_addr_range cfg hi lo = None ->
      A cfg = OFF.
  Proof.
    intros.
    unfold pmp_addr_range in H.
    destruct (A cfg); auto; discriminate.
  Qed.

  Lemma pmp_addr_range_Some : ∀ cfg hi lo p,
      pmp_addr_range cfg hi lo = Some p ->
      A cfg = TOR /\ p = (lo , hi).
  Proof.
    intros.
    unfold pmp_addr_range in H.
    destruct (A cfg); auto; now inversion H.
  Qed.

  Lemma pmp_match_entry_PMP_Continue : ∀ a width m cfg lo hi,
      pmp_match_entry a width m cfg lo hi = PMP_Continue ->
      A cfg = OFF
      ∨ (A cfg ≠ OFF ∧
         (hi <ᵘ lo
          ∨ (lo <=ᵘ hi ∧ (a + width)%bv <=ᵘ lo)
          ∨ (lo <=ᵘ hi ∧ lo <ᵘ (a + width)%bv ∧ hi <=ᵘ a))).
  Proof.
    unfold pmp_match_entry; intros.
    destruct (pmp_addr_range _ _ _) eqn:Hr.
    - apply pmp_addr_range_Some in Hr as [?%addr_match_type_TOR_neq_OFF ->].
      destruct (pmp_match_addr a width _) eqn:Hm;
        try discriminate.
      apply pmp_match_addr_nomatch in Hm.
      right; split; auto.
      destruct Hm as [|Hm]; first discriminate.
      specialize (Hm lo hi eq_refl).
      destruct Hm as [|[|]]; auto.
      + destruct (hi <ᵘ? lo) eqn:?; bv_comp; auto.
      + destruct (hi <ᵘ? lo) eqn:?;
          destruct ((a + width)%bv <=ᵘ? lo) eqn:?;
          bv_comp; auto.
    - apply pmp_addr_range_None in Hr; auto.
  Qed.

  Lemma pmp_match_entry_PMP_Success : ∀ a width m cfg lo hi,
      pmp_match_entry a width m cfg lo hi = PMP_Success ->
      A cfg = TOR
      ∧ lo <=ᵘ hi ∧ lo <ᵘ (a + width)%bv ∧ lo <=ᵘ a ∧ a <ᵘ hi ∧ (a + width)%bv <=ᵘ hi.
  Proof.
    unfold pmp_match_entry; intros.
    destruct (pmp_addr_range _ _ _) eqn:Hr;
      last (simpl in H; discriminate).
    apply pmp_addr_range_Some in Hr as (HA & ->).
    destruct (pmp_match_addr _ _ _) eqn:Ha;
      try discriminate.
    now apply pmp_match_addr_match_conditions_1 in Ha.
  Qed.

  Lemma pmp_check_inversion_fml_aux (n : nat) (a width lo : Val ty_xlenbits) (entries : list (Val ty_pmpentry)) (p : Val ty_privilege) (acc : Val ty_access_type) :
    pmp_check_aux n a width lo entries p acc = true ->
    pmp_check_fml_prop_aux n a width lo entries p acc.
  Proof.
    unfold pmp_check_aux, pmp_check_fml_prop_aux, pmp_check_fml_aux, pmp_check_fml_term_aux.
    generalize dependent lo.
    generalize dependent entries.
    induction n.
    - cbn; destruct entries; cbn.
      intros; destruct p; auto; discriminate.
      intros; discriminate.
    - cbn; destruct entries as [|[cfg0 addr0] entries];
        intros; try discriminate; cbn.
      destruct (@simplify_pmpcheck [ctx] n (term_val ty_xlenbits a) (term_val ty_xlenbits width)
                  (term_val ty_xlenbits addr0) (term_val (ty.list ty_pmpentry) entries)
                  (term_val ty_privilege p) (term_val ty_access_type acc)) eqn:Epmp;
        rewrite Epmp; cbn;
        specialize (IHn entries addr0);
        rewrite Epmp in IHn.
      + destruct (pmp_match_entry _ _ _ _ _ _) eqn:Hm;
          try discriminate.
        * apply pmp_match_entry_PMP_Success in Hm as (?%addr_match_type_TOR_neq_OFF & Hm).
          apply Pmp_check_perms_Access_pmp_perm in H.
          rewrite cfg_record.
          now right.
        * left; split; last (apply IHn; auto).
          apply pmp_match_entry_PMP_Continue in Hm as [|(? & [|[|]])]; auto.
      + destruct (pmp_match_entry _ _ _ _ _ _) eqn:Hm;
          unfold Gen_Pmp_access, pmp_check_aux;
          rewrite Nat2Z.id;
          simpl;
          now rewrite Hm.
  Qed.

  Lemma pmp_check_fml_term_aux_gen_pmp_access : forall {Σ} (n : nat) a width lo es p acc (ι : Valuation Σ),
  instprop (pmp_check_fml_term_aux n a width lo es p acc) ι
  ↔ instprop (formula_user gen_pmp_access [term_val ty.int (Z.of_nat n); a; width; lo; es; p; acc]) ι.
  Proof.
    induction n.
    - cbn.
      intros.
      unfold Gen_Pmp_access, pmp_check_fml_term_aux.
      simpl.
      split; intros H.
      + destruct (@term_get_list_spec Σ ty_pmpentry es) as [[] ?|];
          lsolve.
        cbn in H.
        rewrite (H0 ι).
        now rewrite <- H.
      + destruct (@term_get_list_spec Σ ty_pmpentry es) as [[] ?|];
          lsolve.
        rewrite (H0 ι) in H.
        destruct (inst p ι); auto; try discriminate.
    - intros; cbn.
      unfold Gen_Pmp_access, pmp_check_fml_term_aux, pmp_check_aux.
      rewrite Nat2Z.id.
      cbn - [pmp_check_rec].
      split; intros.
      + destruct (@term_get_list_spec Σ ty_pmpentry es) as [[] ?|].
        destruct p0 as [t t0].
        destruct (term_get_pair_spec t) as [[cfg0 addr0]|].
        rewrite (H0 ι) (H1 ι).
        cbn in H.
        destruct (term_get_record_spec cfg0).
        cbn in a0.
        env.destroy a0.
        simpl in H.
        cbn in IHn.
        unfold Gen_Pmp_access in IHn.
        rewrite Nat2Z.id in IHn.
        destruct (simplify_pmpcheck n a width addr0 t0 p acc) eqn:?;
          cbn in H.
        rewrite (H2 ι).
        destruct H.
        * destruct H as ([|[?%addr_match_type_neq_off_cases [|[(? & ?)|(? & ? & ?)]]]] & ?).
          cbn.
          unfold pmp_match_entry, pmp_addr_range.
          rewrite H.
          simpl.
          unfold Gen_Pmp_access, pmp_check_aux in IHn.
          apply IHn.
          unfold pmp_check_fml_term_aux.
          now rewrite Heqo.
          cbn.
          unfold pmp_match_entry, pmp_addr_range.
          rewrite H.
          simpl.
          rewrite (proj2 (bv.ultb_ult _ _) H3).
          unfold Gen_Pmp_access, pmp_check_aux in IHn.
          apply IHn.
          unfold pmp_check_fml_term_aux.
          now rewrite Heqo.
          cbn.
          unfold pmp_match_entry, pmp_addr_range.
          rewrite H.
          cbn.
          unfold Gen_Pmp_access, pmp_check_aux in IHn.
          bv_comp_bool.
          simpl.
          apply IHn.
          unfold pmp_check_fml_term_aux.
          now rewrite Heqo.
          cbn.
          unfold pmp_match_entry, pmp_match_addr; rewrite H; cbn; bv_comp_bool.
          simpl.
          apply IHn.
          unfold pmp_check_fml_term_aux.
          now rewrite Heqo.
        * cbn.
          destruct H as (? & ? & ? & ? & ? & ? & ?).
          apply addr_match_type_neq_off_cases in H.
          rewrite H.
          unfold pmp_match_entry, pmp_addr_range.
          simpl; bv_comp_bool; simpl.
          now apply Pmp_check_perms_Access_pmp_perm.
        * unfold Gen_Pmp_access, pmp_check_aux in H.
          now rewrite Nat2Z.id (H0 ι) (H1 ι) in H.
        * cbn in H.
          unfold Gen_Pmp_access, pmp_check_aux in H.
          now rewrite Nat2Z.id (H0 ι) (H1 ι) in H.
        * cbn in H.
          unfold Gen_Pmp_access, pmp_check_aux in H.
          now rewrite Nat2Z.id in H.
        * cbn in H.
          unfold Gen_Pmp_access, pmp_check_aux in H.
          now rewrite Nat2Z.id in H.
        * cbn in H.
          unfold Gen_Pmp_access, pmp_check_aux in H.
          now rewrite Nat2Z.id in H.

      + cbn.
        destruct (@term_get_list_spec Σ ty_pmpentry es) as [[] ?|];
          lsolve.
        rewrite (H0 ι) in H.
        destruct (term_get_pair_spec t) as [[cfg0 addr0]|].
        rewrite (H1 ι) in H.
        simpl.
        destruct (term_get_record_spec cfg0).
        cbn in a0.
        env.destroy a0.
        rewrite (H2 ι) in H.
        simpl.
        destruct (simplify_pmpcheck n a width addr0 t0 p acc) eqn:?;
          cbn.
        cbn in H.
        destruct (pmp_match_entry _ _ _ _ _ _) eqn:Hm;
          try discriminate.
        apply pmp_match_entry_PMP_Success in Hm as (HA%addr_match_type_TOR_neq_OFF & Hm).
        simpl in HA.
        apply Pmp_check_perms_Access_pmp_perm in H.
        destruct Hm as (? & ? & ? & ? & ?).
        right; repeat split; auto.
        apply pmp_match_entry_PMP_Continue in Hm.
        unfold pmp_check_fml_term_aux in IHn.
        specialize (IHn a width addr0 t0 p acc ι).
        rewrite Heqo in IHn.
        assert (instprop f ι).
        { apply IHn.
          cbn.
          unfold Gen_Pmp_access, pmp_check_aux.
          now rewrite Nat2Z.id. }
        simpl in Hm.
        left; auto.
        * rewrite (H0 ι) (H1 ι) (H2 ι).
          cbn.
          unfold Gen_Pmp_access.
          now rewrite Nat2Z.id.
        * cbn.
          rewrite (H0 ι) (H1 ι); cbn.
          unfold Gen_Pmp_access.
          now rewrite Nat2Z.id.
        * cbn.
          rewrite (H0 ι); cbn.
          unfold Gen_Pmp_access.
          now rewrite Nat2Z.id.
        * cbn.
          rewrite (H0 ι) in H; cbn in H; discriminate.
        * cbn.
          unfold Gen_Pmp_access.
          now rewrite Nat2Z.id.
  Qed.

  Lemma Z_pmp_check_fml_term_aux_gen_pmp_access : forall {Σ} (n : Z) a width lo es p acc (ι : Valuation Σ),
  instprop (pmp_check_fml_term_aux (Z.to_nat n) a width lo es p acc) ι
  ↔ instprop (formula_user gen_pmp_access [term_val ty.int n; a; width; lo; es; p; acc]) ι.
  Proof.
    intros; cbn; destruct n.
    - rewrite Z2Nat.inj_0.
      apply pmp_check_fml_term_aux_gen_pmp_access.
    - split; intros H.
      apply pmp_check_fml_term_aux_gen_pmp_access in H.
      cbn in H.
      now rewrite positive_nat_Z in H.
      apply pmp_check_fml_term_aux_gen_pmp_access.
      now rewrite positive_nat_Z.
    - split; intros H.
      apply pmp_check_fml_term_aux_gen_pmp_access in H.
      cbn in H.
      unfold Gen_Pmp_access in *.
      rewrite Z2Nat.inj_neg in H.
      rewrite Z2Nat.inj_neg.
      apply H.
      apply pmp_check_fml_term_aux_gen_pmp_access.
      cbn.
      unfold Gen_Pmp_access in *.
      rewrite Z2Nat.inj_neg in H.
      rewrite Z2Nat.inj_neg.
      apply H.
  Qed.

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

  Definition simplify_gen_pmp_access {Σ} (n : Term Σ ty.int) (paddr width lo : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (PathCondition Σ) :=
    let pmp_access_fml := formula_user gen_pmp_access [n; paddr; width; lo; es; p; acc] in
    match term_get_val n , term_get_val paddr , term_get_val width , term_get_val lo , term_get_val es , term_get_val p , term_get_val acc with
    | Some n , Some paddr , Some width , Some lo , Some entries , Some p , Some acc =>
        if pmp_check_aux (Z.to_nat n) paddr width lo entries p acc
        then Some []
        else None
    | Some n, _, _, _ , _ , _, _ =>
        Some [pmp_check_fml_term_aux (Z.to_nat n) paddr width lo es p acc]
    | _, _, _, _ , _ , _, _ => Some [pmp_access_fml]
    end.

  Definition simplify_pmp_access {Σ} (paddr width : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (PathCondition Σ) :=
    simplify_gen_pmp_access (term_val ty.int NumPmpEntries) paddr width
      (term_val ty_xlenbits bv.zero) es p acc.

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
  | gen_pmp_access               | [ n; paddr; width; lo; entries; priv; perm ] => simplify_gen_pmp_access n paddr width lo entries priv perm
  | pmp_access               | [ paddr; width; entries; priv; perm ] => simplify_pmp_access paddr width entries priv perm
  | pmp_check_perms          | [ cfg; acc; priv ]             => simplify_pmp_check_perms cfg acc priv
  | pmp_check_rwx            | [ cfg; acc ]                   => simplify_pmp_check_rwx cfg acc
  | sub_perm                 | [ a1; a2 ]                     => simplify_sub_perm a1 a2
  | access_pmp_perm          | [ a; p ]                       => simplify_access_pmp_perm a p
  | within_cfg               | [ paddr; cfg; prevaddr; addr]  => simplify_within_cfg paddr cfg prevaddr addr
  | not_within_cfg           | [ paddr; entries ]             => Some [formula_user not_within_cfg [paddr; entries]]%ctx
  | prev_addr                | [ cfg; entries; prev ]         => simplify_prev_addr cfg entries prev
  | in_entries               | [ cfg; entries; prev ]         => Some [formula_user in_entries [cfg; entries; prev]]%ctx.

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

  Local Ltac process_inst ι :=
    repeat match goal with
      | a: NamedEnv ?t (recordf_ty ?r) |- _ =>
          simpl in a; env.destroy a
      | H: ∀ ι : Valuation ?Σ, ?P |- _ =>
          specialize (H ι)
      end.

  Lemma simplify_gen_pmp_access_spec {Σ} (n : Term Σ ty.int) (paddr width lo : Term Σ ty_xlenbits)
    (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege)
    (acc : Term Σ ty_access_type) :
    simplify_gen_pmp_access n paddr width lo es p acc ⊣⊢ Some [formula_user gen_pmp_access [n; paddr; width; lo; es; p; acc]].
  Proof.
    unfold simplify_gen_pmp_access.
    lsolve; intros ι;
      try apply Z_pmp_check_fml_term_aux_gen_pmp_access.
    cbn; unfold Gen_Pmp_access.
    destruct (pmp_check_aux _ _ _ _ _ _ _) eqn:?; lsolve.
  Qed.

  Lemma simplify_pmp_access_spec {Σ} (paddr width : Term Σ ty_xlenbits)
    (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege)
    (acc : Term Σ ty_access_type) :
    simplify_pmp_access paddr width es p acc ⊣⊢ Some [formula_user pmp_access [paddr; width; es; p; acc]].
  Proof. apply simplify_gen_pmp_access_spec. Qed.

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
    destruct p; cbv in ts; env.destroy ts; cbn - [simplify_pmp_access].
    - simple apply simplify_gen_pmp_access_spec.
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
