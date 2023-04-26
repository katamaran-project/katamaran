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
      | gen_pmp_access  => [ty_xlenbits; ty_xlenbits; ty_xlenbits; ty.list ty_pmpentry; ty_privilege; ty_access_type]
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

    Definition Gen_Pmp_access (a width lo : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) (acc : Val ty_access_type) : Prop :=
      pmp_check_aux a width lo entries m acc = true.

    Definition Pmp_access (a : Val ty_xlenbits) (width : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) (acc : Val ty_access_type) : Prop :=
      Gen_Pmp_access a width bv.zero entries m acc.

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
    | NA4 | NA4 := true;
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
      | NA4 => (addr <=ᵘ? paddr) && (paddr <ᵘ? addr + (bv.of_nat 4))%bv
      end.

    Definition Within_cfg (paddr : Val ty_xlenbits) (cfg : Val ty_pmpcfg_ent) (prev_addr addr : Val ty_xlenbits) : Prop :=
      decide_within_cfg paddr cfg prev_addr addr = true.

    (* TODO: update for NA4? *)
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

  Definition is_TOR {Σ} (A : Term Σ ty_pmpaddrmatchtype) : Formula Σ :=
    formula_relop bop.eq A (term_val ty_pmpaddrmatchtype TOR).

  Definition is_NA4 {Σ} (A : Term Σ ty_pmpaddrmatchtype) : Formula Σ :=
    formula_relop bop.eq A (term_val ty_pmpaddrmatchtype NA4).

  Definition is_machine_mode {Σ} (p : Term Σ ty_privilege) : Formula Σ :=
    formula_relop bop.eq (term_val ty_privilege Machine) p.

  Definition fml_pmp_match_conditions {Σ} (a width lo hi : Term Σ ty_xlenbits) : Formula Σ :=
    formula_relop bop.bvule lo hi
    ∧ formula_relop bop.bvult lo (term_binop bop.bvadd a width)
    ∧ formula_relop bop.bvule lo a
    ∧ formula_relop bop.bvult a hi
    ∧ formula_relop bop.bvule (term_binop bop.bvadd a width) hi.

  Definition fml_pmp_match {Σ} (a width prev_pmpaddr pmpaddr : Term Σ ty_xlenbits) (cfg : NamedEnv (Term Σ) (recordf_ty rpmpcfg_ent)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : Formula Σ :=
    ((is_TOR cfg.[??"A"] ∧ fml_pmp_match_conditions a width prev_pmpaddr pmpaddr)
    ∨ (is_NA4 cfg.[??"A"] ∧ fml_pmp_match_conditions a width pmpaddr (term_binop bop.bvadd pmpaddr (term_val ty_xlenbits (bv.of_nat 4)))))
    ∧ formula_user pmp_check_perms [term_record rpmpcfg_ent [cfg.[??"L"];cfg.[??"A"];cfg.[??"X"];cfg.[??"W"];cfg.[??"R"]]; acc; p].

  Definition fml_pmp_nomatch_conditions {Σ} (a width lo hi : Term Σ ty_xlenbits) : Formula Σ :=
    formula_relop bop.bvult hi lo
     ∨ (formula_relop bop.bvule lo hi ∧ formula_relop bop.bvule (term_binop bop.bvadd a width) lo)
     ∨ (formula_relop bop.bvule lo hi ∧ formula_relop bop.bvult lo (term_binop bop.bvadd a width) ∧ formula_relop bop.bvule hi a).

  Definition fml_pmp_nomatch {Σ} (a width prev_pmpaddr pmpaddr : Term Σ ty_xlenbits) (cfg : NamedEnv (Term Σ) (recordf_ty rpmpcfg_ent)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) (cont : Formula Σ) : Formula Σ :=
    (is_off cfg.[??"A"]
     ∨ (is_TOR cfg.[??"A"] ∧ fml_pmp_nomatch_conditions a width prev_pmpaddr pmpaddr)
     ∨ (is_NA4 cfg.[??"A"] ∧ fml_pmp_nomatch_conditions a width pmpaddr (term_binop bop.bvadd pmpaddr (term_val ty_xlenbits (bv.of_nat 4)))))
    ∧ cont.

  Definition cfg_to_env {Σ} (cfg : Pmpcfg_ent) : NamedEnv (Term Σ) (recordf_ty rpmpcfg_ent) :=
    [nenv term_val ty.bool (L cfg); term_val ty_pmpaddrmatchtype (A cfg); term_val ty.bool (X cfg); term_val ty.bool (W cfg); term_val ty.bool (R cfg)].

  Fixpoint simplify_pmpcheck_pure_list {Σ} (a width lo : Term Σ ty_xlenbits) (es : list PmpEntryCfg) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : Formula Σ :=
    match es with
    | (cfg , addr) :: es =>
        let cfg  := cfg_to_env cfg in
        let addr := term_val ty_xlenbits addr in
        let fml := simplify_pmpcheck_pure_list a width addr es p acc in
        fml_pmp_nomatch a width lo addr cfg p acc fml
        ∨ fml_pmp_match a width lo addr cfg p acc
    | []                 =>
        is_machine_mode p
    end%list.

  Fixpoint simplify_pmpcheck {Σ t} (a width lo : Term Σ ty_xlenbits) (es : @ListView Σ ty_pmpentry t) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (Formula Σ) :=
    match es with
    | term_list_var _ => None
    | term_list_val l => Some (simplify_pmpcheck_pure_list a width lo l p acc)
    | term_list_cons pmp es =>
        '(cfg , addr) <- term_get_pair pmp ;;
        cfg <- term_get_record cfg ;;
        fml <- simplify_pmpcheck a width addr es p acc ;;
        Some (fml_pmp_nomatch a width lo addr cfg p acc fml
              ∨ fml_pmp_match a width lo addr cfg p acc)
    | term_list_append es1 es2 =>
        None (* TODO: we can do better here *)
    end%list.

  Definition simplify_pmpcheck_term_list {Σ} (a width lo : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (Formula Σ) :=
    simplify_pmpcheck a width lo (view es) p acc.

  (* TODO: remove? *)
  (* Fixpoint simplify_pmpcheck {Σ} (n : nat) (a width lo : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (Formula Σ) := *)
  (*   match n, term_get_list es with *)
  (*   | S n, Some (inl (pmp , es)) => *)
  (*       '(cfg , addr) <- term_get_pair pmp ;; *)
  (*       cfg <- term_get_record cfg ;; *)
  (*       fml <- simplify_pmpcheck n a width addr es p acc ;; *)
  (*       Some (((* PMP_NoMatch *) *)
  (*             (is_off cfg.[??"A"] *)
  (*              ∨ (is_on cfg.[??"A"] ∧ *)
  (*                   (formula_relop bop.bvult addr lo *)
  (*                    ∨ (formula_relop bop.bvule lo addr ∧ formula_relop bop.bvule (term_binop bop.bvadd a width) lo) *)
  (*                    ∨ (formula_relop bop.bvule lo addr ∧ formula_relop bop.bvult lo (term_binop bop.bvadd a width) ∧ formula_relop bop.bvule addr a)))) *)
  (*             ∧ fml) *)
  (*             ∨ *)
  (*               ((* PMP_Match *) *)
  (*                 is_on cfg.[??"A"] *)
  (*                 ∧ formula_relop bop.bvule lo addr *)
  (*                 ∧ formula_relop bop.bvult lo (term_binop bop.bvadd a width) *)
  (*                 ∧ formula_relop bop.bvult a addr *)
  (*                 ∧ formula_relop bop.bvule lo a *)
  (*                 ∧ formula_relop bop.bvule (term_binop bop.bvadd a width) addr *)
  (*                 ∧ formula_user pmp_check_perms [term_record rpmpcfg_ent [cfg.[??"L"];cfg.[??"A"];cfg.[??"X"];cfg.[??"W"];cfg.[??"R"]]; acc; p])) *)
  (*   | O, Some (inr tt) => Some (is_machine_mode p) *)
  (*   | _, _             => None *)
  (*   end%list. *)

  Definition pmp_check_fml_term_aux {Σ} (a width lo : Term Σ ty_xlenbits) (entries : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : Formula Σ :=
    let fml     := simplify_pmpcheck_term_list a width lo entries p acc in
    match fml with
    | Some fml => fml
    | None     =>
        formula_user gen_pmp_access [a; width; lo; entries; p; acc]
    end.

  Definition pmp_check_fml_aux {Σ} (a width lo : Val ty_xlenbits) (entries : list (Val ty_pmpentry)) (p : Val ty_privilege) (acc : Val ty_access_type) : Formula Σ :=
    let a       := term_val ty_xlenbits a in
    let width   := term_val ty_xlenbits width in
    let lo      := term_val ty_xlenbits lo in
    let entries := term_val (ty.list ty_pmpentry) entries in
    let p       := term_val ty_privilege p in
    let acc     := term_val ty_access_type acc in
    pmp_check_fml_term_aux a width lo entries p acc.

  Definition pmp_check_fml_prop_aux (a width lo : Val ty_xlenbits) (entries : list (Val ty_pmpentry)) (p : Val ty_privilege) (acc : Val ty_access_type) : Prop :=
    instprop (pmp_check_fml_aux a width lo entries p acc) [env].

  Lemma cfg_record : ∀ cfg,
      {| L := L cfg; A := A cfg; X := X cfg; W := W cfg; R := R cfg |} = cfg.
  Proof. now intros []. Qed.

  Lemma pmp_check_inversion_fml_aux (a width prev_pmpaddr : Val ty_xlenbits) (entries : list (Val ty_pmpentry)) (p : Val ty_privilege) (acc : Val ty_access_type) :
    pmp_check_aux a width prev_pmpaddr entries p acc = true ->
    pmp_check_fml_prop_aux a width prev_pmpaddr entries p acc.
  Proof.
    unfold pmp_check_aux, pmp_check_fml_prop_aux, pmp_check_fml_aux, pmp_check_fml_term_aux.
    generalize dependent prev_pmpaddr.
    induction entries as [|[cfg0 pmpaddr] entries IHentries].
    - cbn; intros; destruct p; auto; discriminate.
    - intros.
      destruct (@simplify_pmpcheck_term_list [ctx] (term_val ty_xlenbits a) (term_val ty_xlenbits width)
                  (term_val ty_xlenbits pmpaddr) (term_val (ty.list ty_pmpentry) entries)
                  (term_val ty_privilege p) (term_val ty_access_type acc)) eqn:Epmp;
        cbn;
        specialize (IHentries pmpaddr);
        rewrite Epmp in IHentries;
        cbn in H;
        last done.
      destruct (pmp_match_entry a width p cfg0 prev_pmpaddr pmpaddr) eqn:Hm;
        try discriminate.
      + destruct (A cfg0) eqn:HA.
        * left; split.
          now left.
          unfold pmp_match_entry in Hm.
          rewrite (pmp_addr_range_None_2 _ _ _ HA) in Hm.
          now simpl in Hm.
        * rewrite <- HA.
          apply (pmp_addr_range_Some_TOR cfg0 pmpaddr prev_pmpaddr) in HA.
          apply (pmp_match_entry_PMP_Success _ _ _ _ _ _ _ _ HA) in Hm.
          apply Pmp_check_perms_Access_pmp_perm in H.
          rewrite cfg_record.
          right; split; auto; left; repeat split; intuition.
        * rewrite <- HA.
          apply (pmp_addr_range_Some_NA4 cfg0 pmpaddr prev_pmpaddr) in HA.
          apply (pmp_match_entry_PMP_Success _ _ _ _ _ _ _ _ HA) in Hm.
          apply Pmp_check_perms_Access_pmp_perm in H.
          rewrite cfg_record.
          right; split; auto; right; repeat split; intuition.
      + cbn in Epmp.
        inversion Epmp.
        subst.
        destruct (A cfg0) eqn:HA.
        * left; split.
          now left.
          now apply IHentries.
        * rewrite <- HA.
          left; split; last by apply IHentries.
          rename HA into Hrng.
          remember Hrng as HA.
          clear HeqHA.
          apply (pmp_addr_range_Some_TOR cfg0 pmpaddr prev_pmpaddr) in Hrng.
          apply (pmp_match_entry_PMP_Continue _ _ _ _ _ _ _ Hrng) in Hm as [?|Hm]; auto.
          destruct Hm as [[?|Hcon]%addr_match_type_neq_off_cases (lo' & hi' & [Heq Hm])].
          inversion Heq; subst; auto.
          rewrite HA in Hcon; discriminate.
        * rewrite <- HA.
          left; split; last by apply IHentries.
          rename HA into Hrng.
          remember Hrng as HA.
          clear HeqHA.
          apply (pmp_addr_range_Some_NA4 cfg0 pmpaddr prev_pmpaddr) in Hrng.
          apply (pmp_match_entry_PMP_Continue _ _ _ _ _ _ _ Hrng) in Hm as [?|Hm]; auto.
          destruct Hm as [[Hcon|?]%addr_match_type_neq_off_cases (lo' & hi' & [Heq Hm])].
          rewrite HA in Hcon; discriminate.
          inversion Heq; subst; auto.
  Qed.

  Lemma pmp_check_fml_term_aux_gen_pmp_access : forall {Σ} a width lo es p acc (ι : Valuation Σ),
  instprop (pmp_check_fml_term_aux a width lo es p acc) ι
  ↔ instprop (formula_user gen_pmp_access [a; width; lo; es; p; acc]) ι.
  Proof.
    intros ? ? ? ? es.
    revert lo.
    induction (view es);
      auto.
    - induction v as [|[cfg0 addr0] es IHentries].
      + cbn; unfold Gen_Pmp_access; simpl.
        intros.
        destruct (inst p ι) eqn:?; split; auto; try discriminate.
      + intros.
        cbn; unfold Gen_Pmp_access; simpl.
        cbn in IHentries.
        specialize (IHentries (term_val ty_xlenbits addr0) p acc ι).
        unfold Gen_Pmp_access in IHentries.
        split; intros H.
        * destruct H as [([] & ?)|].
          unfold pmp_match_entry, pmp_addr_range.
          rewrite H.
          cbn.
          now apply IHentries.
          destruct H as [(HA & ?)|(HA & ?)].
          remember (inst lo ι) as Vlo.
          remember HA as Hrng.
          clear HeqHrng.
          apply (pmp_addr_range_Some_TOR cfg0 addr0 Vlo) in Hrng.
          subst Vlo.
          apply addr_match_type_TOR_neq_OFF in HA.
          rewrite (pmp_match_entry_cfg_ON_PMP_Continue _ _ _ _ _ _ _ _ Hrng (conj HA H)).
          now apply IHentries.
          remember (inst lo ι) as Vlo.
          remember HA as Hrng.
          clear HeqHrng.
          apply (pmp_addr_range_Some_NA4 cfg0 addr0 Vlo) in Hrng.
          subst Vlo.
          apply addr_match_type_NA4_neq_OFF in HA.
          rewrite (pmp_match_entry_cfg_ON_PMP_Continue _ _ _ _ _ _ _ _ Hrng (conj HA H)).
          now apply IHentries.
          rewrite cfg_record in H.
          rewrite Pmp_check_perms_Access_pmp_perm in H.
          destruct H as [[(HA & H)|(HA & H)] Hperm].
          remember HA as Hrng.
          clear HeqHrng.
          remember (inst lo ι) as Vlo.
          apply (pmp_addr_range_Some_TOR cfg0 addr0 Vlo) in Hrng.
          subst Vlo.
          apply addr_match_type_TOR_neq_OFF in HA.
          now rewrite (proj2 (pmp_match_entry_PMP_Success _ _ _ _ _ _ _ _ Hrng) (conj HA H)).
          remember HA as Hrng.
          clear HeqHrng.
          remember (inst lo ι) as Vlo.
          apply (pmp_addr_range_Some_NA4 cfg0 addr0 Vlo) in Hrng.
          subst Vlo.
          apply addr_match_type_NA4_neq_OFF in HA.
          now rewrite (proj2 (pmp_match_entry_PMP_Success _ _ _ _ _ _ _ _ Hrng) (conj HA H)).
        * destruct (A cfg0) eqn:HA.
          unfold pmp_match_entry in H.
          rewrite (proj2 (pmp_addr_range_None _ _ _) HA) in H.
          simpl in H.
          left; split; auto.
          now apply IHentries.
          rewrite <- HA.
          rewrite cfg_record Pmp_check_perms_Access_pmp_perm;
            unfold Access_pmp_perm.
          remember HA as Hrng.
          clear HeqHrng.
          remember (inst lo ι) as Vlo.
          apply (pmp_addr_range_Some_TOR cfg0 addr0 Vlo) in Hrng.
          subst Vlo.
          destruct (pmp_match_entry _ _ _ _ _ _) eqn:Hpmp;
            try discriminate.
          right; split; auto.
          apply (pmp_match_entry_PMP_Success _ _ _ _ _ _ _ _ Hrng) in Hpmp.
          left; auto; intuition.
          apply (pmp_match_entry_PMP_Continue _ _ _ _ _ _ _ Hrng) in Hpmp as [Hcon|[? (lo' & hi' & [Heq Hpmp])]];
            first (rewrite HA in Hcon; discriminate).
          left; split; last by apply IHentries.
          inversion Heq; subst; right; left; auto.
          rewrite <- HA.
          rewrite cfg_record Pmp_check_perms_Access_pmp_perm;
            unfold Access_pmp_perm.
          remember HA as Hrng.
          clear HeqHrng.
          remember (inst lo ι) as Vlo.
          apply (pmp_addr_range_Some_NA4 cfg0 addr0 Vlo) in Hrng.
          subst Vlo.
          destruct (pmp_match_entry _ _ _ _ _ _) eqn:Hpmp;
            try discriminate.
          right; split; auto.
          apply (pmp_match_entry_PMP_Success _ _ _ _ _ _ _ _ Hrng) in Hpmp.
          right; auto; intuition.
          apply (pmp_match_entry_PMP_Continue _ _ _ _ _ _ _ Hrng) in Hpmp as [Hcon|[? (lo' & hi' & [Heq Hpmp])]];
            first (rewrite HA in Hcon; discriminate).
          left; split; last by apply IHentries.
          inversion Heq; subst; right; right; auto.
    - unfold pmp_check_fml_term_aux.
      cbn.
      destruct (term_get_pair_spec h) as [[cfg0 addr0]|]; auto.
      simpl.
      destruct (term_get_record_spec cfg0); auto.
      cbn in a0; env.destroy a0.
      simpl.
      intros.
      destruct (@simplify_pmpcheck Σ t a width addr0 (view t) p acc) eqn:Hs; auto.
      unfold Gen_Pmp_access, pmp_check_aux.
      cbn.
      rewrite (H ι).
      cbn in H0.
      specialize (H0 ι).
      rewrite H0.
      cbn in IHv.
      unfold Gen_Pmp_access, pmp_check_aux in IHv.
      split; intros Hc.
      + destruct Hc as [[[|]]|].
        unfold pmp_match_entry, pmp_addr_range.
        rewrite H1; simpl.
        apply IHv.
        unfold pmp_check_fml_term_aux.
        unfold simplify_pmpcheck_term_list.
        now rewrite Hs.
        destruct H1 as [(HA & [|[[]|[? []]]])|(HA & [|[[]|[? []]]])];
          unfold pmp_match_entry, pmp_addr_range;
          rewrite HA; simpl;
          bv_comp_bool; simpl;
          apply IHv;
          unfold pmp_check_fml_term_aux, simplify_pmpcheck_term_list;
          now rewrite Hs.
        destruct H1 as ([(-> & ?)|(-> & ?)] & Hperm);
          unfold pmp_match_entry, pmp_addr_range;
          simpl; bv_comp_bool; simpl;
          now apply Pmp_check_perms_Access_pmp_perm.
      + remember (inst cfg0 ι) as Vcfg0.
        remember (inst addr0 ι) as Vaddr0.
        remember (inst lo ι) as Vlo.
        destruct (pmp_addr_range Vcfg0 Vaddr0 Vlo) eqn:Hrng;
          subst.
        destruct p0 as [lo' hi'].

        rewrite <- H0 in Hc.
        destruct (pmp_match_entry _ _ _ _ _ _) eqn:Hpmp;
          try discriminate.
        apply (pmp_match_entry_PMP_Success _ _ _ _ _ _ _ _ Hrng) in Hpmp.
        rewrite Pmp_check_perms_Access_pmp_perm; unfold Access_pmp_perm.
        rewrite H0 in Hc.
        right; split; auto.
        destruct Hpmp as [[HA|HA]%addr_match_type_neq_off_cases Hpmp].
        rewrite (pmp_addr_range_Some_TOR _ _ _ HA) in Hrng.
        inversion Hrng; subst.
        rewrite H0 in HA; simpl in HA.
        left; auto.
        rewrite (pmp_addr_range_Some_NA4 _ _ _ HA) in Hrng.
        inversion Hrng; subst.
        rewrite H0 in HA; simpl in HA.
        right; auto.
        apply (pmp_match_entry_PMP_Continue _ _ _ _ _ _ _ Hrng) in Hpmp.
        left.
        split.
        destruct Hpmp as [HA|([HA|HA]%addr_match_type_neq_off_cases & (lo'' & hi'' & (Heq & Hpmp)))].
        left; rewrite H0 in HA; simpl in HA; auto.
        rewrite (pmp_addr_range_Some_TOR _ _ _ HA) in Hrng.
        inversion Hrng; subst.
        inversion Heq; subst.
        rewrite H0 in HA; simpl in HA.
        right; left; auto.
        rewrite (pmp_addr_range_Some_NA4 _ _ _ HA) in Hrng.
        inversion Hrng; subst.
        inversion Heq; subst.
        rewrite H0 in HA; simpl in HA.
        right; right; auto.
        unfold pmp_check_fml_term_aux, simplify_pmpcheck_term_list in IHv.
        specialize (IHv addr0 p acc ι).
        rewrite Hs in IHv.
        destruct IHv as (? & IH).
        unfold pmp_match_entry in Hc.
        now apply IH in Hc.
        left; split.
        apply pmp_addr_range_None in Hrng; left.
        now rewrite H0 in Hrng; simpl in Hrng.
        unfold pmp_check_fml_term_aux, simplify_pmpcheck_term_list in IHv.
        specialize (IHv addr0 p acc ι).
        rewrite Hs in IHv.
        destruct IHv as (? & IH).
        unfold pmp_match_entry in Hc.
        rewrite <- H0 in Hc.
        rewrite Hrng in Hc.
        now apply IH in Hc.
  Qed.

  Lemma pmp_check_fml_pure_aux_gen_pmp_access : forall {Σ} a width lo es p acc (ι : Valuation Σ),
  instprop (simplify_pmpcheck_pure_list a width lo es p acc) ι
    ↔ instprop (formula_user gen_pmp_access [a; width; lo; term_val (ty.list ty_pmpentry) es; p; acc]) ι.
  Proof.
    intros ? ? ? lo es.
    revert lo.
    induction es as [|[cfg0 addr0] es IHentries];
      cbn; unfold Gen_Pmp_access.
    - intros; cbn.
      split; intros H.
      + now rewrite <- H.
      + destruct (inst p ι); auto; try discriminate.
    - intros; cbn.
      split; intros H.
      destruct H as [([HA|[(HA & ?)|(HA & ?)]] & ?)|?].
      + unfold pmp_match_entry, pmp_addr_range; rewrite HA.
        simpl.
        cbn in IHentries; unfold Gen_Pmp_access, pmp_check_aux in IHentries.
        specialize (IHentries (term_val ty_xlenbits addr0) p acc ι).
        now apply IHentries.
      + remember HA as Hrng.
        clear HeqHrng.
        remember (inst lo ι) as Vlo.
        apply (pmp_addr_range_Some_TOR cfg0 addr0 Vlo) in Hrng.
        subst.
        apply addr_match_type_TOR_neq_OFF in HA.
        rewrite (pmp_match_entry_cfg_ON_PMP_Continue _ _ _ _ _ _ _ _ Hrng (conj HA H)).
        cbn in IHentries; unfold Gen_Pmp_access, pmp_check_aux in IHentries.
        specialize (IHentries (term_val ty_xlenbits addr0) p acc ι).
        now apply IHentries.
      + remember HA as Hrng.
        clear HeqHrng.
        remember (inst lo ι) as Vlo.
        apply (pmp_addr_range_Some_NA4 cfg0 addr0 Vlo) in Hrng.
        subst.
        apply addr_match_type_NA4_neq_OFF in HA.
        rewrite (pmp_match_entry_cfg_ON_PMP_Continue _ _ _ _ _ _ _ _ Hrng (conj HA H)).
        cbn in IHentries; unfold Gen_Pmp_access, pmp_check_aux in IHentries.
        specialize (IHentries (term_val ty_xlenbits addr0) p acc ι).
        now apply IHentries.
      + destruct H as ([(HA & ?)|(HA & ?)] & Hperms);
          apply Pmp_check_perms_Access_pmp_perm in Hperms;
          rewrite cfg_record in Hperms.
        remember HA as Hrng.
        clear HeqHrng.
        remember (inst lo ι) as Vlo.
        apply (pmp_addr_range_Some_TOR cfg0 addr0 Vlo) in Hrng.
        subst.
        apply addr_match_type_TOR_neq_OFF in HA.
        now rewrite (proj2 (pmp_match_entry_PMP_Success _ _ _ _ _ _ _ _ Hrng) (conj HA H)).
        remember HA as Hrng.
        clear HeqHrng.
        remember (inst lo ι) as Vlo.
        apply (pmp_addr_range_Some_NA4 cfg0 addr0 Vlo) in Hrng.
        subst.
        apply addr_match_type_NA4_neq_OFF in HA.
        now rewrite (proj2 (pmp_match_entry_PMP_Success _ _ _ _ _ _ _ _ Hrng) (conj HA H)).
      + destruct (A cfg0) eqn:HA.
        * unfold pmp_match_entry in H.
          rewrite (pmp_addr_range_None_2 _ _ _ HA) in H.
          simpl in H.
          cbn in IHentries; unfold Gen_Pmp_access, pmp_check_aux in IHentries.
          specialize (IHentries (term_val ty_xlenbits addr0) p acc ι).
          left; split.
          left; auto.
          now apply IHentries.
        * remember (inst lo ι) as Vlo.
          rewrite <- HA.
          apply (pmp_addr_range_Some_TOR cfg0 addr0 Vlo) in HA.
          subst.
          rewrite cfg_record.
          rewrite Pmp_check_perms_Access_pmp_perm.
          destruct (pmp_match_entry _ _ _ _ _ _) eqn:Hpmp;
            try discriminate.
          apply (pmp_match_entry_PMP_Success _ _ _ _ _ _ _ _ HA) in Hpmp.
          right; split; auto.
          left; intuition.
          apply (pmp_match_entry_PMP_Continue _ _ _ _ _ _ _ HA) in Hpmp as [Ha|Ha].
          left; split.
          left; auto.
          now apply IHentries.
          destruct Ha as (? & lo' & hi' & Heq & Ha).
          inversion Heq; subst.
          left; split.
          right; left; auto.
          now apply IHentries.
        * remember (inst lo ι) as Vlo.
          rewrite <- HA.
          apply (pmp_addr_range_Some_NA4 cfg0 addr0 Vlo) in HA.
          subst.
          rewrite cfg_record.
          rewrite Pmp_check_perms_Access_pmp_perm.
          destruct (pmp_match_entry _ _ _ _ _ _) eqn:Hpmp;
            try discriminate.
          apply (pmp_match_entry_PMP_Success _ _ _ _ _ _ _ _ HA) in Hpmp.
          right; split; auto.
          right; intuition.
          apply (pmp_match_entry_PMP_Continue _ _ _ _ _ _ _ HA) in Hpmp as [Ha|Ha].
          left; split.
          left; auto.
          now apply IHentries.
          destruct Ha as (? & lo' & hi' & Heq & Ha).
          inversion Heq; subst.
          left; split.
          right; right; auto.
          now apply IHentries.
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

  Definition simplify_gen_pmp_access {Σ} (paddr width lo : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (PathCondition Σ) :=
    let pmp_access_fml := formula_user gen_pmp_access [paddr; width; lo; es; p; acc] in
    match term_get_val paddr , term_get_val width , term_get_val lo , term_get_val es , term_get_val p , term_get_val acc with
    | Some paddr , Some width , Some lo , Some entries , Some p , Some acc =>
        if pmp_check_aux paddr width lo entries p acc
        then Some []
        else None
    | _, _, _, _, _, _ =>
        Some [pmp_check_fml_term_aux paddr width lo es p acc]
    end.

  Definition simplify_pmp_access {Σ} (paddr width : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (PathCondition Σ) :=
    simplify_gen_pmp_access paddr width (term_val ty_xlenbits bv.zero) es p acc.

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
  | gen_pmp_access               | [ paddr; width; lo; entries; priv; perm ] => simplify_gen_pmp_access paddr width lo entries priv perm
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

  Lemma simplify_gen_pmp_access_spec {Σ} (paddr width lo : Term Σ ty_xlenbits)
    (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege)
    (acc : Term Σ ty_access_type) :
    simplify_gen_pmp_access paddr width lo es p acc ⊣⊢ Some [formula_user gen_pmp_access [paddr; width; lo; es; p; acc]].
  Proof.
    unfold simplify_gen_pmp_access.
    lsolve; intros ι;
      try apply pmp_check_fml_term_aux_gen_pmp_access;
      cbn.
    - unfold Gen_Pmp_access; destruct (pmp_check_aux _ _ _ _ _ _) eqn:?; lsolve.
    - apply pmp_check_fml_pure_aux_gen_pmp_access.
    - apply pmp_check_fml_pure_aux_gen_pmp_access.
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
