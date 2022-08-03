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

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Inductive PurePredicate : Set :=
| pmp_access
| pmp_check_perms
| pmp_check_rwx
| sub_perm
| within_cfg
| not_within_cfg
| prev_addr
| in_entries
.

Inductive Predicate : Set :=
| pmp_entries
| pmp_addr_access
| pmp_addr_access_without
| gprs
| ptsto
| encodes_instr
| ptstomem
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
      | pmp_access      => [ty_xlenbits; ty.list ty_pmpentry; ty_privilege; ty_access_type]
      | pmp_check_perms => [ty_pmpcfg_ent; ty_access_type; ty_privilege]
      | pmp_check_rwx   => [ty_pmpcfg_ent; ty_access_type]
      | sub_perm        => [ty_access_type; ty_access_type]
      | within_cfg      => [ty_xlenbits; ty_pmpcfg_ent; ty_xlenbits; ty_xlenbits]
      | not_within_cfg  => [ty_xlenbits; ty.list ty_pmpentry]
      | prev_addr       => [ty_pmpcfgidx; ty.list ty_pmpentry; ty_xlenbits]
      | in_entries      => [ty_pmpcfgidx; ty_pmpentry; ty.list ty_pmpentry]
      end.

    Definition PmpEntryCfg : Set := Pmpcfg_ent * Xlenbits.
    Definition PmpAddrRange := option (Xlenbits * Xlenbits).

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

    Definition pmp_get_RWX (cfg : Val ty_pmpcfg_ent) : Val ty_access_type :=
      match cfg with
      | {| L := _; A := _; X := X; W := W; R := R |} =>
          match X, W, R with
          | false, false, true => Read
          | false, true, false => Write
          | true, false, false => Execute
          | _, _, _ => ReadWrite
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

    Definition pmp_get_perms (cfg : Val ty_pmpcfg_ent) (p : Val ty_privilege) : option (Val ty_access_type) :=
      match p with
      | Machine =>
          if L cfg
          then Some (pmp_get_RWX cfg)
          else None
      | User =>
          Some (pmp_get_RWX cfg)
      end.

    Definition pmp_addr_range (cfg : Pmpcfg_ent) (hi lo : Xlenbits) : PmpAddrRange :=
      match A cfg with
      | OFF => None
      | TOR => Some (lo , hi)
      end.

    Definition pmp_match_addr (a : Val ty_xlenbits) (rng : PmpAddrRange) : Val ty_pmpaddrmatch :=
      match rng with
      | Some (lo, hi) =>
          if hi <? lo
          then PMP_NoMatch
          else if ((a <? lo) || (hi <=? a))%bool
               then PMP_NoMatch
               else if ((lo <=? a) && (a <? hi))%bool
                    then PMP_Match
                    else PMP_PartialMatch
      | None          => PMP_NoMatch
      end.

    Definition pmp_match_entry (a : Val ty_xlenbits) (m : Val ty_privilege) (cfg : Val ty_pmpcfg_ent) (lo hi : Val ty_xlenbits) : Val ty_pmpmatch :=
      let rng := pmp_addr_range cfg hi lo in
      match pmp_match_addr a rng with
      | PMP_NoMatch      => PMP_Continue
      | PMP_PartialMatch => PMP_Fail
      | PMP_Match        => PMP_Success
      end.

    Fixpoint pmp_check (a : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (prev : Val ty_xlenbits) (m : Val ty_privilege) : (bool * option (Val ty_access_type)) :=
      match entries with
      | [] => match m with
              | Machine => (true, None)
              | User    => (false, None)
              end
      | (cfg , addr) :: entries =>
          match pmp_match_entry a m cfg prev addr with
          | PMP_Success  => (true, pmp_get_perms cfg m)
          | PMP_Fail     => (false, None)
          | PMP_Continue => pmp_check a entries addr m
          end
      end%list.

    (* check_access is based on the pmpCheck algorithm, main difference
           is that we can define it less cumbersome because entries will contain
           the PMP entries in highest-priority order. *)
    Definition check_pmp_access (a : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) : (bool * option (Val ty_access_type)) :=
      pmp_check a entries 0 m.

    Equations access_type_eqb (a1 a2 : Val ty_access_type) : bool :=
    | Read      | Read      := true;
    | Write     | Write     := true;
    | ReadWrite | ReadWrite := true;
    | Execute   | Execute   := true;
    | _         | _         := false.

    Equations decide_sub_perm (a1 a2 : Val ty_access_type) : bool :=
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

    Definition decide_pmp_access (a : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) (p : Val ty_access_type) : bool :=
      match check_pmp_access a entries m with
      | (true, Some acc) => decide_sub_perm acc p
      | (true, None)     => true
      | (false, _)       => false
      end.

    Definition Pmp_access (a : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) (m : Val ty_privilege) (p : Val ty_access_type) : Prop :=
      decide_pmp_access a entries m p = true.

    Definition Pmp_check_perms (cfg : Val ty_pmpcfg_ent) (acc : Val ty_access_type) (p : Val ty_privilege) : Prop :=
      decide_pmp_check_perms cfg acc p = true.

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
          (pmpcfg_ent_eqb c c' && (a =? a')%Z)%bool
      | _ => false
      end%list.

    Definition In_entries (idx : Val ty_pmpcfgidx) (e : Val ty_pmpentry) (es : Val (ty.list ty_pmpentry)) : Prop :=
      decide_in_entries idx e es = true.

    Definition decide_prev_addr (cfg : Val ty_pmpcfgidx) (entries : Val (ty.list ty_pmpentry)) (prev : Val ty_xlenbits) : bool :=
      match entries with
      | (c0 , a0) :: (c1 , a1) :: [] =>
          match cfg with
          | PMP0CFG => prev =? 0
          | PMP1CFG => prev =? a0
          end
      | _ => false
      end%list.

    Definition Prev_addr (cfg : Val ty_pmpcfgidx) (entries : Val (ty.list ty_pmpentry)) (prev : Val ty_xlenbits) : Prop :=
      decide_prev_addr cfg entries prev = true.

    Definition decide_within_cfg (paddr : Val ty_xlenbits) (cfg : Val ty_pmpcfg_ent) (prev_addr addr : Val ty_xlenbits) : bool :=
      match A cfg with
      | OFF => false
      | TOR => (prev_addr <=? paddr)%Z && (paddr <? addr)%Z
      end.

    Definition Within_cfg (paddr : Val ty_xlenbits) (cfg : Val ty_pmpcfg_ent) (prev_addr addr : Val ty_xlenbits) : Prop :=
      decide_within_cfg paddr cfg prev_addr addr = true.

    Definition decide_not_within_cfg (paddr : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) : bool :=
      match entries with
      | (c0 , a0) :: (c1 , a1) :: [] =>
          (((PmpAddrMatchType_eqb (A c0) OFF) && (PmpAddrMatchType_eqb (A c1) OFF))
          || ((0 <=? paddr)%Z && (a0 <=? paddr)%Z && (a1 <=? paddr)%Z))%bool
      | _ => false
      end%list.

    Definition Not_within_cfg (paddr : Val ty_xlenbits) (entries : Val (ty.list ty_pmpentry)) : Prop :=
      decide_not_within_cfg paddr entries = true.
    Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
      match p with
      | pmp_access      => Pmp_access
      | pmp_check_perms => Pmp_check_perms
      | pmp_check_rwx   => Pmp_check_rwx
      | sub_perm        => Sub_perm
      | within_cfg      => Within_cfg
      | not_within_cfg  => Not_within_cfg
      | prev_addr       => Prev_addr
      | in_entries      => In_entries
      end.

    Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

    Definition 𝑯 := Predicate.
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | pmp_entries             => [ty.list ty_pmpentry]
      | pmp_addr_access         => [ty.list ty_pmpentry; ty_privilege]
      | pmp_addr_access_without => [ty_xlenbits; ty.list ty_pmpentry; ty_privilege]
      | gprs                    => ctx.nil
      | ptsto                   => [ty_xlenbits; ty_xlenbits]
      | encodes_instr           => [ty.int; ty_ast]
      | ptstomem                => [ty_xlenbits; ty.int; ty.list ty_word]
      | ptstoinstr              => [ty_xlenbits; ty_ast]
      end.

    Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
      is_duplicable p :=
        match p with
        | pmp_entries             => false
        | pmp_addr_access         => false
        | pmp_addr_access_without => false
        | gprs                    => false
        | ptsto                   => false
        | encodes_instr           => true
        | ptstomem                => false
        | ptstoinstr              => false
        end
      }.
    Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

    Local Arguments Some {_} &.

    (* TODO: look up precise predicates again, check if below makes sense *)
    Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
      match p with
      | ptsto                   => Some (MkPrecise [ty_xlenbits] [ty_word] eq_refl)
      | pmp_entries             => Some (MkPrecise ε [ty.list ty_pmpentry] eq_refl)
      | pmp_addr_access         => Some (MkPrecise ε [ty.list ty_pmpentry; ty_privilege] eq_refl)
      | pmp_addr_access_without => Some (MkPrecise [ty_xlenbits] [ty.list ty_pmpentry; ty_privilege] eq_refl)
      | ptstomem                => Some (MkPrecise [ty_xlenbits; ty.int] [ty.list ty_word] eq_refl)
      | ptstoinstr              => Some (MkPrecise [ty_xlenbits] [ty_ast] eq_refl)
      | encodes_instr           => Some (MkPrecise [ty.int] [ty_ast] eq_refl)
      | _                       => None
      end.

  End PredicateKit.

  Include PredicateMixin RiscvPmpBase.

  Section ContractDefKit.

    Local Notation "r '↦' val" := (asn_chunk (chunk_ptsreg r val)) (at level 70).
    Local Notation "a '↦ₘ' t" := (asn_chunk (chunk_user ptsto [a; t])) (at level 70).
    Local Notation "p '∗' q" := (asn_sep p q).
    Local Notation "a '=' b" := (asn_eq a b).
    Local Notation "'∃' w ',' a" := (asn_exist w _ a) (at level 79, right associativity).
    Local Notation "a '∨' b" := (asn_or a b).
    Local Notation "p '⊑' q" := (asn_formula (formula_user sub_perm [p;q])) (at level 70).
    Local Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
    Local Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
    Local Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
    Local Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
    Local Notation asn_match_option T opt xl alt_inl alt_inr := (asn_match_sum T ty.unit opt xl alt_inl "_" alt_inr).
    Local Notation asn_pmp_entries l := (asn_chunk (chunk_user pmp_entries [l])).
    (* TODO: check if I can reproduce the issue with angelic stuff, I think it was checked_mem_read, with the correct postcondition *)
    (* Local Notation asn_pmp_entries_angelic l := (asn_chunk_angelic (chunk_user pmp_entries [l])). *)
    Local Notation asn_pmp_addr_access l m := (asn_chunk (chunk_user pmp_addr_access [l; m])).
    Local Notation asn_pmp_addr_access_without a l m := (asn_chunk (chunk_user pmp_addr_access_without [a;l; m])).
    Local Notation asn_gprs := (asn_chunk (chunk_user gprs env.nil)).
    Local Notation asn_within_cfg a cfg prev_addr addr := (asn_formula (formula_user within_cfg [a; cfg; prev_addr; addr])).
    Local Notation asn_not_within_cfg a es := (asn_formula (formula_user not_within_cfg [a; es])).
    Local Notation asn_prev_addr cfg es prev := (asn_formula (formula_user prev_addr [cfg; es; prev])).
    Local Notation asn_in_entries idx e es := (asn_formula (formula_user in_entries [idx; e; es])).
    Local Notation asn_pmp_access addr es m p := (asn_formula (formula_user pmp_access [addr;es;m;p])).
    Local Notation asn_pmp_check_perms cfg acc p := (asn_formula (formula_user pmp_check_perms [cfg;acc;p])).
    Local Notation asn_pmp_check_rwx cfg acc := (asn_formula (formula_user pmp_check_rwx [cfg;acc])).
    Local Notation asn_expand_pmpcfg_ent cfg := (asn_match_record rpmpcfg_ent cfg
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil "L" "L") "A" "A") "X" "X") "W" "W") "R" "R")
      (asn_true)).

    Definition term_eqb {Σ} (e1 e2 : Term Σ ty.int) : Term Σ ty.bool :=
      term_binop bop.eq e1 e2.

    Local Notation "e1 '=?' e2" := (term_eqb e1 e2).

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

    Fixpoint asn_exists {Σ} (Γ : NCtx string Ty) : Assertion (Σ ▻▻ Γ) -> Assertion Σ :=
      match Γ return Assertion (Σ ▻▻ Γ) -> Assertion Σ with
      | ctx.nil => fun asn => asn
      | ctx.snoc Γ (x :: τ) =>
        fun asn =>
          @asn_exists Σ Γ (asn_exist x τ asn)
      end.

    Definition asn_with_reg {Σ} (r : Term Σ ty.int) (asn : Reg ty_xlenbits -> Assertion Σ) (asn_default : Assertion Σ) : Assertion Σ :=
      asn_if (r =? z_term 1)
             (asn x1)
             (asn_if (r =? z_term 2)
                     (asn x2)
                     (asn_if (r =? z_term 3)
                             (asn x3)
                             asn_default)).

    Definition asn_and_regs {Σ} (f : Reg ty_xlenbits -> Assertion Σ) : Assertion Σ :=
      f x1 ∗ f x2 ∗ f x3 ∗ f x4 ∗ f x5 ∗ f x6 ∗ f x7.

    Definition asn_regs_ptsto {Σ} : Assertion Σ :=
      asn_and_regs
        (fun r => ∃ "w", r ↦ term_var "w").

    Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

    (* TODO: abstract away the concrete type, look into unions for that *)
    (* TODO: length of list should be 16, no duplicates *)
    Definition term_pmp_entries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfgidx ty_pmpaddridx)) :=
      term_list
        (cons (term_val ty_pmpcfgidx PMP0CFG ,ₜ term_val ty_pmpaddridx PMPADDR0)
              (cons (term_val ty_pmpcfgidx PMP1CFG ,ₜ term_val ty_pmpaddridx PMPADDR1) nil)).

  End ContractDefKit.
End RiscvPmpSignature.

Module RiscvPmpSolverKit <: SolverKit RiscvPmpBase RiscvPmpSignature.

  Definition simplify_sub_perm {Σ} (a1 a2 : Term Σ ty_access_type) : option (List Formula Σ) :=
    match term_get_val a1 , term_get_val a2 with
    | Some a1 , Some a2 => if decide_sub_perm a1 a2 then Some nil else None
    | _       , _       => Some (cons (formula_user sub_perm [a1;a2]) nil)
    end.

  Definition simplify_pmp_access {Σ} (paddr : Term Σ ty_xlenbits) (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (List Formula Σ) :=
    match term_get_val paddr , term_get_val es , term_get_val p with
    | Some paddr , Some entries , Some p =>
      match check_pmp_access paddr entries p with
      | (true, Some typ) => simplify_sub_perm (term_val ty_access_type typ) acc
      | (true, None)     => Some nil
      | (false, _)       => None
      end
    | _ , _ , _ =>
      Some (cons (formula_user pmp_access [paddr; es; p; acc]) nil)
    end.

  (* TODO: User predicates can be simplified smarter *)
  Equations(noeqns) decide_pmp_check_rwx {Σ} (X W R : Term Σ ty.bool) (acc : Term Σ ty_access_type) : bool :=
  | term_val true | _             | _             | term_union KExecute (term_val tt)   := true;
  | _             | term_val true | _             | term_union KWrite (term_val tt)     := true;
  | _             | _             | term_val true | term_union KRead (term_val tt)      := true;
  | _             | term_val true | term_val true | term_union KReadWrite (term_val tt) := true;
  | _             | _             | _             | _                                   := false.

  Equations(noeqns) simplify_pmp_check_rwx {Σ} (cfg : Term Σ ty_pmpcfg_ent) (acc : Term Σ ty_access_type) : option (List Formula Σ) :=
  | term_record pmpcfg_ent [_;_;X;W;R] | acc          :=
    if decide_pmp_check_rwx X W R acc then Some nil else None;
  | term_val cfg                       | term_val acc :=
    if pmp_check_RWX cfg acc then Some nil else None;
  | cfg                                | acc          :=
    Some (cons (formula_user pmp_check_rwx [cfg;acc]) nil).

  Equations(noeqns) simplify_pmp_check_perms {Σ} (cfg : Term Σ ty_pmpcfg_ent) (acc : Term Σ ty_access_type) (p : Term Σ ty_privilege) : option (List Formula Σ) :=
  | term_record pmpcfg_ent [term_val false;_;_;_;_] | acc | term_val Machine :=
    Some nil;
  | cfg                                             | acc | p                :=
    simplify_pmp_check_rwx cfg acc.

  Equations(noeqns) simplify_within_cfg {Σ} (paddr : Term Σ ty_xlenbits) (cfg : Term Σ ty_pmpcfg_ent) (prev_addr addr : Term Σ ty_xlenbits) : option (List Formula Σ) :=
  | term_val paddr | term_val cfg | term_val a | term_val a' :=
    if decide_within_cfg paddr cfg a a' then Some nil else None;
  | paddr          | cfg          | a          | a'          :=
    Some (cons (formula_user within_cfg [paddr; cfg; a; a']) nil).

  Equations(noeqns) simplify_prev_addr {Σ} (cfg : Term Σ ty_pmpcfgidx) (entries : Term Σ (ty.list ty_pmpentry)) (prev : Term Σ ty_xlenbits) : option (List Formula Σ) :=
  | term_val cfg | term_val entries | term_val prev := if decide_prev_addr cfg entries prev then Some nil else None;
  | cfg          | entries          | prev          :=
    Some (cons (formula_user prev_addr [cfg; entries; prev]) nil).


  Equations(noeqns) simplify_user [Σ] (p : 𝑷) : Env (Term Σ) (𝑷_Ty p) -> option (List Formula Σ) :=
  | pmp_access             | [ paddr; entries; priv; perm ] => simplify_pmp_access paddr entries priv perm
  | pmp_check_perms        | [ cfg; acc; priv ]             => simplify_pmp_check_perms cfg acc priv
  | pmp_check_rwx          | [ cfg; acc ]                   => simplify_pmp_check_rwx cfg acc
  | sub_perm               | [ a1; a2 ]                     => simplify_sub_perm a1 a2
  | within_cfg             | [ paddr; cfg; prevaddr; addr]  => simplify_within_cfg paddr cfg prevaddr addr
  | not_within_cfg         | [ paddr; entries ]             => Some (cons (formula_user not_within_cfg [paddr; entries]) nil)
  | prev_addr              | [ cfg; entries; prev ]         => simplify_prev_addr cfg entries prev
  | in_entries             | [ cfg; entries; prev ]         => Some (cons (formula_user in_entries [cfg; entries; prev]) nil).

  Local Ltac lsolve :=
    repeat
      lazymatch goal with
      | |- option.spec _ _ (match @term_get_val ?Σ ?σ ?v with _ => _ end) =>
          destruct (@term_get_val_spec Σ σ v); subst;
          try progress cbn - [simplify_sub_perm]
      | |- option.spec _ _ (match check_pmp_access _ _ _ with _ => _ end) =>
          unfold Pmp_access, decide_pmp_access;
          let o := fresh "o" in
          destruct check_pmp_access as [[] o]; [destruct o|]
      | |- option.spec _ _ (Some _) =>
          constructor; cbn; try intuition fail
      | |- option.spec _ _ None =>
          constructor; cbn; try intuition fail
      end; auto.

  Lemma simplify_sub_perm_spec {Σ} (a1 a2 : Term Σ ty_access_type) :
    option.spec
      (fun r => forall ι, Sub_perm (inst a1 ι) (inst a2 ι) <-> instpc r ι)
      (forall ι, ~ Sub_perm (inst a1 ι) (inst a2 ι))
      (simplify_sub_perm a1 a2).
  Proof.
    unfold simplify_sub_perm. lsolve.
    destruct decide_sub_perm eqn:?; constructor;
      intros ?; intuition; constructor.
  Qed.

  Lemma simplify_pmp_access_spec {Σ} (paddr : Term Σ ty_exc_code)
    (es : Term Σ (ty.list ty_pmpentry)) (p : Term Σ ty_privilege)
    (acc : Term Σ ty_access_type) :
    option.spec
      (fun r => forall ι,
           Pmp_access (inst paddr ι) (inst es ι) (inst p ι) (inst acc ι) <->
             instpc r ι)
      (forall ι, ~ Pmp_access (inst paddr ι) (inst es ι) (inst p ι) (inst acc ι))
      (simplify_pmp_access paddr es p acc).
  Proof.
    unfold simplify_pmp_access. lsolve.
    apply (simplify_sub_perm_spec (term_val _ _)).
  Qed.

  Lemma simplify_user_spec : SolverUserOnlySpec simplify_user.
  Proof.
    intros Σ p ts.
    destruct p; cbv in ts; env.destroy ts; cbn.
    - simple apply simplify_pmp_access_spec.
    - admit.
    - admit.
    - simple apply simplify_sub_perm_spec.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Definition solver : Solver :=
    solveruseronly_to_solver simplify_user.

  Lemma solver_spec : SolverSpec solver.
  Proof.
    apply solveruseronly_to_solver_spec, simplify_user_spec.
  Qed.

End RiscvPmpSolverKit.
Module RiscvPmpSolver := MakeSolver RiscvPmpBase RiscvPmpSignature RiscvPmpSolverKit.
