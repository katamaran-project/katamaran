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
From RiscvPmp Require Import
     Machine.
From Katamaran Require Import
     Notations
     SemiConcrete.Mutator
     Specification
     Symbolic.Mutator
     Symbolic.Solver
     Symbolic.Propositions
     Symbolic.Worlds.
From Equations Require Import
     Equations.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope ctx_scope.
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
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

Module Import RiscvPmpSpecification <: Specification RiscvPmpBase.
Module PROG := RiscvPmpProgram.

Section PredicateKit.
  Definition 𝑷 := PurePredicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    | pmp_access      => [ty_xlenbits; ty_list ty_pmpentry; ty_privilege; ty_access_type]
    | pmp_check_perms => [ty_pmpcfg_ent; ty_access_type; ty_privilege]
    | pmp_check_rwx   => [ty_pmpcfg_ent; ty_access_type]
    | sub_perm        => [ty_access_type; ty_access_type]
    | within_cfg      => [ty_xlenbits; ty_pmpcfg_ent; ty_xlenbits; ty_xlenbits]
    | not_within_cfg  => [ty_xlenbits; ty_list ty_pmpentry]
    | prev_addr       => [ty_pmpcfgidx; ty_list ty_pmpentry; ty_xlenbits]
    | in_entries      => [ty_pmpcfgidx; ty_pmpentry; ty_list ty_pmpentry]
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

  Fixpoint pmp_check (a : Val ty_xlenbits) (entries : Val (ty_list ty_pmpentry)) (prev : Val ty_xlenbits) (m : Val ty_privilege) : (bool * option (Val ty_access_type)) :=
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
  Definition decide_pmp_access (a : Val ty_xlenbits) (entries : Val (ty_list ty_pmpentry)) (m : Val ty_privilege) : (bool * option (Val ty_access_type)) :=
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

  Definition Pmp_access (a : Val ty_xlenbits) (entries : Val (ty_list ty_pmpentry)) (m : Val ty_privilege) (p : Val ty_access_type) : Prop :=
    match decide_pmp_access a entries m with
    | (true, Some acc) => Sub_perm acc p
    | (true, None)     => True
    | (false, _)       => False
    end.

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

  Definition decide_in_entries (idx : Val ty_pmpcfgidx) (e : Val ty_pmpentry) (es : Val (ty_list ty_pmpentry)) : bool :=
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

  Definition In_entries (idx : Val ty_pmpcfgidx) (e : Val ty_pmpentry) (es : Val (ty_list ty_pmpentry)) : Prop :=
    decide_in_entries idx e es = true.

  Definition decide_prev_addr (cfg : Val ty_pmpcfgidx) (entries : Val (ty_list ty_pmpentry)) (prev : Val ty_xlenbits) : bool :=
    match entries with
    | (c0 , a0) :: (c1 , a1) :: [] =>
        match cfg with
        | PMP0CFG => prev =? 0
        | PMP1CFG => prev =? a0
        end
    | _ => false
    end%list.

  Definition Prev_addr (cfg : Val ty_pmpcfgidx) (entries : Val (ty_list ty_pmpentry)) (prev : Val ty_xlenbits) : Prop :=
    decide_prev_addr cfg entries prev = true.

  Definition decide_within_cfg (paddr : Val ty_xlenbits) (cfg : Val ty_pmpcfg_ent) (prev_addr addr : Val ty_xlenbits) : bool :=
    match A cfg with
    | OFF => false
    | TOR => (prev_addr <=? paddr)%Z && (paddr <? addr)%Z
    end.

  Definition Within_cfg (paddr : Val ty_xlenbits) (cfg : Val ty_pmpcfg_ent) (prev_addr addr : Val ty_xlenbits) : Prop :=
    decide_within_cfg paddr cfg prev_addr addr = true.

  Definition decide_not_within_cfg (paddr : Val ty_xlenbits) (entries : Val (ty_list ty_pmpentry)) : bool :=
    match entries with
    | (c0 , a0) :: (c1 , a1) :: [] =>
        (((PmpAddrMatchType_eqb (A c0) OFF) && (PmpAddrMatchType_eqb (A c1) OFF))
        || ((0 <=? paddr)%Z && (a0 <=? paddr)%Z && (a1 <=? paddr)%Z))%bool
    | _ => false
    end%list.

  Definition Not_within_cfg (paddr : Val ty_xlenbits) (entries : Val (ty_list ty_pmpentry)) : Prop :=
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
    | pmp_entries             => [ty_list ty_pmpentry]
    | pmp_addr_access         => [ty_list ty_pmpentry; ty_privilege]
    | pmp_addr_access_without => [ty_xlenbits; ty_list ty_pmpentry; ty_privilege]
    | gprs                    => ctx.nil
    | ptsto                   => [ty_xlenbits; ty_xlenbits]
    end.

  Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
    is_duplicable p :=
      match p with
      | pmp_entries             => false
      | pmp_addr_access         => false
      | pmp_addr_access_without => false
      | gprs                    => false
      | ptsto                   => false
      end
    }.
  Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

  Local Arguments Some {_} &.

  (* TODO: look up precise predicates again, check if below makes sense *)
  Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
    match p with
    | ptsto                   => Some (MkPrecise [ty_xlenbits] [ty_word] eq_refl)
    | pmp_entries             => Some (MkPrecise ε [ty_list ty_pmpentry] eq_refl)
    | pmp_addr_access         => Some (MkPrecise ε [ty_list ty_pmpentry; ty_privilege] eq_refl)
    | pmp_addr_access_without => Some (MkPrecise [ty_xlenbits] [ty_list ty_pmpentry; ty_privilege] eq_refl)
    | _                       => None
    end.

End PredicateKit.

Include ContractDeclMixin RiscvPmpBase RiscvPmpProgram.

Section ContractDefKit.

  Local Notation "r '↦' val" := (asn_chunk (chunk_ptsreg r val)) (at level 70).
  Local Notation "a '↦ₘ' t" := (asn_chunk (chunk_user ptsto [a; t])) (at level 70).
  Local Notation "p '∗' q" := (asn_sep p q).
  Local Notation "a '=' b" := (asn_eq a b).
  Local Notation "'∃' w ',' a" := (asn_exist w _ a) (at level 79, right associativity).
  Local Notation "a '∨' b" := (asn_or a b).
  Local Notation "p '⊑' q" := (asn_formula (formula_user sub_perm [p;q])) (at level 70).
  Local Notation "a <ₜ b" := (term_binop binop_lt a b) (at level 60).
  Local Notation "a <=ₜ b" := (term_binop binop_le a b) (at level 60).
  Local Notation "a &&ₜ b" := (term_binop binop_and a b) (at level 80).
  Local Notation "a ||ₜ b" := (term_binop binop_or a b) (at level 85).
  Local Notation asn_match_option T opt xl alt_inl alt_inr := (asn_match_sum T ty_unit opt xl alt_inl "_" alt_inr).
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


  Definition term_eqb {Σ} (e1 e2 : Term Σ ty_int) : Term Σ ty_bool :=
    term_binop binop_eq e1 e2.

  Local Notation "e1 '=?' e2" := (term_eqb e1 e2).

  Definition z_term {Σ} : Z -> Term Σ ty_int := term_val ty_int.

  Definition sep_contract_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
    ctx.map (fun '(x::σ) => x::σ) Δ ▻▻ Σ.

  Definition create_localstore (Δ : PCtx) (Σ : LCtx) : SStore Δ (sep_contract_logvars Δ Σ) :=
    (env.tabulate (fun '(x::σ) xIn =>
                     @term_var
                       (sep_contract_logvars Δ Σ)
                       x
                       σ
                       (ctx.in_cat_left Σ (ctx.in_map (fun '(y::τ) => y::τ) xIn)))).

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepLemma {Δ} (f : Lem Δ) : Type :=
    Lemma Δ.

  Fixpoint asn_exists {Σ} (Γ : NCtx string Ty) : Assertion (Σ ▻▻ Γ) -> Assertion Σ :=
    match Γ return Assertion (Σ ▻▻ Γ) -> Assertion Σ with
    | ctx.nil => fun asn => asn
    | ctx.snoc Γ (x :: τ) =>
      fun asn =>
        @asn_exists Σ Γ (asn_exist x τ asn)
    end.

  Definition asn_with_reg {Σ} (r : Term Σ ty_int) (asn : Reg ty_xlenbits -> Assertion Σ) (asn_default : Assertion Σ) : Assertion Σ :=
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

  Local Notation "e1 ',ₜ' e2" := (term_binop binop_pair e1 e2) (at level 100).

  (* TODO: abstract away the concrete type, look into unions for that *)
  (* TODO: length of list should be 16, no duplicates *)
  Definition pmp_entries {Σ} : Term Σ (ty_list (ty_prod ty_pmpcfgidx ty_pmpaddridx)) :=
    term_list
      (cons (term_val ty_pmpcfgidx PMP0CFG ,ₜ term_val ty_pmpaddridx PMPADDR0)
            (cons (term_val ty_pmpcfgidx PMP1CFG ,ₜ term_val ty_pmpaddridx PMPADDR1) nil)).

  Section Contracts.
    Import RiscvNotations.

  (** Machine Invariant **)
  (*
    TODO: - this should work for the execute{,_/x/} functions, but step and loop will update 
            the pc, so this should be reflected in their contract (2nd pc(i) -> pc(i + 4)?)



    TODO: short notation out of sync with actual contract
    @pre ∀ m h i . mode(m) ∗ mtvec(h) ∗ pmp_entries(ents) ∗ pc(i) ∗ mepc(_) ∗ mpp(_)
    @post pmp_entries(ents) ∗ (mode(m) ∗ pc(i)) ∨ (mode(M) ∗ pc(h) ...)
    τ f(Δ...)*)
  Definition instr_exec_contract {τ Δ} : SepContract Δ τ :=
    let Σ := ["m" :: ty_privilege; "h" :: ty_xlenbits; "i" :: ty_xlenbits; "entries" :: ty_list ty_pmpentry; "mpp" :: ty_privilege; "mepc" :: ty_xlenbits; "npc" :: ty_xlenbits] in
    {| sep_contract_logic_variables := sep_contract_logvars Δ Σ;
       sep_contract_localstore      := create_localstore Δ Σ;
       sep_contract_precondition    :=
                     cur_privilege ↦ term_var "m" ∗
                     mtvec         ↦ term_var "h" ∗
                     pc            ↦ term_var "i" ∗
                     nextpc        ↦ term_var "npc" ∗
         ∃ "mcause", mcause        ↦ term_var "mcause" ∗
                     mepc          ↦ term_var "mepc" ∗
                     mstatus       ↦ term_record rmstatus [ term_var "mpp" ] ∗
                     asn_pmp_entries (term_var "entries") ∗
                     asn_pmp_addr_access (term_var "entries") (term_var "m") ∗
                     asn_gprs;
       sep_contract_result          := "result_mach_inv";
       sep_contract_postcondition   :=
                     asn_pmp_addr_access (term_var "entries") (term_var "m") ∗
                     asn_gprs ∗
                     pc     ↦ term_var "i" ∗
         ∃ "mcause", mcause ↦ term_var "mcause" ∗
         (  (* Executing normally *)
                 asn_pmp_entries (term_var "entries") ∗
                 cur_privilege ↦ term_var "m" ∗
            ∃ v, nextpc        ↦ term_var v ∗
                 mtvec         ↦ term_var "h" ∗
                 mstatus       ↦ term_record rmstatus [ term_var "mpp" ] ∗
                 mepc          ↦ term_var "mepc"
          ∨
            (* Modified CSRs, requires Machine mode *)
                           term_var "m"  =  term_val ty_privilege Machine ∗
            ∃ "entries",   asn_pmp_entries (term_var "entries") ∗
                           cur_privilege ↦ term_val ty_privilege Machine ∗
                           nextpc        ↦ term_var "npc" ∗
            ∃ "new_mtvec", mtvec         ↦ term_var "new_mtvec" ∗
            ∃ "new_mpp",   mstatus       ↦ term_record rmstatus [ term_var "new_mpp" ] ∗
            ∃ "new_mepc",  mepc          ↦ term_var "new_mepc"
          ∨
            (* Trap occured -> Go into M-mode *)
            asn_pmp_entries (term_var "entries") ∗
            cur_privilege ↦ (term_val ty_privilege Machine) ∗
            nextpc        ↦ term_var "h" ∗
            mtvec         ↦ term_var "h" ∗
            mstatus       ↦ term_record rmstatus [ term_var "m" ] ∗
            mepc          ↦ term_var "i"
          ∨
            (* MRET = Recover *)
            asn_pmp_entries (term_var "entries") ∗
            term_var "m"  =  term_val ty_privilege Machine ∗
            cur_privilege ↦ term_var "mpp" ∗
            nextpc        ↦ term_var "mepc" ∗
            mtvec         ↦ term_var "h" ∗
            mstatus       ↦ term_record rmstatus [ term_val ty_privilege User ] ∗
            mepc          ↦ term_var "mepc")
    |}.

  Definition sep_contract_execute_RTYPE : SepContractFun execute_RTYPE :=
    instr_exec_contract.

  Definition sep_contract_execute_ITYPE : SepContractFun execute_ITYPE :=
    instr_exec_contract.

  Definition sep_contract_execute_UTYPE : SepContractFun execute_UTYPE :=
    instr_exec_contract.

  Definition sep_contract_execute_BTYPE : SepContractFun execute_BTYPE :=
    instr_exec_contract.

  Definition sep_contract_execute_RISCV_JAL : SepContractFun execute_RISCV_JAL :=
    instr_exec_contract.

  Definition sep_contract_execute_RISCV_JALR : SepContractFun execute_RISCV_JALR :=
    instr_exec_contract.

  Definition sep_contract_execute_ECALL : SepContractFun execute_ECALL :=
    instr_exec_contract.

  Definition sep_contract_execute_MRET : SepContractFun execute_MRET :=
    instr_exec_contract.

  Definition sep_contract_execute_CSR : SepContractFun execute_CSR :=
    instr_exec_contract.

  Definition sep_contract_execute_STORE : SepContractFun execute_STORE :=
    instr_exec_contract.

  Definition sep_contract_execute_LOAD : SepContractFun execute_LOAD :=
    instr_exec_contract.

  Definition sep_contract_execute : SepContractFun execute :=
    instr_exec_contract.

  Definition sep_contract_process_load : SepContractFun process_load :=
    {| sep_contract_logic_variables := [rd :: ty_regno; vaddr :: ty_xlenbits; value :: ty_memory_op_result; "i" :: ty_xlenbits; tvec :: ty_xlenbits; p :: ty_privilege; "mpp" :: ty_privilege; "mepc" :: ty_xlenbits; "npc" :: ty_xlenbits; "mcause" :: ty_mcause];
       sep_contract_localstore      := [term_var rd; term_var vaddr; term_var value];
       sep_contract_precondition    :=
         asn_gprs
         ∗ pc            ↦ term_var "i"
         ∗ nextpc        ↦ term_var "npc"
         ∗ cur_privilege ↦ term_var p
         ∗ mcause        ↦ term_var "mcause"
         ∗ mstatus       ↦ term_record rmstatus [ term_var "mpp" ]
         ∗ mtvec         ↦ term_var tvec
         ∗ mepc          ↦ term_var "mepc";
       sep_contract_result          := "result_process_load";
       sep_contract_postcondition   :=
         asn_gprs ∗
         asn_match_union memory_op_result (term_var value)
          (fun K => match K with
                    | KMemValue     => [v :: ty_xlenbits]
                    | KMemException => [e :: ty_exception_type]
                    end)
          (fun K => match K with
                    | KMemValue     => pat_var v
                    | KMemException => pat_var e
                    end)
          (fun K => match K with
                    | KMemValue     =>
                        term_var "result_process_load" = term_val ty_retired RETIRE_SUCCESS
                        ∗ pc            ↦ term_var "i"
                        ∗ nextpc        ↦ term_var "npc"
                        ∗ cur_privilege ↦ term_var p
                        ∗ mcause        ↦ term_var "mcause"
                        ∗ mstatus       ↦ term_record rmstatus [ term_var "mpp" ]
                        ∗ mtvec         ↦ term_var tvec
                        ∗ mepc          ↦ term_var "mepc"
                    | KMemException =>
                        term_var "result_process_load" = term_val ty_retired RETIRE_FAIL
                        ∗             pc            ↦ term_var "i"
                        ∗             nextpc        ↦ term_var tvec
                        ∗             cur_privilege ↦ term_val ty_privilege Machine
                        ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
                        ∗             mstatus       ↦ term_record rmstatus [ term_var p ]
                        ∗             mepc          ↦ term_var "i"
                        ∗             mtvec         ↦ term_var tvec
                    end);
    |}.

  Definition sep_contract_readCSR : SepContractFun readCSR :=
    {| sep_contract_logic_variables := [csr :: ty_csridx; "mpp" :: ty_privilege;
                                        "mtvec" :: ty_xlenbits; "mcause" :: ty_exc_code;
                                        "mepc" :: ty_xlenbits; "cfg0" :: ty_pmpcfg_ent; "cfg1" :: ty_pmpcfg_ent; "addr0" :: ty_xlenbits; "addr1" :: ty_xlenbits];
       sep_contract_localstore      := [term_var csr];
       sep_contract_precondition    :=
         mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ mtvec ↦ term_var "mtvec"
         ∗ mcause ↦ term_var "mcause"
         ∗ mepc ↦ term_var "mepc"
         ∗ pmp0cfg ↦ term_var "cfg0"
         ∗ pmp1cfg ↦ term_var "cfg1"
         ∗ pmpaddr0 ↦ term_var "addr0"
         ∗ pmpaddr1 ↦ term_var "addr1";
       sep_contract_result          := "result_readCSR";
       sep_contract_postcondition   :=
         ∃ "result", term_var "result_readCSR" = term_var "result"
         ∗ mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ mtvec ↦ term_var "mtvec"
         ∗ mcause ↦ term_var "mcause"
         ∗ mepc ↦ term_var "mepc"
         ∗ pmp0cfg ↦ term_var "cfg0"
         ∗ pmp1cfg ↦ term_var "cfg1"
         ∗ pmpaddr0 ↦ term_var "addr0"
         ∗ pmpaddr1 ↦ term_var "addr1";
    |}.

  Definition sep_contract_writeCSR : SepContractFun writeCSR :=
    {| sep_contract_logic_variables := [csr :: ty_csridx; value :: ty_xlenbits];
       sep_contract_localstore      := [term_var csr; term_var value];
       sep_contract_precondition    :=
         ∃ "mpp", mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ ∃ "mtvec", mtvec ↦ term_var "mtvec"
         ∗ ∃ "mcause", mcause ↦ term_var "mcause"
         ∗ ∃ "mepc", mepc ↦ term_var "mepc"
         ∗ ∃ "cfg0", (pmp0cfg ↦ term_var "cfg0" ∗ asn_expand_pmpcfg_ent (term_var "cfg0"))
         ∗ ∃ "cfg1", (pmp1cfg ↦ term_var "cfg1" ∗ asn_expand_pmpcfg_ent (term_var "cfg1"))
         ∗ ∃ "addr0", pmpaddr0 ↦ term_var "addr0"
         ∗ ∃ "addr1", pmpaddr1 ↦ term_var "addr1";
       sep_contract_result          := "result_writeCSR";
       sep_contract_postcondition   :=
         term_var "result_writeCSR" = term_val ty_unit tt
         ∗ ∃ "mpp", mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ ∃ "mtvec", mtvec ↦ term_var "mtvec"
         ∗ ∃ "mcause", mcause ↦ term_var "mcause"
         ∗ ∃ "mepc", mepc ↦ term_var "mepc"
         ∗ ∃ "cfg0", pmp0cfg ↦ term_var "cfg0"
         ∗ ∃ "cfg1", pmp1cfg ↦ term_var "cfg1"
         ∗ ∃ "addr0", pmpaddr0 ↦ term_var "addr0"
         ∗ ∃ "addr1", pmpaddr1 ↦ term_var "addr1";
    |}.

  Definition sep_contract_check_CSR : SepContractFun check_CSR :=
    {| sep_contract_logic_variables := [csr :: ty_csridx; p :: ty_privilege];
       sep_contract_localstore      := [term_var csr; term_var p];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_check_CSR";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var p)
                        (fun K => match K with
                                  | Machine => term_var "result_check_CSR" = term_val ty_bool true
                                  | User    => term_var "result_check_CSR" = term_val ty_bool false
                                  end)
    |}.

  Definition sep_contract_is_CSR_defined : SepContractFun is_CSR_defined :=
    {| sep_contract_logic_variables := [csr :: ty_csridx; p :: ty_privilege];
       sep_contract_localstore      := [term_var csr; term_var p];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_is_CSR_defined";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var p)
                        (fun K => match K with
                                  | Machine => term_var "result_is_CSR_defined" =
                                                 term_val ty_bool true
                                  | User    =>term_var "result_is_CSR_defined" =
                                                term_val ty_bool false
                                  end);
    |}.

  Definition sep_contract_check_CSR_access : SepContractFun check_CSR_access :=
    {| sep_contract_logic_variables := [csrrw :: ty_access_type; csrpr :: ty_privilege; p :: ty_privilege];
       sep_contract_localstore      := [term_var csrrw; term_var csrpr; term_var p];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_check_CSR_access";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var csrpr)
                        (fun K => match K with
                                  | Machine =>
                                      asn_match_enum privilege (term_var p)
                                                     (fun K => match K with
                                                               | Machine => term_var "result_check_CSR_access" =
                                                                              term_val ty_bool true
                                                               | User    => term_var "result_check_CSR_access" =
                                                                              term_val ty_bool false
                                                               end)
                                  | User =>
                                      asn_match_enum privilege (term_var p)
                                                     (fun K => match K with
                                                               | Machine => term_var "result_check_CSR_access" =
                                                                              term_val ty_bool true
                                                               | User    => term_var "result_check_CSR_access" =
                                                                                   term_val ty_bool true
                                                               end)
                                  end);
    |}.

  Definition sep_contract_privLevel_to_bits : SepContractFun privLevel_to_bits :=
    {| sep_contract_logic_variables := [p :: ty_privilege];
       sep_contract_localstore      := [term_var p];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_privLevel_to_bits";
       sep_contract_postcondition   :=
         asn_match_enum privilege (term_var p)
                        (fun K => match K with
                                  | Machine => term_var "result_privLevel_to_bits" =
                                                 term_val ty_xlenbits 3%Z
                                  | User    => term_var "result_privLevel_to_bits" =
                                                 term_val ty_xlenbits 0%Z
                                  end);
    |}.

  Definition sep_contract_mstatus_to_bits : SepContractFunX mstatus_to_bits :=
    {| sep_contract_logic_variables := [value :: ty_mstatus];
       sep_contract_localstore      := [term_var value];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_mstatus_to_bits";
       sep_contract_postcondition   :=
         ∃ "result", term_var "result_mstatus_to_bits" = term_var "result";
    |}.

  Definition sep_contract_mstatus_from_bits : SepContractFunX mstatus_from_bits :=
    {| sep_contract_logic_variables := [value :: ty_xlenbits];
       sep_contract_localstore      := [term_var value];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_mstatus_from_bits";
       sep_contract_postcondition   :=
         ∃ "MPP", term_var "result_mstatus_from_bits" = term_record rmstatus [ term_var "MPP" ];
    |}.

  Definition sep_contract_pmpcfg_ent_from_bits : SepContractFunX pmpcfg_ent_from_bits :=
    {| sep_contract_logic_variables := [value :: ty_xlenbits];
       sep_contract_localstore      := [term_var value];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpcfg_ent_from_bits";
       sep_contract_postcondition   :=
         ∃ "cfg", term_var "result_pmpcfg_ent_from_bits" = term_var "cfg";
    |}.

  Definition sep_contract_pmpcfg_ent_to_bits : SepContractFunX pmpcfg_ent_to_bits :=
    {| sep_contract_logic_variables := [value :: ty_pmpcfg_ent];
       sep_contract_localstore      := [term_var value];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpcfg_ent_to_bits";
       sep_contract_postcondition   :=
         ∃ "cfg", term_var "result_pmpcfg_ent_to_bits" = term_var "cfg";
    |}.

  Definition sep_contract_csrAccess : SepContractFun csrAccess :=
    {| sep_contract_logic_variables := [csr :: ty_csridx];
       sep_contract_localstore      := [term_var csr];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_csrAccess";
       sep_contract_postcondition   :=
         term_var "result_csrAccess" = term_val ty_access_type ReadWrite;
    |}.

  Definition sep_contract_csrPriv : SepContractFun csrPriv :=
    {| sep_contract_logic_variables := [csr :: ty_csridx];
       sep_contract_localstore      := [term_var csr];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_csrPriv";
       sep_contract_postcondition   :=
         term_var "result_csrPriv" = term_val ty_privilege Machine;
    |}.

  Definition sep_contract_handle_mem_exception : SepContractFun handle_mem_exception :=
    {| sep_contract_logic_variables := [addr :: ty_xlenbits; e :: ty_exception_type; "i" :: ty_xlenbits; tvec :: ty_xlenbits; p :: ty_privilege; "mpp" :: ty_privilege; "mepc" :: ty_xlenbits];
       sep_contract_localstore      := [term_var addr; term_var e];
       sep_contract_precondition    :=
                        pc            ↦ term_var "i"
         ∗ ∃ "npc",    nextpc        ↦ term_var "npc"
         ∗             cur_privilege ↦ term_var p
         ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
         ∗             mstatus       ↦ term_record rmstatus [ term_var "mpp" ]
         ∗             mtvec         ↦ term_var tvec
         ∗             mepc          ↦ term_var "mepc";
       sep_contract_result          := "result_handle_mem_exception";
       sep_contract_postcondition   :=
         term_var "result_handle_mem_exception" = term_val ty_unit tt
         ∗             pc            ↦ term_var "i"
         ∗             nextpc        ↦ term_var tvec
         ∗             cur_privilege ↦ term_val ty_privilege Machine
         ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
         ∗             mstatus       ↦ term_record rmstatus [ term_var p ]
         ∗             mepc          ↦ term_var "i"
         ∗             mtvec         ↦ term_var tvec
    |}.

  Definition sep_contract_exception_handler : SepContractFun exception_handler :=
    {| sep_contract_logic_variables := [cur_priv :: ty_privilege; ctl :: ty_ctl_result; "pc" :: ty_xlenbits; "mpp" :: ty_privilege; "mepc" :: ty_xlenbits; tvec :: ty_xlenbits; p :: ty_privilege];
       sep_contract_localstore      := [term_var cur_priv; term_var ctl; term_var "pc"];
       sep_contract_precondition    :=
         cur_privilege ↦ (term_var p)
         ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
         ∗             mstatus       ↦ (term_record rmstatus [ term_var "mpp" ])
         ∗             mtvec         ↦ (term_var tvec)
         ∗             mepc          ↦ (term_var "mepc");
       sep_contract_result          := "result_exception_handler";
       sep_contract_postcondition   := asn_match_union ctl_result (term_var ctl)
        (fun K => match K with
                | KCTL_TRAP => ctx.snoc ε (e ∷ ty_exception_type)
                | KCTL_MRET => ε
                end)
        (fun K => match K with
                | KCTL_TRAP => pat_var e
                | KCTL_MRET => pat_unit
                end)
        (fun K => match K with
                | KCTL_TRAP =>
                    term_var "result_exception_handler" = term_var tvec
                    ∗             cur_privilege ↦ term_val ty_privilege Machine
                    ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
                    ∗             mstatus       ↦ term_record rmstatus [ term_var p ]
                    ∗             mepc          ↦ term_var "pc"
                    ∗             mtvec         ↦ term_var tvec
                | KCTL_MRET =>
                    term_var "result_exception_handler" = term_var "mepc"
                    ∗             cur_privilege ↦ term_var "mpp"
                    ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
                    ∗             mstatus       ↦ term_record rmstatus [ term_val ty_privilege User ]
                    ∗             mtvec         ↦ term_var tvec
                    ∗             mepc          ↦ term_var "mepc"
                end);
    |}.

  Definition sep_contract_handle_illegal : SepContractFun handle_illegal :=
    {| sep_contract_logic_variables := [p :: ty_privilege; "pc" :: ty_xlenbits; tvec :: ty_xlenbits];
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    :=
         cur_privilege ↦ term_var p
         ∗ pc ↦ term_var "pc"
         ∗ ∃ "mcause_val", mcause  ↦ term_var "mcause_val"
         ∗ ∃ "mpp", mstatus ↦ term_record rmstatus [term_var "mpp"]
         ∗ ∃ "mepc_val", mepc ↦ term_var "mepc_val"
         ∗ mtvec ↦ term_var tvec
         ∗ ∃ v, nextpc ↦ term_var v;
       sep_contract_result          := "result_handle_illegal";
       sep_contract_postcondition   :=
         term_var "result_handle_illegal" = term_val ty_unit tt
         ∗ cur_privilege ↦ term_val ty_privilege Machine
         ∗ pc ↦ term_var "pc"
         ∗ ∃ "mcause", mcause ↦ term_var "mcause"
         ∗ mstatus ↦ term_record rmstatus [ term_var p ]
         ∗ mepc ↦ term_var "pc"
         ∗ mtvec ↦ term_var tvec
         ∗ nextpc ↦ term_var tvec
    |}.

  Definition sep_contract_trap_handler : SepContractFun trap_handler :=
    {| sep_contract_logic_variables := [del_priv :: ty_privilege; c :: ty_exc_code; "pc" :: ty_xlenbits; p :: ty_privilege; tvec :: ty_xlenbits];
       sep_contract_localstore      := [term_var del_priv; term_var c; term_var "pc"];
       sep_contract_precondition    :=
         cur_privilege ↦ term_var p
         ∗ ∃ "mcause_val", mcause  ↦ term_var "mcause_val"
         ∗ ∃ "mstatus_val", mstatus ↦ term_var "mstatus_val"
         ∗ ∃ "mepc_val", mepc    ↦ term_var "mepc_val"
         ∗ mtvec ↦ term_var tvec;
       sep_contract_result          := "result_trap_handler";
       sep_contract_postcondition   :=
         term_var "result_trap_handler" = term_var tvec
         ∗ term_var del_priv = term_val ty_privilege Machine
         ∗ cur_privilege ↦ term_var del_priv
         ∗ mcause        ↦ term_var c
         ∗ mstatus       ↦ term_record rmstatus [ term_var p ]
         ∗ mepc          ↦ term_var "pc"
         ∗ mtvec         ↦ term_var tvec;
    |}.

  Definition sep_contract_prepare_trap_vector : SepContractFun prepare_trap_vector :=
    {| sep_contract_logic_variables := [p :: ty_privilege; cause :: ty_mcause; tvec :: ty_xlenbits];
       sep_contract_localstore      := [term_var p; term_var cause];
       sep_contract_precondition    := mtvec ↦ term_var tvec;
       sep_contract_result          := "result_prepare_trap_vector";
       sep_contract_postcondition   :=
         term_var "result_prepare_trap_vector" = term_var tvec
         ∗ term_var p = term_val ty_privilege Machine
         ∗ mtvec ↦ term_var tvec;
    |}.

  Definition sep_contract_tvec_addr : SepContractFun tvec_addr :=
    {| sep_contract_logic_variables := [m :: ty_xlenbits; c :: ty_mcause];
       sep_contract_localstore      := [term_var m; term_var c];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_tvec_addr";
       sep_contract_postcondition   :=
         term_var "result_tvec_addr" = term_inl (term_var m);
    |}.

  Definition sep_contract_exceptionType_to_bits : SepContractFun exceptionType_to_bits :=
    {| sep_contract_logic_variables := [e :: ty_exception_type];
       sep_contract_localstore      := [term_var e];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_exceptionType_to_bits";
       sep_contract_postcondition   :=
         ∃ result, term_var "result_exceptionType_to_bits" = term_var result
    |}.

  Definition sep_contract_exception_delegatee : SepContractFun exception_delegatee :=
    {| sep_contract_logic_variables := [p :: ty_privilege];
       sep_contract_localstore      := [term_var p];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_exception_delegatee";
       sep_contract_postcondition   :=
        term_var "result_exception_delegatee" = term_val ty_privilege Machine
    |}.

  Definition sep_contract_get_arch_pc : SepContractFun get_arch_pc :=
    {| sep_contract_logic_variables := [v :: ty_xlenbits];
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    := pc ↦ term_var v;
       sep_contract_result          := "result_get_arch_pc";
       sep_contract_postcondition   :=
         term_var "result_get_arch_pc" = term_var v
         ∗ pc ↦ term_var v;
    |}.

  Definition sep_contract_set_next_pc : SepContractFun set_next_pc :=
    {| sep_contract_logic_variables := [addr :: ty_xlenbits];
       sep_contract_localstore      := [term_var addr];
       sep_contract_precondition    := ∃ v, nextpc ↦ term_var v;
       sep_contract_result          := "result_set_next_pc";
       sep_contract_postcondition   :=
         term_var "result_set_next_pc" = term_val ty_unit tt
         ∗ nextpc ↦ term_var addr;
    |}.

  Definition sep_contract_get_next_pc : SepContractFun get_next_pc :=
    {| sep_contract_logic_variables := [v :: ty_xlenbits];
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    := nextpc ↦ term_var v;
       sep_contract_result          := "result_get_next_pc";
       sep_contract_postcondition   :=
         term_var "result_get_next_pc" = term_var v
         ∗ nextpc ↦ term_var v;
    |}.

  Definition sep_contract_tick_pc : SepContractFun tick_pc :=
    {| sep_contract_logic_variables := ["npc" :: ty_xlenbits];
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    := nextpc ↦ term_var "npc" ∗ ∃ "i", pc ↦ term_var "i";
       sep_contract_result          := "result_tick_pc";
       sep_contract_postcondition   :=
         term_var "result_tick_pc" = term_val ty_unit tt
         ∗ nextpc ↦ term_var "npc"
         ∗ pc     ↦ term_var "npc";
    |}.

  Definition sep_contract_rX : SepContractFun rX :=
    {| sep_contract_logic_variables := [rs :: ty_regno];
       sep_contract_localstore      := [term_var rs];
       sep_contract_precondition    := asn_gprs;
       sep_contract_result          := "result_rX";
       sep_contract_postcondition   := asn_gprs;
    |}.

  Definition sep_contract_wX : SepContractFun wX :=
    {| sep_contract_logic_variables := [rs :: ty_regno; v :: ty_xlenbits];
       sep_contract_localstore      := [term_var rs; term_var v];
       sep_contract_precondition    := asn_gprs;
       sep_contract_result          := "result_wX";
       sep_contract_postcondition   :=
         term_var "result_wX" = term_val ty_unit tt
         ∗ asn_gprs;
    |}.

  Definition sep_contract_abs : SepContractFun abs :=
    {| sep_contract_logic_variables := [v :: ty_int];
       sep_contract_localstore      := [term_var v];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_abs";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition sep_contract_step : SepContractFun step :=
    {| sep_contract_logic_variables := ["m" :: ty_privilege; "entries" :: ty_list ty_pmpentry];
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    :=
                     cur_privilege ↦ term_var "m" ∗
         ∃ "h",      mtvec         ↦ term_var "h" ∗
         ∃ "npc",    nextpc        ↦ term_var "npc" ∗
         ∃ "i",      pc            ↦ term_var "i" ∗
         ∃ "mcause", mcause        ↦ term_var "mcause" ∗
         ∃ "mepc",   mepc          ↦ term_var "mepc" ∗
         ∃ "mpp",    mstatus       ↦ term_record rmstatus [ term_var "mpp" ] ∗
                     asn_pmp_entries (term_var "entries") ∗
                     asn_pmp_addr_access (term_var "entries") (term_var "m") ∗
                     asn_gprs ;
       sep_contract_result          := "result_step";
       sep_contract_postcondition   := ∃ "p", ∃ "es",
         (           cur_privilege ↦ term_var "p" ∗
         ∃ "h",      mtvec         ↦ term_var "h" ∗
         ∃ "npc",   (nextpc        ↦ term_var "npc" ∗
                     pc            ↦ term_var "npc") ∗
         ∃ "mcause", mcause        ↦ term_var "mcause" ∗
         ∃ "mepc",   mepc          ↦ term_var "mepc" ∗
         ∃ "mpp",    mstatus       ↦ term_record rmstatus [ term_var "mpp" ] ∗
                     asn_pmp_entries (term_var "es") ∗
                     asn_pmp_addr_access (term_var "entries") (term_var "m") ∗
                     asn_gprs);
    |}.

  Definition sep_contract_fetch : SepContractFun fetch :=
    {| sep_contract_logic_variables := ["i" :: ty_xlenbits; p :: ty_privilege; "entries" :: ty_list ty_pmpentry];
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    :=
           pc ↦ term_var "i"
           ∗ cur_privilege ↦ term_var p
           ∗ asn_pmp_entries (term_var "entries")
           ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
       sep_contract_result          := "result_fetch";
       sep_contract_postcondition   :=
         pc ↦ term_var "i"
         ∗ cur_privilege ↦ term_var p
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
    |}.

  Definition sep_contract_init_model : SepContractFun init_model :=
    {| sep_contract_logic_variables := ctx.nil;
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    :=
         ∃ p, cur_privilege ↦ term_var p
         ∗ ∃ "es", asn_pmp_entries (term_var "es");
       sep_contract_result          := "result_init_model";
       sep_contract_postcondition   :=
         term_var "result_init_model" = term_val ty_unit tt
         ∗ cur_privilege ↦ term_val ty_privilege Machine
         ∗ ∃ "es", asn_pmp_entries (term_var "es");
    |}.

  Definition sep_contract_init_sys : SepContractFun init_sys :=
    {| sep_contract_logic_variables := ctx.nil;
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    :=
         ∃ p, cur_privilege ↦ term_var p
         ∗ ∃ "es", asn_pmp_entries (term_var "es");
       sep_contract_result          := "result_init_sys";
       sep_contract_postcondition   :=
         term_var "result_init_sys" = term_val ty_unit tt
         ∗ cur_privilege ↦ term_val ty_privilege Machine
         ∗ ∃ "es", asn_pmp_entries (term_var "es");
    |}.

  Definition sep_contract_init_pmp : SepContractFun init_pmp :=
    {| sep_contract_logic_variables := ctx.nil;
       sep_contract_localstore      := env.nil;
       sep_contract_precondition    :=
         ∃ "cfg0", pmp0cfg ↦ term_var "cfg0" ∗ ∃ "cfg1", pmp1cfg ↦ term_var "cfg1";
       sep_contract_result          := "result_init_pmp";
       sep_contract_postcondition   :=
         ∃ "cfg0", pmp0cfg ↦ term_var "cfg0" ∗ ∃ "cfg1", pmp1cfg ↦ term_var "cfg1"
         ∗ term_var "result_init_pmp" = term_val ty_unit tt;
    |}.

  Definition sep_contract_within_phys_mem : SepContractFun within_phys_mem :=
    {| sep_contract_logic_variables := [paddr :: ty_xlenbits];
       sep_contract_localstore      := [term_var paddr];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_within_phys_mem";
       sep_contract_postcondition   :=
         asn_if (term_var "result_within_phys_mem")
                (asn_bool (term_val ty_xlenbits minAddr <=ₜ term_var paddr)
                 ∗ asn_bool (term_var paddr <=ₜ term_val ty_xlenbits maxAddr))
                asn_true;
    |}.

  Definition sep_contract_checked_mem_read : SepContractFun checked_mem_read :=
    {| sep_contract_logic_variables := [t :: ty_access_type; paddr :: ty_xlenbits; p :: ty_privilege; "entries" :: ty_list ty_pmpentry];
       sep_contract_localstore      := [term_var t; term_var paddr];
       sep_contract_precondition    :=
           term_union access_type KRead (term_val ty_unit tt) ⊑ term_var t
           ∗ cur_privilege ↦ term_var p
           ∗ asn_pmp_entries (term_var "entries")
           ∗ asn_pmp_addr_access (term_var "entries") (term_var p)
           ∗ asn_pmp_access (term_var paddr) (term_var "entries") (term_var p) (term_var t);
       sep_contract_result          := "result_checked_mem_read";
       sep_contract_postcondition   :=
         cur_privilege ↦ term_var p
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var p)
    |}.

  Definition sep_contract_checked_mem_write : SepContractFun checked_mem_write :=
    {| sep_contract_logic_variables := [paddr :: ty_xlenbits; data :: ty_xlenbits; p :: ty_privilege; "entries" :: ty_list ty_pmpentry; acc :: ty_access_type];
       sep_contract_localstore      := [term_var paddr; term_var data];
       sep_contract_precondition    :=
          term_union access_type KWrite (term_val ty_unit tt) ⊑ term_var acc
          ∗ cur_privilege ↦ term_var p
          ∗ asn_pmp_entries (term_var "entries")
          ∗ asn_pmp_addr_access (term_var "entries") (term_var p)
          ∗ asn_pmp_access (term_var paddr) (term_var "entries") (term_var p) (term_var acc);
       sep_contract_result          := "result_checked_mem_write";
       sep_contract_postcondition   :=
         cur_privilege ↦ term_var p
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
    |}.

  Definition sep_contract_pmp_mem_read : SepContractFun pmp_mem_read :=
    {| sep_contract_logic_variables := [t :: ty_access_type; p :: ty_privilege; paddr :: ty_xlenbits; "entries" :: ty_list ty_pmpentry];
       sep_contract_localstore      := [term_var t; term_var p; term_var paddr];
       sep_contract_precondition    :=
           term_union access_type KRead (term_val ty_unit tt) ⊑ term_var t
         ∗ cur_privilege ↦ term_var p
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
       sep_contract_result          := "result_pmp_mem_read";
       sep_contract_postcondition   :=
         cur_privilege ↦ term_var p
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
    |}.

  Definition sep_contract_pmp_mem_write : SepContractFun pmp_mem_write :=
    {| sep_contract_logic_variables := [paddr :: ty_xlenbits; data :: ty_xlenbits; typ :: ty_access_type; priv :: ty_privilege; "entries" :: ty_list ty_pmpentry];
       sep_contract_localstore      := [term_var paddr; term_var data; term_var typ; term_var priv];
       sep_contract_precondition    := (* NOTE: only ever called with typ = Write *)
         (term_var typ = term_union access_type KWrite (term_val ty_unit tt)
          ∨ term_var typ = term_union access_type KReadWrite (term_val ty_unit tt))
         ∗ cur_privilege ↦ term_var priv
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var priv);
       sep_contract_result          := "result_pmp_mem_write";
       sep_contract_postcondition   :=
         cur_privilege ↦ term_var priv
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var priv);
    |}.

  Definition sep_contract_mem_write_value : SepContractFun mem_write_value :=
    {| sep_contract_logic_variables := [paddr :: ty_xlenbits; value :: ty_xlenbits; p :: ty_privilege; "entries" :: ty_list ty_pmpentry];
       sep_contract_localstore      := [term_var paddr; term_var value];
       sep_contract_precondition    :=
         cur_privilege ↦ term_var p
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
       sep_contract_result          := "result_pmp_mem_write";
       sep_contract_postcondition   :=
         cur_privilege ↦ term_var p
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
    |}.

  Definition sep_contract_mem_read : SepContractFun mem_read :=
    {| sep_contract_logic_variables := [typ :: ty_access_type; paddr :: ty_xlenbits; p :: ty_privilege; "entries" :: ty_list ty_pmpentry];
       sep_contract_localstore      := [term_var typ; term_var paddr];
       sep_contract_precondition    :=
          (term_var typ = term_union access_type KRead (term_val ty_unit tt)
           ∨ term_var typ = term_union access_type KExecute (term_val ty_unit tt))
         ∗ cur_privilege ↦ term_var p
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
       sep_contract_result          := "result_mem_read";
       sep_contract_postcondition   :=
         cur_privilege ↦ term_var p
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_addr_access (term_var "entries") (term_var p);
    |}.

  Definition sep_contract_pmpCheck : SepContractFun pmpCheck :=
    {| sep_contract_logic_variables := [addr :: ty_xlenbits; acc :: ty_access_type; priv :: ty_privilege; "entries" :: ty_list ty_pmpentry];
       sep_contract_localstore      := [term_var addr; term_var acc; term_var priv];
       sep_contract_precondition    :=
         asn_pmp_entries (term_var "entries");
       sep_contract_result          := "result_pmpCheck";
       sep_contract_postcondition   := 
         asn_match_option
           _ (term_var "result_pmpCheck") e
           (asn_pmp_entries (term_var "entries"))
           (asn_pmp_entries (term_var "entries") ∗ asn_pmp_access (term_var addr) (term_var "entries") (term_var priv) (term_var acc));
    |}.

  Definition sep_contract_pmpCheckPerms : SepContractFun pmpCheckPerms :=
    let Σ : LCtx := [acc :: ty_access_type; priv :: ty_privilege; L :: ty_bool; A :: ty_pmpaddrmatchtype; X :: ty_bool; W :: ty_bool; R :: ty_bool] in
    let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := [nenv entry; term_var acc; term_var priv];
       sep_contract_precondition    :=
         asn_true;
       sep_contract_result          := "result_pmpCheckPerms";
       sep_contract_postcondition   :=
         let entry := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
         asn_if (term_var "result_pmpCheckPerms")
                (asn_pmp_check_perms entry (term_var acc) (term_var priv))
                asn_true;
    |}.

  Definition sep_contract_pmpCheckRWX : SepContractFun pmpCheckRWX :=
    let Σ : LCtx := [acc :: ty_access_type; L :: ty_bool; A :: ty_pmpaddrmatchtype; X :: ty_bool; W :: ty_bool; R :: ty_bool] in
    let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := [nenv entry; term_var acc];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpCheckRWX";
       sep_contract_postcondition   :=
         let entry := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
         asn_if (term_var "result_pmpCheckRWX")
                (asn_pmp_check_rwx entry (term_var acc))
                asn_true;
    |}.

  Definition sep_contract_pmpAddrRange : SepContractFun pmpAddrRange :=
    let Σ : LCtx := [pmpaddr :: ty_xlenbits; prev_pmpaddr :: ty_xlenbits; L :: ty_bool; A :: ty_pmpaddrmatchtype; X :: ty_bool; W :: ty_bool; R :: ty_bool] in
    let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := [nenv entry; term_var pmpaddr; term_var prev_pmpaddr];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpAddrRange";
       sep_contract_postcondition   :=
         asn_match_enum pmpaddrmatchtype (term_var A)
           (fun K => match K with
                     | OFF => term_var "result_pmpAddrRange" = term_inr (term_val ty_unit tt)
                     | TOR => term_var "result_pmpAddrRange" = term_inl (term_var prev_pmpaddr ,ₜ term_var pmpaddr)
                     end);
    |}.

  Definition sep_contract_pmpMatchAddr : SepContractFun pmpMatchAddr :=
    {| sep_contract_logic_variables := [addr :: ty_xlenbits; rng :: ty_pmp_addr_range];
       sep_contract_localstore      := [term_var addr; term_var rng];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpMatchAddr";
       sep_contract_postcondition   :=
         asn_match_option
           _ (term_var rng) v
           (asn_match_prod
              (term_var v) lo hi
              (asn_match_enum pmpaddrmatch (term_var "result_pmpMatchAddr")
                (fun K => match K with
                          | PMP_NoMatch =>
                              asn_bool (term_var hi <ₜ term_var lo) ∨ asn_bool (term_var addr <ₜ term_var lo ||ₜ term_var hi <=ₜ term_var addr) ∨ term_var rng = term_inr (term_val ty_unit tt)
                          | PMP_PartialMatch => asn_bool
                                                  (term_not
                                                     (term_var lo <=ₜ term_var addr &&ₜ term_var addr <ₜ term_var hi))
                          | PMP_Match => asn_formula (formula_bool (term_var lo <=ₜ term_var addr)) ∗ asn_formula (formula_bool (term_var addr <ₜ term_var hi))
                        end)))
              (term_var "result_pmpMatchAddr" = term_val ty_pmpaddrmatch PMP_NoMatch);
    |}.

  Definition sep_contract_pmpMatchEntry : SepContractFun pmpMatchEntry :=
    let Σ : LCtx := [addr :: ty_xlenbits; acc :: ty_access_type; priv :: ty_privilege; ent :: ty_pmpcfg_ent; pmpaddr :: ty_xlenbits; prev_pmpaddr :: ty_xlenbits; L :: ty_bool; A :: ty_pmpaddrmatchtype; X :: ty_bool; W :: ty_bool; R :: ty_bool] in
    let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := [nenv term_var addr; term_var acc; term_var priv; entry; term_var pmpaddr; term_var prev_pmpaddr];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpMatchEntry";
       sep_contract_postcondition   :=
         let entry := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
         asn_match_enum pmpmatch (term_var "result_pmpMatchEntry")
                        (fun K => match K with
                                  | PMP_Continue =>
                                      asn_bool (term_var pmpaddr <ₜ term_var prev_pmpaddr) ∨ asn_bool (term_var addr <ₜ term_var prev_pmpaddr ||ₜ term_var pmpaddr <=ₜ term_var addr) ∨ term_var A = term_val ty_pmpaddrmatchtype OFF
                                  | PMP_Fail     =>
                                                  asn_bool (term_not
                                                              (term_var prev_pmpaddr <=ₜ term_var addr &&ₜ term_var addr <ₜ term_var pmpaddr)) ∨ 
                                      asn_true (* TODO: either we have a partial match, or we don't have the required permissions! *)
                                  | PMP_Success  =>
                                      asn_bool (term_var prev_pmpaddr <=ₜ term_var addr &&ₜ term_var addr <ₜ term_var pmpaddr) ∗
                                      asn_pmp_check_perms entry (term_var acc) (term_var priv)
                                  end);
    |}.

  Definition sep_contract_pmpLocked : SepContractFun pmpLocked :=
    let Σ : LCtx := [L :: ty_bool; A :: ty_pmpaddrmatchtype; X :: ty_bool; W :: ty_bool; R :: ty_bool] in
    let entry : Term Σ _ := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := env.snoc env.nil (_::_) entry;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpLocked";
       sep_contract_postcondition   := term_var "result_pmpLocked" = term_var L;
    |}.

  Definition sep_contract_pmpWriteCfg : SepContractFun pmpWriteCfg :=
    {| sep_contract_logic_variables := [cfg :: ty_pmpcfg_ent; value :: ty_xlenbits];
       sep_contract_localstore      := [term_var cfg; term_var value];
       sep_contract_precondition    := asn_expand_pmpcfg_ent (term_var cfg);
       sep_contract_result          := "result_pmpWriteCfg";
       sep_contract_postcondition   :=
         ∃ "cfg", term_var "result_pmpWriteCfg" = term_var "cfg";
    |}.

  Definition sep_contract_pmpWriteCfgReg : SepContractFun pmpWriteCfgReg :=
    {| sep_contract_logic_variables := [idx :: ty_pmpcfgidx; value :: ty_xlenbits];
       sep_contract_localstore      := [term_var idx; term_var value];
       sep_contract_precondition    :=
         ∃ "cfg0", (pmp0cfg ↦ term_var "cfg0" ∗ asn_expand_pmpcfg_ent (term_var "cfg0"))
         ∗ ∃ "cfg1", (pmp1cfg ↦ term_var "cfg1" ∗ asn_expand_pmpcfg_ent (term_var "cfg1"));
       sep_contract_result          := "result_pmpWriteCfgReg";
       sep_contract_postcondition   :=
         term_var "result_pmpWriteCfgReg" = term_val ty_unit tt
         ∗ ∃ "cfg0", pmp0cfg ↦ term_var "cfg0"
         ∗ ∃ "cfg1", pmp1cfg ↦ term_var "cfg1";
    |}.

  Definition sep_contract_pmpWriteAddr : SepContractFun pmpWriteAddr :=
    {| sep_contract_logic_variables := [locked :: ty_bool; addr :: ty_xlenbits; value :: ty_xlenbits];
       sep_contract_localstore      := [term_var locked; term_var addr; term_var value];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_pmpWriteAddr";
       sep_contract_postcondition   :=
         asn_if (term_var locked)
                (term_var "result_pmpWriteAddr" = term_var addr)
                (term_var "result_pmpWriteAddr" = term_var value);
    |}.

  Definition sep_contract_read_ram : SepContractFunX read_ram :=
    {| sep_contract_logic_variables := [paddr :: ty_xlenbits; w :: ty_xlenbits; "entries" :: ty_list ty_pmpentry; p :: ty_privilege; t :: ty_access_type];
       sep_contract_localstore      := [term_var paddr];
       sep_contract_precondition    :=
         term_union access_type KRead (term_val ty_unit tt) ⊑ term_var t
         ∗ cur_privilege ↦ term_var p
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_access (term_var paddr) (term_var "entries") (term_var p) (term_var t) (* TODO: move predicates that do unification earlier in the precond *)
         ∗ term_var paddr ↦ₘ term_var w;
       sep_contract_result          := "result_read_ram";
       sep_contract_postcondition   := term_var "result_read_ram" = term_var w
        ∗ cur_privilege ↦ term_var p
        ∗ term_var paddr ↦ₘ term_var w
        ∗ asn_pmp_entries (term_var "entries");
    |}.

  Definition sep_contract_write_ram : SepContractFunX write_ram :=
    {| sep_contract_logic_variables := [paddr :: ty_int; data :: ty_word; "entries" :: ty_list ty_pmpentry; p :: ty_privilege; t :: ty_access_type];
       sep_contract_localstore      := [term_var paddr; term_var data];
       sep_contract_precondition    :=
         term_union access_type KWrite (term_val ty_unit tt) ⊑ term_var t
         ∗ cur_privilege ↦ term_var p
         ∗ asn_pmp_entries (term_var "entries")
         ∗ asn_pmp_access (term_var paddr) (term_var "entries") (term_var p) (term_var t)
         ∗ ∃ w, term_var paddr ↦ₘ term_var w;
       sep_contract_result          := "result_write_ram";
       sep_contract_postcondition   :=
         cur_privilege ↦ term_var p
         ∗ term_var paddr ↦ₘ term_var data
         ∗ asn_pmp_entries (term_var "entries");
    |}.

  Definition sep_contract_decode    : SepContractFunX decode :=
    {| sep_contract_logic_variables := [bv :: ty_int];
       sep_contract_localstore      := [term_var bv];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_decode";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition lemma_open_gprs : SepLemma open_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := asn_gprs;
       lemma_postcondition   := asn_regs_ptsto;
    |}.

  Definition lemma_close_gprs : SepLemma close_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := asn_regs_ptsto;
       lemma_postcondition   := asn_gprs;
    |}.

  Definition lemma_open_pmp_entries : SepLemma open_pmp_entries :=
    {| lemma_logic_variables := ["entries" :: ty_list ty_pmpentry];
       lemma_patterns        := env.nil;
       lemma_precondition    := asn_pmp_entries (term_var "entries");
       lemma_postcondition   := ∃ "cfg0", ∃ "addr0", ∃ "cfg1", ∃ "addr1",
          (pmp0cfg ↦ term_var "cfg0" ∗ pmpaddr0 ↦ term_var "addr0" ∗
           pmp1cfg ↦ term_var "cfg1" ∗ pmpaddr1 ↦ term_var "addr1" ∗
           asn_expand_pmpcfg_ent (term_var "cfg0") ∗
           asn_expand_pmpcfg_ent (term_var "cfg1") ∗
           term_var "entries" = term_list [(term_var "cfg0" ,ₜ term_var "addr0");
                                           (term_var "cfg1" ,ₜ term_var "addr1")]);
    |}.

  Definition lemma_close_pmp_entries : SepLemma close_pmp_entries :=
    {| lemma_logic_variables := ["entries" :: ty_list ty_pmpentry];
       lemma_patterns        := env.nil;
       lemma_precondition    := ∃ "cfg0", ∃ "addr0", ∃ "cfg1", ∃ "addr1",
         (pmp0cfg ↦ term_var "cfg0" ∗ pmpaddr0 ↦ term_var "addr0" ∗
          pmp1cfg ↦ term_var "cfg1" ∗ pmpaddr1 ↦ term_var "addr1" ∗
          asn_expand_pmpcfg_ent (term_var "cfg0") ∗
          asn_expand_pmpcfg_ent (term_var "cfg1") ∗
          term_var "entries" = term_list [(term_var "cfg0" ,ₜ term_var "addr0");
                                          (term_var "cfg1" ,ₜ term_var "addr1")]);
       lemma_postcondition   := asn_pmp_entries (term_var "entries");
    |}.

  Definition lemma_update_pmp_entries : SepLemma update_pmp_entries :=
    {| lemma_logic_variables := ["cfg0" :: ty_pmpcfg_ent; "addr0" :: ty_xlenbits; "cfg1" :: ty_pmpcfg_ent; "addr1" :: ty_xlenbits];
       lemma_patterns        := env.nil;
       lemma_precondition    :=
         pmp0cfg ↦ term_var "cfg0" ∗ pmpaddr0 ↦ term_var "addr0" ∗
         pmp1cfg ↦ term_var "cfg1" ∗ pmpaddr1 ↦ term_var "addr1" ∗
         cur_privilege ↦ term_val ty_privilege Machine;
       lemma_postcondition   :=
         cur_privilege ↦ term_val ty_privilege Machine ∗
         asn_pmp_entries (term_list [(term_var "cfg0" ,ₜ term_var "addr0");
                                     (term_var "cfg1" ,ₜ term_var "addr1")]);
    |}.

  Definition lemma_extract_pmp_ptsto : SepLemma extract_pmp_ptsto :=
    {| lemma_logic_variables := [paddr :: ty_xlenbits; acc :: ty_access_type; "entries" :: ty_list ty_pmpentry; p :: ty_privilege];
       lemma_patterns        := [term_var paddr];
       lemma_precondition    :=
          asn_pmp_entries (term_var "entries")
          ∗ asn_pmp_addr_access (term_var "entries") (term_var p)
          ∗ asn_bool (term_val ty_xlenbits minAddr <=ₜ term_var paddr)
          ∗ asn_bool (term_var paddr <=ₜ term_val ty_xlenbits maxAddr)
          ∗ asn_pmp_access (term_var paddr) (term_var "entries") (term_var p) (term_var acc);
       lemma_postcondition   :=
          asn_pmp_entries (term_var "entries")
          ∗ asn_pmp_addr_access_without (term_var paddr) (term_var "entries") (term_var p)
          ∗ ∃ "w", term_var paddr ↦ₘ term_var w;
    |}.

  Definition lemma_return_pmp_ptsto : SepLemma return_pmp_ptsto :=
    {| lemma_logic_variables := [paddr :: ty_xlenbits; "entries" :: ty_list ty_pmpentry; p :: ty_privilege];
       lemma_patterns        := [term_var paddr];
       lemma_precondition    :=
          asn_pmp_entries (term_var "entries")
          ∗ asn_pmp_addr_access_without (term_var paddr) (term_var "entries") (term_var p)
          ∗ ∃ "w", term_var paddr ↦ₘ term_var w;
       lemma_postcondition   :=
          asn_pmp_entries (term_var "entries")
          ∗ asn_pmp_addr_access (term_var "entries") (term_var p)
    |}.

  End Contracts.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | execute_RTYPE         => Some sep_contract_execute_RTYPE
      | execute_ITYPE         => Some sep_contract_execute_ITYPE
      | execute_UTYPE         => Some sep_contract_execute_UTYPE
      | execute_BTYPE         => Some sep_contract_execute_BTYPE
      | execute_RISCV_JAL     => Some sep_contract_execute_RISCV_JAL
      | execute_RISCV_JALR    => Some sep_contract_execute_RISCV_JALR
      | execute_ECALL         => Some sep_contract_execute_ECALL
      | execute_MRET          => Some sep_contract_execute_MRET
      | execute_CSR           => Some sep_contract_execute_CSR
      | execute_STORE         => Some sep_contract_execute_STORE
      | execute_LOAD          => Some sep_contract_execute_LOAD
      | process_load          => Some sep_contract_process_load
      | get_arch_pc           => Some sep_contract_get_arch_pc
      | get_next_pc           => Some sep_contract_get_next_pc
      | set_next_pc           => Some sep_contract_set_next_pc
      | tick_pc               => Some sep_contract_tick_pc
      | exception_handler     => Some sep_contract_exception_handler
      | handle_mem_exception  => Some sep_contract_handle_mem_exception
      | handle_illegal        => Some sep_contract_handle_illegal
      | trap_handler          => Some sep_contract_trap_handler
      | prepare_trap_vector   => Some sep_contract_prepare_trap_vector
      | tvec_addr             => Some sep_contract_tvec_addr
      | exceptionType_to_bits => Some sep_contract_exceptionType_to_bits
      | exception_delegatee   => Some sep_contract_exception_delegatee
      | rX                    => Some sep_contract_rX
      | wX                    => Some sep_contract_wX
      | abs                   => Some sep_contract_abs
      | within_phys_mem       => Some sep_contract_within_phys_mem
      | readCSR               => Some sep_contract_readCSR
      | writeCSR              => Some sep_contract_writeCSR
      | check_CSR             => Some sep_contract_check_CSR
      | is_CSR_defined        => Some sep_contract_is_CSR_defined
      | check_CSR_access      => Some sep_contract_check_CSR_access
      | privLevel_to_bits     => Some sep_contract_privLevel_to_bits
      | csrAccess             => Some sep_contract_csrAccess
      | csrPriv               => Some sep_contract_csrPriv
      | checked_mem_read      => Some sep_contract_checked_mem_read
      | checked_mem_write     => Some sep_contract_checked_mem_write
      | pmp_mem_read          => Some sep_contract_pmp_mem_read
      | pmp_mem_write         => Some sep_contract_pmp_mem_write
      | pmpCheck              => Some sep_contract_pmpCheck
      | pmpCheckPerms         => Some sep_contract_pmpCheckPerms
      | pmpCheckRWX           => Some sep_contract_pmpCheckRWX
      | pmpAddrRange          => Some sep_contract_pmpAddrRange
      | pmpMatchAddr          => Some sep_contract_pmpMatchAddr
      | pmpMatchEntry         => Some sep_contract_pmpMatchEntry
      | pmpLocked             => Some sep_contract_pmpLocked
      | pmpWriteCfgReg        => Some sep_contract_pmpWriteCfgReg
      | pmpWriteCfg           => Some sep_contract_pmpWriteCfg
      | pmpWriteAddr          => Some sep_contract_pmpWriteAddr
      | mem_write_value       => Some sep_contract_mem_write_value
      | mem_read              => Some sep_contract_mem_read
      | init_model            => Some sep_contract_init_model
      | init_sys              => Some sep_contract_init_sys
      | init_pmp              => Some sep_contract_init_pmp
      | fetch                 => Some sep_contract_fetch
      | execute               => Some sep_contract_execute
      | step                  => Some sep_contract_step
      | _                     => None
      end.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | read_ram             => sep_contract_read_ram
      | write_ram            => sep_contract_write_ram
      | decode               => sep_contract_decode
      | mstatus_from_bits    => sep_contract_mstatus_from_bits
      | mstatus_to_bits      => sep_contract_mstatus_to_bits
      | pmpcfg_ent_from_bits => sep_contract_pmpcfg_ent_from_bits
      | pmpcfg_ent_to_bits   => sep_contract_pmpcfg_ent_to_bits
      end.

  Definition LEnv : LemmaEnv :=
    fun Δ l =>
      match l with
      | open_gprs             => lemma_open_gprs
      | close_gprs            => lemma_close_gprs
      | open_pmp_entries      => lemma_open_pmp_entries
      | close_pmp_entries     => lemma_close_pmp_entries
      | update_pmp_entries    => lemma_update_pmp_entries
      | extract_pmp_ptsto     => lemma_extract_pmp_ptsto
      | return_pmp_ptsto      => lemma_return_pmp_ptsto
      end.

  Lemma linted_cenvex :
    forall Δ τ (f : FunX Δ τ),
      Linted (CEnvEx f).
  Proof.
    intros ? ? []; try constructor.
  Qed.

End ContractDefKit.

Include SpecificationMixin RiscvPmpBase RiscvPmpProgram.

End RiscvPmpSpecification.

Module RiscvPmpSolverKit <: SolverKit RiscvPmpBase RiscvPmpSpecification.
  (* TODO: User predicates can be simplified smarter *)
  Equations(noeqns) decide_pmp_check_rwx {Σ} (X W R : Term Σ ty_bool) (acc : Term Σ ty_access_type) : bool :=
  | term_val true | _             | _             | term_union KExecute (term_val tt)   := true;
  | _             | term_val true | _             | term_union KWrite (term_val tt)     := true;
  | _             | _             | term_val true | term_union KRead (term_val tt)      := true;
  | _             | term_val true | term_val true | term_union KReadWrite (term_val tt) := true;
  | _             | _             | _             | _                                   := false.

  Equations(noeqns) simplify_sub_perm {Σ} (a1 a2 : Term Σ ty_access_type) : option (List Formula Σ) :=
  | term_val a1 | term_val a2 := if decide_sub_perm a1 a2 then Some nil else None;
  | a1          | a2          := Some (cons (formula_user sub_perm [a1;a2]) nil).

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

  Equations(noeqns) simplify_prev_addr {Σ} (cfg : Term Σ ty_pmpcfgidx) (entries : Term Σ (ty_list ty_pmpentry)) (prev : Term Σ ty_xlenbits) : option (List Formula Σ) :=
  | term_val cfg | term_val entries | term_val prev := if decide_prev_addr cfg entries prev then Some nil else None;
  | cfg          | entries          | prev          :=
    Some (cons (formula_user prev_addr [cfg; entries; prev]) nil).

  Equations(noeqns) simplify_pmp_access {Σ} (paddr : Term Σ ty_xlenbits) (es : Term Σ (ty_list ty_pmpentry)) (p : Term Σ ty_privilege) (acc : Term Σ ty_access_type) : option (List Formula Σ) :=
  | term_val paddr | term_val entries | term_val p | acc :=
    match decide_pmp_access paddr entries p with
    | (true, Some typ) => simplify_sub_perm (term_val ty_access_type typ) acc
    | (true, None)     => Some nil
    | (false, _)       => None
    end
  | paddr          | entries          | p          | acc          :=
    Some (cons (formula_user pmp_access [paddr; entries; p; acc]) nil).

  Definition simplify_user {Σ} (p : 𝑷) : Env (Term Σ) (𝑷_Ty p) -> option (List Formula Σ) :=
    match p with
    | pmp_access      => fun ts =>
                           let (ts,perm)    := env.snocView ts in
                           let (ts,priv)    := env.snocView ts in
                           let (ts,entries) := env.snocView ts in
                           let (ts,paddr)   := env.snocView ts in
                           simplify_pmp_access paddr entries priv perm
    | pmp_check_perms => fun ts =>
                           let (ts,priv)    := env.snocView ts in
                           let (ts,acc) := env.snocView ts in
                           let (ts,cfg)   := env.snocView ts in
                           simplify_pmp_check_perms cfg acc priv
    | pmp_check_rwx   => fun ts =>
                           let (ts,acc) := env.snocView ts in
                           let (ts,cfg)   := env.snocView ts in
                           simplify_pmp_check_rwx cfg acc
    | sub_perm        => fun ts =>
                           let (ts,a2) := env.snocView ts in
                           let (ts,a1) := env.snocView ts in
                           simplify_sub_perm a1 a2
    | within_cfg      => fun ts =>
                           let (ts,addr) := env.snocView ts in
                           let (ts,prev_addr)     := env.snocView ts in
                           let (ts,cfg)     := env.snocView ts in
                           let (ts,paddr)   := env.snocView ts in
                           simplify_within_cfg paddr cfg prev_addr addr
    | not_within_cfg  => fun ts =>
                           let (ts,entries) := env.snocView ts in
                           let (ts,paddr)   := env.snocView ts in
                           Some (cons (formula_user not_within_cfg [paddr; entries]) nil)
    | prev_addr       => fun ts =>
                           let (ts,prev)    := env.snocView ts in
                           let (ts,entries) := env.snocView ts in
                           let (ts,cfg)     := env.snocView ts in
                           simplify_prev_addr cfg entries prev
    | in_entries      => fun ts =>
                           let (ts,prev)    := env.snocView ts in
                           let (ts,entries) := env.snocView ts in
                           let (ts,cfg)     := env.snocView ts in
                           Some (cons (formula_user in_entries [cfg; entries; prev]) nil)
    end.

  Definition simplify_formula {Σ} (fml : Formula Σ) : option (List Formula Σ) :=
    match fml with
    | formula_user p ts => simplify_user p ts
    | _                 => Some (cons fml nil)
    end.

  Import base.
  Definition simplify_all {Σ} (g : Formula Σ -> option (List Formula Σ)) :=
    fix simplify_all (fmls k : List Formula Σ) {struct fmls} : option (List Formula Σ) :=
      match fmls with
      | nil => Some k
      | cons fml0 fmls =>
        ks ← simplify_all fmls k ;
        k0 ← g fml0 ;
        Some (app k0 ks)
      end.

  Definition solver : Solver :=
    fun w fmls => option_map (fun l => existT w (tri_id , l)) (simplify_all simplify_formula fmls nil).
  Definition solver_spec : SolverSpec solver.
  Admitted.
End RiscvPmpSolverKit.
Module RiscvPmpSolver := MakeSolver RiscvPmpBase RiscvPmpSpecification RiscvPmpSolverKit.

Module Import RiscvPmpExecutor :=
  MakeExecutor RiscvPmpBase RiscvPmpSpecification RiscvPmpSolver.
Import SMut.
Import SMut.SMutNotations.
Import Postprocessing.

Notation "r '↦' val" := (chunk_ptsreg r val) (at level 79).

Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
  match CEnv f with
  | Some c => ValidContractReflect c (FunDef f)
  | None => False
  end.

Definition ValidContractDebug {Δ τ} (f : Fun Δ τ) : Prop :=
  match CEnv f with
  | Some c => SMut.ValidContract c (FunDef f)
  | None => False
  end.

Section Debug.
  Coercion stm_exp : Exp >-> Stm.
  Local Notation "'use' 'lemma' lem args" := (stm_lemma lem args%env) (at level 10, lem at next level) : exp_scope.
  Local Notation "'use' 'lemma' lem" := (stm_lemma lem env.nil) (at level 10, lem at next level) : exp_scope.
  Local Notation "a '↦ₘ' t" := (asn_chunk (chunk_user ptsto [a; t])) (at level 70).
  Local Notation "p '∗' q" := (asn_sep p q).
  Local Notation "a '=' b" := (asn_eq a b).
  Local Notation "'∃' w ',' a" := (asn_exist w _ a) (at level 79, right associativity).

  (* Import RiscvNotations.
     Import RiscvμSailNotations. *)
  Import SymProp.notations.

End Debug.

Lemma valid_contract_step : ValidContract step.
Proof. reflexivity. Qed.

Lemma valid_contract_pmpWriteCfgReg : ValidContract pmpWriteCfgReg.
Proof. reflexivity. Qed.

Lemma valid_contract_pmpWriteCfg : ValidContract pmpWriteCfg.
Proof. reflexivity. Qed.

Lemma valid_contract_pmpWriteAddr : ValidContract pmpWriteAddr.
Proof. reflexivity. Qed.

Lemma valid_contract_init_model : ValidContract init_model.
Proof. reflexivity. Qed.

Lemma valid_contract_fetch : ValidContract fetch.
Proof. reflexivity. Qed.

Lemma valid_contract_execute : ValidContract execute.
Proof. reflexivity. Qed.

Lemma valid_contract_init_sys : ValidContract init_sys.
Proof. reflexivity. Qed.

Lemma valid_contract_init_pmp : ValidContract init_pmp.
Proof. reflexivity. Qed.

Lemma valid_contract_handle_mem_exception : ValidContract handle_mem_exception.
Proof. reflexivity. Qed.

Lemma valid_contract_mem_write_value : ValidContract mem_write_value.
Proof. reflexivity. Qed.

Lemma valid_contract_mem_read : ValidContractDebug mem_read.
Proof.
  compute; constructor; cbn.
  intros typ paddr p entries; repeat split; auto.
Qed.

Lemma valid_contract_process_load : ValidContract process_load.
Proof. reflexivity. Qed.

Lemma valid_contract_checked_mem_read : ValidContractDebug checked_mem_read.
Proof.
  compute.
  constructor.
  cbn.
  intros acc paddr p entries Hsub Hacc **.
  firstorder.
Qed.

Lemma valid_contract_checked_mem_write : ValidContractDebug checked_mem_write.
Proof.
  compute.
  constructor.
  cbn.
  intros addr _ p entries acc.
  repeat split; firstorder.
Qed.

Lemma valid_contract_pmp_mem_read : ValidContract pmp_mem_read.
Proof. reflexivity. Qed.

Lemma valid_contract_pmp_mem_write : ValidContractDebug pmp_mem_write.
Proof.
  compute.
  constructor.
  cbn.
  firstorder.
Qed.

Lemma valid_contract_pmpCheckRWX : ValidContract pmpCheckRWX.
Proof. reflexivity. Qed.
  
Lemma valid_contract_pmpCheckPerms : ValidContract pmpCheckPerms.
Proof. reflexivity. Qed.

Lemma valid_contract_pmpAddrRange : ValidContract pmpAddrRange.
Proof. reflexivity. Qed.

Lemma valid_contract_pmpMatchAddr : ValidContract pmpMatchAddr.
Proof. reflexivity. Qed.

Lemma valid_contract_pmpMatchEntry : ValidContract pmpMatchEntry.
Proof. reflexivity. Qed.

Lemma valid_contract_pmpLocked : ValidContract pmpLocked.
Proof. reflexivity. Qed.

Lemma valid_contract_readCSR : ValidContract readCSR.
Proof. reflexivity. Qed.

Lemma valid_contract_writeCSR : ValidContract writeCSR.
Proof. reflexivity. Qed.

Lemma valid_contract_check_CSR : ValidContract check_CSR.
Proof. reflexivity. Qed.

Lemma valid_contract_is_CSR_defined : ValidContract is_CSR_defined.
Proof. reflexivity. Qed.

Lemma valid_contract_check_CSR_access : ValidContract check_CSR_access.
Proof. reflexivity. Qed.

Lemma valid_contract_csrAccess : ValidContract csrAccess.
Proof. reflexivity. Qed.

Lemma valid_contract_csrPriv : ValidContract csrPriv.
Proof. reflexivity. Qed.

Lemma valid_contract_privLevel_to_bits : ValidContract privLevel_to_bits.
Proof. reflexivity. Qed.

Lemma valid_contract_exception_handler : ValidContract exception_handler.
Proof. reflexivity. Qed.

Lemma valid_contract_handle_illegal : ValidContract handle_illegal.
Proof. reflexivity. Qed.

Lemma valid_contract_trap_handler : ValidContract trap_handler.
Proof. reflexivity. Qed.

Lemma valid_contract_prepare_trap_vector : ValidContract prepare_trap_vector.
Proof. reflexivity. Qed.

Lemma valid_contract_tvec_addr : ValidContract tvec_addr.
Proof. reflexivity. Qed.

Lemma valid_contract_exceptionType_to_bits : ValidContract exceptionType_to_bits.
Proof. reflexivity. Qed.

Lemma valid_contract_exception_delegatee : ValidContract exception_delegatee.
Proof. reflexivity. Qed.

Lemma valid_contract_get_arch_pc : ValidContract get_arch_pc.
Proof. reflexivity. Qed.

Lemma valid_contract_get_next_pc : ValidContract get_next_pc.
Proof. reflexivity. Qed.

Lemma valid_contract_set_next_pc : ValidContract set_next_pc.
Proof. reflexivity. Qed.

Lemma valid_contract_tick_pc : ValidContract tick_pc.
Proof. reflexivity. Qed.

Lemma valid_contract_rX : ValidContract rX.
Proof. reflexivity. Qed.

Lemma valid_contract_wX : ValidContract wX.
Proof. reflexivity. Qed.

Lemma valid_contract_abs : ValidContract abs.
Proof. reflexivity. Qed.

Lemma valid_contract_within_phys_mem : ValidContract within_phys_mem.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_RTYPE : ValidContract execute_RTYPE.
Proof. reflexivity. Qed. 

Lemma valid_contract_execute_ITYPE : ValidContract execute_ITYPE.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_UTYPE : ValidContract execute_UTYPE.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_BTYPE : ValidContract execute_BTYPE.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_RISCV_JAL : ValidContract execute_RISCV_JAL.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_RISCV_JALR : ValidContract execute_RISCV_JALR.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_ECALL : ValidContract execute_ECALL.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_MRET : ValidContract execute_MRET.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_STORE : ValidContract execute_STORE.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_LOAD : ValidContract execute_LOAD.
Proof. reflexivity. Qed.

Lemma valid_contract_execute_CSR : ValidContract execute_CSR.
Proof. reflexivity. Qed.

(* TODO: the pmpCheck contract requires some manual proof effort in the case
         that no pmp entry matches (i.e. we end up in the final check of
         the unrolled loop, more specifically the match on the privilege level,
         and the Machine case (= the check is true)
   Ideas:
   - A lemma capturing the different conditions that can arise that lead to those
     cases (have the conditions as precond, and asn_pmp_access ... as postcond,
     we can then proof it sound in the model (which should be equivalent to what        
     is currently happening in the proof below, but we should be able to define
     the contract is one that can be proven by reflexivity))
 *)
Lemma valid_contract_pmpCheck : ValidContractDebug pmpCheck.
Proof. (* NOTE: this proof holds, it's just quite slow (the cbn takes a few minutes *)
  (* compute.
  constructor.

  unfold SymProp.safe.
  intros addr acc priv addr0 addr1 R0 W0 X0 A0 L0 R1 W1 X1 A1 L1.
  cbn.
  cbn in *.
  eexists; try repeat constructor;
    unfold Pmp_access, decide_pmp_access, pmp_check,
    pmp_match_entry, pmp_match_addr;
    destruct A0; destruct A1; simpl; auto;
    repeat match goal with
           | H: ?x < ?y |- _ =>
               apply Z.ltb_lt in H as [= ->]
           | H: (?x || ?y)%bool = true |- _ =>
               apply Bool.orb_prop in H as [[= ->]|[= ->]]
           end; auto;
    rewrite ?Bool.orb_true_r;
    simpl;
    auto;
    destruct (addr1 <? addr0); auto;
    destruct (addr0 <? 0); auto. *)
Abort.

(* TODO: this is just to make sure that all contracts defined so far are valid
         (i.e. ensure no contract was defined and then forgotten to validate it) *)
Lemma defined_contracts_valid : forall {Δ τ} (f : Fun Δ τ),
    match CEnv f with
    | Some c => ValidContract f
    | None => True
    end.
Proof.
  destruct f; simpl; trivial;
    try reflexivity.
Admitted.

