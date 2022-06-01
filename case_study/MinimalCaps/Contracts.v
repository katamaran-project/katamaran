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

From MinimalCaps Require Import
     Machine.

From Coq Require Import
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Notations
     Specification
     Shallow.Executor
     Symbolic.Mutator
     Symbolic.Solver.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Inductive PurePredicate : Set :=
| subperm
.

Inductive Predicate : Set :=
  ptsreg
| ptsto
| safe
| expression
| dummy
| gprs
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

Module Import MinCapsSignature <: ProgramLogicSignature MinCapsBase.
  Module PROG := MinCapsProgram.

Section PredicateKit.
  Definition 𝑷 := PurePredicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    | subperm => [ty.perm; ty.perm]
    end.

  (* Permission Lattice:
    RW
     |
     R
     |
     E
     |
     O *)
  Definition decide_subperm (p p' : Val ty.perm) : bool :=
    match p with
    | O => true
    | E => match p' with
           | O => false
           | _ => true
           end
    | R => match p' with
           | O => false
           | E => false
           | _ => true
           end
    | RW => match p' with
            | RW => true
            | _ => false
            end
    end.

  Definition Subperm (p p' : Val ty.perm) : Prop :=
    decide_subperm p p' = true.

  Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
    match p with
    | subperm => Subperm
    end.

  Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

  Definition 𝑯 := Predicate.
  Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
    match p with
    | ptsreg     => [ty.enum regname; ty.word]
    | ptsto      => [ty.addr; ty.memval]
    | safe       => [ty.word]
    | expression => [ty.cap]
    | dummy      => [ty.cap]
    | gprs       => []
    end.
  Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
    is_duplicable p :=
      match p with
      | ptsreg     => false
      | ptsto      => false
      | safe       => true
      | expression => false (* TODO: check if it is duplicable when implemented *)
      | dummy      => false
      | gprs       => false
      end
    }.
  Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

  Local Arguments Some {_} &.
  Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
    match p with
    | ptsreg => Some (MkPrecise [ty.enum regname] [ty.word] eq_refl)
    | ptsto => Some (MkPrecise [ty.addr] [ty.memval] eq_refl)
    | _ => None
    end.

End PredicateKit.

  Include ContractDeclMixin MinCapsBase MinCapsProgram.

  Module MinCapsContractNotations.
    Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 70).
    Notation "p '∗' q" := (asn_sep p q).

    Open Scope env_scope.

    Notation "p '<=ₚ' p'" := (asn_formula (formula_user subperm (env.nil ► (ty.perm ↦ p) ► (ty.perm ↦ p')))) (at level 70).

    Notation "r '↦r' t" := (asn_chunk (chunk_user ptsreg (env.nil ► (ty.enum regname ↦ r) ► (ty.word ↦ t)))) (at level 70).
    Notation "a '↦m' t" := (asn_chunk (chunk_user ptsto (env.nil ► (ty.addr ↦ a) ► (ty.int ↦ t)))) (at level 70).
    Notation asn_match_option T opt xl alt_inl alt_inr := (asn_match_sum T ty.unit opt xl alt_inl "_" alt_inr).
    Notation asn_safe w := (asn_chunk (chunk_user safe (env.nil ► (ty.word ↦ w)))).
    Notation asn_csafe c := (asn_chunk (chunk_user safe (env.nil ► (ty.word ↦ (term_inr c))))).
    Notation asn_csafe_angelic c := (asn_chunk_angelic (chunk_user safe (env.nil ► (ty.word ↦ (term_inr c))))).
    Notation asn_expression c := (asn_chunk (chunk_user expression [c])).
    Notation asn_dummy c := (asn_chunk (chunk_user dummy (env.nil ► (ty.cap ↦ c)))).
    Notation asn_gprs := (asn_chunk (chunk_user gprs env.nil)).
    Notation asn_match_cap c p b e a asn :=
      (asn_match_record
         capability c
         (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
                                                                         "cap_permission" p)
                                                         "cap_begin" b)
                                         "cap_end" e)
                         "cap_cursor" a)
         asn).
    Notation asn_within_bounds a b e :=
      (asn_formula (formula_bool (term_binop bop.and
                                             (term_binop bop.le b a)
                                             (term_binop bop.le a e)))).
  End MinCapsContractNotations.

Section ContractDefKit.
  Import MinCapsContractNotations.

  (* Arguments asn_prop [_] & _. *)

  Definition sep_contract_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
    ctx.map (fun '(x::σ) => x::σ) Δ ▻▻ Σ.

  Definition create_localstore (Δ : PCtx) (Σ : LCtx) : SStore Δ (sep_contract_logvars Δ Σ) :=
    (env.tabulate (fun '(x::σ) xIn =>
                     @term_var
                       (sep_contract_logvars Δ Σ)
                       x
                       σ
                       (ctx.in_cat_left Σ (ctx.in_map (fun '(y::τ) => y::τ) xIn)))).


  (* regInv(r) = ∃ w : word. r ↦ w * safe(w) *)
  Definition regInv {Σ} (r : Reg ty.word) : Assertion Σ :=
    asn_exist "w" ty.word
              (r ↦ (@term_var _ _ _ ctx.in_zero) ∗
                asn_safe (@term_var _ _ _ ctx.in_zero)).

  (* regInv(r) = ∃ c : cap. r ↦ c * csafe(c) *)
  Definition regInvCap {Σ} (r : Reg ty.cap) : Assertion Σ :=
    asn_exist "c" ty.cap
              (r ↦ term_var "c" ∗
                 asn_csafe (term_var "c")).

  Definition asn_and_regs {Σ} (f : Reg ty.word -> Assertion Σ) : Assertion Σ :=
    f reg0 ∗ f reg1 ∗ f reg2 ∗ f reg3.

  Definition asn_regs_ptsto_safe {Σ} : Assertion Σ :=
    asn_and_regs regInv.

  (* mach_inv = regInv(r1) * regInv(r2) * regInv(r3) * regInv(r4) * regInvCap(pc) *)
  Definition mach_inv {Σ} : Assertion Σ :=
    asn_gprs ∗ (regInvCap pc).

  (*
Universal Contract
{ ∀ r ∈ GPRS . ∃ w . r → w ∗ V(w) ∗ pc ↦ c ∗ V(c) ∗ IH }
fdeCycle()
{ interp_loop ≡ wp Loop ⊤ }
   *)
End ContractDefKit.

Include SpecificationMixin MinCapsBase MinCapsProgram.

End MinCapsSignature.

Module Import MinCapsSpecification <: Specification MinCapsBase MinCapsSignature.
  Import MinCapsContractNotations.

  Section ContractDefKit.
  (*
     @pre mach_inv;
     @post mach_inv;
     τ f(Δ...) *)
  Definition mach_inv_contract {Δ τ} : SepContract Δ τ :=
    {| sep_contract_logic_variables := sep_contract_logvars Δ [];
       sep_contract_localstore      := create_localstore Δ [];
       sep_contract_precondition    := mach_inv;
       sep_contract_result          := "result_mach_inv";
       sep_contract_postcondition   := mach_inv;
    |}.

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepLemma {Δ} (f : Lem Δ) : Type :=
    Lemma Δ.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition sep_contract_read_reg : SepContractFun read_reg :=
    {| sep_contract_logic_variables := ["rreg" ∷ ty.enum regname];
       sep_contract_localstore      := [term_var "rreg"];
       sep_contract_precondition    := asn_gprs;
       sep_contract_result          := "result_read_reg";
       sep_contract_postcondition   := asn_gprs ∗ asn_safe (term_var "result_read_reg")
    |}.

  Definition sep_contract_read_reg_cap : SepContractFun read_reg_cap :=
    {| sep_contract_logic_variables := ["creg" ∷ ty.enum regname];
       sep_contract_localstore      := [term_var "creg"];
       sep_contract_precondition    := asn_gprs;
       sep_contract_result          := "result_read_reg_cap";
       sep_contract_postcondition   := asn_gprs ∗ asn_csafe (term_var "result_read_reg_cap")
    |}.

  Definition sep_contract_read_reg_num : SepContractFun read_reg_num :=
    {| sep_contract_logic_variables := ["nreg" ∷ ty.enum regname];
       sep_contract_localstore      := [term_var "nreg"];
       sep_contract_precondition    := asn_gprs;
       sep_contract_result          := "result_read_reg_num";
       sep_contract_postcondition   := asn_gprs ∗ asn_safe (term_inl (term_var "result_read_reg_num"))
    |}.

  Definition sep_contract_write_reg : SepContract ["wreg" ∷ ty.enum regname; "w" ∷ ty.word] ty.unit :=
    {| sep_contract_logic_variables := ["wreg" ∷ ty.enum regname; "w" ∷ ty.word];
       sep_contract_localstore      := [term_var "wreg"; term_var "w"];
       sep_contract_precondition    := asn_gprs ∗ asn_safe (term_var "w");
       sep_contract_result          := "result_write_reg";
       sep_contract_postcondition   := asn_eq (term_var "result_write_reg") (term_val ty.unit tt) ∗ asn_gprs
    |}.

  Definition sep_contract_next_pc : SepContract [] ty.cap :=
    {| sep_contract_logic_variables := ["opc" ∷ ty.cap];
       sep_contract_localstore      := [];
       sep_contract_precondition    := pc ↦ term_var "opc";
       sep_contract_result          := "result_next_pc";
       sep_contract_postcondition   :=
         pc ↦ term_var "opc" ∗
            asn_match_cap (term_var "opc") "perm" "beg" "end" "cur"
            (asn_eq
               (term_var "result_next_pc")
               (term_record capability
                            [term_var "perm";
                             term_var "beg";
                             term_var "end";
                             term_binop bop.plus (term_var "cur") (term_val ty.addr 1)]))
    |}.

  Definition sep_contract_update_pc : SepContract [] ty.unit :=
    {| sep_contract_logic_variables := ["opc" ∷ ty.cap];
       sep_contract_localstore      := [];
       sep_contract_precondition    := pc ↦ term_var "opc" ∗ asn_csafe (term_var "opc");
       sep_contract_result          := "result_update_pc";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_update_pc") (term_val ty.unit tt) ∗
                asn_exist "npc" ty.cap
                (pc ↦ term_var "npc" ∗ asn_csafe (term_var "npc"));
    |}.

  Definition sep_contract_add_pc : SepContract ["offset" ∷ ty.int] ty.unit :=
    {| sep_contract_logic_variables := ["opc" ∷ ty.cap; "offset" ∷ ty.int];
       sep_contract_localstore      := [term_var "offset"];
       sep_contract_precondition    := pc ↦ term_var "opc" ∗ asn_csafe (term_var "opc");
       sep_contract_result          := "result_add_pc";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_add_pc") (term_val ty.unit tt) ∗
                asn_exist "npc" ty.cap
                (pc ↦ term_var "npc" ∗ asn_csafe (term_var "npc"));
    |}.

  Definition sep_contract_read_mem : SepContract ["c" ∷ ty.cap ] ty.memval :=
    {| sep_contract_logic_variables := ["c" ∷ ty.cap];
       sep_contract_localstore      := [term_var "c"];
       sep_contract_precondition    := asn_csafe (term_var "c");
       sep_contract_result          := "read_mem_result";
       sep_contract_postcondition   := asn_safe (term_var "read_mem_result")
    |}.

  Definition sep_contract_write_mem : SepContract ["c" ∷ ty.cap; "v" ∷ ty.memval ] ty.unit :=
    {| sep_contract_logic_variables := ["c" ∷ ty.cap; "v" ∷ ty.memval];
       sep_contract_localstore      := [term_var "c"; term_var "v"];
       sep_contract_precondition    := asn_safe (term_var "v") ∗ asn_csafe (term_var "c");
       sep_contract_result          := "write_mem_result";
       sep_contract_postcondition   :=
         asn_csafe (term_var "c") ∗ asn_eq (term_var "write_mem_result") (term_val ty.unit tt);
    |}.

  Definition sep_contract_read_allowed : SepContract ["p" ∷ ty.perm ] ty.bool :=
    {| sep_contract_logic_variables := ["p" ∷ ty.perm];
       sep_contract_localstore      := [term_var "p"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_read_allowed";
       sep_contract_postcondition   := 
         asn_if (term_var "result_read_allowed")
                (term_val ty.perm R <=ₚ term_var "p")
                (asn_eq (term_var "result_read_allowed") (term_val ty.bool false));
    |}.

  Definition sep_contract_write_allowed : SepContract ["p" ∷ ty.perm ] ty.bool :=
    {| sep_contract_logic_variables := ["p" ∷ ty.perm];
       sep_contract_localstore      := [term_var "p"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_write_allowed";
       sep_contract_postcondition   :=
         asn_if (term_var "result_write_allowed")
                (term_val ty.perm RW <=ₚ term_var "p")
                (asn_eq (term_var "result_write_allowed") (term_val ty.bool false));
    |}.

  Definition sep_contract_upper_bound : SepContract ["a" ∷ ty.addr; "e" ∷ ty.addr ] ty.bool :=
    {| sep_contract_logic_variables := ["a" ∷ ty.addr; "e" ∷ ty.addr ];
       sep_contract_localstore      := [term_var "a"; term_var "e"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_upper_bound";
       sep_contract_postcondition   := 
         (asn_eq (term_var "result_upper_bound")
                 (term_binop bop.le (term_var "a") (term_var "e")));
    |}.

  (* 
      @pre true;
      @post ∃ b,e,a,p. c = mkcap(b,e,a,p) ∧ result = (a >= b && (e = none ∨ e = inl e' ∧ e' >= a));
      bool within_bounds(c : capability);
   *)
  Definition sep_contract_within_bounds : SepContract ["c" ∷ ty.cap] ty.bool :=
    {| sep_contract_logic_variables := ["c" ∷ ty.cap];
       sep_contract_localstore      := [term_var "c"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_within_bounds";
       sep_contract_postcondition   :=
         asn_match_cap (term_var "c") "perm" "b" "e" "a"
                       (asn_eq (term_var "result_within_bounds")
                               (term_binop bop.and
                                           (term_binop bop.le (term_var "b") (term_var "a"))
                                           (term_binop bop.le (term_var "a") (term_var "e"))));
    |}.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_jr(lv : lv) *)
  Definition sep_contract_exec_jr : SepContractFun exec_jr :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_jalr(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_jalr : SepContractFun exec_jalr :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_j(offset : Z) *)
  Definition sep_contract_exec_j : SepContractFun exec_j :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_jal(lv : lv, offset : Z) *)
  Definition sep_contract_exec_jal : SepContractFun exec_jal :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_bnez(lv : lv, immediate : Z) *)
  Definition sep_contract_exec_bnez : SepContractFun exec_bnez :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_mv(lv : lv, hv : ty.hv) *)
  Definition sep_contract_exec_mv : SepContractFun exec_mv :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_ld(lv : lv, hv : memval, immediate : Z) *)
  Definition sep_contract_exec_ld : SepContractFun exec_ld :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_sd(hv : memval, lv : lv, immediate : Z) *)
  Definition sep_contract_exec_sd : SepContractFun exec_sd :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_lea(lv : lv, hv : ty.hv) *)
  Definition sep_contract_exec_lea : SepContractFun exec_lea :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_restrict(lv : lv, hv : ty.hv) *)
  Definition sep_contract_exec_restrict : SepContractFun exec_restrict :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_restricti(lv : lv, immediate : Z) *)
  Definition sep_contract_exec_restricti : SepContractFun exec_restricti :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_subseg(lv : lv, hv1 hv2 : ty.hv) *)
  Definition sep_contract_exec_subseg : SepContractFun exec_subseg :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_subsegi(lv : lv, hv : ty.hv, immediate : Z) *)
  Definition sep_contract_exec_subsegi : SepContractFun exec_subsegi :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_addi(lv : lv, hv : hv, immediate : Z) *)
  Definition sep_contract_exec_addi : SepContractFun exec_addi :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_add(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_add : SepContractFun exec_add :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_sub(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_sub : SepContractFun exec_sub :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_slt(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_slt : SepContractFun exec_slt :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_slti(lv : lv, hv : hv, immediate : Z) *)
  Definition sep_contract_exec_slti : SepContractFun exec_slti :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_sltu(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_sltu : SepContractFun exec_sltu :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_sltiu(lv : lv, hv : hv, immediate : Z) *)
  Definition sep_contract_exec_sltiu : SepContractFun exec_sltiu :=
    mach_inv_contract.

  (*
      @pre true;
      @post true;
      int perm_to_bits(p : perm) *)
  Definition sep_contract_perm_to_bits : SepContractFun perm_to_bits :=
    {| sep_contract_logic_variables := ["p" ∷ ty.perm];
       sep_contract_localstore      := [term_var "p"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   := asn_true;
    |}.

  (*
      @pre true;
      @post true;
      int perm_from_bits(i : Z) *)
  Definition sep_contract_perm_from_bits : SepContractFun perm_from_bits :=
    {| sep_contract_logic_variables := ["i" ∷ ty.int];
       sep_contract_localstore      := [term_var "i"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   := asn_true;
    |}.

  (*
      @pre true;
      @post true;
      int abs(i : int) *)
  Definition sep_contract_abs : SepContractFun abs :=
    {| sep_contract_logic_variables := ["i" ∷ ty.int];
       sep_contract_localstore      := [term_var "i"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   := asn_true;
    |}.

  (*
      @pre true;
      @post if p <= p' then (result = true ✱ p ≤ p') else result = false;
      int is_sub_perm(p : perm, p' : perm) *)
  Definition sep_contract_is_sub_perm : SepContractFun is_sub_perm :=
    {| sep_contract_logic_variables := ["p" ∷ ty.perm; "p'" ∷ ty.perm];
       sep_contract_localstore      := [term_var "p"; term_var "p'"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_is_sub_perm";
       sep_contract_postcondition   :=
         asn_if (term_var "result_is_sub_perm")
                (term_var "p" <=ₚ term_var "p'")
                (asn_eq (term_var "result_is_sub_perm") (term_val ty.bool false));
    |}.

  (*
      @pre true;
      @post result = (b ≤ b' && e' ≤ e) ;
      bool is_within_range(b' e' b e : Addr) *)
  Definition sep_contract_is_within_range : SepContractFun is_within_range :=
    {| sep_contract_logic_variables := ["b'" ∷ ty.addr; "e'" ∷ ty.addr;
                                        "b" ∷ ty.addr; "e" ∷ ty.addr];
       sep_contract_localstore      := [term_var "b'"; term_var "e'"; term_var "b"; term_var "e"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_is_within_range";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_is_within_range")
                (term_binop bop.and
                            (term_binop bop.le (term_var "b") (term_var "b'"))
                            (term_binop bop.le (term_var "e'") (term_var "e")))
    |}.
  
  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_isptr(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_isptr : SepContractFun exec_isptr :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_getp(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_getp : SepContractFun exec_getp :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_getb(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_getb : SepContractFun exec_getb :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_gete(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_gete : SepContractFun exec_gete :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_geta(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_geta : SepContractFun exec_geta :=
    mach_inv_contract.

  (* @pre mach_inv;
     @post mach_inv;
     bool exec_fail *)
  Definition sep_contract_exec_fail : SepContractFun exec_fail :=
    mach_inv_contract.

  (* @pre mach_inv;
     @post mach_inv;
     bool exec_ret *)
  Definition sep_contract_exec_ret : SepContractFun exec_ret :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_instr(i : instr) *)
  Definition sep_contract_exec_instr : SepContractFun exec_instr :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec *)
  Definition sep_contract_exec : SepContractFun exec :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      unit loop *)
  Definition sep_contract_loop : SepContractFun loop :=
    mach_inv_contract.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | read_allowed    => Some sep_contract_read_allowed
      | write_allowed   => Some sep_contract_write_allowed
      | upper_bound     => Some sep_contract_upper_bound
      | within_bounds   => Some sep_contract_within_bounds
      | read_reg        => Some sep_contract_read_reg
      | read_reg_cap    => Some sep_contract_read_reg_cap
      | read_reg_num    => Some sep_contract_read_reg_num
      | write_reg       => Some sep_contract_write_reg
      | next_pc         => Some sep_contract_next_pc
      | add_pc          => Some sep_contract_add_pc
      | update_pc       => Some sep_contract_update_pc
      | read_mem        => Some sep_contract_read_mem
      | write_mem       => Some sep_contract_write_mem
      | perm_to_bits    => Some sep_contract_perm_to_bits
      | perm_from_bits  => Some sep_contract_perm_from_bits
      | is_sub_perm     => Some sep_contract_is_sub_perm
      | is_within_range => Some sep_contract_is_within_range
      | abs             => Some sep_contract_abs
      | exec_jr         => Some sep_contract_exec_jr
      | exec_jalr       => Some sep_contract_exec_jalr
      | exec_j          => Some sep_contract_exec_j
      | exec_jal        => Some sep_contract_exec_jal
      | exec_bnez       => Some sep_contract_exec_bnez
      | exec_mv         => Some sep_contract_exec_mv
      | exec_ld         => Some sep_contract_exec_ld
      | exec_sd         => Some sep_contract_exec_sd
      | exec_lea        => Some sep_contract_exec_lea
      | exec_restrict   => Some sep_contract_exec_restrict
      | exec_restricti  => Some sep_contract_exec_restricti
      | exec_subseg     => Some sep_contract_exec_subseg
      | exec_subsegi    => Some sep_contract_exec_subsegi
      | exec_addi       => Some sep_contract_exec_addi
      | exec_add        => Some sep_contract_exec_add
      | exec_sub        => Some sep_contract_exec_sub
      | exec_slt        => Some sep_contract_exec_slt
      | exec_slti       => Some sep_contract_exec_slti
      | exec_sltu       => Some sep_contract_exec_sltu
      | exec_sltiu      => Some sep_contract_exec_slti
      | exec_isptr      => Some sep_contract_exec_isptr
      | exec_getp       => Some sep_contract_exec_getp
      | exec_getb       => Some sep_contract_exec_getb
      | exec_gete       => Some sep_contract_exec_gete
      | exec_geta       => Some sep_contract_exec_geta
      | exec_fail       => Some sep_contract_exec_fail
      | exec_ret        => Some sep_contract_exec_ret
      | exec_instr      => Some sep_contract_exec_instr
      | exec            => Some sep_contract_exec
      | loop            => Some sep_contract_loop
      end.

  Lemma linted_cenv :
    forall Δ τ (f : Fun Δ τ),
      match CEnv f with
      | Some c => Linted c
      | None   => True
      end.
  Proof. intros ? ? []; try constructor. Qed.

  Definition lemma_open_ptsreg : SepLemma open_ptsreg :=
    {| lemma_logic_variables := [ "reg" ∷ ty.enum regname; "w" ∷ ty.word];
       lemma_patterns        := [term_var "reg"];
       lemma_precondition    := term_var "reg" ↦r term_var "w";
       lemma_postcondition   :=
         asn_match_enum
           regname (term_var "reg")
           (fun k => match k with
                     | R0 => reg0 ↦ term_var "w"
                     | R1 => reg1 ↦ term_var "w"
                     | R2 => reg2 ↦ term_var "w"
                     | R3 => reg3 ↦ term_var "w"
                     end)
    |}.

  Definition lemma_open_gprs : SepLemma open_gprs :=
    {| lemma_logic_variables := [];
       lemma_patterns        := [];
       lemma_precondition    := asn_gprs;
       lemma_postcondition   := asn_regs_ptsto_safe;
    |}.

  Definition lemma_close_gprs : SepLemma close_gprs :=
    {| lemma_logic_variables := [];
       lemma_patterns        := [];
       lemma_precondition    := asn_regs_ptsto_safe;
       lemma_postcondition   := asn_gprs;
    |}.

  Definition lemma_safe_move_cursor : SepLemma safe_move_cursor :=
    let Σ : LCtx := ["p" ∷ ty.perm; "b" ∷ ty.addr; "e" ∷ ty.addr; "a" ∷ ty.addr; "a'" ∷ ty.addr]%ctx in
    let c  : Term Σ _ := term_record capability [term_var "p"; term_var "b"; term_var "e"; term_var "a"] in
    let c' : Term Σ _ := term_record capability [term_var "p"; term_var "b"; term_var "e"; term_var "a'"] in
    {| lemma_logic_variables := Σ;
       lemma_patterns        := [nenv c'; c];
       lemma_precondition    := asn_csafe c;
       lemma_postcondition   :=
         asn_csafe c ∗
         asn_csafe c';
    |}.

  (*
    @pre c = mkcap(p,b,e,a) ✱ c' = mkcap(p',b,e,a) ✱ csafe(c) ✱ p' ≤ p
    @post csafe(c) ✱ csafe(c')
    unit csafe_sub_perm(c : capability, c' : capability);
   *)
  Definition lemma_safe_sub_perm : SepLemma safe_sub_perm :=
    let Σ : LCtx := ["p" ∷ ty.perm; "p'" ∷ ty.perm; "b" ∷ ty.addr; "e" ∷ ty.addr; "a" ∷ ty.addr]%ctx in
    let c  : Term Σ _ := term_record capability [term_var "p"; term_var "b"; term_var "e"; term_var "a"] in
    let c' : Term Σ _ := term_record capability [term_var "p'"; term_var "b"; term_var "e"; term_var "a"] in
    {| lemma_logic_variables := Σ;
       lemma_patterns        := [nenv c'; c];
       lemma_precondition    :=
         asn_csafe c ∗ term_var "p'" <=ₚ term_var "p";
       lemma_postcondition   :=
         asn_csafe c ∗
         asn_csafe c';
    |}.

  (*
    @pre c = mkcap(p,b,e,a) ✱ c' = mkcap(p,b',e',a) ✱ csafe(c) ✱ b ≤ b' ✱ e' ≤ e
    @post csafe(c) ✱ csafe(c')
    unit csafe_within_range(c' : capability, c : capability);
   *)
  Definition lemma_safe_within_range : SepLemma safe_within_range :=
    let Σ : LCtx := ["p" ∷ ty.perm; "b" ∷ ty.addr; "b'" ∷ ty.addr; "e" ∷ ty.addr; "e'" ∷ ty.addr; "a" ∷ ty.addr]%ctx in
    let c  : Term Σ _ := term_record capability [term_var "p"; term_var "b"; term_var "e"; term_var "a"] in
    let c' : Term Σ _ := term_record capability [term_var "p"; term_var "b'"; term_var "e'"; term_var "a"] in
    {| lemma_logic_variables := Σ;
       lemma_patterns        := [nenv c'; c];
       lemma_precondition    :=
         asn_csafe c ∗
         asn_dummy c' ∗
         asn_formula
         (formula_bool
            (term_binop bop.and
                        (term_binop bop.le (term_var "b") (term_var "b'"))
                        (term_binop bop.le (term_var "e'") (term_var "e"))));
       lemma_postcondition   :=
         asn_csafe c ∗
         asn_csafe c';
    |}.

  (*
    @pre true
    @post safe(i)
    unit int_safe(i : int);
   *)
  Definition lemma_int_safe : SepLemma int_safe :=
    {| lemma_logic_variables := ["i" ∷ ty.int];
       lemma_patterns        := [term_var "i"];
       lemma_precondition    := asn_true;
       lemma_postcondition   :=
         asn_safe (term_inl (term_var "i"));
    |}.

  Definition regtag_to_reg (R : RegName) : Reg ty.word :=
    match R with
    | R0 => reg0
    | R1 => reg1
    | R2 => reg2
    | R3 => reg3
    end.

  Definition lemma_close_ptsreg (r : RegName) : SepLemma (close_ptsreg r) :=
    {| lemma_logic_variables := ["w" ∷ ty.word];
       lemma_patterns        := [];
       lemma_precondition    := regtag_to_reg r ↦ term_var "w";
       lemma_postcondition   := term_enum regname r ↦r term_var "w"
    |}.

  Definition sep_contract_rM : SepContractFunX rM :=
    {| sep_contract_logic_variables := ["address" ∷ ty.addr; "p" ∷ ty.perm; "b" ∷ ty.addr; "e" ∷ ty.addr];
       sep_contract_localstore      := [term_var "address"];
       sep_contract_precondition    :=
         asn_csafe_angelic (term_record capability
                            [term_var "p";
                             term_var "b";
                             term_var "e";
                             term_var "address"]) ∗
                   term_val ty.perm R <=ₚ term_var "p" ∗
                   asn_within_bounds (term_var "address") (term_var "b") (term_var "e");
       sep_contract_result          := "rM_result";
       sep_contract_postcondition   :=
         asn_safe (term_var "rM_result")
    |}.

  Definition sep_contract_wM : SepContractFunX wM :=
    {| sep_contract_logic_variables := ["address" ∷ ty.addr; "new_value" ∷ ty.memval; "p" ∷ ty.perm; "b" ∷ ty.addr; "e" ∷ ty.addr];
       sep_contract_localstore      := [term_var "address"; term_var "new_value"];
       sep_contract_precondition    :=
         asn_safe (term_var "new_value")
                  ∗ asn_csafe_angelic (term_record capability
                                           [term_var "p";
                                            term_var "b";
                                            term_var "e";
                                            term_var "address"])
                  ∗ term_val ty.perm RW <=ₚ term_var "p"
                  ∗ asn_within_bounds (term_var "address") (term_var "b") (term_var "e");
       sep_contract_result          := "wM_result";
       sep_contract_postcondition   :=
         asn_eq (term_var "wM_result") (term_val ty.unit tt)
    |}.

  Definition sep_contract_dI : SepContractFunX dI :=
    {| sep_contract_logic_variables := ["code" ∷ ty.int];
       sep_contract_localstore      := [term_var "code"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "_";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition lemma_gen_dummy : SepLemma gen_dummy :=
    {| lemma_logic_variables := ["c" ∷ ty.cap];
       lemma_patterns        := [term_var "c"];
       lemma_precondition    := asn_true;
       lemma_postcondition   := asn_dummy (term_var "c");
    |}.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | rM => sep_contract_rM
      | wM => sep_contract_wM
      | dI => sep_contract_dI
      end.

  Definition LEnv : LemmaEnv :=
    fun Δ l =>
      match l with
        | open_ptsreg       => lemma_open_ptsreg
        | close_ptsreg r    => lemma_close_ptsreg r
        | open_gprs         => lemma_open_gprs
        | close_gprs        => lemma_close_gprs
        | safe_move_cursor  => lemma_safe_move_cursor
        | safe_sub_perm     => lemma_safe_sub_perm
        | safe_within_range => lemma_safe_within_range
        | int_safe          => lemma_int_safe
        | gen_dummy         => lemma_gen_dummy
      end.

  Lemma linted_cenvex :
    forall Δ τ (f : FunX Δ τ),
      Linted (CEnvEx f).
  Proof.
    intros ? ? []; try constructor.
  Qed.

End ContractDefKit.

End MinCapsSpecification.

Module MinCapsSolverKit <: SolverKit MinCapsBase MinCapsSignature MinCapsSpecification.
  Equations(noeqns) simplify_subperm {Σ} (p q : Term Σ ty.perm) : option (List Formula Σ) :=
  | term_val p | term_val q := if decide_subperm p q then Some nil else None;
  | term_val O | q          := Some nil;
  | p          | q          :=
    let ts := env.nil ► (ty.perm ↦ p) ► (ty.perm ↦ q) in
    Some (cons (formula_user subperm ts) nil).

  Definition simplify_user {Σ} (p : 𝑷) : Env (Term Σ) (𝑷_Ty p) -> option (List Formula Σ) :=
    match p with
    | subperm => fun ts =>
                   let (ts,q) := env.snocView ts in
                   let (ts,p) := env.snocView ts in
                   simplify_subperm p q
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
End MinCapsSolverKit.
Module MinCapsSolver := MakeSolver MinCapsBase MinCapsSignature MinCapsSpecification MinCapsSolverKit.

Module Import MinCapsExecutor :=
  MakeExecutor MinCapsBase MinCapsSignature MinCapsSpecification MinCapsSolver.

(* Module Import MinCapsCMut := MakeShallowExecutor MinCapsBase MinCapsSignature MinCapsSpecification. *)
(* Import CMut. *)

Local Ltac solve :=
  repeat
    (repeat
       match goal with
       | H: _ /\ _ |- _ => destruct H
       | H: Empty_set |- _ => destruct H
       | |- forall _, _ => cbn [Val snd]; intro
       | |- False \/ _ =>  right
       | |- _ \/ False =>  left
       | |- _ \/ exists _, _ =>  left (* avoid existentials, bit fishy but fine for now *)
       | |- _ /\ _ => constructor
       | |- VerificationCondition _ =>
         constructor;
         cbv [SymProp.safe env.remove env.lookup ctx.in_case_snoc bop.eval is_true
              inst inst_term inst_formula env.Env_rect];
         cbn
       | |- Obligation _ _ _ => constructor; cbn
       | |- Debug _ _ => constructor
       | |- Debug _ True \/ _ => left
       | |- (_ \/ _) \/ _ => rewrite or_assoc
       | |- context[Z.leb ?x ?y] =>
         destruct (Z.leb_spec x y)
       end;
     cbn [List.length andb is_true Val snd];
     subst; try congruence; try lia;
     auto
    ).

Import MinCapsContractNotations.

Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
  match CEnv f with
  | Some c => SMut.ValidContractReflect c (FunDef f)
  | None => False
  end.

Definition ValidContractDebug {Δ τ} (f : Fun Δ τ) : Prop :=
  match CEnv f with
  | Some c => SMut.ValidContract c (FunDef f)
  | None => False
  end.

Goal True. idtac "Timing before: minimalcaps". Abort.
Lemma ValidContractsFun : forall {Δ τ} (f : Fun Δ τ),
    ValidContract f.
Proof.
  destruct f; reflexivity.
Qed.
Goal True. idtac "Timing after: minimalcaps". Abort.

Goal True. idtac "Assumptions for minimalcaps contracts:". Abort.
Print Assumptions ValidContractsFun.

Section Statistics.
  Import List.ListNotations.
  Import SMut.Statistics.

  Definition all_functions : list { Δ & { σ & Fun Δ σ } } :=
    [ existT _ (existT _ read_reg);
      existT _ (existT _ read_reg_cap);
      existT _ (existT _ read_reg_num);
      existT _ (existT _ write_reg);
      existT _ (existT _ next_pc);
      existT _ (existT _ update_pc);
      existT _ (existT _ add_pc);
      existT _ (existT _ read_mem);
      existT _ (existT _ write_mem);
      existT _ (existT _ read_allowed);
      existT _ (existT _ write_allowed);
      existT _ (existT _ upper_bound);
      existT _ (existT _ within_bounds);
      existT _ (existT _ perm_to_bits);
      existT _ (existT _ perm_from_bits);
      existT _ (existT _ is_sub_perm);
      existT _ (existT _ is_within_range);
      existT _ (existT _ abs);
      existT _ (existT _ exec_jr);
      existT _ (existT _ exec_jalr);
      existT _ (existT _ exec_j);
      existT _ (existT _ exec_jal);
      existT _ (existT _ exec_bnez);
      existT _ (existT _ exec_mv);
      existT _ (existT _ exec_ld);
      existT _ (existT _ exec_sd);
      existT _ (existT _ exec_lea);
      existT _ (existT _ exec_restrict);
      existT _ (existT _ exec_restricti);
      existT _ (existT _ exec_subseg);
      existT _ (existT _ exec_subsegi);
      existT _ (existT _ exec_isptr);
      existT _ (existT _ exec_addi);
      existT _ (existT _ exec_add);
      existT _ (existT _ exec_sub);
      existT _ (existT _ exec_slt);
      existT _ (existT _ exec_slti);
      existT _ (existT _ exec_sltu);
      existT _ (existT _ exec_sltiu);
      existT _ (existT _ exec_getp);
      existT _ (existT _ exec_getb);
      existT _ (existT _ exec_gete);
      existT _ (existT _ exec_geta);
      existT _ (existT _ exec_fail);
      existT _ (existT _ exec_ret);
      existT _ (existT _ exec_instr);
      existT _ (existT _ exec);
      existT _ (existT _ loop)
    ]%list.

  Definition all_stats : Stats :=
    List.fold_right
      (fun '(existT _ (existT _ f)) r =>
         match calc_statistics f with
         | Some (_,s) => plus_stats s r
         | None       => r
         end)
      empty_stats
      all_functions.

  Goal ("minimalcaps", all_stats) = ("", empty_stats).
    idtac "Branching statistics:".
    compute.
    match goal with
    | |- ?x = _ =>
        idtac x
    end.
  Abort.

End Statistics.
