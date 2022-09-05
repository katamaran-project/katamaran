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
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     MinimalCaps.Machine
     Notations
     Specification
     Shallow.Executor
     Symbolic.Executor
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
| correctPC
| not_is_perm
.

Inductive Predicate : Set :=
  ptsreg
| ptsto
| safe
| expr
| gprs
| ih
| wp_loop
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

Module Import MinCapsSignature <: Signature MinCapsBase.

Section PredicateKit.
  Definition 𝑷 := PurePredicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    | subperm     => [ty.perm; ty.perm]
    | correctPC   => [ty.cap]
    | not_is_perm => [ty.perm; ty.perm]
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

  Lemma Subperm_refl : forall (p : Val ty.perm),
      Subperm p p.
  Proof. destruct p; simpl; reflexivity. Qed.

  Equations(noeqns) is_perm (p p' : Val ty.perm) : bool :=
  | O  | O  := true;
  | R  | R  := true;
  | RW | RW := true;
  | E  | E  := true;
  | _  | _  := false.

  Definition decide_correct_pc (c : Val ty.cap) : bool :=
    match c with
    | {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |} =>
        (b <=? a) && (a <? e) && (is_perm p R || is_perm p RW)
    end.

  Definition CorrectPC (c : Val ty.cap) : Prop :=
    decide_correct_pc c = true.

  Definition Not_is_perm (p p' : Val ty.perm) : Prop :=
    (negb (is_perm p p')) = true.

  Lemma Not_is_perm_prop (p p' : Val ty.perm) :
    Not_is_perm p p' -> p <> p'.
  Proof. unfold Not_is_perm; destruct p, p'; intros; auto. Qed.

  Lemma Not_is_perm_iff (p p' : Val ty.perm) :
    Not_is_perm p p' <-> p <> p'.
  Proof. unfold Not_is_perm; destruct p, p'; split; intros; auto. Qed.

  Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
    match p with
    | subperm     => Subperm
    | correctPC   => CorrectPC
    | not_is_perm => Not_is_perm
    end.

  Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

  Definition 𝑯 := Predicate.
  Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
    match p with
    | ptsreg  => [ty.enum regname; ty.word]
    | ptsto   => [ty.addr; ty.memval]
    | safe    => [ty.word]
    | expr    => [ty.cap]
    | gprs    => []
    | ih      => []
    | wp_loop => []
    end.
  Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
    is_duplicable p :=
      match p with
      | ptsreg  => false
      | ptsto   => false
      | safe    => true
      | expr    => false (* TODO: check if it is duplicable when implemented *)
      | gprs    => false
      | ih      => true
      | wp_loop => false
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

  Include PredicateMixin MinCapsBase.
  Include SignatureMixin MinCapsBase.

  Module MinCapsContractNotations.
    Export asn.notations.
    Open Scope env_scope.

    Notation "x '≠' y" := (asn.formula (formula_neq x y)) (at level 70) : asn_scope.
    Notation "p '<=ₚ' p'" := (asn.formula (formula_user subperm (env.nil ► (ty.perm ↦ p) ► (ty.perm ↦ p')))) (at level 70).

    Notation "r '↦r' t" := (asn.chunk (chunk_user ptsreg (env.nil ► (ty.enum regname ↦ r) ► (ty.word ↦ t)))) (at level 70).
    Notation "a '↦m' t" := (asn.chunk (chunk_user ptsto (env.nil ► (ty.addr ↦ a) ► (ty.int ↦ t)))) (at level 70).
    Notation asn_correctPC c := (asn.formula (formula_user correctPC [c])).
    Notation "p '≠ₚ' p'" := (asn.formula (formula_user not_is_perm [p;p'])) (at level 70).
    Notation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
    Notation asn_IH := (asn.chunk (chunk_user ih [])).
    Notation asn_WP_loop := (asn.chunk (chunk_user wp_loop [])).
    Notation asn_safe w := (asn.chunk (chunk_user safe (env.nil ► (ty.word ↦ w)))).
    Notation asn_csafe c := (asn.chunk (chunk_user safe (env.nil ► (ty.word ↦ (term_inr c))))).
    Notation asn_csafe_angelic c := (asn.chunk_angelic (chunk_user safe (env.nil ► (ty.word ↦ (term_inr c))))).
    Notation asn_expr c := (asn.chunk (chunk_user expr [c])).
    Notation asn_gprs := (asn.chunk (chunk_user gprs env.nil)).
    Notation asn_match_cap c p b e a asn :=
      (asn.match_record
         capability c
         (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
                                                                         "cap_permission" p)
                                                         "cap_begin" b)
                                         "cap_end" e)
                         "cap_cursor" a)
         asn).
    Notation asn_within_bounds a b e :=
      (asn.formula (formula_bool (term_binop bop.and
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
    asn.exist "w" ty.word
              (r ↦ (@term_var _ _ _ ctx.in_zero) ∗
                asn_safe (@term_var _ _ _ ctx.in_zero)).

  (* regInv(r) = ∃ c : cap. r ↦ c * csafe(c) *)
  Definition regInvCap {Σ} (r : Reg ty.cap) : Assertion Σ :=
    asn.exist "c" ty.cap
              (r ↦ term_var "c" ∗
                 asn_csafe (term_var "c")).

  Definition asn_and_regs {Σ} (f : Reg ty.word -> Assertion Σ) : Assertion Σ :=
    f reg0 ∗ f reg1 ∗ f reg2 ∗ f reg3.

  Definition asn_regs_ptsto_safe {Σ} : Assertion Σ :=
    asn_and_regs regInv.

  Definition asn_pc_correct {Σ} (r : Reg ty.cap) : Assertion Σ :=
    asn.exist "c" ty.cap (r ↦ term_var "c" ∗
                          asn_csafe (term_var "c") ∗
                          asn_correctPC (term_var "c")).

  Definition asn_pc_safe {Σ} (r : Reg ty.cap) : Assertion Σ :=
    asn.exist "c" ty.cap (r ↦ term_var "c" ∗
                          asn_csafe (term_var "c")).

  Definition asn_pc_expr {Σ} (r : Reg ty.cap) : Assertion Σ :=
    asn.exist "c" ty.cap (r ↦ term_var "c" ∗
                          asn_expr (term_var "c")).

  (* mach_inv = regInv(r1) * regInv(r2) * regInv(r3) * regInv(r4) * asn_pc_safe pc *)
  (* Definition mach_inv {Σ} : Assertion Σ :=
    asn_gprs ∗ asn_pc_safe pc. *)

  (*
Universal Contract
{ ∀ r ∈ GPRS . ∃ w . r → w ∗ V(w) ∗ pc ↦ c ∗ V(c) ∗ IH }
fdeCycle()
{ interp_loop ≡ wp Loop ⊤ }
   *)
End ContractDefKit.

End MinCapsSignature.

Module Import MinCapsSpecification <: Specification MinCapsBase MinCapsProgram MinCapsSignature.
  Include SpecificationMixin MinCapsBase MinCapsProgram MinCapsSignature.
  Import MinCapsContractNotations.

  Section ContractDefKit.
  (*
     @pre gprs ∗ pc_pre;
     @post gprs ∗ pc_post;
     τ f(Δ...) *)
  Definition mach_inv_contract {Δ τ} : SepContract Δ τ :=
    {| sep_contract_logic_variables := sep_contract_logvars Δ [];
       sep_contract_localstore      := create_localstore Δ [];
       sep_contract_precondition    := asn_gprs ∗ asn_pc_correct pc ∗ asn_IH;
       sep_contract_result          := "result_mach_inv";
       sep_contract_postcondition   := asn_gprs ∗ (asn_pc_safe pc ∨ asn_pc_expr pc);
    |}.

  Definition mach_inv_jump_contract {Δ τ} : SepContract Δ τ :=
    {| sep_contract_logic_variables := sep_contract_logvars Δ [];
       sep_contract_localstore      := create_localstore Δ [];
       sep_contract_precondition    := asn_gprs ∗ asn_pc_correct pc ∗ asn_IH;
       sep_contract_result          := "result_mach_inv";
       sep_contract_postcondition   := (asn_gprs ∗ asn_pc_safe pc) ∨ asn_WP_loop;
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
       sep_contract_postcondition   := asn_gprs ∗ (* asn_csafe (term_var "result_read_reg_cap") *)
            asn_match_cap (term_var "result_read_reg_cap") "p" "b" "e" "a"
            (asn_csafe (term_var "result_read_reg_cap"));
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
       sep_contract_postcondition   := term_var "result_write_reg" = term_val ty.unit tt ∗ asn_gprs
    |}.

  Definition sep_contract_next_pc : SepContract [] ty.cap :=
    {| sep_contract_logic_variables := ["opc" ∷ ty.cap];
       sep_contract_localstore      := [];
       sep_contract_precondition    := pc ↦ term_var "opc";
       sep_contract_result          := "result_next_pc";
       sep_contract_postcondition   :=
         pc ↦ term_var "opc" ∗
            asn_match_cap (term_var "opc") "perm" "beg" "end" "cur"
            (term_var "result_next_pc" =
             term_record capability
               [term_var "perm";
                term_var "beg";
                term_var "end";
                term_binop bop.plus (term_var "cur") (term_val ty.addr 1)])
    |}.

  Definition sep_contract_update_pc : SepContract [] ty.unit :=
    {| sep_contract_logic_variables := ["opc" ∷ ty.cap];
       sep_contract_localstore      := [];
       sep_contract_precondition    := pc ↦ term_var "opc" ∗ asn_csafe (term_var "opc") ∗ asn_correctPC (term_var "opc");
       sep_contract_result          := "result_update_pc";
       sep_contract_postcondition   :=
         term_var "result_update_pc" = term_val ty.unit tt ∗
         asn.exist "npc" ty.cap
           (pc ↦ term_var "npc" ∗ asn_csafe (term_var "npc"));
    |}.

  Definition sep_contract_update_pc_perm : SepContract ["c" :: ty.cap] ty.cap :=
    let Σ : LCtx := ["p" :: ty.perm; "b" :: ty.addr; "e" :: ty.addr; "a" :: ty.addr]%ctx in
    let c : Term Σ _ := term_record capability [term_var "p"; term_var "b"; term_var "e"; term_var "a"] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := (env.snoc env.nil (_∷_) c);
       sep_contract_precondition    := asn_csafe c;
       sep_contract_result          := "result_update_pc_perm";
       sep_contract_postcondition   :=
         asn.exist "p'" ty.perm
           (let c : Term _ _ := term_record capability [term_var "p"; term_var "b"; term_var "e"; term_var "a"] in
            let c' : Term _ _ := term_record capability [term_var "p'"; term_var "b"; term_var "e"; term_var "a"] in
            term_var "result_update_pc_perm" = c' ∗
            term_var "p'" ≠ₚ term_val ty.perm E ∗
            asn.match_enum permission (term_var "p")
                           (fun p => match p with
                                     | E => asn_expr c'
                                     | _ => asn_csafe c' ∗ c = c'
                                     end))
    |}.

  Definition sep_contract_is_correct_pc : SepContract ["c" :: ty.cap] ty.bool :=
    {| sep_contract_logic_variables := ["c" :: ty.cap];
       sep_contract_localstore      := [term_var "c"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result_is_correct_pc";
       sep_contract_postcondition   :=
         if:  term_var "result_is_correct_pc"
         then asn_correctPC (term_var "c")
         else ⊤
    |}.

  Definition sep_contract_is_perm : SepContract ["p" :: ty.perm; "p'" :: ty.perm] ty.bool :=
    {| sep_contract_logic_variables := ["p" :: ty.perm; "p'" :: ty.perm];
       sep_contract_localstore      := [term_var "p"; term_var "p'"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result_is_perm";
       sep_contract_postcondition   :=
         if:  term_var "result_is_perm"
         then term_var "p" = term_var "p'"
         else ⊤
    |}.

  Definition sep_contract_add_pc : SepContract ["offset" ∷ ty.int] ty.unit :=
    {| sep_contract_logic_variables := ["opc" ∷ ty.cap; "offset" ∷ ty.int];
       sep_contract_localstore      := [term_var "offset"];
       sep_contract_precondition    := pc ↦ term_var "opc" ∗ asn_csafe (term_var "opc") ∗ asn_correctPC (term_var "opc");
       sep_contract_result          := "result_add_pc";
       sep_contract_postcondition   :=
         term_var "result_add_pc" = term_val ty.unit tt ∗
         asn.exist "npc" ty.cap
           (pc ↦ term_var "npc" ∗ asn_csafe (term_var "npc"));
    |}.

  Definition sep_contract_read_mem : SepContract ["c" ∷ ty.cap ] ty.memval :=
    let Σ : LCtx := ["p" :: ty.perm; "b" :: ty.addr; "e" :: ty.addr; "a" :: ty.addr]%ctx in
    let c : Term Σ _ := term_record capability [term_var "p"; term_var "b"; term_var "e"; term_var "a"] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := (env.snoc env.nil (_∷_) c);
       sep_contract_precondition    :=
         asn_csafe c ∗ term_val ty.perm R <=ₚ term_var "p";
       sep_contract_result          := "read_mem_result";
       sep_contract_postcondition   := asn_safe (term_var "read_mem_result")
    |}.

  Definition sep_contract_write_mem : SepContract ["c" ∷ ty.cap; "v" ∷ ty.memval ] ty.unit :=
    let Σ : LCtx := ["p" :: ty.perm; "b" :: ty.addr; "e" :: ty.addr; "a" :: ty.addr; "v" :: ty.memval]%ctx in
    let c : Term Σ _ := term_record capability [term_var "p"; term_var "b"; term_var "e"; term_var "a"] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := (env.snoc (env.snoc env.nil (_∷_) c) _ (term_var "v"));
       sep_contract_precondition    :=
         asn_safe (term_var "v") ∗ asn_csafe c ∗ term_val ty.perm RW <=ₚ term_var "p";
       sep_contract_result          := "write_mem_result";
       sep_contract_postcondition   :=
         let c : Term (Σ ▻ "write_mem_result"∷_) _ := term_record capability [term_var "p"; term_var "b"; term_var "e"; term_var "a"] in
         asn_csafe c ∗ term_var "write_mem_result" = term_val ty.unit tt;
    |}.

  Definition sep_contract_read_allowed : SepContract ["p" ∷ ty.perm ] ty.bool :=
    {| sep_contract_logic_variables := ["p" ∷ ty.perm];
       sep_contract_localstore      := [term_var "p"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result_read_allowed";
       sep_contract_postcondition   := 
         if: term_var "result_read_allowed"
         then term_val ty.perm R <=ₚ term_var "p"
         else term_var "result_read_allowed" = term_val ty.bool false;
    |}.

  Definition sep_contract_write_allowed : SepContract ["p" ∷ ty.perm ] ty.bool :=
    {| sep_contract_logic_variables := ["p" ∷ ty.perm];
       sep_contract_localstore      := [term_var "p"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result_write_allowed";
       sep_contract_postcondition   :=
         if: term_var "result_write_allowed"
         then term_val ty.perm RW <=ₚ term_var "p"
         else term_var "result_write_allowed" = term_val ty.bool false;
    |}.

  Definition sep_contract_upper_bound : SepContract ["a" ∷ ty.addr; "e" ∷ ty.addr ] ty.bool :=
    {| sep_contract_logic_variables := ["a" ∷ ty.addr; "e" ∷ ty.addr ];
       sep_contract_localstore      := [term_var "a"; term_var "e"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result_upper_bound";
       sep_contract_postcondition   :=
         term_var "result_upper_bound" =
           term_binop bop.le (term_var "a") (term_var "e");
    |}.

  (* 
      @pre true;
      @post ∃ b,e,a,p. c = mkcap(b,e,a,p) ∧ result = (a >= b && (e = none ∨ e = inl e' ∧ e' >= a));
      bool within_bounds(c : capability);
   *)
  Definition sep_contract_within_bounds : SepContract ["c" ∷ ty.cap] ty.bool :=
    {| sep_contract_logic_variables := ["c" ∷ ty.cap];
       sep_contract_localstore      := [term_var "c"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result_within_bounds";
       sep_contract_postcondition   :=
         asn_match_cap (term_var "c") "perm" "b" "e" "a"
                       (term_var "result_within_bounds" =
                          term_binop bop.and
                            (term_binop bop.le (term_var "b") (term_var "a"))
                            (term_binop bop.le (term_var "a") (term_var "e")));
    |}.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_jalr(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_jalr : SepContractFun exec_jalr :=
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
      bool exec_bne(lv1 : lv, lv2: lv, immediate : Z) *)
  Definition sep_contract_exec_bne : SepContractFun exec_bne :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_cmove(lv : lv, hv : ty.hv) *)
  Definition sep_contract_exec_cmove : SepContractFun exec_cmove :=
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
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result";
       sep_contract_postcondition   := ⊤;
    |}.

  (*
      @pre true;
      @post true;
      int perm_from_bits(i : Z) *)
  Definition sep_contract_perm_from_bits : SepContractFun perm_from_bits :=
    {| sep_contract_logic_variables := ["i" ∷ ty.int];
       sep_contract_localstore      := [term_var "i"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result";
       sep_contract_postcondition   := ⊤;
    |}.

  (*
      @pre true;
      @post true;
      int abs(i : int) *)
  Definition sep_contract_abs : SepContractFun abs :=
    {| sep_contract_logic_variables := ["i" ∷ ty.int];
       sep_contract_localstore      := [term_var "i"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result";
       sep_contract_postcondition   := ⊤;
    |}.

  (*
      @pre true;
      @post if p <= p' then (result = true ✱ p ≤ p') else result = false;
      int is_sub_perm(p : perm, p' : perm) *)
  Definition sep_contract_is_sub_perm : SepContractFun is_sub_perm :=
    {| sep_contract_logic_variables := ["p" ∷ ty.perm; "p'" ∷ ty.perm];
       sep_contract_localstore      := [term_var "p"; term_var "p'"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result_is_sub_perm";
       sep_contract_postcondition   :=
         if: term_var "result_is_sub_perm"
         then term_var "p" <=ₚ term_var "p'"
         else term_var "result_is_sub_perm" = term_val ty.bool false;
    |}.

  (*
      @pre true;
      @post result = (b ≤ b' && e' ≤ e) ;
      bool is_within_range(b' e' b e : Addr) *)
  Definition sep_contract_is_within_range : SepContractFun is_within_range :=
    {| sep_contract_logic_variables := ["b'" ∷ ty.addr; "e'" ∷ ty.addr;
                                        "b" ∷ ty.addr; "e" ∷ ty.addr];
       sep_contract_localstore      := [term_var "b'"; term_var "e'"; term_var "b"; term_var "e"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result_is_within_range";
       sep_contract_postcondition   :=
         term_var "result_is_within_range" =
           term_binop bop.and
             (term_binop bop.le (term_var "b") (term_var "b'"))
             (term_binop bop.le (term_var "e'") (term_var "e"))
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
      bool exec_cgetperm(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_cgetperm : SepContractFun exec_cgetperm :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_cgetbase(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_cgetbase : SepContractFun exec_cgetbase :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_cgetlen(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_cgetlen : SepContractFun exec_cgetlen :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_cgetaddr(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_cgetaddr : SepContractFun exec_cgetaddr :=
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
  Definition sep_contract_step : SepContractFun step :=
    mach_inv_contract.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | read_allowed           => Some sep_contract_read_allowed
      | write_allowed          => Some sep_contract_write_allowed
      | upper_bound            => Some sep_contract_upper_bound
      | within_bounds          => Some sep_contract_within_bounds
      | read_reg               => Some sep_contract_read_reg
      | read_reg_cap           => Some sep_contract_read_reg_cap
      | read_reg_num           => Some sep_contract_read_reg_num
      | write_reg              => Some sep_contract_write_reg
      | next_pc                => Some sep_contract_next_pc
      | add_pc                 => Some sep_contract_add_pc
      | update_pc              => Some sep_contract_update_pc
      | update_pc_perm         => Some sep_contract_update_pc_perm
      | is_correct_pc          => Some sep_contract_is_correct_pc
      | MinCapsProgram.is_perm => Some sep_contract_is_perm
      | read_mem               => Some sep_contract_read_mem
      | write_mem              => Some sep_contract_write_mem
      | perm_to_bits           => Some sep_contract_perm_to_bits
      | perm_from_bits         => Some sep_contract_perm_from_bits
      | is_sub_perm            => Some sep_contract_is_sub_perm
      | is_within_range        => Some sep_contract_is_within_range
      | abs                    => Some sep_contract_abs
      | exec_jalr              => Some sep_contract_exec_jalr
      | exec_jal               => Some sep_contract_exec_jal
      | exec_bne               => Some sep_contract_exec_bne
      | exec_cmove             => Some sep_contract_exec_cmove
      | exec_ld                => Some sep_contract_exec_ld
      | exec_sd                => Some sep_contract_exec_sd
      | exec_lea               => Some sep_contract_exec_lea
      | exec_restrict          => Some sep_contract_exec_restrict
      | exec_restricti         => Some sep_contract_exec_restricti
      | exec_subseg            => Some sep_contract_exec_subseg
      | exec_subsegi           => Some sep_contract_exec_subsegi
      | exec_addi              => Some sep_contract_exec_addi
      | exec_add               => Some sep_contract_exec_add
      | exec_sub               => Some sep_contract_exec_sub
      | exec_slt               => Some sep_contract_exec_slt
      | exec_slti              => Some sep_contract_exec_slti
      | exec_sltu              => Some sep_contract_exec_sltu
      | exec_sltiu             => Some sep_contract_exec_slti
      | exec_isptr             => Some sep_contract_exec_isptr
      | exec_cgetperm          => Some sep_contract_exec_cgetperm
      | exec_cgetbase          => Some sep_contract_exec_cgetbase
      | exec_cgetlen           => Some sep_contract_exec_cgetlen
      | exec_cgetaddr          => Some sep_contract_exec_cgetaddr
      | exec_fail              => Some sep_contract_exec_fail
      | exec_ret               => Some sep_contract_exec_ret
      | exec_instr             => Some sep_contract_exec_instr
      | exec                   => Some sep_contract_exec
      | step                   => Some sep_contract_step
      | loop                   => None
      end.

  Lemma linted_cenv :
    forall Δ τ (f : Fun Δ τ),
      match CEnv f with
      | Some c => Linted c
      | None   => True
      end.
  Proof. intros ? ? []; try constructor. Qed.

  Definition lemma_correctPC_subperm_R : SepLemma correctPC_subperm_R :=
    let Σ : LCtx := ["p" :: ty.perm; "b" :: ty.addr; "e" :: ty.addr; "a" :: ty.addr]%ctx in
    let c  : Term Σ _ := term_record capability [term_var "p"; term_var "b"; term_var "e"; term_var "a"] in
    {| lemma_logic_variables := Σ;
       lemma_patterns        := (env.snoc env.nil (_∷_) c);
       lemma_precondition    := asn_correctPC c;
       lemma_postcondition   := term_val ty.perm R <=ₚ term_var "p";
    |}.

  Definition lemma_subperm_not_E : SepLemma subperm_not_E :=
    {| lemma_logic_variables := ["p" :: ty.perm; "p'" :: ty.perm];
       lemma_patterns        := [term_var "p"; term_var "p'"];
       lemma_precondition    :=
         (term_var "p" = term_val ty.perm R ∨ term_var "p" = term_val ty.perm RW) ∗
         term_var "p" <=ₚ term_var "p'";
       lemma_postcondition   := term_var "p'" ≠ₚ term_val ty.perm E;
    |}.

  Definition lemma_safe_to_execute : SepLemma safe_to_execute :=
    let Σ : LCtx := ["p" :: ty.perm; "b" :: ty.addr; "e" :: ty.addr; "a" :: ty.addr]%ctx in
    let c  : Term Σ _ := term_record capability [term_var "p"; term_var "b"; term_var "e"; term_var "a"] in
    {| lemma_logic_variables := Σ;
       lemma_patterns        := (env.snoc env.nil (_∷_) c);
       lemma_precondition    := asn_csafe c ∗ term_var "p" = term_val ty.perm E;
       lemma_postcondition   :=
         asn.exist "p'" ty.perm
                   (let c : Term _ _ := term_record capability [term_var "p'"; term_var "b"; term_var "e"; term_var "a"] in
                    term_var "p'" = term_val ty.perm R ∗ asn_expr c);
    |}.

  Definition lemma_open_ptsreg : SepLemma open_ptsreg :=
    {| lemma_logic_variables := [ "reg" ∷ ty.enum regname; "w" ∷ ty.word];
       lemma_patterns        := [term_var "reg"];
       lemma_precondition    := term_var "reg" ↦r term_var "w";
       lemma_postcondition   :=
         asn.match_enum
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
       lemma_precondition    := asn_csafe c ∗ term_var "p" ≠ₚ term_val ty.perm E;
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
         asn_csafe c ∗ term_var "p'" <=ₚ term_var "p" ∗ asn_IH;
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
         term_var "p" ≠ₚ term_val ty.perm E ∗
         asn_IH ∗
         asn.formula
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
       lemma_precondition    := ⊤;
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
         term_var "wM_result" = term_val ty.unit tt
    |}.

  Definition sep_contract_dI : SepContractFunX dI :=
    {| sep_contract_logic_variables := ["code" ∷ ty.int];
       sep_contract_localstore      := [term_var "code"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "_";
       sep_contract_postcondition   := ⊤;
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
      | open_ptsreg         => lemma_open_ptsreg
      | close_ptsreg r      => lemma_close_ptsreg r
      | open_gprs           => lemma_open_gprs
      | close_gprs          => lemma_close_gprs
      | safe_move_cursor    => lemma_safe_move_cursor
      | safe_sub_perm       => lemma_safe_sub_perm
      | safe_within_range   => lemma_safe_within_range
      | int_safe            => lemma_int_safe
      | correctPC_subperm_R => lemma_correctPC_subperm_R
      | subperm_not_E       => lemma_subperm_not_E
      | safe_to_execute     => lemma_safe_to_execute
      end.

  Lemma linted_cenvex :
    forall Δ τ (f : FunX Δ τ),
      Linted (CEnvEx f).
  Proof.
    intros ? ? []; try constructor.
  Qed.

End ContractDefKit.

End MinCapsSpecification.

Module MinCapsSolverKit <: SolverKit MinCapsBase MinCapsSignature.
  Definition simplify_subperm {Σ} (p q : Term Σ ty.perm) : option (List Formula Σ) :=
    match term_get_val p, term_get_val q with
    | Some O , _       => Some nil
    | Some p', Some q' => if decide_subperm p' q' then Some nil else None
    | _      , _       => Some (cons (formula_user subperm [p;q]) nil)
    end.

  (* Equations(noeqns) simplify_subperm {Σ} (p q : Term Σ ty.perm) : option (List Formula Σ) :=
  | term_val p | term_val q := if decide_subperm p q then Some nil else None;
  | term_val O | q          := Some nil;
  | p          | q          :=
    let ts := env.nil ► (ty.perm ↦ p) ► (ty.perm ↦ q) in
    Some (cons (formula_user subperm ts) nil). *)

  Definition simplify_correctPC {Σ} (c : Term Σ ty.cap) : option (List Formula Σ) :=
    match term_get_record c with
    | Some c' => match term_get_val c'.[??"cap_permission"] with
                 | Some O => None
                 | Some E => None
                 | Some _ =>
                     let b := c'.[??"cap_begin"] in
                     let e := c'.[??"cap_end"] in
                     let a := c'.[??"cap_cursor"] in
                     Some (cons (formula_bool (term_binop bop.and
                                                          (term_binop bop.le b a)
                                                          (term_binop bop.lt a e))) nil)
                 | None   => Some (cons (formula_user correctPC [c]) nil)
                 end
    | _       => Some (cons (formula_user correctPC [c]) nil)
    end.

  Definition simplify_not_is_perm {Σ} (p q : Term Σ ty.perm) : option (List Formula Σ) :=
    match term_get_val p, term_get_val q with
    | Some p', Some q' => if negb (is_perm p' q') then Some nil else None
    | _      , _       => Some (cons (formula_user not_is_perm [p;q]) nil)
    end.

  Definition solve_user : SolverUserOnly :=
    fun Σ p =>
      match p with
      | subperm     => fun ts =>
                         let (ts,q) := env.snocView ts in
                         let (ts,p) := env.snocView ts in
                         simplify_subperm p q
      | correctPC   => fun ts =>
                         let (ts,c) := env.snocView ts in
                         simplify_correctPC c
      | not_is_perm => fun ts =>
                         let (ts,q) := env.snocView ts in
                         let (ts,p) := env.snocView ts in
                         simplify_not_is_perm p q
      end.

  Lemma subperm_O : forall p, Subperm O p.
  Proof. destruct p; reflexivity. Qed.

  Local Ltac lsolve_match x :=
    match x with
    | @term_get_val ?Σ ?σ ?v =>
        destruct (@term_get_val_spec Σ σ v); subst;
        try progress cbn
    | match ?x with _ => _ end =>
        lsolve_match x
    end.

  Local Ltac lsolve :=
    repeat
      lazymatch goal with
      | |- option.spec _ _ (match ?x with _ => _ end) =>
          lsolve_match x
      | |- option.spec _ _ (Some _) =>
          constructor; cbn; try intuition fail
      | |- option.spec _ _ None =>
          constructor; cbn; try intuition fail
      end; auto.

  Lemma solve_user_spec : SolverUserOnlySpec solve_user.
  Proof.
    intros Σ p ts.
    destruct p; cbv in ts; env.destroy ts; cbn.
    - dependent elimination v0.
      + constructor. cbn. intuition.
      + dependent elimination v.
        * destruct v0; constructor; cbn; auto; intuition. apply subperm_O.
        * destruct v, v0; constructor; cbn; auto; unfold Subperm; intuition.
        * dependent elimination op.
      + dependent elimination op.
    - dependent elimination v.
      + constructor. cbn. intuition.
      + destruct v.
        unfold CorrectPC.
        cbn.
        destruct cap_permission; constructor; cbn; auto; intuition;
          try (apply andb_prop in H; destruct H as [H _];
               apply andb_prop in H; destruct H as [H1 H2];
               apply Bool.andb_true_iff; split; intuition).
      + constructor. cbn. intuition.
      + cbn in es; env.destroy es.
        unfold CorrectPC, simplify_correctPC.
        dependent elimination v2.
        * constructor; cbn; intuition.
        * destruct v2; constructor; cbn; auto; intuition;
            apply andb_prop in H as [H _]; auto.
        * dependent elimination op.
    - dependent elimination v0.
      + constructor. cbn. intuition.
      + dependent elimination v.
        * constructor. cbn. intuition.
        * destruct v, v0; constructor; cbn; auto; unfold Not_is_perm; intuition.
        * dependent elimination op.
      + dependent elimination op.
  Qed.

  Definition solver : Solver :=
    solveruseronly_to_solver solve_user.

  Lemma solver_spec : SolverSpec solver.
  Proof.
    apply solveruseronly_to_solver_spec, solve_user_spec.
  Qed.

End MinCapsSolverKit.
Module MinCapsSolver :=
  MakeSolver MinCapsBase MinCapsSignature MinCapsSolverKit.
Module Import MinCapsExecutor :=
  MakeExecutor MinCapsBase MinCapsProgram MinCapsSignature MinCapsSpecification MinCapsSolver.
Module Import MinCapsShallowExec :=
  MakeShallowExecutor MinCapsBase MinCapsProgram MinCapsSignature MinCapsSpecification.

Module MinCapsValidContracts.
  Import MinCapsExecutor.

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
             cbv [SymProp.safe env.remove env.lookup bop.eval is_true
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
    | Some c => Symbolic.ValidContractReflect c (FunDef f)
    | None => False
    end.

  Definition ValidContractDebug {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContract c (FunDef f)
    | None => False
    end.

  Ltac symbolic_simpl :=
    apply Symbolic.validcontract_with_erasure_sound;
    compute;
    constructor;
    cbn.

  Lemma valid_contract_read_reg : ValidContract read_reg.
  Proof. reflexivity. Qed.

  Lemma valid_contract_read_reg_cap : ValidContract read_reg_cap.
  Proof. reflexivity. Qed.

  Lemma valid_contract_read_reg_num : ValidContract read_reg_num.
  Proof. reflexivity. Qed.

  Lemma valid_contract_write_reg : ValidContract write_reg.
  Proof. reflexivity. Qed.

  Lemma valid_contract_next_pc : ValidContract next_pc.
  Proof. reflexivity. Qed.

  Lemma valid_contract_update_pc : ValidContract update_pc.
  Proof. reflexivity. Qed.

  Lemma valid_contract_update_pc_perm : ValidContract update_pc_perm.
  Proof. reflexivity. Qed.

  Lemma valid_contract_is_correct_pc : ValidContract is_correct_pc.
  Proof. reflexivity. Qed.

  Lemma valid_contract_is_perm : ValidContract MinCapsProgram.is_perm.
  Proof. reflexivity. Qed.

  Lemma valid_contract_add_pc : ValidContract add_pc.
  Proof. reflexivity. Qed.

  Lemma valid_contract_read_mem : ValidContract read_mem.
  Proof. reflexivity. Qed.

  Lemma valid_contract_write_mem : ValidContract write_mem.
  Proof. reflexivity. Qed.

  Lemma valid_contract_read_allowed : ValidContract read_allowed.
  Proof. reflexivity. Qed.

  Lemma valid_contract_write_allowed : ValidContract write_allowed.
  Proof. reflexivity. Qed.

  Lemma valid_contract_upper_bound : ValidContract upper_bound.
  Proof. reflexivity. Qed.

  Lemma valid_contract_within_bounds : ValidContract within_bounds.
  Proof. reflexivity. Qed.

  Lemma valid_contract_perm_to_bits : ValidContract perm_to_bits.
  Proof. reflexivity. Qed.

  Lemma valid_contract_perm_from_bits : ValidContract perm_from_bits.
  Proof. reflexivity. Qed.

  Lemma valid_contract_is_sub_perm : ValidContract is_sub_perm.
  Proof. reflexivity. Qed.

  Lemma valid_contract_is_within_range : ValidContract is_within_range.
  Proof. reflexivity. Qed.

  Lemma valid_contract_abs : ValidContract abs.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_jalr : ValidContract exec_jalr.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_jal : ValidContract exec_jal.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_bne : ValidContract exec_bne.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cmove : ValidContract exec_cmove.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_ld : ValidContract exec_ld.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_sd : ValidContract exec_sd.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_lea : ValidContract exec_lea.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_restrict : ValidContract exec_restrict.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_restricti : ValidContract exec_restricti.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_subseg : ValidContract exec_subseg.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_subsegi : ValidContract exec_subsegi.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_isptr : ValidContract exec_isptr.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_addi : ValidContract exec_addi.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_add : ValidContract exec_add.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_sub : ValidContract exec_sub.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_slt : ValidContract exec_slt.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_slti : ValidContract exec_slti.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_sltu : ValidContract exec_sltu.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_sltiu : ValidContract exec_sltiu.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cgetperm : ValidContract exec_cgetperm.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cgetbase : ValidContract exec_cgetbase.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cgetlen : ValidContract exec_cgetlen.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cgetaddr : ValidContract exec_cgetaddr.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_fail : ValidContract exec_fail.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_ret : ValidContract exec_ret.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_instr : ValidContract exec_instr.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec : ValidContract exec.
  Proof. reflexivity. Qed.

  Lemma valid_contract_step : ValidContract step.
  Proof. reflexivity. Qed.

  Lemma valid_contract : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContract f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContract in Hvc.
    rewrite Hcenv in Hvc.
    apply Symbolic.validcontract_reflect_sound.
    apply Hvc.
  Qed.

  Lemma valid_contract_debug : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContractDebug f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContractDebug in Hvc.
    rewrite Hcenv in Hvc.
    apply Hvc.
  Qed.

  Lemma ValidContracts : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros; destruct f.
    - apply (valid_contract _ H valid_contract_read_reg).
    - apply (valid_contract _ H valid_contract_read_reg_cap).
    - apply (valid_contract _ H valid_contract_read_reg_num).
    - apply (valid_contract _ H valid_contract_write_reg).
    - apply (valid_contract _ H valid_contract_next_pc).
    - apply (valid_contract _ H valid_contract_update_pc).
    - apply (valid_contract _ H valid_contract_update_pc_perm).
    - apply (valid_contract _ H valid_contract_is_correct_pc).
    - apply (valid_contract _ H valid_contract_is_perm).
    - apply (valid_contract _ H valid_contract_add_pc).
    - apply (valid_contract _ H valid_contract_read_mem).
    - apply (valid_contract _ H valid_contract_write_mem).
    - apply (valid_contract _ H valid_contract_read_allowed).
    - apply (valid_contract _ H valid_contract_write_allowed).
    - apply (valid_contract _ H valid_contract_upper_bound).
    - apply (valid_contract _ H valid_contract_within_bounds).
    - apply (valid_contract _ H valid_contract_perm_to_bits).
    - apply (valid_contract _ H valid_contract_perm_from_bits).
    - apply (valid_contract _ H valid_contract_is_sub_perm).
    - apply (valid_contract _ H valid_contract_is_within_range).
    - apply (valid_contract _ H valid_contract_abs).
    - apply (valid_contract _ H valid_contract_exec_jalr).
    - apply (valid_contract _ H valid_contract_exec_jal).
    - apply (valid_contract _ H valid_contract_exec_bne).
    - apply (valid_contract _ H valid_contract_exec_cmove).
    - apply (valid_contract _ H valid_contract_exec_ld).
    - apply (valid_contract _ H valid_contract_exec_sd).
    - apply (valid_contract _ H valid_contract_exec_lea).
    - apply (valid_contract _ H valid_contract_exec_restrict).
    - apply (valid_contract _ H valid_contract_exec_restricti).
    - apply (valid_contract _ H valid_contract_exec_subseg).
    - apply (valid_contract _ H valid_contract_exec_subsegi).
    - apply (valid_contract _ H valid_contract_exec_isptr).
    - apply (valid_contract _ H valid_contract_exec_addi).
    - apply (valid_contract _ H valid_contract_exec_add).
    - apply (valid_contract _ H valid_contract_exec_sub).
    - apply (valid_contract _ H valid_contract_exec_slt).
    - apply (valid_contract _ H valid_contract_exec_slti).
    - apply (valid_contract _ H valid_contract_exec_sltu).
    - apply (valid_contract _ H valid_contract_exec_sltiu).
    - apply (valid_contract _ H valid_contract_exec_cgetperm).
    - apply (valid_contract _ H valid_contract_exec_cgetbase).
    - apply (valid_contract _ H valid_contract_exec_cgetlen).
    - apply (valid_contract _ H valid_contract_exec_cgetaddr).
    - apply (valid_contract _ H valid_contract_exec_fail).
    - apply (valid_contract _ H valid_contract_exec_ret).
    - apply (valid_contract _ H valid_contract_exec_instr).
    - apply (valid_contract _ H valid_contract_exec).
    - apply (valid_contract _ H valid_contract_step).
    - cbn in H; inversion H.
  Qed.

  Goal True. idtac "Timing before: minimalcaps". Abort.
  Lemma valid_contracts : forall {Δ τ} (f : Fun Δ τ),
      ValidContract f.
  Proof.
  (* destruct f; reflexivity.
Qed. *)
  Admitted.
  Goal True. idtac "Timing after: minimalcaps". Abort.

  Goal True. idtac "Assumptions for minimalcaps contracts:". Abort.
  Print Assumptions valid_contracts.
End MinCapsValidContracts.

Section Statistics.
  Import List.ListNotations.

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
      existT _ (existT _ exec_jalr);
      existT _ (existT _ exec_jal);
      existT _ (existT _ exec_bne);
      existT _ (existT _ exec_cmove);
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
      existT _ (existT _ exec_cgetperm);
      existT _ (existT _ exec_cgetbase);
      existT _ (existT _ exec_cgetlen);
      existT _ (existT _ exec_cgetaddr);
      existT _ (existT _ exec_fail);
      existT _ (existT _ exec_ret);
      existT _ (existT _ exec_instr);
      existT _ (existT _ exec);
      existT _ (existT _ step);
      existT _ (existT _ loop)
    ]%list.

  Definition symbolic_stats : Stats :=
    List.fold_right
      (fun '(existT _ (existT _ f)) r =>
         match Symbolic.Statistics.calc f with
         | Some s => plus_stats s r
         | None   => r
         end)
      empty_stats
      all_functions.

  Goal True.
    idtac "Symbolic branching statistics:".
    let t := eval compute in symbolic_stats in idtac t.
  Abort.

  (* The counting of the shallow nodes is too slow in Ltac. Hence there is and
     alternative command line solution. *)

End Statistics.
