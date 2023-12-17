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
  Strings.String
  ZArith.ZArith
  Classes.EquivDec
  micromega.Lia.

From Equations Require Import
  Equations.

From Katamaran Require Import
  MinimalCaps.Base
  Notations
  Specification
  Symbolic.Solver.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope ctx_scope.
Open Scope Z_scope.

(* PurePredicates used for the contracts. These are not spatial, i.e., they are
   duplicable. *)
Inductive PurePredicate : Set :=
| subperm
| correctPC
| not_is_perm
.

(* Predicate denotes the spatial predicates used in this case study. *)
Inductive Predicate : Set :=
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
    (* decide_subperm is the decision procedure that determines whether p is a
     subpermission of p' according to the permission lattice given above. *)
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

    (* Subperm is the predicate implementation using the decision procedure *)
    Definition Subperm (p p' : Val ty.perm) : Prop :=
      decide_subperm p p' = true.

    Lemma Subperm_refl : forall (p : Val ty.perm),
        Subperm p p.
    Proof. destruct p; simpl; reflexivity. Qed.

    (* decide_correct_pc returns a boolean indicating whether a pc is correct.  A
     correct pc means that it doesn't have the E permission and the cursor is
     within bounds. *)
    Definition decide_correct_pc (c : Val ty.cap) : bool :=
      match c with
      | {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |} =>
          (b <=? a) && (a <? e) && (Base.is_perm p R || Base.is_perm p RW)
      end.

    (* CorrectPC is the predicate implementation of decide_correct_pc. *)
    Definition CorrectPC (c : Val ty.cap) : Prop :=
      decide_correct_pc c = true.

    (* Not_is_perm is the negation of is_perm as a Prop. *)
    Definition Not_is_perm :=
      complement (@Equivalence.equiv _ _ (@eq_equivalence Permission)).

    Lemma is_perm_Not_is_perm_false (p p' : Val ty.perm) :
      Not_is_perm p p' -> Base.is_perm p p' = false.
    Proof.
      unfold Not_is_perm, equiv, complement.
      destruct (Base.is_perm p p') eqn:E; auto.
      apply is_perm_iff in E; subst.
      intros H.
      exfalso; exact (H eq_refl).
    Qed.

    (* 𝑷_inst instructs Katamaran how our defined predicates for this case can be
     instantiated. *)
    Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
      match p with
      | subperm     => Subperm
      | correctPC   => CorrectPC
      | not_is_perm => Not_is_perm
      end.

    Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

    Definition 𝑯 := Predicate.
    (* 𝑯_Ty defines the signatures of the spatial predicates. *)
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | ptsto   => [ty.addr; ty.memval]
      | safe    => [ty.word]
      | expr    => [ty.cap]
      | gprs    => []
      | ih      => []
      | wp_loop => []
      end.
    (* 𝑯_is_dup specifies which predicates are duplicable. A spatial predicate can
     be duplicable if it is timeless. Note that spatial predicates are defined
     using the Iris logic, while pure predicates are defined using standard
     Coq. *)
    Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
        is_duplicable p :=
          match p with
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
    (* 𝑯_precise specifies which predicates are precise and gives information
     about the input and output parameters of a predicate. *)
    Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
      match p with
      | ptsto => Some (MkPrecise [ty.addr] [ty.memval] eq_refl)
      | _ => None
      end.

  End PredicateKit.

  Include PredicateMixin MinCapsBase.
  Include WorldsMixin MinCapsBase.

  (* In the MinCapsSolverKit we provide simplification procedures for the pure
     predicates and prove that these simplifiers are sound. *)
  Section MinCapsSolverKit.
    Open Scope string.
    #[local] Arguments Some {_} _%ctx.

    Definition simplify_subperm {Σ} (p q : Term Σ ty.perm) : option (PathCondition Σ) :=
      match term_get_val p, term_get_val q with
      | Some O , _       => Some []
      | Some p', Some q' => if decide_subperm p' q' then Some [] else None
      | _      , _       => Some [formula_user subperm [p;q]]
      end%ctx.

    Definition simplify_correctPC {Σ} (c : Term Σ ty.cap) : option (PathCondition Σ) :=
      match term_get_record c with
      | Some c' => match term_get_val c'.[??"cap_permission"] with
                   | Some O => None
                   | Some E => None
                   | Some _ =>
                       let b := c'.[??"cap_begin"] in
                       let e := c'.[??"cap_end"] in
                       let a := c'.[??"cap_cursor"] in
                       Some [formula_bool (term_binop bop.and
                                             (term_binop (bop.relop bop.le) b a)
                                             (term_binop (bop.relop bop.lt) a e))]
                   | None   => Some [formula_user correctPC [c]]
                   end
      | _       => Some [formula_user correctPC [c]]
      end%ctx.

    Definition simplify_not_is_perm {Σ} (p q : Term Σ ty.perm) : option (PathCondition Σ) :=
      match term_get_val p, term_get_val q with
      | Some p', Some q' => if negb (Base.is_perm p' q') then Some [] else None
      | _      , _       => Some [formula_user not_is_perm [p;q]]
      end.

    Definition solve_user : SolverUserOnly :=
      fun Σ p =>
        match p with
        | subperm     => fun ts =>
                           let (ts,q) := env.view ts in
                           let (ts,p) := env.view ts in
                           simplify_subperm p q
        | correctPC   => fun ts =>
                           let (ts,c) := env.view ts in
                           simplify_correctPC c
        | not_is_perm => fun ts =>
                           let (ts,q) := env.view ts in
                           let (ts,p) := env.view ts in
                           simplify_not_is_perm p q
        end.

    Lemma subperm_O : forall p, Subperm O p.
    Proof. destruct p; reflexivity. Qed.

    Import Entailment.

    Local Ltac lsolve :=
      repeat
        lazymatch goal with
        | |- Some _             ⊣⊢ Some _             => apply @proper_some
        | |- ctx.snoc ctx.nil _ ⊣⊢ ctx.snoc ctx.nil _ => apply proper_snoc; [easy|]
        | |- None               ⊣⊢ Some _             => apply @unsatisfiable_none_some
        | |- Unsatisfiable (ctx.snoc ctx.nil _)       => apply unsatisfiable_snoc_r
        | op : BinOp _ _ ty.perm |- _                 => dependent elimination op
        end; try easy; auto.

    Lemma solve_user_spec : SolverUserOnlySpec solve_user.
    Proof.
      intros Σ p ts.
      destruct p; cbv in ts; env.destroy ts; cbn.
      - dependent elimination v0; lsolve.
        dependent elimination v; lsolve.
        * destruct v0; cbn; lsolve.
        * destruct v, v0; cbn; lsolve.
      - dependent elimination v; lsolve.
        + destruct v as [[] b e a]; cbn; lsolve;
            intros ι; cbn; unfold CorrectPC; cbn; lia.
        + cbn in ts0; env.destroy ts0.
          dependent elimination v2; cbn; lsolve.
          destruct v2; lsolve;
            intros ι; cbn; unfold CorrectPC; cbn; try lia.
      - dependent elimination v0; lsolve.
        dependent elimination v; lsolve.
        destruct v, v0; cbn; lsolve.
        all: (intros ι []; cbn; intuition auto; try easy).
    Qed.

    Definition solver : Solver :=
      solveruseronly_to_solver solve_user.

    Lemma solver_spec : SolverSpec solver.
    Proof.
      apply solveruseronly_to_solver_spec, solve_user_spec.
    Qed.

  End MinCapsSolverKit.

  Include SignatureMixin MinCapsBase.

  Module MinCapsContractNotations.
    Export asn.notations.
    Open Scope env_scope.
    Open Scope string.

    Notation "x '≠' y" := (asn.formula (formula_relop bop.neq x y)) (at level 70) : asn_scope.
    Notation "p '<=ₚ' p'" := (asn.formula (formula_user subperm (env.nil ► (ty.perm ↦ p) ► (ty.perm ↦ p')))) (at level 70).

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
                                    (term_binop (bop.relop bop.le) b a)
                                    (term_binop (bop.relop bop.le) a e)))).
  End MinCapsContractNotations.

  (* Note: Using *Lemma in definition body messes up coqwc... *)
  Definition KatamaranLem := Lemma.

  Section ContractDefKit.
    Import MinCapsContractNotations.

    (* Arguments asn_prop [_] & _. *)

    (* sep_contract_logvars is a helper function to extract the minimum required
     logical variables from a function signature. *)
    Definition sep_contract_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
      ctx.map (fun '(x::σ) => x::σ) Δ ▻▻ Σ.

    (* create_localstore returns a localstore based on a function signature. *)
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

    (* regInvCap(r) = ∃ c : cap. r ↦ c * csafe(c) *)
    Definition regInvCap {Σ} (r : Reg ty.cap) : Assertion Σ :=
      asn.exist "c" ty.cap
        (r ↦ term_var "c" ∗
           asn_csafe (term_var "c")).

    (* asn_and_regs is an assertion that takes a function with one parameter, a
     register. This function is applied for each register of the machine. *)
    Definition asn_and_regs {Σ} (f : Reg ty.word -> Assertion Σ) : Assertion Σ :=
      f reg1 ∗ f reg2 ∗ f reg3.

    (* asn_regs_ptsto_safe = ∀ r ∈ GPRs. regInv(r) *)
    Definition asn_regs_ptsto_safe {Σ} : Assertion Σ :=
      asn_and_regs regInv.

    (* asn_pc_correct(r) = ∃ c : cap. r ↦ c ∗ csafe(c) ∗ correctPC(c) *)
    Definition asn_pc_correct {Σ} (r : Reg ty.cap) : Assertion Σ :=
      asn.exist "c" ty.cap (r ↦ term_var "c" ∗
                              asn_csafe (term_var "c") ∗
                              asn_correctPC (term_var "c")).

    (* asn_pc_safe(r) = ∃ c : cap. r ↦ c ∗ csafe(c) *)
    Definition asn_pc_safe {Σ} (r : Reg ty.cap) : Assertion Σ :=
      asn.exist "c" ty.cap (r ↦ term_var "c" ∗
                              asn_csafe (term_var "c")).

    (* asn_pc_expr(r) = ∃ c : cap. r ↦ c ∗ expr(c) *)
    Definition asn_pc_expr {Σ} (r : Reg ty.cap) : Assertion Σ :=
      asn.exist "c" ty.cap (r ↦ term_var "c" ∗
                              asn_expr (term_var "c")).

  End ContractDefKit.

End MinCapsSignature.
