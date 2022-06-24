(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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
     Arith.PeanoNat
     Bool.Bool
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations
     Classes.RelationClasses
     Relations.Relation_Definitions
     Lists.List
     NArith.NArith
     Program.Tactics
     Strings.String
     ZArith.BinInt.
From Coq Require
     Classes.CRelationClasses.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Symbolic.Propositions
     Symbolic.Worlds
     Syntax.ContractDecl
     Specification
     Base.

From stdpp Require
     base.

Import ctx.notations.
Import env.notations.
Import ListNotations.

Set Implicit Arguments.

Module Type SymbolicExecOn
  (Import B : Base)
  (Import SIG : ProgramLogicSignature B)
  (Import SPEC : Specification B SIG)
  (Import SOLV : SolverKit B SIG).

  Import Entailment.
  Import ModalNotations.
  Local Open Scope modal.

  Section DebugInfo.

    Record DebugCall (Σ : LCtx) : Type :=
      MkDebugCall
        { debug_call_function_parameters    : PCtx;
          debug_call_function_result_type   : Ty;
          debug_call_function_name          : 𝑭 debug_call_function_parameters debug_call_function_result_type;
          debug_call_function_contract      : SepContract debug_call_function_parameters debug_call_function_result_type;
          debug_call_function_arguments     : SStore debug_call_function_parameters Σ;
          debug_call_program_context        : PCtx;
          debug_call_pathcondition          : PathCondition Σ;
          debug_call_localstore             : SStore debug_call_program_context Σ;
          debug_call_heap                   : SHeap Σ;
        }.

    Record DebugStm (Σ : LCtx) : Type :=
      MkDebugStm
        { debug_stm_program_context        : PCtx;
          debug_stm_statement_type         : Ty;
          debug_stm_statement              : Stm debug_stm_program_context debug_stm_statement_type;
          debug_stm_pathcondition          : PathCondition Σ;
          debug_stm_localstore             : SStore debug_stm_program_context Σ;
          debug_stm_heap                   : SHeap Σ;
        }.

    Record DebugAsn (Σ : LCtx) : Type :=
      MkDebugAsn
        { debug_asn_program_context        : PCtx;
          debug_asn_pathcondition          : PathCondition Σ;
          debug_asn_localstore             : SStore debug_asn_program_context Σ;
          debug_asn_heap                   : SHeap Σ;
        }.

    Record DebugConsumeChunk (Σ : LCtx) : Type :=
      MkDebugConsumeChunk
        { debug_consume_chunk_program_context        : PCtx;
          debug_consume_chunk_pathcondition          : PathCondition Σ;
          debug_consume_chunk_localstore             : SStore debug_consume_chunk_program_context Σ;
          debug_consume_chunk_heap                   : SHeap Σ;
          debug_consume_chunk_chunk                  : Chunk Σ;
        }.

    Record DebugAssertFormula (Σ : LCtx) : Type :=
      MkDebugAssertFormula
        { debug_assert_formula_program_context : PCtx;
          debug_assert_formula_pathcondition   : PathCondition Σ;
          debug_assert_formula_localstore      : SStore debug_assert_formula_program_context Σ;
          debug_assert_formula_heap            : SHeap Σ;
          debug_assert_formula_formula         : Formula Σ;
        }.

    Global Instance SubstDebugCall : Subst DebugCall :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugCall f c ts pc δ h =>
          MkDebugCall f c (subst ts ζ01) (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    Global Instance SubstLawsDebugCall : SubstLaws DebugCall.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    Import option.notations.
    Global Instance OccursCheckDebugCall : OccursCheck DebugCall :=
      fun Σ x xIn d =>
        match d with
        | MkDebugCall f c ts pc δ h =>
            ts' <- occurs_check xIn ts ;;
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugCall f c ts' pc' δ' h')
        end.

    Global Instance SubstDebugStm : Subst DebugStm :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugStm s pc δ h =>
          MkDebugStm s (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    Global Instance SubstLawsDebugStm : SubstLaws DebugStm.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    Global Instance OccursCheckDebugStm : OccursCheck DebugStm :=
      fun Σ x xIn d =>
        match d with
        | MkDebugStm s pc δ h =>
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugStm s pc' δ' h')
        end.

    Global Instance SubstDebugAsn : Subst DebugAsn :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugAsn pc δ h =>
          MkDebugAsn (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    Global Instance SubstLawsDebugAsn : SubstLaws DebugAsn.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    Global Instance OccursCheckDebugAsn : OccursCheck DebugAsn :=
      fun Σ x xIn d =>
        match d with
        | MkDebugAsn pc δ h =>
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugAsn pc' δ' h')
        end.

    Global Instance SubstDebugConsumeChunk : Subst DebugConsumeChunk :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugConsumeChunk pc δ h c =>
          MkDebugConsumeChunk (subst pc ζ01) (subst δ ζ01) (subst h ζ01) (subst c ζ01)
        end.

    Global Instance OccursCheckDebugConsumeChunk : OccursCheck DebugConsumeChunk :=
      fun Σ x xIn d =>
        match d with
        | MkDebugConsumeChunk pc δ h c =>
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            c'  <- occurs_check xIn c ;;
            Some (MkDebugConsumeChunk pc' δ' h'  c')
        end.

    Global Instance SubstDebugAssertFormula : Subst DebugAssertFormula :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugAssertFormula pc δ h fml =>
          MkDebugAssertFormula (subst pc ζ01) (subst δ ζ01) (subst h ζ01) (subst fml ζ01)
        end.

    Global Instance SubstLawsDebugAssertFormula : SubstLaws DebugAssertFormula.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    Global Instance OccursCheckDebugAssertFormula : OccursCheck DebugAssertFormula :=
      fun Σ x xIn d =>
        match d with
        | MkDebugAssertFormula pc δ h fml =>
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            fml'  <- occurs_check xIn fml ;;
            Some (MkDebugAssertFormula pc' δ' h' fml')
        end.

  End DebugInfo.

  Module WorldInstance.

    Record WInstance (w : World) : Set :=
      MkWInstance
        { ιassign :> Valuation w;
          ιvalid  : instpc (wco w) ιassign;
        }.

    Program Definition winstance_formula {w} (ι : WInstance w) (fml : Formula w) (p : inst (A := Prop) fml ι) :
      WInstance (wformula w fml) :=
      {| ιassign := ι; |}.
    Next Obligation.
    Proof.
      intros. cbn.
      apply inst_pathcondition_cons. split; auto.
      apply ιvalid.
    Qed.

    Program Definition winstance_snoc {w} (ι : WInstance w) {b : 𝑺 ∷ Ty} (v : Val (type b)) :
      WInstance (wsnoc w b) :=
      {| ιassign := env.snoc (ιassign ι) b v; |}.
    Next Obligation.
    Proof.
      intros. unfold wsnoc. cbn [wctx wco].
      rewrite inst_subst, inst_sub_wk1.
      apply ιvalid.
    Qed.

    Program Definition winstance_subst {w} (ι : WInstance w) {x σ} {xIn : x∷σ ∈ w}
      (t : Term (w - x∷σ) σ) (p : inst t (env.remove (x∷σ) (ιassign ι) xIn) = env.lookup (ιassign ι) xIn) :
      WInstance (wsubst w x t) :=
      @MkWInstance (wsubst w x t) (env.remove _ (ιassign ι) xIn) _.
    Next Obligation.
      intros * p. cbn. rewrite inst_subst, <- inst_sub_shift in *.
      rewrite inst_sub_single_shift; auto using ιvalid.
    Qed.

    Program Definition instacc {w0 w1} (ω01 : w0 ⊒ w1) : WInstance w1 -> WInstance w0 :=
      match ω01 in (_ ⊒ w) return (WInstance w -> WInstance w0) with
      | acc_refl            => fun ι => ι
      | @acc_sub _ w1 ζ ent => fun ι1 => {| ιassign := inst ζ ι1; |}
      end.
    Next Obligation.
    Proof.
      intros. specialize (ent ι1).
      rewrite <- inst_subst.
      apply ent.
      apply ιvalid.
    Qed.

  End WorldInstance.

  Definition PROP : TYPE :=
    fun _ => Prop.

  Import SymProp.
  Import Postprocessing.

  Section VerificationConditions.

    Inductive VerificationCondition (p : 𝕊 ctx.nil) : Prop :=
    | vc (P : safe p env.nil).

    Lemma vc_debug (p : 𝕊 ctx.nil) (H : safe_debug p env.nil) : VerificationCondition p.
    Proof.
      constructor; now rewrite safe_debug_safe in H.
    Qed.

    Global Instance proper_vc : Proper (sequiv ctx.nil ==> iff) VerificationCondition.
    Proof. intros p q pq. split; intros []; constructor; now apply pq. Qed.

    Inductive VerificationConditionWithErasure (p : Erasure.ESymProp) : Prop :=
    | vce (P : Erasure.inst_symprop nil p).

  End VerificationConditions.

  Definition SPureSpecM (A : TYPE) : TYPE :=
    □(A -> 𝕊) -> 𝕊.

  Module SPureSpecM.

    Definition pure {A : TYPE} :
      ⊢ A -> SPureSpecM A :=
      fun w0 a POST => T POST a.

    Definition map {A B} :
      ⊢ □(A -> B) -> SPureSpecM A -> SPureSpecM B :=
      fun w0 f m POST => m (comp <$> POST <*> f).

    Definition bind {A B} :
      ⊢ SPureSpecM A -> □(A -> SPureSpecM B) -> SPureSpecM B :=
      fun w0 m f POST => m (fun w1 ω01 a1 => f w1 ω01 a1 (four POST ω01)).

    Definition error {M A} {subM : Subst M} {occM : OccursCheck M} :
      ⊢ M -> SPureSpecM A := fun w msg POST => SymProp.error (EMsgHere msg).
    Definition block {A} : ⊢ SPureSpecM A :=
      fun w POST => SymProp.block.
    Global Arguments block {A w}.

    Definition angelic (x : option 𝑺) σ :
      ⊢ SPureSpecM (STerm σ) :=
      fun w k =>
        let y := fresh w x in
        angelicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    Global Arguments angelic x σ {w} k.

    Local Notation "⟨ ω ⟩ x <- ma ;; mb" :=
      (bind ma (fun _ ω x => mb))
        (at level 80, x at next level,
          ma at next level, mb at level 200,
          right associativity).

    Local Notation "⟨ w , ω ⟩ x <- ma ;; mb" :=
      (bind ma (fun w ω x => mb))
        (at level 80, x at next level,
          ma at next level, mb at level 200,
          right associativity, only printing).
    Notation "x ⟨ ω ⟩" := (persist x ω) (at level 9, format "x ⟨ ω ⟩").

    Local Hint Extern 2 (Persistent (WTerm ?σ)) =>
      refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.

    Definition angelic_ctx {N : Set} (n : N -> 𝑺) :
      ⊢ ∀ Δ : NCtx N Ty, SPureSpecM (fun w => NamedEnv (Term w) Δ) :=
      fix rec {w} Δ {struct Δ} :=
        match Δ with
         | []%ctx => pure []
         | Γ ▻ x∷σ => ⟨ _  ⟩ tσ <- angelic (Some (n x)) σ;;
                      ⟨ ω2 ⟩ tΔ <- rec Γ;;
                      pure (tΔ ► (x∷σ ↦ tσ⟨ω2⟩))
         end.
    Global Arguments angelic_ctx {N} n [w] Δ : rename.

    Definition demonic (x : option 𝑺) σ :
      ⊢ SPureSpecM (STerm σ) :=
      fun w k =>
        let y := fresh w x in
        demonicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    Global Arguments demonic x σ {w} k.

    Definition demonic_ctx {N : Set} (n : N -> 𝑺) :
      ⊢ ∀ Δ : NCtx N Ty, SPureSpecM (fun w => NamedEnv (Term w) Δ) :=
      fix demonic_ctx {w} Δ {struct Δ} :=
        match Δ with
        | []      => fun k => T k env.nil
        | Δ ▻ x∷σ =>
          fun k =>
            demonic (Some (n x)) σ (fun w1 ω01 t =>
              demonic_ctx Δ (fun w2 ω12 EΔ =>
                k w2 (acc_trans ω01 ω12) (EΔ ► (x∷σ ↦ persist__term t ω12))))
        end%ctx.
    Global Arguments demonic_ctx {_} n [w] Δ : rename.

    Definition assume_formulas :
      ⊢ List Formula -> SPureSpecM Unit :=
      fun w0 fmls0 POST =>
        match solver fmls0 with
        | Some (existT w1 (ν , fmls1)) =>
          (* Assume variable equalities and the residual constraints *)
          assume_triangular ν
            (assume_formulas_without_solver fmls1
               (* Run POST in the world with the variable and residual
                  formulas included. This is a critical piece of code since
                  this is the place where we really meaningfully change the
                  world. We changed the type of assume_formulas_without_solver
                  just to not forget adding the formulas to the path constraints.
               *)
               (four POST (acc_triangular ν) (acc_formulas_right w1 fmls1) tt))
        | None =>
          (* The formulas are inconsistent with the path constraints. *)
          SymProp.block
        end.

    Definition assume_formula :
      ⊢ Formula -> SPureSpecM Unit :=
      fun w0 fml0 =>
        assume_formulas (cons fml0 nil).

    Definition assert_formulas :
      ⊢ AMessage -> List Formula -> SPureSpecM Unit :=
      fun w0 msg fmls0 POST =>
        match solver fmls0 with
        | Some (existT w1 (ν , fmls1)) =>
          (* Assert variable equalities and the residual constraints *)
          assert_triangular msg ν
            (fun msg' =>
               assert_formulas_without_solver msg' fmls1
                 (* Critical code. Like for assume_formulas. *)
                 (four POST (acc_triangular ν) (acc_formulas_right w1 fmls1) tt))
        | None =>
          (* The formulas are inconsistent with the path constraints. *)
          SymProp.error (EMsgHere msg)
        end.

    Definition assert_formula :
      ⊢ AMessage -> Formula -> SPureSpecM Unit :=
      fun w0 msg fml0 =>
        assert_formulas msg (cons fml0 nil).

    Equations(noeqns) assert_eq_env {Δ : Ctx Ty} :
      let E := fun w : World => Env (Term w) Δ in
      ⊢ AMessage -> E -> E -> SPureSpecM Unit :=
      assert_eq_env msg env.nil          env.nil            := pure tt;
      assert_eq_env msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
        ⟨ ω ⟩ _ <- assert_eq_env msg δ δ' ;;
        assert_formula msg⟨ω⟩ (formula_eq t⟨ω⟩ t'⟨ω⟩).

    Equations(noeqns) assert_eq_nenv {N} {Δ : NCtx N Ty} :
      let E := fun w : World => NamedEnv (Term w) Δ in
      ⊢ AMessage -> E -> E -> SPureSpecM Unit :=
      assert_eq_nenv msg env.nil          env.nil            := pure tt;
      assert_eq_nenv msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
        ⟨ ω ⟩ _ <- assert_eq_nenv msg δ δ' ;;
        assert_formula msg⟨ω⟩ (formula_eq t⟨ω⟩ t'⟨ω⟩).

    Definition assert_eq_chunk : ⊢ AMessage -> Chunk -> Chunk -> □(SPureSpecM Unit).
      refine (
      fix assert_eq w0 msg c1 c2 w1 ω01 {struct c1} :=
        match c1 , c2 with
        | chunk_user p1 vs1 as c1 , chunk_user p2 vs2 as c2 =>
            match eq_dec p1 p2 with
            | left e => assert_eq_env msg⟨ω01⟩
                          (eq_rect p1 (fun p => Env (Term w1) (𝑯_Ty p)) vs1⟨ω01⟩ p2 e) vs2⟨ω01⟩
            | right _ => error msg⟨ω01⟩
            end
        | chunk_ptsreg r1 v1 as c1 , chunk_ptsreg r2 v2 as c2 =>
            match eq_dec_het r1 r2 with
            | left e => assert_formula msg⟨ω01⟩
                          (formula_eq (eq_rect _ (Term w1) v1⟨ω01⟩ _ (f_equal projT1 e)) v2⟨ω01⟩)
            | right _ => error msg⟨ω01⟩
            end
        | chunk_conj c11 c12 , chunk_conj c21 c22 =>
            ⟨ ω12 ⟩ _ <- assert_eq _ msg c11 c21 w1 ω01 ;;
            assert_eq _ msg c12 c22 _ (ω01 ∘ ω12)
        | chunk_wand c11 c12 , chunk_wand c21 c22 =>
            ⟨ ω12 ⟩ _ <- assert_eq _ msg c11 c21 w1 ω01 ;;
            assert_eq _ msg c12 c22 _ (ω01 ∘ ω12)
        | _ , _ => error msg⟨ω01⟩
        end).
      refine (persistent_subst).
    Defined.

    Definition angelic_binary {A} :
      ⊢ SPureSpecM A -> SPureSpecM A -> SPureSpecM A :=
      fun w m1 m2 POST =>
        angelic_binary (m1 POST) (m2 POST).
    Definition demonic_binary {A} :
      ⊢ SPureSpecM A -> SPureSpecM A -> SPureSpecM A :=
      fun w m1 m2 POST =>
        demonic_binary (m1 POST) (m2 POST).

    Definition angelic_list {M} {subM : Subst M} {occM : OccursCheck M} {A} :
      ⊢ M -> List A -> SPureSpecM A :=
      fun w msg =>
        fix rec xs :=
        match xs with
        | nil        => error msg
        | cons x xs  => angelic_binary (pure x) (rec xs)
        end.

    Definition demonic_list {A} :
      ⊢ List A -> SPureSpecM A :=
      fun w =>
        fix rec xs :=
        match xs with
        | nil        => block
        | cons x xs  => demonic_binary (pure x) (rec xs)
        end.

    Definition angelic_finite F `{finite.Finite F} :
      ⊢ AMessage -> SPureSpecM ⌜F⌝ :=
      fun w msg => angelic_list msg (finite.enum F).

    Definition demonic_finite F `{finite.Finite F} :
      ⊢ SPureSpecM ⌜F⌝ :=
      fun w => demonic_list (finite.enum F).

    Definition angelic_match_bool' :
      ⊢ AMessage -> STerm ty.bool -> SPureSpecM ⌜bool⌝ :=
      fun _ msg t =>
        angelic_binary
          (⟨_⟩ _ <- assert_formula msg (formula_bool t) ;;
                    pure true)
          (⟨_⟩ _ <- assert_formula msg (formula_bool (term_not t)) ;;
                    pure false).

    Definition angelic_match_bool :
      ⊢ AMessage -> STerm ty.bool -> SPureSpecM ⌜bool⌝ :=
      fun w msg t =>
        let t' := peval t in
        match term_get_val t' with
        | Some l => pure  l
        | None   => angelic_match_bool' msg t'
        end.

    Definition demonic_match_bool' :
      ⊢ STerm ty.bool -> SPureSpecM ⌜bool⌝ :=
      fun _ t =>
        demonic_binary
          (⟨_⟩ _ <- assume_formula (formula_bool t) ;;
                    pure true)
          (⟨_⟩ _ <- assume_formula (formula_bool (term_not t)) ;;
                    pure false).

    Definition demonic_match_bool :
      ⊢ STerm ty.bool -> SPureSpecM ⌜bool⌝ :=
      fun w t =>
        let t' := peval t in
        match term_get_val t' with
        | Some l => pure  l
        | None   => demonic_match_bool' t'
        end.

    Definition angelic_match_sum' {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ AMessage -> STerm (ty.sum σ τ) ->
        □(STerm σ -> SPureSpecM A) -> □(STerm τ -> SPureSpecM A) -> SPureSpecM A :=
      fun _ msg t kinl kinr =>
        angelic_binary
          (⟨ω1⟩ tl <- angelic (Some x) σ;;
           ⟨ω2⟩ _  <- assert_formula msg⟨ω1⟩ (formula_eq (term_inl tl) t⟨ω1⟩) ;;
                     T kinl⟨ω1∘ω2⟩ tl⟨ω2⟩)
          (⟨ω1⟩ tr <- angelic (Some y) τ;;
           ⟨ω2⟩ _  <- assert_formula msg⟨ω1⟩ (formula_eq (term_inr tr) t⟨ω1⟩);;
                     T kinr⟨ω1∘ω2⟩ tr⟨ω2⟩).

    Definition angelic_match_sum {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ AMessage -> STerm (ty.sum σ τ) -> □(STerm σ -> SPureSpecM A) -> □(STerm τ -> SPureSpecM A) -> SPureSpecM A :=
      fun w0 msg t kinl kinr =>
        match term_get_sum t with
        | Some (inl tσ) => T kinl tσ
        | Some (inr tτ) => T kinr tτ
        | None => angelic_match_sum' x y msg t kinl kinr
        end.

    Definition demonic_match_sum' {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty.sum σ τ) -> □(STerm σ -> SPureSpecM A) -> □(STerm τ -> SPureSpecM A) -> SPureSpecM A :=
      fun w0 t kinl kinr =>
       demonic_binary
         (⟨ω1⟩ t1 <- demonic (Some x) σ;;
          ⟨ω2⟩ _  <- assume_formula (formula_eq (term_inl t1) t⟨ω1⟩);;
                    T kinl⟨ω1∘ω2⟩ t1⟨ω2⟩)
         (⟨ω1⟩ t1 <- demonic (Some y) τ;;
          ⟨ω2⟩ _  <- assume_formula (formula_eq (term_inr t1) t⟨ω1⟩);;
                    T kinr⟨ω1∘ω2⟩ t1⟨ω2⟩).

    Definition demonic_match_sum {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty.sum σ τ) -> □(STerm σ -> SPureSpecM A) -> □(STerm τ -> SPureSpecM A) -> SPureSpecM A :=
      fun w0 t kinl kinr =>
        match term_get_sum t with
        | Some (inl tσ) => T kinl tσ
        | Some (inr tτ) => T kinr tτ
        | None => demonic_match_sum' x y t kinl kinr
        end.

    Definition angelic_match_prod {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ AMessage -> STerm (ty.prod σ τ) -> □(STerm σ -> STerm τ -> SPureSpecM A) -> SPureSpecM A :=
      fun _ msg t k =>
        ⟨ω1⟩ t1 <- angelic (Some x) σ;;
        ⟨ω2⟩ t2 <- angelic (Some y) τ;;
                  let ω12 := ω1 ∘ ω2 in
                  let fml := formula_eq (term_binop bop.pair t1⟨ω2⟩ t2) t⟨ω12⟩ in
        ⟨ω3⟩ _  <- assert_formula msg⟨ω12⟩ fml;;
                  T k⟨ω12∘ω3⟩ t1⟨ω2∘ω3⟩ t2⟨ω3⟩.

    Definition demonic_match_prod {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty.prod σ τ) -> □(STerm σ -> STerm τ -> SPureSpecM A) -> SPureSpecM A :=
      fun _ t k =>
        ⟨ω1⟩ t1 <- demonic (Some x) σ;;
        ⟨ω2⟩ t2 <- demonic (Some y) τ;;
                  let ω12 := ω1 ∘ ω2 in
                  let fml := formula_eq (term_binop bop.pair t1⟨ω2⟩ t2) t⟨ω12⟩ in
       ⟨ω3⟩ _   <- assume_formula fml;;
                  T k⟨ω12∘ω3⟩ t1⟨ω2∘ω3⟩ t2⟨ω3⟩.

    Global Instance proper_debug {B Σ b} : Proper (iff ==> iff) (@Debug B Σ b).
    Proof.
      intros P Q PQ.
      split; intros []; constructor; intuition.
    Qed.

  End SPureSpecM.

  Section Configuration.

    Record Config : Type :=
      MkConfig
        { config_debug_function : forall Δ τ, 𝑭 Δ τ -> bool;
        }.

    Definition default_config : Config :=
      {| config_debug_function _ _ f := false;
      |}.

  End Configuration.

  Definition SHeapSpecM (Γ1 Γ2 : PCtx) (A : TYPE) : TYPE :=
    □(A -> SStore Γ2 -> SHeap -> 𝕊) -> SStore Γ1 -> SHeap -> 𝕊.
  Bind Scope mut_scope with SHeapSpecM.

  Module SHeapSpecM.

    Local Hint Extern 2 (Persistent (WTerm ?σ)) =>
      refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.

    Section Basic.

      Definition lift_purem {Γ} {A : TYPE} :
        ⊢ SPureSpecM A -> SHeapSpecM Γ Γ A :=
        fun w0 m POST δ0 h0 =>
          m (fun w1 ω01 a1 => POST w1 ω01 a1 (persist δ0 ω01) (persist h0 ω01)).

      Definition pure {Γ} {A : TYPE} :
        ⊢ A -> SHeapSpecM Γ Γ A := fun _ a k => T k a.

      Definition bind {Γ1 Γ2 Γ3 A B} :
        ⊢ SHeapSpecM Γ1 Γ2 A -> □(A -> SHeapSpecM Γ2 Γ3 B) -> SHeapSpecM Γ1 Γ3 B :=
        fun w0 ma f k => ma (fun w1 ω01 a1 => f w1 ω01 a1 (four k ω01)).

      Definition bind_box {Γ1 Γ2 Γ3 A B} :
        ⊢ □(SHeapSpecM Γ1 Γ2 A) -> □(A -> SHeapSpecM Γ2 Γ3 B) -> □(SHeapSpecM Γ1 Γ3 B) :=
        fun w0 m f => bind <$> m <*> four f.

      Definition bind_right {Γ1 Γ2 Γ3 A B} :
        ⊢ SHeapSpecM Γ1 Γ2 A -> □(SHeapSpecM Γ2 Γ3 B) -> SHeapSpecM Γ1 Γ3 B :=
        fun _ m k POST => m (fun _ ω1 _ => k _ ω1 (four POST ω1)).

      Definition error {Γ1 Γ2 A D} (func : string) (msg : string) (data:D) :
        ⊢ SHeapSpecM Γ1 Γ2 A :=
        fun w _ δ h =>
          error
            (EMsgHere
               {| msg_function := func;
                  msg_message := msg;
                  msg_program_context := Γ1;
                  msg_localstore := δ;
                  msg_heap := h;
                  msg_pathcondition := wco w
               |}).
      Global Arguments error {_ _ _ _} func msg data {w} _ _.

      Definition block {Γ1 Γ2 A} :
        ⊢ SHeapSpecM Γ1 Γ2 A := fun _ POST δ h => block.

      Definition angelic_binary {Γ1 Γ2 A} :
        ⊢ SHeapSpecM Γ1 Γ2 A -> SHeapSpecM Γ1 Γ2 A -> SHeapSpecM Γ1 Γ2 A :=
        fun w m1 m2 POST δ1 h1 =>
          angelic_binary (m1 POST δ1 h1) (m2 POST δ1 h1).
      Definition demonic_binary {Γ1 Γ2 A} :
        ⊢ SHeapSpecM Γ1 Γ2 A -> SHeapSpecM Γ1 Γ2 A -> SHeapSpecM Γ1 Γ2 A :=
        fun w m1 m2 POST δ1 h1 =>
          demonic_binary (m1 POST δ1 h1) (m2 POST δ1 h1).

      Definition angelic_list {M} {subM : Subst M} {occM : OccursCheck M} {A Γ} :
        ⊢ (SStore Γ -> SHeap -> M) -> List A -> SHeapSpecM Γ Γ A :=
        fun w msg xs POST δ h => lift_purem (SPureSpecM.angelic_list (msg δ h) xs) POST δ h.

      Definition angelic_finite {Γ} F `{finite.Finite F} :
        ⊢ (SStore Γ -> SHeap -> AMessage) -> SHeapSpecM Γ Γ ⌜F⌝ :=
        fun w msg POST δ h => lift_purem (SPureSpecM.angelic_finite (msg δ h)) POST δ h.

      Definition demonic_finite {Γ} F `{finite.Finite F} :
        ⊢ SHeapSpecM Γ Γ ⌜F⌝ :=
        fun w => lift_purem (SPureSpecM.demonic_finite (w:=w)).
      Global Arguments demonic_finite {Γ} [_] {_ _} {w}.

      Definition angelic {Γ} (x : option 𝑺) σ :
        ⊢ SHeapSpecM Γ Γ (STerm σ) :=
        fun w => lift_purem (SPureSpecM.angelic x σ (w:=w)).
      Global Arguments angelic {Γ} x σ {w}.

      Definition demonic {Γ} (x : option 𝑺) σ :
        ⊢ SHeapSpecM Γ Γ (STerm σ) :=
        fun w => lift_purem (SPureSpecM.demonic x σ (w:=w)).
      Global Arguments demonic {Γ} x σ {w}.

      Definition debug {AT DT} `{Subst DT, SubstLaws DT, OccursCheck DT} {Γ1 Γ2} :
        ⊢ (SStore Γ1 -> SHeap -> DT) -> (SHeapSpecM Γ1 Γ2 AT) -> (SHeapSpecM Γ1 Γ2 AT) :=
        fun _ d m POST δ h => SymProp.debug (MkAMessage _ (d δ h)) (m POST δ h).

      Definition angelic_ctx {N : Set} (n : N -> 𝑺) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SHeapSpecM Γ Γ (fun w => NamedEnv (Term w) Δ) :=
        fun w0 Δ => lift_purem (SPureSpecM.angelic_ctx n Δ).
      Global Arguments angelic_ctx {N} n {Γ} [w] Δ : rename.

      Definition demonic_ctx {N : Set} (n : N -> 𝑺) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SHeapSpecM Γ Γ (fun w => NamedEnv (Term w) Δ) :=
        fun w0 Δ => lift_purem (SPureSpecM.demonic_ctx n Δ).
      Global Arguments demonic_ctx {N} n {Γ} [w] Δ : rename.

    End Basic.

    Module Import notations.

      (* Infix "⊗" := demonic_binary (at level 40, left associativity) : mut_scope. *)
      (* Infix "⊕" := angelic_binary (at level 50, left associativity) : mut_scope. *)

      (* Notation "x <- ma ;; mb" := (bind ma (fun _ _ x => mb)) (at level 80, ma at level 90, mb at level 200, right associativity) : mut_scope. *)
      (* Notation "ma >>= f" := (bind ma f) (at level 50, left associativity, only parsing) : mut_scope. *)
      (* Notation "ma >> mb" := (bind_right ma mb) (at level 50, left associativity, only parsing) : mut_scope. *)
      (* Notation "m1 ;; m2" := (bind_right m1 m2) : mut_scope. *)

      Notation "⟨ ω ⟩ x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 80, x at next level,
            ma at next level, mb at level 200,
            right associativity) : mut_scope.
                               (*  *)
      Notation "x ⟨ ω ⟩" := (persist x ω) (at level 9, format "x ⟨ ω ⟩").

    End notations.
    Local Open Scope mut_scope.

    Section AssumeAssert.

      (* Add the provided formula to the path condition. *)
      Definition assume_formula {Γ} :
        ⊢ Formula -> SHeapSpecM Γ Γ Unit.
      Proof.
        intros w0 fml. apply lift_purem.
        apply (SPureSpecM.assume_formula fml).
      Defined.

      Definition box_assume_formula {Γ} :
        ⊢ Formula -> □(SHeapSpecM Γ Γ Unit) :=
        fun w0 fml => assume_formula <$> persist fml.

      Definition assert_formula {Γ} :
        ⊢ Formula -> SHeapSpecM Γ Γ Unit :=
        fun w0 fml POST δ0 h0 =>
          lift_purem
            (SPureSpecM.assert_formula
               (MkAMessage _ (MkDebugAssertFormula (wco w0) δ0 h0 fml)) fml)
            POST δ0 h0.

      Definition box_assert_formula {Γ} :
        ⊢ Formula -> □(SHeapSpecM Γ Γ Unit) :=
        fun w0 fml => assert_formula <$> persist fml.

      Definition assert_formulas {Γ} :
        ⊢ List Formula -> SHeapSpecM Γ Γ Unit.
      Proof.
        intros w0 fmls POST δ0 h0.
        eapply lift_purem.
        apply SPureSpecM.assert_formulas.
        apply (MkAMessage _ (BT := Message)).
        apply
          {| msg_function := "smut_assert_formula";
             msg_message := "Proof obligation";
             msg_program_context := Γ;
             msg_localstore := δ0;
             msg_heap := h0;
             msg_pathcondition := wco w0
          |}.
        apply fmls.
        apply POST.
        apply δ0.
        apply h0.
      Defined.

      Definition assert_eq_env {Γ} {Δ : Ctx Ty} :
        let E := fun w : World => Env (Term w) Δ in
        ⊢ E -> E -> SHeapSpecM Γ Γ Unit :=
        fun w0 E1 E2 POST δ0 h0 =>
          lift_purem
            (SPureSpecM.assert_eq_env
               (MkAMessage w0
                  {| msg_function := "smut/assert_eq_env";
                     msg_message := "Proof obligation";
                     msg_program_context := Γ;
                     msg_localstore := δ0;
                     msg_heap := h0;
                     msg_pathcondition := wco w0
                  |}) E1 E2)
            POST δ0 h0.

      Definition assert_eq_nenv {N Γ} {Δ : NCtx N Ty} :
        let E := fun w : World => NamedEnv (Term w) Δ in
        ⊢ E -> E -> SHeapSpecM Γ Γ Unit :=
        fun w0 E1 E2 POST δ0 h0 =>
          lift_purem
            (SPureSpecM.assert_eq_nenv
               (MkAMessage w0
                  {| msg_function := "smut/assert_eq_env";
                     msg_message := "Proof obligation";
                     msg_program_context := Γ;
                     msg_localstore := δ0;
                     msg_heap := h0;
                     msg_pathcondition := wco w0
                  |}) E1 E2)
            POST δ0 h0.

      Definition assert_eq_chunk {Γ} : ⊢ Chunk -> Chunk -> SHeapSpecM Γ Γ Unit.
      Proof.
        intros w0 c1 c2 POST δ0 h0.
        refine (lift_purem _ POST δ0 h0). apply T.
        refine (SPureSpecM.assert_eq_chunk _ c1 c2).
        apply (MkAMessage w0
                  {| msg_function := "SHeapSpecM.assert_eq_chunk";
                     msg_message := "Proof obligation";
                     msg_program_context := Γ;
                     msg_localstore := δ0;
                     msg_heap := h0;
                     msg_pathcondition := wco w0
                  |}).
      Defined.

    End AssumeAssert.

    Section PatternMatching.

      Definition angelic_match_bool' {AT} {Γ1 Γ2} :
        ⊢ STerm ty.bool -> □(SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t kt kf =>
          angelic_binary
            (⟨ ω ⟩ _ <- assert_formula (formula_bool t) ;; kt _ ω)
            (⟨ ω ⟩ _ <- assert_formula (formula_bool (term_not t)) ;; kf _ ω).

      Definition angelic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty.bool -> □(SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t kt kf =>
          match term_get_val t with
          | Some true => T kt
          | Some false => T kf
          | None => angelic_match_bool' t kt kf
          end.

      Definition box_angelic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty.bool -> □(SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) :=
        fun w0 t kt kf =>
          angelic_match_bool <$> persist__term t <*> four kt <*> four kf.

      Definition demonic_match_bool' {AT} {Γ1 Γ2} :
        ⊢ STerm ty.bool -> □(SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t kt kf =>
          demonic_binary
            (⟨ ω ⟩ _ <- assume_formula (formula_bool t) ;; kt _ ω)
            (⟨ ω ⟩ _ <- assume_formula (formula_bool (term_not t)) ;; kf _ ω).

      Definition demonic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty.bool -> □(SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t kt kf =>
          match term_get_val t with
          | Some true => T kt
          | Some false => T kf
          | None => demonic_match_bool' t kt kf
          end.

      Definition box_demonic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty.bool -> □(SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) :=
        fun w0 t kt kf =>
          demonic_match_bool <$> persist__term t <*> four kt <*> four kf.

      Definition angelic_match_enum {AT E} {Γ1 Γ2} :
        ⊢ STerm (ty.enum E) -> (⌜enumt E⌝ -> □(SHeapSpecM Γ1 Γ2 AT)) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t cont =>
          ⟨ ω01 ⟩ EK <- angelic_finite (F := enumt E)
                          (fun δ h =>
                             MkAMessage w0
                               {| msg_function := "SHeapSpecM.angelic_match_enum";
                                  msg_message := "pattern match assertion";
                                  msg_program_context := Γ1;
                                  msg_localstore := δ;
                                  msg_heap := h;
                                  msg_pathcondition := wco w0
                               |}) ;;
          ⟨ ω12 ⟩ _ <- assert_formula (formula_eq (persist__term t ω01) (term_enum E EK)) ;;
          cont EK _ (ω01 ∘ ω12).

      Definition demonic_match_enum {A E} {Γ1 Γ2} :
        ⊢ STerm (ty.enum E) -> (⌜enumt E⌝ -> □(SHeapSpecM Γ1 Γ2 A)) -> SHeapSpecM Γ1 Γ2 A :=
        fun w0 t cont =>
          ⟨ ω01 ⟩ EK <- demonic_finite (F := enumt E) ;;
          ⟨ ω12 ⟩ _ <- assume_formula (formula_eq (persist__term t ω01) (term_enum E EK)) ;;
          cont EK _ (ω01 ∘ ω12).

      Definition box_demonic_match_enum {AT E} {Γ1 Γ2} :
        ⊢ STerm (ty.enum E) -> (⌜enumt E⌝ -> □(SHeapSpecM Γ1 Γ2 AT)) -> □(SHeapSpecM Γ1 Γ2 AT) :=
        fun w0 t k =>
          demonic_match_enum
            <$> persist__term t
            <*> (fun (w1 : World) (ω01 : w0 ⊒ w1) (EK : enumt E) => four (k EK) ω01).

      Definition angelic_match_sum {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty.sum σ τ) -> □(STerm σ -> SHeapSpecM Γ1 Γ2 AT) -> □(STerm τ -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT :=
      fun w0 t kinl kinr =>
        angelic_binary
          (⟨ω1⟩ tl <- angelic (Some x) σ;;
           ⟨ω2⟩ _  <- assert_formula (formula_eq (term_inl tl) t⟨ω1⟩) ;;
                     T kinl⟨ω1∘ω2⟩ tl⟨ω2⟩)
          (⟨ω1⟩ tr <- angelic (Some y) τ;;
           ⟨ω2⟩ _  <- assert_formula (formula_eq (term_inr tr) t⟨ω1⟩);;
                     T kinr⟨ω1∘ω2⟩ tr⟨ω2⟩).

      Definition demonic_match_sum {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty.sum σ τ) -> □(STerm σ -> SHeapSpecM Γ1 Γ2 AT) -> □(STerm τ -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t kinl kinr =>
          demonic_binary
            (⟨ω1⟩ t1 <- demonic (Some x) σ;;
             ⟨ω2⟩ _  <- assume_formula (formula_eq (term_inl t1) t⟨ω1⟩);;
                       T kinl⟨ω1∘ω2⟩ t1⟨ω2⟩)
            (⟨ω1⟩ t1 <- demonic (Some y) τ;;
             ⟨ω2⟩ _  <- assume_formula (formula_eq (term_inr t1) t⟨ω1⟩);;
                       T kinr⟨ω1∘ω2⟩ t1⟨ω2⟩).

      Definition demonic_match_sum_lifted {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty.sum σ τ) -> □(STerm σ -> SHeapSpecM Γ1 Γ2 AT) -> □(STerm τ -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t kinl kinr POST δ0 h0.
        eapply (SPureSpecM.demonic_match_sum (A := fun w => SStore Γ2 w * SHeap w * AT w)%type x _ y _ _ t).
        - intros w1 ω01 t' POSTl.
          apply kinl. auto. auto.
          intros w2 ω12 a2 δ2 h2.
          apply POSTl. auto. auto.
          apply (persist (A := SStore _) δ0 ω01).
          apply (persist (A := SHeap) h0 ω01).
        - intros w1 ω01 t' POSTr.
          apply kinr. auto. auto.
          intros w2 ω12 a2 δ2 h2.
          apply POSTr. auto. auto.
          apply (persist (A := SStore _) δ0 ω01).
          apply (persist (A := SHeap) h0 ω01).
        - intros w1 ω01 [ [δ1 h1] a1]. apply POST. auto. auto. auto. auto.
      Defined.

      Definition angelic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty.list σ) -> □(SHeapSpecM Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty.list σ) -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t knil kcons.
        apply angelic_binary.
        - eapply bind.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "SHeapSpecM.angelic_match_list"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := δ0; *)
          (*      msg_heap            := h0; *)
          (*      msg_pathcondition   := wco w0; *)
          (*   |}. *)
          apply (formula_eq (term_val (ty.list σ) []%list) t).
          intros w1 ω01 _.
          apply knil. auto.
        - eapply bind.
          apply (angelic (Some x) σ).
          intros w1 ω01 thead.
          eapply bind.
          apply (angelic (Some y) (ty.list σ)).
          intros w2 ω12 ttail.
          eapply bind.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "SHeapSpecM.angelic_match_list"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*      msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*      msg_pathcondition   := wco w2; *)
          (*   |}. *)
          apply (formula_eq (term_binop bop.cons (persist__term thead ω12) ttail) (persist__term t (acc_trans ω01 ω12))).
          intros w3 ω23 _.
          apply (four kcons (acc_trans ω01 ω12)). auto.
          apply (persist__term thead (acc_trans ω12 ω23)).
          apply (persist__term ttail ω23).
      Defined.

      Definition box_angelic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty.list σ) -> □(SHeapSpecM Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty.list σ) -> SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) :=
        fun w0 t knil kcons => angelic_match_list x y <$> persist__term t <*> four knil <*> four kcons.

      Definition demonic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty.list σ) -> □(SHeapSpecM Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty.list σ) -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t knil kcons.
        apply demonic_binary.
        - eapply bind.
          apply assume_formula.
          apply (formula_eq (term_val (ty.list σ) []%list) t).
          intros w1 ω01 _.
          apply knil. auto.
        - eapply bind.
          apply (demonic (Some x) σ).
          intros w1 ω01 thead.
          eapply bind.
          apply (demonic (Some y) (ty.list σ)).
          intros w2 ω12 ttail.
          eapply bind.
          apply assume_formula.
          apply (formula_eq (term_binop bop.cons (persist__term thead ω12) ttail) (persist__term t (acc_trans ω01 ω12))).
          intros w3 ω23 _.
          apply (four kcons (acc_trans ω01 ω12)). auto.
          apply (persist__term thead (acc_trans ω12 ω23)).
          apply (persist__term ttail ω23).
      Defined.

      Definition box_demonic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty.list σ) -> □(SHeapSpecM Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty.list σ) -> SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) :=
        fun w0 t knil kcons => demonic_match_list x y <$> persist__term t <*> four knil <*> four kcons.

      Definition angelic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty.prod σ τ) -> □(STerm σ -> STerm τ -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        apply (bind (angelic (Some x) σ)).
        intros w1 ω01 tσ.
        apply (bind (angelic (Some y) τ)).
        intros w2 ω12 tτ.
        eapply bind.
        apply assert_formula.
          (* {| msg_function        := "SHeapSpecM.angelic_match_prod"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*    msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
          (* |}. *)
        apply (formula_eq (term_binop bop.pair (persist__term tσ ω12) tτ) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23 _.
        apply (four k (acc_trans ω01 ω12)). auto.
        apply (persist__term tσ (acc_trans ω12 ω23)).
        apply (persist__term tτ ω23).
      Defined.

      Definition box_angelic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty.prod σ τ) -> □(STerm σ -> STerm τ -> SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_prod x y <$> persist__term t <*> four k.

      Definition demonic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty.prod σ τ) -> □(STerm σ -> STerm τ -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        apply (bind (demonic (Some x) σ)).
        intros w1 ω01 tσ.
        apply (bind (demonic (Some y) τ)).
        intros w2 ω12 tτ.
        eapply bind.
        apply assume_formula.
        apply (formula_eq (term_binop bop.pair (persist__term tσ ω12) tτ) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23 _.
        apply (four k (acc_trans ω01 ω12)). auto.
        apply (persist__term tσ (acc_trans ω12 ω23)).
        apply (persist__term tτ ω23).
      Defined.

      Definition box_demonic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty.prod σ τ) -> □(STerm σ -> STerm τ -> SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_prod x y <$> persist__term t <*> four k.

      Definition angelic_match_record' {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ) :
        ⊢ STerm (ty.record R) -> □((fun w => NamedEnv (Term w) Δ) -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind.
        apply assert_formula.
          (* {| msg_function        := "SHeapSpecM.angelic_match_record"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*    msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
          (* |}. *)
        apply (formula_eq (term_record R (record_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition angelic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ) :
        ⊢ STerm (ty.record R) -> □((fun w => NamedEnv (Term w) Δ) -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        destruct (term_get_record t).
        - apply (T k).
          apply (record_pattern_match_env p n0).
        - apply (angelic_match_record' n p t k).
      Defined.

      Definition box_angelic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ) :
        ⊢ STerm (ty.record R) -> □((fun w => NamedEnv (Term w) Δ) -> SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_record n p <$> persist__term t <*> four k.

      Definition demonic_match_record' {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ) :
        ⊢ STerm (ty.record R) -> □((fun w => NamedEnv (Term w) Δ) -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind.
        apply assume_formula.
        apply (formula_eq (term_record R (record_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition demonic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ) :
        ⊢ STerm (ty.record R) -> □((fun w => NamedEnv (Term w) Δ) -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        destruct (term_get_record t).
        - apply (T k).
          apply (record_pattern_match_env p n0).
        - apply (demonic_match_record' n p t k).
      Defined.

      Definition box_demonic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ) :
        ⊢ STerm (ty.record R) -> □((fun w => NamedEnv (Term w) Δ) -> SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_record n p <$> persist__term t <*> four k.

      Definition angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty.tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind.
        apply assert_formula.
          (* {| msg_function        := "SHeapSpecM.angelic_match_tuple"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*    msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
        (* |}. *)
        apply (formula_eq (term_tuple (tuple_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition box_angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty.tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_tuple n p <$> persist__term t <*> four k.

      Definition demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty.tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind.
        apply assume_formula.
        apply (formula_eq (term_tuple (tuple_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition box_demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty.tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SHeapSpecM Γ1 Γ2 AT) -> □(SHeapSpecM Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_tuple n p <$> persist__term t <*> four k.

      Definition angelic_match_pattern {N : Set} (n : N -> 𝑺) {σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) {Γ} :
        ⊢ (SStore Γ -> SHeap -> AMessage) -> STerm σ -> SHeapSpecM Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 msg t.
        eapply (bind).
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind.
        apply assert_formula.
        apply (formula_eq (pattern_match_env_reverse p ts) (persist__term t ω01)).
        intros w2 ω12 _.
        apply pure.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition demonic_match_pattern {N : Set} (n : N -> 𝑺) {σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) {Γ} :
        ⊢ STerm σ -> SHeapSpecM Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 t.
        eapply (bind).
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind.
        apply assume_formula.
        apply (formula_eq (pattern_match_env_reverse p ts) (persist__term t ω01)).
        intros w2 ω12 _.
        apply pure.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition angelic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : unionk U -> NCtx N Ty} (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K)) :
        ⊢ STerm (ty.union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SHeapSpecM Γ1 Γ2 AT)) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (angelic_finite (F := unionk U)).
        intros δ h.
        apply (MkAMessage _ (BT := Message)).
        apply
            {| msg_function        := "SHeapSpecM.angelic_match_union";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ;
               msg_heap            := h;
               msg_pathcondition   := wco w0;
            |}.
        intros w1 ω01 UK.
        eapply bind.
        apply (angelic None (unionk_ty U UK)).
        intros w2 ω12 t__field.
        eapply bind.
        apply assert_formula.
        apply (formula_eq (term_union U UK t__field) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23 _.
        eapply bind.
        apply (angelic_match_pattern n (p UK)).
        intros δ h.
        apply (MkAMessage _ (BT := Message)).
        apply
            {| msg_function        := "SHeapSpecM.angelic_match_union";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ;
               msg_heap            := h;
               msg_pathcondition   := wco w3;
            |}.
        apply (persist__term t__field ω23).
        apply (four (cont UK)).
        apply (acc_trans ω01 (acc_trans ω12 ω23)).
      Defined.

      Definition box_angelic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : unionk U -> NCtx N Ty} (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K)) :
        ⊢ STerm (ty.union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SHeapSpecM Γ1 Γ2 AT)) -> □(SHeapSpecM Γ1 Γ2 AT).
      Proof.
        refine (fun w0 t k => angelic_match_union n p <$> persist__term t <*> _).
        intros w1 ω01 UK. apply (four (k UK) ω01).
      Defined.

      Definition demonic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : unionk U -> NCtx N Ty} (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K)) :
        ⊢ STerm (ty.union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SHeapSpecM Γ1 Γ2 AT)) -> SHeapSpecM Γ1 Γ2 AT.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (demonic_finite (F := unionk U)).
        intros w1 ω01 UK.
        eapply bind.
        apply (demonic None (unionk_ty U UK)).
        intros w2 ω12 t__field.
        eapply bind.
        apply assume_formula.
        apply (formula_eq (term_union U UK t__field) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23 _.
        eapply bind.
        apply (demonic_match_pattern n (p UK)).
        apply (persist__term t__field ω23).
        apply (four (cont UK)).
        apply (acc_trans ω01 (acc_trans ω12 ω23)).
      Defined.

      Definition box_demonic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : unionk U -> NCtx N Ty} (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K)) :
        ⊢ STerm (ty.union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SHeapSpecM Γ1 Γ2 AT)) -> □(SHeapSpecM Γ1 Γ2 AT).
      Proof.
        refine (fun w0 t k => demonic_match_union n p <$> persist__term t <*> _).
        intros w1 ω01 UK. apply (four (k UK) ω01).
      Defined.

      Definition angelic_match_bvec' {AT n} {Γ1 Γ2} :
        ⊢ STerm (ty.bvec n) -> (⌜bv n⌝ -> □(SHeapSpecM Γ1 Γ2 AT)) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t k =>
          ⟨ ω1 ⟩ b <- angelic_finite
                        (fun (δ : SStore Γ1 w0) (h : SHeap w0) =>
                           (MkAMessage _ {| msg_function := "SHeapSpecM.angelic_match_bvec";
                              msg_message := "pattern match assertion";
                              msg_program_context := Γ1;
                              msg_localstore := δ;
                              msg_heap := h;
                              msg_pathcondition := wco w0
                           |})) ;;
          let t1 := persist__term t ω1 in
          ⟨ ω2 ⟩ _ <- assert_formula (formula_eq t1 (term_val (ty.bvec n) b)) ;;
          four (k b) ω1 ω2.

      Definition angelic_match_bvec {AT n} {Γ1 Γ2} :
        ⊢ STerm (ty.bvec n) -> (⌜bv n⌝ -> □(SHeapSpecM Γ1 Γ2 AT)) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t k =>
          match term_get_val t with
          | Some b => T (k b)
          | None   => angelic_match_bvec' t k
          end.

      Definition demonic_match_bvec' {AT n} {Γ1 Γ2} :
        ⊢ STerm (ty.bvec n) -> (⌜bv n⌝ -> □(SHeapSpecM Γ1 Γ2 AT)) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t k =>
          ⟨ ω1 ⟩ b <- demonic_finite (F := bv n) ;;
          let s1 := term_val (ty.bvec n) b in
          let t1 := persist__term t ω1 in
          ⟨ ω2 ⟩ _ <- assume_formula (formula_eq s1 t1) ;;
          four (k b) ω1 ω2.

      Definition demonic_match_bvec {AT n} {Γ1 Γ2} :
        ⊢ STerm (ty.bvec n) -> (⌜bv n⌝ -> □(SHeapSpecM Γ1 Γ2 AT)) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t k =>
          match term_get_val t with
          | Some b => T (k b)
          | None   => demonic_match_bvec' t k
          end.

    End PatternMatching.

    Section State.

      Definition pushpop {AT Γ1 Γ2 x σ} :
        ⊢ STerm σ -> SHeapSpecM (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) AT -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t m POST δ h =>
          m (fun w1 ω01 a1 δ1 => POST w1 ω01 a1 (env.tail δ1)) δ.[x∷σ↦t] h.

      Definition pushspops {AT Γ1 Γ2 Δ} :
        ⊢ SStore Δ -> SHeapSpecM (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 δΔ m POST δ h =>
          m (fun w1 ω01 a1 δ1 => POST w1 ω01 a1 (env.drop Δ δ1)) (δ ►► δΔ) h.

      Definition get_local {Γ} : ⊢ SHeapSpecM Γ Γ (SStore Γ) :=
        fun w0 POST δ => T POST δ δ.
      Definition put_local {Γ1 Γ2} : ⊢ SStore Γ2 -> SHeapSpecM Γ1 Γ2 Unit :=
        fun w0 δ POST _ => T POST tt δ.
      Definition get_heap {Γ} : ⊢ SHeapSpecM Γ Γ SHeap :=
        fun w0 POST δ h => T POST h δ h.
      Definition put_heap {Γ} : ⊢ SHeap -> SHeapSpecM Γ Γ Unit :=
        fun w0 h POST δ _ => T POST tt δ h.

      Definition eval_exp {Γ σ} (e : Exp Γ σ) :
        ⊢ SHeapSpecM Γ Γ (STerm σ) :=
        fun w POST δ => T POST (peval (seval_exp δ e)) δ.

      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        ⊢ SHeapSpecM Γ Γ (SStore σs).
        intros w POST δ h.
        apply (T POST).
        refine (env.map _ es).
        intros b e. apply peval. apply (seval_exp δ e).
        auto.
        auto.
      Defined.

      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} : ⊢ STerm σ -> SHeapSpecM Γ Γ Unit :=
        fun w0 t POST δ => T POST tt (δ ⟪ x ↦ t ⟫).
      Global Arguments assign {Γ} x {σ xIn w} v.

    End State.

    Section ProduceConsume.
      Import EqNotations.

      Definition produce_chunk {Γ} :
        ⊢ Chunk -> SHeapSpecM Γ Γ Unit :=
        fun w0 c k δ h => T k tt δ (cons (peval_chunk c) h).

      Fixpoint try_consume_chunk_exact {Σ} (h : SHeap Σ) (c : Chunk Σ) {struct h} : option (SHeap Σ) :=
        match h with
        | nil       => None
        | cons c' h =>
          if chunk_eqb c c'
          then Some (if is_duplicable c then (cons c h) else h)
          else option_map (cons c') (try_consume_chunk_exact h c)
        end.

      Section ConsumePreciseUser.

        Context {Σ} (p : 𝑯) {ΔI ΔO : Ctx Ty} (prec : 𝑯_Ty p = ΔI ▻▻ ΔO) (tsI : Env (Term Σ) ΔI) (tsO : Env (Term Σ) ΔO).

        Equations(noeqns) match_chunk_user_precise (c : Chunk Σ) : option (List Formula Σ) :=
        match_chunk_user_precise (chunk_user p' ts')
        with eq_dec p p' => {
          match_chunk_user_precise (chunk_user ?(p) ts') (left eq_refl) :=
            match env.catView (rew prec in ts') with
            | env.isCat tsI' tsO' =>
                if env.eqb_hom Term_eqb tsI tsI'
                then Some (formula_eqs_ctx tsO tsO')
                else None
            end;
          match_chunk_user_precise (chunk_user p' ts') (right _) := None
        };
        match_chunk_user_precise _ := None.

        Fixpoint find_chunk_user_precise (h : SHeap Σ) : option (SHeap Σ * List Formula Σ) :=
          match h with
          | nil => None
          | cons c h' =>
              match match_chunk_user_precise c with
              | Some eqs => Some (if is_duplicable p then cons c h' else h', eqs)
              | None => option_map (base.prod_map (cons c) id) (find_chunk_user_precise h')
              end
          end.

      End ConsumePreciseUser.

      Section ConsumePrecisePtsreg.

        Context {Σ σ} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ).

        Equations(noeqns) match_chunk_ptsreg_precise (c : Chunk Σ) : option (Formula Σ) :=
        match_chunk_ptsreg_precise (chunk_ptsreg r' t')
        with eq_dec_het r r' => {
          match_chunk_ptsreg_precise (chunk_ptsreg ?(r) t') (left eq_refl) := Some (formula_eq t t');
          match_chunk_ptsreg_precise (chunk_ptsreg r' t') (right _) := None
        };
        match_chunk_ptsreg_precise _ := None.

        Fixpoint find_chunk_ptsreg_precise (h : SHeap Σ) : option (SHeap Σ * List Formula Σ) :=
          match h with
          | nil => None
          | cons c h' =>
              match match_chunk_ptsreg_precise c with
              | Some fml => Some (h', cons fml nil)
              | None => option_map (base.prod_map (cons c) id) (find_chunk_ptsreg_precise h')
              end
          end.

      End ConsumePrecisePtsreg.

      Definition try_consume_chunk_precise {Σ} (h : SHeap Σ) (c : Chunk Σ) : option (SHeap Σ * List Formula Σ) :=
        match c with
        | chunk_user p ts =>
            match 𝑯_precise p with
            | Some (MkPrecise ΔI ΔO Δeq) =>
                match env.catView (rew Δeq in ts) with
                | env.isCat tsI tsO => find_chunk_user_precise Δeq tsI tsO h
                end
            | None => None
            end
        | chunk_ptsreg r t => find_chunk_ptsreg_precise r t h
        | _ => None
        end.

      Definition consume_chunk {Γ} :
        ⊢ Chunk -> SHeapSpecM Γ Γ Unit.
      Proof.
        intros w0 c.
        eapply bind.
        apply get_heap.
        intros w1 ω01 h.
        pose proof (peval_chunk (persist c ω01)) as c1. clear c.
        destruct (try_consume_chunk_exact h c1) as [h'|].
        { apply put_heap. apply h'. }
        destruct (try_consume_chunk_precise h c1) as [[h' eqs]|].
        { eapply bind.
          apply put_heap. apply h'.
          intros w2 ω12 _.
          apply assert_formulas.
          apply (persist (A := List Formula) eqs ω12).
        }
        { intros _ δ1 h1.
          apply
            (SymProp.error
               (EMsgHere
                  {| debug_consume_chunk_program_context := Γ;
                     debug_consume_chunk_pathcondition := wco w1;
                     debug_consume_chunk_localstore := δ1;
                     debug_consume_chunk_heap := h1;
                     debug_consume_chunk_chunk := c1
                  |})).
        }
      Defined.

      Definition consume_chunk_angelic {Γ} :
        ⊢ Chunk -> SHeapSpecM Γ Γ Unit.
      Proof.
        intros w0 c.
        eapply bind.
        apply get_heap.
        intros w1 ω01 h.
        pose proof (peval_chunk (persist c ω01)) as c1. clear c.
        destruct (try_consume_chunk_exact h c1) as [h'|].
        { apply put_heap. apply h'. }
        destruct (try_consume_chunk_precise h c1) as [[h' eqs]|].
        { eapply bind.
          apply put_heap. apply h'.
          intros w2 ω12 _.
          apply assert_formulas.
          apply (persist (A := List Formula) eqs ω12).
        }
        { eapply bind.
          refine (angelic_list
                    (A := Pair Chunk SHeap)
                    (fun δ h =>
                       {| debug_consume_chunk_program_context := Γ;
                          debug_consume_chunk_pathcondition := wco w1;
                          debug_consume_chunk_localstore := δ;
                          debug_consume_chunk_heap := h;
                          debug_consume_chunk_chunk := c1
                        |})
                    (heap_extractions h)).
          intros w2 ω12 [c' h'].
          eapply bind.
          apply (assert_eq_chunk (persist c1 ω12) c').
          intros w3 ω23 _.
          apply put_heap.
          apply (persist (A := SHeap) h' ω23).
        }
      Defined.

      Definition produce {Γ} :
        ⊢ Assertion -> □(SHeapSpecM Γ Γ Unit).
      Proof.
        refine (fix produce w0 asn {struct asn} := _).
        destruct asn.
        - apply (box_assume_formula fml).
        - apply (produce_chunk <$> persist c).
        - apply (produce_chunk <$> persist c).
        - apply (demonic_match_bool <$> persist__term b <*> four (produce _ asn1) <*> four (produce _ asn2)).
        - intros w1 ω01.
          apply (demonic_match_enum
                    (persist__term k ω01)
                    (fun EK : enumt E => four (produce w0 (alts EK)) ω01)).
        - refine (demonic_match_sum (AT := Unit) (Γ1 := Γ) (Γ2 := Γ) xl xr <$> persist__term s <*> four _ <*> four _).
          intros w1 ω01 t1.
          apply (produce (wsnoc w0 (xl∷σ)) asn1).
          apply (acc_snoc_left ω01 (xl∷σ) t1).
          intros w1 ω01 t1.
          apply (produce (wsnoc w0 (xr∷τ)) asn2).
          apply (acc_snoc_left ω01 (xr∷τ) t1).
        - apply (box_demonic_match_list xh xt s).
          + apply (produce _ asn1).
          + intros w1 ω01 thead ttail.
            apply (produce (wsnoc (wsnoc w0 (xh∷_)) (xt∷_)) asn2 w1).
            apply (acc_snoc_left (acc_snoc_left ω01 (xh∷_) thead) (xt∷_) ttail).
        - apply (box_demonic_match_prod xl xr s).
          intros w1 ω01 t1 t2.
          apply (produce (wsnoc (wsnoc w0 (xl∷σ1)) (xr∷σ2)) asn w1).
          apply (acc_snoc_left (acc_snoc_left ω01 (xl∷σ1) t1) (xr∷σ2) t2).
        - apply (box_demonic_match_tuple id p s).
          intros w1 ω01 ts.
          apply (produce (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_demonic_match_record id p s).
          intros w1 ω01 ts.
          apply (produce (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_demonic_match_union id alt__pat s).
          intros UK w1 ω01 ts.
          apply (produce (wcat w0 (alt__ctx UK)) (alt__rhs UK) w1).
          apply acc_cat_left; auto.
        - intros w1 ω01.
          eapply bind.
          apply (produce _ asn1 _ ω01).
          intros w2 ω12 _.
          apply (produce _ asn2 _ (ω01 ∘ ω12)).
        - apply (demonic_binary <$> produce _ asn1 <*> produce _ asn2).
        - intros w1 ω01.
          eapply bind.
          apply (@demonic _ (Some ς) τ).
          intros w2 ω12 t2.
          apply (produce (wsnoc w0 (ς∷τ)) asn w2).
          apply (acc_snoc_left (acc_trans ω01 ω12) (ς∷τ) t2).
        - intros w1 ω01.
          eapply (debug (DT := DebugAsn)).
          intros δ h.
          apply (MkDebugAsn (wco w1) δ h).
          apply pure.
          constructor.
      Defined.

      Definition consume {Γ} :
        ⊢ Assertion -> □(SHeapSpecM Γ Γ Unit).
      Proof.
        refine (fix consume w0 asn {struct asn} := _).
        destruct asn.
        - apply (box_assert_formula fml).
        - apply (consume_chunk <$> persist c).
        - apply (consume_chunk_angelic <$> persist c).
        - apply (angelic_match_bool <$> persist__term b <*> four (consume _ asn1) <*> four (consume _ asn2)).
        - intros w1 ω01.
          apply (angelic_match_enum
                    (persist__term k ω01)
                    (fun EK : enumt E => four (consume w0 (alts EK)) ω01)).
        - refine (angelic_match_sum (AT := Unit) (Γ1 := Γ) (Γ2 := Γ) xl xr <$> persist__term s <*> four _ <*> four _).
          intros w1 ω01 t1.
          apply (consume (wsnoc w0 (xl∷σ)) asn1).
          apply (acc_snoc_left ω01 (xl∷σ) t1).
          intros w1 ω01 t1.
          apply (consume (wsnoc w0 (xr∷τ)) asn2).
          apply (acc_snoc_left ω01 (xr∷τ) t1).
        - apply (box_angelic_match_list xh xt s).
          + apply (consume _ asn1).
          + intros w1 ω01 thead ttail.
            apply (consume (wsnoc (wsnoc w0 (xh∷_)) (xt∷_)) asn2 w1).
            apply (acc_snoc_left (acc_snoc_left ω01 (xh∷_) thead) (xt∷_) ttail).
        - apply (box_angelic_match_prod xl xr s).
          intros w1 ω01 t1 t2.
          apply (consume (wsnoc (wsnoc w0 (xl∷σ1)) (xr∷σ2)) asn w1).
          apply (acc_snoc_left (acc_snoc_left ω01 (xl∷σ1) t1) (xr∷σ2) t2).
        - apply (box_angelic_match_tuple id p s).
          intros w1 ω01 ts.
          apply (consume (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_angelic_match_record id p s).
          intros w1 ω01 ts.
          apply (consume (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_angelic_match_union id alt__pat s).
          intros UK w1 ω01 ts.
          apply (consume (wcat w0 (alt__ctx UK)) (alt__rhs UK) w1).
          apply acc_cat_left; auto.
        - intros w1 ω01.
          eapply bind.
          apply (consume _ asn1 _ ω01).
          intros w2 ω12 _.
          apply (consume _ asn2 _ (ω01 ∘ ω12)).
        - apply (angelic_binary <$> consume _ asn1 <*> consume _ asn2).
        - intros w1 ω01.
          eapply bind.
          apply (@angelic _ (Some ς) τ).
          intros w2 ω12 t2.
          apply (consume (wsnoc w0 (ς∷τ)) asn w2).
          apply (acc_snoc_left (acc_trans ω01 ω12) (ς∷τ) t2).
        - intros w1 ω01.
          apply (debug (DT := DebugAsn)).
          intros δ h.
          apply (MkDebugAsn (wco w1) δ h).
          apply pure.
          constructor.
      Defined.

    End ProduceConsume.

    Section Exec.

      Variable cfg : Config.

      Definition call_contract {Γ Δ τ} (c : SepContract Δ τ) :
        ⊢ SStore Δ -> SHeapSpecM Γ Γ (STerm τ).
      Proof.
        destruct c as [Σe δe req result ens].
        intros w0 args.
        eapply bind.
        apply (angelic_ctx id Σe).
        intros w1 ω01 evars.
        eapply bind.
        apply (assert_eq_nenv (subst δe evars)).
        refine (persist args ω01).
        intros w2 ω12 _.
        eapply bind.
        apply (consume (w := @MkWorld Σe nil) req).
        refine (acc_trans _ ω12).
        constructor 2 with evars. cbn. constructor.
        intros w3 ω23 _.
        eapply bind.
        apply (demonic (Some result)).
        intros w4 ω34 res.
        eapply bind.
        apply (produce
                 (w := @MkWorld (Σe ▻ result∷τ) nil)
                 ens).
        constructor 2 with (sub_snoc (persist (A := Sub _) evars (acc_trans ω12 (acc_trans ω23 ω34))) (result∷τ) res).
        cbn. constructor.
        intros w5 ω45 _. clear - res ω45.
        apply pure.
        apply (persist__term res ω45).
      Defined.

      Definition call_lemma {Γ Δ} (lem : Lemma Δ) :
        ⊢ SStore Δ -> SHeapSpecM Γ Γ Unit.
      Proof.
        destruct lem as [Σe δe req ens].
        intros w0 args.
        eapply bind.
        apply (angelic_ctx id Σe).
        intros w1 ω01 evars.
        eapply bind.
        apply (assert_formulas
                 (* {| *)
                 (*   msg_function := "SHeapSpecM.call"; *)
                 (*   msg_message := "argument pattern match"; *)
                 (*   msg_program_context := Γ; *)
                 (*   msg_localstore := subst δ0 ω01; *)
                 (*   msg_heap := subst h0 ω01; *)
                 (*   msg_pathcondition := wco w1; *)
                 (* |} *) (formula_eqs_nctx (subst δe evars) (persist args ω01))).
        intros w2 ω12 _.
        eapply bind.
        apply (consume (w := @MkWorld Σe nil) req).
        refine (acc_trans _ ω12).
        constructor 2 with evars. cbn. constructor.
        intros w3 ω23 _.
        apply (produce
                 (w := @MkWorld Σe nil)
                 ens).
        constructor 2 with (persist (A := Sub _) evars (acc_trans ω12 ω23)).
        cbn. constructor.
      Defined.

      Definition call_contract_debug {Γ Δ τ} (f : 𝑭 Δ τ) (c : SepContract Δ τ) :
        ⊢ SStore Δ -> SHeapSpecM Γ Γ (STerm τ) :=
        fun w0 δΔ =>
          let o := call_contract c δΔ in
          if config_debug_function cfg f
          then
            debug
              (fun δ h => {| debug_call_function_parameters := Δ;
                             debug_call_function_result_type := τ;
                             debug_call_function_name := f;
                             debug_call_function_contract := c;
                             debug_call_function_arguments := δΔ;
                             debug_call_program_context := Γ;
                             debug_call_pathcondition := wco w0;
                             debug_call_localstore := δ;
                             debug_call_heap := h|})
              o
          else o.

      (* The paper discusses the case that a function call is replaced by
         interpreting the contract instead. However, this is not always
         convenient. We therefore make contracts for functions optional and
         if a function does not have a contract, we continue executing
         the body of the called function. A paramter [inline_fuel] controls the
         number of levels this is allowed before failing execution. Therefore,
         we write the executor in an open-recusion style and [Exec] is the
         closed type of such an executor. *)
      Definition Exec := forall Γ τ (s : Stm Γ τ), ⊢ SHeapSpecM Γ Γ (STerm τ).

      Section ExecAux.

        (* The executor for "inlining" a call. *)
        Variable rec : Exec.

        (* The openly-recursive executor. *)
        Definition exec_aux : forall {Γ τ} (s : Stm Γ τ), ⊢ SHeapSpecM Γ Γ (STerm τ) :=
          fix exec_aux {Γ τ} s {w0} :=
            match s with
            | stm_val _ v => pure (term_val τ v)
            | stm_exp e => eval_exp e (w:=w0)
            | stm_let x σ s__σ s__τ =>
                ⟨ ω01 ⟩ t <- exec_aux s__σ;;
                pushpop t (exec_aux s__τ)
            | stm_block δ s =>
                pushspops (lift δ) (exec_aux s)
            | stm_assign x s =>
                ⟨ ω01 ⟩ t <- exec_aux s;;
                ⟨ ω12 ⟩ _ <- assign x t;;
                pure (persist__term t ω12)
            | stm_call f es =>
                ⟨ ω01 ⟩ args <- eval_exps es (w:=w0) ;;
                match CEnv f with
                | Some a => call_contract_debug f a args
                | None => fun POST δΓ =>
                            rec (FunDef f)
                              (fun w2 ω12 res _ => POST w2 ω12 res (persist δΓ ω12))
                              args
                end
            | stm_call_frame δ s =>
                ⟨ ω01 ⟩ δ1 <- get_local (w:=w0);;
                ⟨ ω12 ⟩ _  <- put_local (lift δ);;
                ⟨ ω23 ⟩ t  <- exec_aux s;;
                ⟨ ω34 ⟩ _  <- put_local (persist δ1 (ω12 ∘ ω23));;
                pure (persist__term t ω34)
            | stm_foreign f es =>
                ⟨ ω01 ⟩ args <- eval_exps es (w:=w0) ;;
                call_contract (CEnvEx f) args
            | stm_lemmak l es k =>
                ⟨ ω01 ⟩ args <- eval_exps es (w:=w0) ;;
                ⟨ ω12 ⟩ _  <- call_lemma (LEnv l) args;;
                exec_aux k
            | stm_if e s1 s2 =>
                ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
                demonic_match_bool t
                  (fun _ _ => exec_aux s1)
                  (fun _ _ => exec_aux s2)
            | stm_seq s1 s2 =>
                ⟨ ω01 ⟩ _ <- exec_aux s1 ;;
                exec_aux s2
            | stm_assertk e _ k =>
                ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
                (* This uses assume_formula for a partial correctness
                interpretation of the object language failure effect. *)
                ⟨ ω12 ⟩ _ <- assume_formula (formula_bool t) ;;
                exec_aux k
            | stm_fail _ _ =>
                (* Same as stm_assert: partial correctness of failure. *)
                block (w:=w0)
            | stm_match_list e alt_nil xh xt alt_cons =>
                ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
                demonic_match_list (𝑿to𝑺 xh) (𝑿to𝑺 xt) t
                  (fun _ _ => exec_aux alt_nil)
                  (fun _ _ thead ttail =>
                     pushspops [env].[xh∷_ ↦ thead].[xt∷_↦ ttail] (exec_aux alt_cons ))
            | stm_match_sum e xinl alt_inl xinr alt_inr =>
                ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
                demonic_match_sum (𝑿to𝑺 xinl) (𝑿to𝑺 xinr) t
                  (fun _ _ tl => pushpop tl (exec_aux alt_inl))
                  (fun _ _ tr => pushpop tr (exec_aux alt_inr))
            | stm_match_prod e xl xr rhs =>
                ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
                demonic_match_prod (𝑿to𝑺 xl) (𝑿to𝑺 xr) t
                  (fun _ _ t1 t2 => pushspops [env].[xl∷_ ↦ t1].[xr∷_ ↦ t2] (exec_aux rhs))
            | stm_match_enum E e alts =>
                ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
                demonic_match_enum t (fun EK _ _ => exec_aux (alts EK))
            | stm_match_tuple e pat rhs =>
                ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
                demonic_match_tuple 𝑿to𝑺 pat t
                  (fun _ _ ts => pushspops ts (exec_aux rhs))
            | stm_match_union U e alt__pat alt__rhs =>
                ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
                demonic_match_union 𝑿to𝑺 alt__pat t
                  (fun UK _ _ ts => pushspops ts (exec_aux (alt__rhs UK)))
            | stm_match_record R e pat rhs =>
                ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
                demonic_match_record 𝑿to𝑺 pat t
                  (fun _ _ ts => pushspops ts (exec_aux rhs))
            | stm_match_bvec n e rhs =>
                ⟨ ω01 ⟩ t <- eval_exp e (w:=w0) ;;
                demonic_match_bvec t (fun bs _ _ => exec_aux (rhs bs))
            | stm_read_register reg =>
                ⟨ ω01 ⟩ t <- angelic None _ ;;
                ⟨ ω12 ⟩ _ <- T (consume (asn_chunk (chunk_ptsreg reg t))) ;;
                ⟨ ω23 ⟩ _ <- T (produce (asn_chunk (chunk_ptsreg reg (persist__term t ω12))));;
                pure (persist__term t (ω12 ∘ ω23))
            | stm_write_register reg e =>
                ⟨ ω01 ⟩ told <- angelic None _ ;;
                ⟨ ω12 ⟩ _    <- T (consume (asn_chunk (chunk_ptsreg reg told))) ;;
                ⟨ ω23 ⟩ tnew <- eval_exp e (w:=_) ;;
                ⟨ ω34 ⟩ _ <- T (produce (asn_chunk (chunk_ptsreg reg tnew))) ;;
                pure (persist__term tnew ω34)
            | stm_bind _ _ =>
                error "SHeapSpecM.exec" "stm_bind not supported" tt
            | stm_debugk k =>
                debug
                  (fun (δ0 : SStore Γ w0) (h0 : SHeap w0) =>
                     {| debug_stm_program_context := Γ;
                        debug_stm_statement_type := τ;
                        debug_stm_statement := k;
                        debug_stm_pathcondition := wco w0;
                        debug_stm_localstore := δ0;
                        debug_stm_heap := h0
                     |})
                  (exec_aux k)
            end.

      End ExecAux.

      (* The constructed closed executor. *)
      Fixpoint exec (inline_fuel : nat) : Exec :=
        match inline_fuel with
        | O   => fun _ _ _ _ => error "SHeapSpecM.exec" "out of fuel for inlining" tt
        | S n => @exec_aux (@exec n)
        end.
      Global Arguments exec _ {_ _} _ {w} _ _ _.

      Import Notations.

      Variable inline_fuel : nat.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
        SHeapSpecM Δ Δ Unit {| wctx := sep_contract_logic_variables c; wco := [] |} :=
        match c with
        | MkSepContract _ _ _ _ req result ens =>
          ⟨ ω01 ⟩ _   <- produce (w:=@MkWorld _ _) req acc_refl ;;
          ⟨ ω12 ⟩ res <- exec inline_fuel s ;;
          consume
            (w:=wsnoc (@MkWorld _ []) (result∷τ)%ctx)
            ens
            (acc_snoc_left (acc_trans ω01 ω12) (result∷τ)%ctx res)
        end.

      Definition vcgen {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) (s : Stm Δ τ) : 𝕊 wnil :=
        demonic_close
          (exec_contract c s (fun w1 ω01 _ δ1 h1 => SymProp.block)
             (sep_contract_localstore c) nil).

    End Exec.

  End SHeapSpecM.

  Module Symbolic.
    Import SHeapSpecM.

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition
        (postprocess
           (* Use inline_fuel = 1 by default. *)
           (vcgen default_config 1 c body)).

    Definition ok {Σ} (p : 𝕊 Σ) : bool :=
      match prune p with
      | SymProp.block => true
      | _           => false
      end.

    Lemma ok_sound {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) :
      is_true (ok p) -> safe p ι.
    Proof.
      rewrite <- prune_sound. unfold ok.
      generalize (prune p) as q. clear. intros q.
      destruct q; try discriminate; cbn; auto.
    Qed.

    Definition ValidContractReflect {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      is_true (ok (postprocess (vcgen default_config 1 c body))).

    Lemma validcontract_reflect_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractReflect c body ->
      ValidContract c body.
    Proof.
      unfold ValidContractReflect, ValidContract. intros Hok.
      apply (ok_sound _ env.nil) in Hok. now constructor.
    Qed.

    Definition VcGenErasure {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Erasure.ESymProp :=
      Erasure.erase_symprop (postprocess (vcgen default_config 1 c body)).

    Definition ValidContractWithErasure {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationConditionWithErasure (VcGenErasure c body).

    Lemma validcontract_with_erasure_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractWithErasure c body ->
      ValidContract c body.
    Proof.
      unfold ValidContractWithErasure, VcGenErasure, ValidContract. intros [H].
      constructor. now rewrite <- Erasure.erase_safe.
    Qed.

    Module Statistics.

      Import SymProp.Statistics.

      Definition extend_postcond_with_debug {Δ τ} (c : SepContract Δ τ) : SepContract Δ τ :=
        match c with
        | {| sep_contract_logic_variables := lvars;
             sep_contract_localstore      := store;
             sep_contract_precondition    := pre;
             sep_contract_result          := res;
             sep_contract_postcondition   := post;
          |} => {| sep_contract_logic_variables := lvars;
                   sep_contract_localstore      := store;
                   sep_contract_precondition    := pre;
                   sep_contract_result          := res;
                   sep_contract_postcondition   := asn_sep post asn_debug;
                |}
        end.

      Definition count_to_stats (c : Count) : Stats :=
        match c with
        | {| block := b; error := e; debug := d |} =>
          {| branches := b + e; pruned := b + e - d |}
        end.

      Definition calc {Δ τ} (f : 𝑭 Δ τ) : option (Stats) :=
        match CEnv f with
        | Some contract =>
            let contract' := extend_postcond_with_debug contract in
            let body      := FunDef f in
            let vc        := vcgen default_config 1 contract' body in
            Some (count_to_stats (count_nodes vc empty))
        | None   => None
        end.

    End Statistics.

  End Symbolic.

End SymbolicExecOn.

Module MakeExecutor
  (Import B    : Base)
  (Import SIG  : ProgramLogicSignature B)
  (Import SPEC : Specification B SIG)
  (Import SOLV : SolverKit B SIG).

  Include SymbolicExecOn B SIG SPEC SOLV.

End MakeExecutor.
