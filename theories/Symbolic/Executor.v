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
     Signature
     Symbolic.Propositions
     Symbolic.Worlds
     Specification
     Base.

From stdpp Require
     base.

Import ctx.notations.
Import env.notations.
Import ListNotations.
Import (hints) bv.finite.

Set Implicit Arguments.

Module Type SymbolicExecOn
  (Import B : Base)
  (Import PROG : Program B)
  (Import SIG : Signature B)
  (Import SPEC : Specification B PROG SIG)
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

    #[export] Instance SubstDebugCall : Subst DebugCall :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugCall f c ts pc δ h =>
          MkDebugCall f c (subst ts ζ01) (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    #[export] Instance SubstLawsDebugCall : SubstLaws DebugCall.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    Import option.notations.
    #[export] Instance OccursCheckDebugCall : OccursCheck DebugCall :=
      fun Σ x xIn d =>
        match d with
        | MkDebugCall f c ts pc δ h =>
            ts' <- occurs_check xIn ts ;;
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugCall f c ts' pc' δ' h')
        end.

    #[export] Instance SubstDebugStm : Subst DebugStm :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugStm s pc δ h =>
          MkDebugStm s (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    #[export] Instance SubstLawsDebugStm : SubstLaws DebugStm.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance OccursCheckDebugStm : OccursCheck DebugStm :=
      fun Σ x xIn d =>
        match d with
        | MkDebugStm s pc δ h =>
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugStm s pc' δ' h')
        end.

    #[export] Instance SubstDebugAsn : Subst DebugAsn :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugAsn pc δ h =>
          MkDebugAsn (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    #[export] Instance SubstLawsDebugAsn : SubstLaws DebugAsn.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance OccursCheckDebugAsn : OccursCheck DebugAsn :=
      fun Σ x xIn d =>
        match d with
        | MkDebugAsn pc δ h =>
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugAsn pc' δ' h')
        end.

    #[export] Instance SubstDebugConsumeChunk : Subst DebugConsumeChunk :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugConsumeChunk pc δ h c =>
          MkDebugConsumeChunk (subst pc ζ01) (subst δ ζ01) (subst h ζ01) (subst c ζ01)
        end.

    #[export] Instance SubstLawsDebugConsumeChunk : SubstLaws DebugConsumeChunk.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance OccursCheckDebugConsumeChunk : OccursCheck DebugConsumeChunk :=
      fun Σ x xIn d =>
        match d with
        | MkDebugConsumeChunk pc δ h c =>
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            c'  <- occurs_check xIn c ;;
            Some (MkDebugConsumeChunk pc' δ' h'  c')
        end.

    #[export] Instance SubstDebugAssertFormula : Subst DebugAssertFormula :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugAssertFormula pc δ h fml =>
          MkDebugAssertFormula (subst pc ζ01) (subst δ ζ01) (subst h ζ01) (subst fml ζ01)
        end.

    #[export] Instance SubstLawsDebugAssertFormula : SubstLaws DebugAssertFormula.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance OccursCheckDebugAssertFormula : OccursCheck DebugAssertFormula :=
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
          ιvalid  : instprop (wco w) ιassign;
        }.

    Program Definition winstance_formula {w} (ι : WInstance w) (fml : Formula w) (p : instprop fml ι) :
      WInstance (wformula w fml) :=
      {| ιassign := ι; |}.
    Next Obligation.
    Proof. intros. cbn. split; auto. apply ιvalid. Qed.

    Program Definition winstance_snoc {w} (ι : WInstance w) {b : LVar ∷ Ty} (v : Val (type b)) :
      WInstance (wsnoc w b) :=
      {| ιassign := env.snoc (ιassign ι) b v; |}.
    Next Obligation.
    Proof.
      intros. unfold wsnoc. cbn [wctx wco].
      rewrite instprop_subst, inst_sub_wk1.
      apply ιvalid.
    Qed.

    Program Definition winstance_subst {w} (ι : WInstance w) {x σ} {xIn : x∷σ ∈ w}
      (t : Term (w - x∷σ) σ) (p : inst t (env.remove (x∷σ) (ιassign ι) xIn) = env.lookup (ιassign ι) xIn) :
      WInstance (wsubst w x t) :=
      @MkWInstance (wsubst w x t) (env.remove _ (ιassign ι) xIn) _.
    Next Obligation.
      intros * p. cbn. rewrite instprop_subst, <- inst_sub_shift in *.
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
      rewrite <- instprop_subst.
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

    #[export] Instance proper_vc : Proper (sequiv ctx.nil ==> iff) VerificationCondition.
    Proof. intros p q pq. split; intros []; constructor; now apply pq. Qed.

    Inductive VerificationConditionWithErasure (p : Erasure.ESymProp) : Prop :=
    | vce (P : Erasure.inst_symprop nil p).

  End VerificationConditions.

  Definition symprop_assume_pathcondition :
    ⊢ PathCondition -> □SymProp -> SymProp :=
    fun w0 C0 POST =>
      match solver _ C0 with
      | Some (existT w1 (ν , C1)) =>
          (* Assume variable equalities and the residual constraints *)
          assume_triangular ν
            (assume_pathcondition_without_solver C1
               (* Run POST in the world with the variable and residual formulas
                  included. This is a critical piece of code since this is the
                  place where we really meaningfully change the world. We
                  changed the type of assume_pathcondition_without_solver just
                  to not forget adding the new path constraints. *)
               (four POST (acc_triangular ν) (acc_pathcondition_right w1 C1)))
      | None =>
          (* The new path constraints are inconsistent with the old path
             constraints. *)
          SymProp.block
      end.

  Definition SMatchResult {N σ} (pat : @Pattern N σ) (w : World) : Type :=
    { pc : PatternCase pat & NamedEnv (Term w) (PatternCaseCtx pc) }.

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
    #[global] Arguments bind {A B} [w] m f _ /.

    Definition error {A} :
      ⊢ AMessage -> SPureSpecM A := fun w msg POST => SymProp.error msg.
    Definition block {A} : ⊢ SPureSpecM A :=
      fun w POST => SymProp.block.
    Global Arguments block {A w}.

    Definition angelic (x : option LVar) :
      ⊢ ∀ σ, SPureSpecM (STerm σ) :=
      fun w σ k =>
        let y := fresh_lvar w x in
        angelicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    Global Arguments angelic x [w] σ k : rename.

    Module Import notations.
      Notation "⟨ ω ⟩ x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 80, x at next level,
            ma at next level, mb at level 200,
            right associativity).
      (* Notation "⟨ w , ω ⟩ x <- ma ;; mb" := *)
      (*   (bind ma (fun w ω x => mb)) *)
      (*     (at level 80, x at next level, *)
      (*       ma at next level, mb at level 200, *)
      (*       right associativity, only printing). *)
      Notation "x ⟨ ω ⟩" := (persist x ω).
    End notations.

    Local Hint Extern 2 (Persistent (WTerm ?σ)) =>
      refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.
    Local Hint Extern 2 (Persistent (fun w : World => NamedEnv (Term (wctx w)) ?Γ)) =>
      refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.

    Definition angelic_ctx {N : Set} (n : N -> LVar) :
      ⊢ ∀ Δ : NCtx N Ty, SPureSpecM (fun w => NamedEnv (Term w) Δ) :=
      fix rec {w} Δ {struct Δ} :=
        match Δ with
         | []%ctx => pure []%env
         | Γ ▻ x∷σ => ⟨ ω1 ⟩ tΔ <- rec Γ;;
                      ⟨ ω2 ⟩ tσ <- angelic (Some (n x)) σ;;
                      pure (tΔ⟨ω2⟩ ► (x∷σ ↦ tσ))
         end.
    Global Arguments angelic_ctx {N} n [w] Δ : rename.

    Definition demonic (x : option LVar) :
      ⊢ ∀ σ, SPureSpecM (STerm σ) :=
      fun w σ k =>
        let y := fresh_lvar w x in
        demonicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    Global Arguments demonic x [w] σ k : rename.

    Definition demonic_ctx {N : Set} (n : N -> LVar) :
      ⊢ ∀ Δ : NCtx N Ty, SPureSpecM (fun w => NamedEnv (Term w) Δ) :=
      fix rec {w} Δ {struct Δ} :=
        match Δ with
        | []%ctx  => pure []%env
        | Δ ▻ x∷σ => ⟨ ω1 ⟩ tΔ <- rec Δ;;
                     ⟨ ω2 ⟩ tσ <- demonic (Some (n x)) σ;;
                     pure (tΔ⟨ω2⟩ ► (x∷σ ↦ tσ))
        end%ctx.
    Global Arguments demonic_ctx {_} n [w] Δ : rename.

    Definition assume_pathcondition :
      ⊢ PathCondition -> SPureSpecM Unit :=
      fun w C POST =>
        symprop_assume_pathcondition C (POST <*> (fun w r => tt)).

    Definition assume_formula :
      ⊢ Formula -> SPureSpecM Unit :=
      fun w F => assume_pathcondition ([ctx] ▻ F).

    Definition assert_pathcondition :
      ⊢ AMessage -> PathCondition -> SPureSpecM Unit :=
      fun w0 msg C0 POST =>
        match solver _ C0 with
        | Some (existT w1 (ν , C1)) =>
          (* Assert variable equalities and the residual constraints *)
          assert_triangular msg ν
            (fun msg' =>
               assert_pathcondition_without_solver msg' C1
                 (* Critical code. Like for assume_pathcondition. *)
                 (four POST (acc_triangular ν) (acc_pathcondition_right w1 C1) tt))
        | None =>
          (* The new path constraints are inconsistent with the old path
             constraints. *)
          SymProp.error msg
        end.

    Definition assert_formula :
      ⊢ AMessage -> Formula -> SPureSpecM Unit :=
      fun w0 msg fml0 =>
        assert_pathcondition msg (ctx.nil ▻ fml0 ).

    Equations(noeqns) assert_eq_env :
      let E Δ := fun w : World => Env (Term w) Δ in
      ⊢ ∀ Δ : Ctx Ty, AMessage -> E Δ -> E Δ -> SPureSpecM Unit :=
      assert_eq_env msg env.nil          env.nil            := pure tt;
      assert_eq_env msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
        ⟨ ω ⟩ _ <- assert_eq_env msg δ δ' ;;
        assert_formula msg⟨ω⟩ (formula_relop bop.eq t t')⟨ω⟩.

    Equations(noeqns) assert_eq_nenv {N} :
      let E Δ := fun w : World => NamedEnv (Term w) Δ in
      ⊢ ∀ Δ : NCtx N Ty, AMessage -> E Δ -> E Δ -> SPureSpecM Unit :=
      assert_eq_nenv msg env.nil          env.nil            := pure tt;
      assert_eq_nenv msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
        ⟨ ω ⟩ _ <- assert_eq_nenv msg δ δ' ;;
        assert_formula msg⟨ω⟩ (formula_relop bop.eq t t')⟨ω⟩.

    Definition assert_eq_chunk : ⊢ AMessage -> Chunk -> Chunk -> □(SPureSpecM Unit) :=
      fix assert_eq w0 msg c1 c2 w1 ω01 {struct c1} :=
        match c1 , c2 with
        | chunk_user p1 vs1 as c1 , chunk_user p2 vs2 as c2 =>
            match eq_dec p1 p2 with
            | left e => assert_eq_env msg⟨ω01⟩
                          (eq_rect p1 (fun p => Env (Term w1) (𝑯_Ty p)) vs1⟨ω01⟩ p2 e)
                          (persist (A := fun w => (fun Σ => Env (Term Σ) _) (wctx w)) vs2 ω01)
            | right _ => error msg⟨ω01⟩
            end
        | chunk_ptsreg r1 v1 as c1 , chunk_ptsreg r2 v2 as c2 =>
            match eq_dec_het r1 r2 with
            | left e => assert_formula msg⟨ω01⟩
                          (formula_relop bop.eq (eq_rect _ (Term w1) v1⟨ω01⟩ _ (f_equal projT1 e)) v2⟨ω01⟩)
            | right _ => error msg⟨ω01⟩
            end
        | chunk_conj c11 c12 , chunk_conj c21 c22 =>
            ⟨ ω12 ⟩ _ <- assert_eq _ msg c11 c21 w1 ω01 ;;
            assert_eq _ msg c12 c22 _ (ω01 ∘ ω12)
        | chunk_wand c11 c12 , chunk_wand c21 c22 =>
            ⟨ ω12 ⟩ _ <- assert_eq _ msg c11 c21 w1 ω01 ;;
            assert_eq _ msg c12 c22 _ (ω01 ∘ ω12)
        | _ , _ => error msg⟨ω01⟩
        end.

    Definition angelic_binary {A} :
      ⊢ SPureSpecM A -> SPureSpecM A -> SPureSpecM A :=
      fun w m1 m2 POST =>
        angelic_binary (m1 POST) (m2 POST).
    Definition demonic_binary {A} :
      ⊢ SPureSpecM A -> SPureSpecM A -> SPureSpecM A :=
      fun w m1 m2 POST =>
        demonic_binary (m1 POST) (m2 POST).

    Definition angelic_list' {A} :
      ⊢ A -> WList A -> SPureSpecM A :=
      fun w =>
        fix rec d xs :=
        match xs with
        | nil        => pure d
        | cons x xs  => angelic_binary (pure d) (rec x xs)
        end.
    #[global] Arguments angelic_list' {A} [w].

    Definition angelic_list {A} :
      ⊢ AMessage -> WList A -> SPureSpecM A :=
      fun w msg xs =>
        match xs with
        | nil        => error msg
        | cons x xs  => angelic_list' x xs
        end.

    Definition demonic_list' {A} :
      ⊢ A -> WList A -> SPureSpecM A :=
      fun w =>
        fix rec d xs :=
        match xs with
        | nil        => pure d
        | cons x xs  => demonic_binary (pure d) (rec x xs)
        end.

    Definition demonic_list {A} :
      ⊢ WList A -> SPureSpecM A :=
      fun w xs =>
        match xs with
        | nil        => block
        | cons x xs  => demonic_list' x xs
        end.

    Definition angelic_finite F `{finite.Finite F} :
      ⊢ AMessage -> SPureSpecM ⌜F⌝ :=
      fun w msg => angelic_list msg (finite.enum F).
    #[global] Arguments angelic_finite F {_ _} [w].

    Definition demonic_finite F `{finite.Finite F} :
      ⊢ SPureSpecM ⌜F⌝ :=
      fun w => demonic_list (finite.enum F).
    #[global] Arguments demonic_finite F {_ _} [w].

    #[export] Instance proper_debug {B Σ b} : Proper (iff ==> iff) (@Debug B Σ b).
    Proof. intros P Q PQ. split; intros []; constructor; intuition. Qed.

    Definition pattern_match_regular {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) :
      ⊢ STerm σ -> SPureSpecM (SMatchResult pat) :=
      fun w0 scr POST =>
        SymProp.pattern_match scr (freshen_pattern n w0 pat)
          (fun pc : PatternCase _ =>
             let w1 : World   := wmatch w0 scr _ pc in
             let r1 : w0 ⊒ w1 := acc_match_right pc in
             POST w1 r1
               (existT
                  (unfreshen_patterncase n w0 pat pc)
                  (unfreshen_patterncaseenv n pat pc (sub_cat_right _)))).
    #[global] Arguments pattern_match_regular {N} n {σ} pat [w] t.

    Definition pattern_match_var {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) :
      ⊢ ∀ x, ctx.In (x∷σ) -> SPureSpecM (SMatchResult pat) :=
      fun w0 x xIn POST =>
        let pat' := freshen_pattern n w0 pat in
        SymProp.pattern_match_var x pat'
          (fun pc : PatternCase _ =>
             let Δ   : LCtx       := PatternCaseCtx pc in
             let w1  : World      := wcat w0 Δ in
             let r1  : w0 ⊒ w1    := acc_cat_right w0 Δ in
             let ts  : NamedEnv (Term (ctx.remove (ctx.in_cat_left Δ xIn))) Δ
                                  := eq_rect _ (fun Σ => NamedEnv (Term Σ) Δ)
                                       (sub_cat_right Δ) _
                                       (eq_sym (ctx.remove_in_cat_left xIn)) in
             let t   : Term (ctx.remove (ctx.in_cat_left Δ xIn)) σ
                                  := pattern_match_term_reverse pat' pc ts in
             let w2  : World      := wsubst w1 x t in
             let r2  : w1 ⊒ w2    := @acc_subst_right w1 x σ _ t in
             let r12 : w0 ⊒ w2    := r1 ∘ r2 in
             POST w2 r12
               (existT
                  (unfreshen_patterncase n w0 pat pc)
                  (unfreshen_patterncaseenv n pat pc ts))).
    #[global] Arguments pattern_match_var {N} n {σ} pat [w x] xIn : rename.

    Definition pattern_match_basic {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) :
      ⊢ STerm σ -> SPureSpecM (SMatchResult pat) :=
      fun w0 scr =>
        match scr with
        | @term_var _ x σ xIn => fun pat => pattern_match_var n pat xIn
        | t => fun pat => pattern_match_regular n pat t
        end pat.
    #[global] Arguments pattern_match_basic {N} n {σ} pat [w] t.

    Fixpoint pattern_match {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) :
      ⊢ WTerm σ -> SPureSpecM (SMatchResult pat) :=
      fun w0 : World =>
        match pat as p in (Pattern t) return (forall _ : Term (wctx w0) t, SPureSpecM (@SMatchResult N t p) w0) with
        | pat_var x       => fun scr => pure (existT tt [env].[x∷_ ↦ scr])
        | pat_bool        =>
            fun scr => match term_get_val scr with
                       | Some a => pure (existT a [env])
                       | None => pattern_match_basic n pat_bool scr
                       end
        | pat_list σ x y  =>
            fun scr => pattern_match_basic n (pat_list σ x y) scr
        | pat_pair x y    =>
            fun scr =>
              match term_get_pair scr with
              | Some (a, b) => pure (existT tt [env].[x∷_ ↦ a].[y∷_ ↦ b])
              | None        => pattern_match_basic n (pat_pair x y) scr
              end
        | pat_sum σ τ x y =>
            fun scr => match term_get_sum scr with
                       | Some (inl a) => pure (existT true [env].[x∷σ ↦ a])
                       | Some (inr b) => pure (existT false [env].[y∷τ ↦ b])
                       | None => pattern_match_basic n (pat_sum σ τ x y) scr
                       end
        | pat_unit        => fun _ => pure (existT tt [env])
        | pat_enum E      =>
            fun scr => match term_get_val scr with
                       | Some a => pure (existT a [env])
                       | None => pattern_match_basic n (pat_enum E) scr
                       end
        | pat_bvec_split m k x y =>
            fun scr => pattern_match_basic n (pat_bvec_split m k x y) scr
        | pat_bvec_exhaustive m =>
            fun scr =>
              match term_get_val scr with
              | Some a => pure (existT a [env])
              | None => pattern_match_basic n (pat_bvec_exhaustive m) scr
              end
        | @pat_tuple _ σs Δ p =>
            fun scr =>
              match term_get_tuple scr with
              | Some a => pure (existT tt (tuple_pattern_match_env p a))
              | None => pattern_match_basic n (pat_tuple p) scr
              end
        | pat_record R Δ p =>
            fun scr =>
              match term_get_record scr with
              | Some a => pure (existT tt (record_pattern_match_env p a))
              | None => pattern_match_basic n (pat_record R Δ p) scr
              end
        | pat_union U p =>
            fun scr =>
              match term_get_union scr with
              | Some (existT K t) =>
                  @map (SMatchResult (p K)) (SMatchResult (pat_union U p)) _
                    (fun w1 _ '(existT pc ts) =>
                       @existT (PatternCase (pat_union U p))
                         (fun pc => NamedEnv (Term w1) (PatternCaseCtx pc))
                         (existT (P := fun K => PatternCase (p K)) K pc) ts)
                    (pattern_match n t)
              | None => pattern_match_basic n (pat_union U p) scr
              end
        end.
    #[global] Arguments pattern_match {N} n {σ} pat [w].

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

      Definition error {Γ1 Γ2 A} :
        ⊢ (SStore Γ1 -> SHeap -> AMessage) -> SHeapSpecM Γ1 Γ2 A :=
        fun w msg _ δ h => SymProp.error (msg δ h).

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

      Definition angelic_list {A Γ} :
        ⊢ (SStore Γ -> SHeap -> AMessage) -> WList A -> SHeapSpecM Γ Γ A :=
        fun w msg xs POST δ h => lift_purem (SPureSpecM.angelic_list (msg δ h) xs) POST δ h.

      Definition angelic_finite F `{finite.Finite F} {Γ} :
        ⊢ (SStore Γ -> SHeap -> AMessage) -> SHeapSpecM Γ Γ ⌜F⌝ :=
        fun w msg POST δ h => lift_purem (SPureSpecM.angelic_finite F (msg δ h)) POST δ h.
      #[global] Arguments angelic_finite F {_ _ Γ w}.

      Definition demonic_finite F `{finite.Finite F} {Γ} :
        ⊢ SHeapSpecM Γ Γ ⌜F⌝ :=
        fun w => lift_purem (SPureSpecM.demonic_finite F (w:=w)).
      #[global] Arguments demonic_finite F {_ _ Γ w}.

      Definition angelic {Γ} (x : option LVar) :
        ⊢ ∀ σ, SHeapSpecM Γ Γ (STerm σ) :=
        fun w σ => lift_purem (SPureSpecM.angelic x σ).
      Global Arguments angelic {Γ} x [w] σ : rename.

      Definition demonic {Γ} (x : option LVar) :
        ⊢ ∀ σ, SHeapSpecM Γ Γ (STerm σ) :=
        fun w σ => lift_purem (SPureSpecM.demonic x σ).
      Global Arguments demonic {Γ} x [w] σ : rename.

      Definition debug {AT} {Γ1 Γ2} :
        ⊢ (SStore Γ1 -> SHeap -> AMessage) -> (SHeapSpecM Γ1 Γ2 AT) -> (SHeapSpecM Γ1 Γ2 AT) :=
        fun _ d m POST δ h => SymProp.debug (d δ h) (m POST δ h).

      Definition angelic_ctx {N : Set} (n : N -> LVar) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SHeapSpecM Γ Γ (fun w => NamedEnv (Term w) Δ) :=
        fun w Δ => lift_purem (SPureSpecM.angelic_ctx n Δ).
      Global Arguments angelic_ctx {N} n {Γ} [w] Δ : rename.

      Definition demonic_ctx {N : Set} (n : N -> LVar) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SHeapSpecM Γ Γ (fun w => NamedEnv (Term w) Δ) :=
        fun w Δ => lift_purem (SPureSpecM.demonic_ctx n Δ).
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
      Notation "⟨ ω ⟩ ' x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 80, x pattern,
           ma at next level, mb at level 200,
           right associativity) : mut_scope.
      Notation "x ⟨ ω ⟩" := (persist x ω).

    End notations.
    Local Open Scope mut_scope.

    Section AssumeAssert.

      (* Add the provided formula to the path condition. *)
      Definition assume_formula {Γ} :
        ⊢ Formula -> SHeapSpecM Γ Γ Unit :=
        fun w0 fml => lift_purem (SPureSpecM.assume_formula fml).

      Definition box_assume_formula {Γ} :
        ⊢ Formula -> □(SHeapSpecM Γ Γ Unit) :=
        fun w0 fml => assume_formula <$> persist fml.

      Definition assert_formula {Γ} :
        ⊢ Formula -> SHeapSpecM Γ Γ Unit :=
        fun w0 fml POST δ0 h0 =>
          lift_purem
            (SPureSpecM.assert_formula
               (amsg.mk (MkDebugAssertFormula (wco w0) δ0 h0 fml)) fml)
            POST δ0 h0.

      Definition box_assert_formula {Γ} :
        ⊢ Formula -> □(SHeapSpecM Γ Γ Unit) :=
        fun w0 fml => assert_formula <$> persist fml.

      Definition assert_pathcondition {Γ} :
        ⊢ PathCondition -> SHeapSpecM Γ Γ Unit :=
        fun w0 fmls POST δ0 h0 =>
          lift_purem
            (SPureSpecM.assert_pathcondition
               (amsg.mk
                  {| msg_function := "smut_assert_formula";
                     msg_message := "Proof obligation";
                     msg_program_context := Γ;
                     msg_localstore := δ0;
                     msg_heap := h0;
                     msg_pathcondition := wco w0
                  |}) fmls) POST δ0 h0.

      Definition assert_eq_env {Γ} {Δ : Ctx Ty} :
        let E := fun w : World => Env (Term w) Δ in
        ⊢ E -> E -> SHeapSpecM Γ Γ Unit :=
        fun w0 E1 E2 POST δ0 h0 =>
          lift_purem
            (SPureSpecM.assert_eq_env
               (amsg.mk
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
               (amsg.mk
                  {| msg_function := "smut/assert_eq_env";
                     msg_message := "Proof obligation";
                     msg_program_context := Γ;
                     msg_localstore := δ0;
                     msg_heap := h0;
                     msg_pathcondition := wco w0
                  |}) E1 E2)
            POST δ0 h0.

      Definition assert_eq_chunk {Γ} :
        ⊢ Chunk -> Chunk -> SHeapSpecM Γ Γ Unit :=
        fun w0 c1 c2 POST δ0 h0 =>
          lift_purem
            (T (SPureSpecM.assert_eq_chunk
                  (amsg.mk
                     {| msg_function := "SHeapSpecM.assert_eq_chunk";
                        msg_message := "Proof obligation";
                        msg_program_context := Γ;
                        msg_localstore := δ0;
                        msg_heap := h0;
                        msg_pathcondition := wco w0
                     |}) c1 c2))
         POST δ0 h0.

    End AssumeAssert.

    Section PatternMatching.

      Definition angelic_pattern_match' {N : Set} (n : N -> LVar) {AT Γ1 Γ2 σ} (pat : @Pattern N σ) :
        ⊢ STerm σ ->
        (∀ pc : PatternCase pat, □((fun w => NamedEnv (Term w) (PatternCaseCtx pc)) -> SHeapSpecM Γ1 Γ2 AT)) ->
        SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t k =>
          ⟨ ω1 ⟩ pc <- angelic_finite (PatternCase pat)
                         (fun δ h =>
                            amsg.mk
                              {| msg_function := "SHeapSpecM.angelic_pattern_match";
                                 msg_message := "pattern match assertion";
                                 msg_program_context := Γ1;
                                 msg_localstore := δ;
                                 msg_heap := h;
                                 msg_pathcondition := wco w0
                              |});;
          ⟨ ω2 ⟩ ts <- angelic_ctx n (PatternCaseCtx pc) ;;
          let ω12 := ω1 ∘ ω2 in
          ⟨ ω3 ⟩ _  <- assert_formula (formula_relop bop.eq (pattern_match_term_reverse pat pc ts) t⟨ω12⟩) ;;
          k pc _ (ω12 ∘ ω3) (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) _) (wctx w)) ts ω3).

      Definition angelic_pattern_match {N : Set} (n : N -> LVar) {AT Γ1 Γ2} :
        forall {σ} (pat : @Pattern N σ),
          ⊢ STerm σ ->
          (∀ pc : PatternCase pat, □((fun w => NamedEnv (Term w) (PatternCaseCtx pc)) -> SHeapSpecM Γ1 Γ2 AT)) ->
          SHeapSpecM Γ1 Γ2 AT :=
        fix angelic (σ : Ty) (pat : Pattern σ) {struct pat} :
          ⊢ WTerm σ ->
          (∀ pc : PatternCase pat,
              □((fun w : World => NamedEnv (Term w) (PatternCaseCtx pc)) -> SHeapSpecM Γ1 Γ2 AT)) ->
          SHeapSpecM Γ1 Γ2 AT :=
          match pat with
          | pat_var x => fun w0 scr k => k tt w0 acc_refl [env].[x∷_ ↦ scr]
          | pat_bool => fun w0 scr k =>
                          match term_get_val scr with
                          | Some v => k v w0 acc_refl [env]
                          | None => angelic_pattern_match' n _ scr k
                          end
          | pat_pair x y => fun w0 scr k =>
                              match term_get_pair scr with
                              | Some (tl, tr) => k tt w0 acc_refl [env].[x∷_ ↦ tl].[y∷_ ↦ tr]
                              | None => angelic_pattern_match' n (pat_pair x y) scr k
                              end
          | pat_sum _ _ _ _ => fun w0 scr k =>
                                 match term_get_sum scr with
                                 | Some (inl tl) => k true w0 acc_refl [env].[_∷_ ↦ tl]
                                 | Some (inr tr) => k false w0 acc_refl [env].[_∷_ ↦ tr]
                                 | None => angelic_pattern_match' n (pat_sum _ _ _ _) scr k
                                 end
          | pat_unit => fun w0 scr k => k tt w0 acc_refl [env]
          | pat_enum E => fun w0 scr k => match term_get_val scr with
                                          | Some v => k v w0 acc_refl [env]
                                          | None => angelic_pattern_match' n _ scr k
                                          end
          | pat_bvec_exhaustive m => fun w0 scr k => match term_get_val scr with
                                                     | Some v => k v w0 acc_refl [env]
                                                     | None => angelic_pattern_match' n _ scr k
                                                     end
          | pat_tuple p => fun w0 scr k =>
                             match term_get_tuple scr with
                             | Some a => k tt w0 acc_refl (tuple_pattern_match_env p a)
                             | None => angelic_pattern_match' n (pat_tuple p) scr k
                             end
          | pat_record R Δ p => fun w0 scr k =>
                                  match term_get_record scr with
                                  | Some a => k tt w0 acc_refl (record_pattern_match_env p a)
                                  | None => angelic_pattern_match' n (pat_record R Δ p) scr k
                                  end
          | pat_union U p => fun w0 scr k =>
                               match term_get_union scr with
                               | Some (existT K scr') =>
                                   angelic (unionk_ty U K) (p K) w0 scr'
                                     (fun pc => k (existT K pc))
                               | None => angelic_pattern_match' n (pat_union U p) scr k
                               end
          | _ => angelic_pattern_match' n _
          end.

      Definition demonic_pattern_match' {N : Set} (n : N -> LVar) {AT Γ1 Γ2 σ} (pat : @Pattern N σ) :
        ⊢ STerm σ ->
        (∀ pc : PatternCase pat, □((fun w => NamedEnv (Term w) (PatternCaseCtx pc)) -> SHeapSpecM Γ1 Γ2 AT)  ) ->
        SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t k =>
          ⟨ ω1 ⟩ pc <- demonic_finite (PatternCase pat) ;;
          ⟨ ω2 ⟩ ts <- demonic_ctx n (PatternCaseCtx pc) ;;
          let ω12 := ω1 ∘ ω2 in
          ⟨ ω3 ⟩ _  <- assume_formula (formula_relop bop.eq (pattern_match_term_reverse pat pc ts) t⟨ω12⟩) ;;
          k pc _ (ω12 ∘ ω3) (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) _) (wctx w)) ts ω3).

      Definition demonic_pattern_match {N : Set} (n : N -> LVar) {AT Γ1 Γ2} :
        forall {σ} (pat : @Pattern N σ),
          ⊢ STerm σ ->
          (∀ pc : PatternCase pat, □((fun w => NamedEnv (Term w) (PatternCaseCtx pc)) -> SHeapSpecM Γ1 Γ2 AT)) ->
          SHeapSpecM Γ1 Γ2 AT :=
        fix demonic (σ : Ty) (pat : Pattern σ) {struct pat} :
          ⊢ WTerm σ ->
          (∀ pc : PatternCase pat,
              □((fun w : World => NamedEnv (Term w) (PatternCaseCtx pc)) -> SHeapSpecM Γ1 Γ2 AT)) ->
          SHeapSpecM Γ1 Γ2 AT :=
          match pat with
          | pat_var x => fun w0 scr k => k tt w0 acc_refl [env].[x∷_ ↦ scr]
          | pat_bool => fun w0 scr k =>
                          match term_get_val scr with
                          | Some v => k v w0 acc_refl [env]
                          | None => demonic_pattern_match' n _ scr k
                          end
          | pat_pair x y => fun w0 scr k =>
                              match term_get_pair scr with
                              | Some (tl, tr) => k tt w0 acc_refl [env].[x∷_ ↦ tl].[y∷_ ↦ tr]
                              | None => demonic_pattern_match' n (pat_pair x y) scr k
                              end
          | pat_sum _ _ _ _ => fun w0 scr k =>
                                 match term_get_sum scr with
                                 | Some (inl tl) => k true w0 acc_refl [env].[_∷_ ↦ tl]
                                 | Some (inr tr) => k false w0 acc_refl [env].[_∷_ ↦ tr]
                                 | None => demonic_pattern_match' n (pat_sum _ _ _ _) scr k
                                 end
          | pat_unit => fun w0 scr k => k tt w0 acc_refl [env]
          | pat_enum E => fun w0 scr k => match term_get_val scr with
                                          | Some v => k v w0 acc_refl [env]
                                          | None => demonic_pattern_match' n _ scr k
                                          end
          | pat_bvec_exhaustive m => fun w0 scr k => match term_get_val scr with
                                                     | Some v => k v w0 acc_refl [env]
                                                     | None => demonic_pattern_match' n _ scr k
                                                     end
          | pat_tuple p => fun w0 scr k =>
                             match term_get_tuple scr with
                             | Some a => k tt w0 acc_refl (tuple_pattern_match_env p a)
                             | None => demonic_pattern_match' n (pat_tuple p) scr k
                             end
          | pat_record R Δ p => fun w0 scr k =>
                                  match term_get_record scr with
                                  | Some a => k tt w0 acc_refl (record_pattern_match_env p a)
                                  | None => demonic_pattern_match' n (pat_record R Δ p) scr k
                                  end
          | pat_union U p => fun w0 scr k =>
                               match term_get_union scr with
                               | Some (existT K scr') =>
                                   demonic (unionk_ty U K) (p K) w0 scr'
                                     (fun pc => k (existT K pc))
                               | None => demonic_pattern_match' n (pat_union U p) scr k
                               end
          | _ => demonic_pattern_match' n _
          end.

      Definition angelic_match_bvec' {AT n} {Γ1 Γ2} :
        ⊢ STerm (ty.bvec n) -> (⌜bv n⌝ -> □(SHeapSpecM Γ1 Γ2 AT)) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t k =>
          ⟨ ω1 ⟩ b <- angelic_finite (bv n)
                        (fun (δ : SStore Γ1 w0) (h : SHeap w0) =>
                           (amsg.mk {| msg_function := "SHeapSpecM.angelic_match_bvec";
                              msg_message := "pattern match assertion";
                              msg_program_context := Γ1;
                              msg_localstore := δ;
                              msg_heap := h;
                              msg_pathcondition := wco w0
                           |})) ;;
          let t1 := persist__term t ω1 in
          ⟨ ω2 ⟩ _ <- assert_formula (formula_relop bop.eq t1 (term_val (ty.bvec n) b)) ;;
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
          ⟨ ω1 ⟩ b <- demonic_finite (bv n) ;;
          let s1 := term_val (ty.bvec n) b in
          let t1 := persist__term t ω1 in
          ⟨ ω2 ⟩ _ <- assume_formula (formula_relop bop.eq s1 t1) ;;
          four (k b) ω1 ω2.

      Definition demonic_match_bvec {AT n} {Γ1 Γ2} :
        ⊢ STerm (ty.bvec n) -> (⌜bv n⌝ -> □(SHeapSpecM Γ1 Γ2 AT)) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t k =>
          match term_get_val t with
          | Some b => T (k b)
          | None   => demonic_match_bvec' t k
          end.

      Definition demonic_match_bvec_split {AT m n} (x y : LVar) {Γ1 Γ2} :
        ⊢ STerm (ty.bvec (m + n)) -> □(STerm (ty.bvec m) -> STerm (ty.bvec n) -> SHeapSpecM Γ1 Γ2 AT) -> SHeapSpecM Γ1 Γ2 AT :=
        fun w0 t k =>
          ⟨ ω1 ⟩ t1 <- demonic (Some x) (ty.bvec m) ;;
          ⟨ ω2 ⟩ t2 <- demonic (Some y) (ty.bvec n) ;;
          let ω12 := ω1 ∘ ω2 in
          let t   := persist__term t ω12 in
          let t1  := persist__term t1 ω2 in
          ⟨ ω3 ⟩ _  <- assume_formula (formula_relop bop.eq (term_binop (@bop.bvapp _ m n) t1 t2) t) ;;
          let t1 := persist__term t1 ω3 in
          let t2 := persist__term t2 ω3 in
          k _ (ω12 ∘ ω3) t1 t2.

      Definition pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : @Pattern N σ) :
        ⊢ WTerm σ -> SHeapSpecM Γ Γ (SMatchResult pat) :=
        fun w t => lift_purem (SPureSpecM.pattern_match n pat t).
      #[global] Arguments pattern_match {N} n {Γ σ} pat [w].

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
        ⊢ SHeapSpecM Γ Γ (SStore σs) :=
        fun w POST δ =>
          T POST (env.map (fun (b : PVar∷Ty) (e : Exp Γ (type b)) => peval (seval_exp δ e)) es) δ.

      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} : ⊢ STerm σ -> SHeapSpecM Γ Γ Unit :=
        fun w0 t POST δ => T POST tt (δ ⟪ x ↦ t ⟫).
      Global Arguments assign {Γ} x {σ xIn} [w] v.

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

        Equations(noeqns) match_chunk_user_precise (c : Chunk Σ) : option (PathCondition Σ) :=
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

        Fixpoint find_chunk_user_precise (h : SHeap Σ) : option (SHeap Σ * PathCondition Σ) :=
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
          match_chunk_ptsreg_precise (chunk_ptsreg ?(r) t') (left eq_refl) :=
                Some (formula_relop bop.eq t t');
          match_chunk_ptsreg_precise (chunk_ptsreg r' t') (right _) := None
        };
        match_chunk_ptsreg_precise _ := None.

        Fixpoint find_chunk_ptsreg_precise (h : SHeap Σ) : option (SHeap Σ * PathCondition Σ) :=
          match h with
          | nil => None
          | cons c h' =>
              match match_chunk_ptsreg_precise c with
              | Some fml => Some (h', ctx.nil ▻ fml)
              | None => option_map (base.prod_map (cons c) id) (find_chunk_ptsreg_precise h')
              end
          end.

      End ConsumePrecisePtsreg.

      Definition try_consume_chunk_precise {Σ} (h : SHeap Σ) (c : Chunk Σ) : option (SHeap Σ * PathCondition Σ) :=
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
        ⊢ Chunk -> SHeapSpecM Γ Γ Unit :=
        fun w0 c =>
          ⟨ ω1 ⟩ h <- get_heap (w := _) ;;
          match try_consume_chunk_exact h (peval_chunk c⟨ω1⟩) with
          | Some h' => put_heap h'
          | None =>
            match try_consume_chunk_precise h (peval_chunk c⟨ω1⟩) with
            | Some (h', Fs) => ⟨ ω2 ⟩ _ <- put_heap h' ;; assert_pathcondition Fs⟨ω2⟩
            | None =>
              error
                (fun δ1 h1 =>
                   amsg.mk
                   {| debug_consume_chunk_program_context := Γ;
                      debug_consume_chunk_pathcondition := wco _;
                      debug_consume_chunk_localstore := δ1;
                      debug_consume_chunk_heap := h1;
                      debug_consume_chunk_chunk := peval_chunk c⟨ω1⟩
                   |})
              end
          end.

      Definition consume_chunk_angelic {Γ} :
        ⊢ Chunk -> SHeapSpecM Γ Γ Unit :=
        fun w0 c =>
          ⟨ ω1 ⟩ h <- get_heap (w := _) ;;
          match try_consume_chunk_exact h (peval_chunk c⟨ω1⟩) with
          | Some h' => put_heap h'
          | None =>
            match try_consume_chunk_precise h (peval_chunk c⟨ω1⟩) with
            | Some (h', Fs) => ⟨ ω2 ⟩ _ <- put_heap h' ;; assert_pathcondition Fs⟨ω2⟩
            | None =>
                ⟨ ω2 ⟩ '(c',h') <-
                  angelic_list
                    (A := Pair Chunk SHeap)
                    (fun δ1 h1 =>
                       amsg.mk
                       {| debug_consume_chunk_program_context := Γ;
                          debug_consume_chunk_pathcondition := wco _;
                          debug_consume_chunk_localstore := δ1;
                          debug_consume_chunk_heap := h1;
                          debug_consume_chunk_chunk := peval_chunk c⟨ω1⟩
                       |})
                    (heap_extractions h);;
                ⟨ ω3 ⟩ _ <- assert_eq_chunk (peval_chunk c⟨ω1 ∘ ω2⟩) c' ;;
                put_heap h'⟨ω3⟩
              end
          end.

      Definition produce {Γ} :
        ⊢ Assertion -> □(SHeapSpecM Γ Γ Unit) :=
        fix produce w0 asn :=
          match asn with
          | asn.formula fml => box_assume_formula fml
          | asn.chunk c => produce_chunk <$> persist c
          | asn.chunk_angelic c => produce_chunk <$> persist c
          | asn.pattern_match s pat rhs =>
             fun w1 r01 =>
               demonic_pattern_match id pat s⟨r01⟩
                 (fun pc w2 r12 ζ =>
                    produce (wcat w0 (PatternCaseCtx pc))
                      (rhs pc) w2 (acc_cat_left (r01 ∘ r12) ζ))
               (* ⟨ r12 ⟩ '(existT pc ζ) <- pattern_match id pat s⟨r01⟩ ;; *)
               (* produce (wcat w0 (PatternCaseCtx pc)) *)
               (*   (rhs pc) _ (acc_cat_left (r01 ∘ r12) ζ) *)
           | asn.sep a1 a2 =>
             fun w1 ω01 =>
               ⟨ ω12 ⟩ _ <- produce w0 a1 w1 ω01 ;;
               produce w0 a2 _ (ω01 ∘ ω12)
          | asn.or a1 a2 => demonic_binary <$> produce w0 a1 <*> produce w0 a2
          | asn.exist ς τ a =>
            fun w1 ω01 =>
              ⟨ ω12 ⟩ t2 <- demonic (Some ς) τ;;
              produce (wsnoc w0 (ς∷τ)) a _ (acc_snoc_left (ω01 ∘ ω12) (ς∷τ) t2)
          | asn.debug =>
            fun w1 _ =>
              debug
                (fun δ1 h1 =>
                   amsg.mk
                   {| debug_asn_program_context := Γ;
                      debug_asn_pathcondition := wco w1;
                      debug_asn_localstore := δ1;
                      debug_asn_heap := h1
                   |})
                (pure tt)
         end.

      Definition consume {Γ} :
        ⊢ Assertion -> □(SHeapSpecM Γ Γ Unit) :=
        fix consume w0 asn :=
          match asn with
          | asn.formula fml => box_assert_formula fml
          | asn.chunk c => consume_chunk <$> persist c
          | asn.chunk_angelic c => consume_chunk_angelic <$> persist c
          | asn.pattern_match s pat rhs =>
             fun w1 r01 =>
               angelic_pattern_match id pat s⟨r01⟩
                 (fun pc w2 r12 ζ =>
                    consume (wcat w0 (PatternCaseCtx pc))
                      (rhs pc) w2 (acc_cat_left (r01 ∘ r12) ζ))
               (* ⟨ r12 ⟩ '(existT pc ζ) <- wip_pattern_match id pat s⟨r01⟩ ;; *)
               (* consume (wcat w0 (PatternCaseCtx pc)) *)
               (*   (rhs pc) _ (acc_cat_left (r01 ∘ r12) ζ) *)
          | asn.sep a1 a2 =>
            fun w1 ω01 =>
              ⟨ ω12 ⟩ _ <- consume w0 a1 w1 ω01 ;;
              consume w0 a2 _ (ω01 ∘ ω12)
          | asn.or a1 a2 => angelic_binary <$> consume w0 a1 <*> consume w0 a2
          | asn.exist ς τ a =>
            fun w1 ω01 =>
              ⟨ ω12 ⟩ t2 <- angelic (Some ς) τ;;
              consume (wsnoc w0 (ς∷τ)) a _ (acc_snoc_left (ω01 ∘ ω12) (ς∷τ) t2)
          | asn.debug =>
            fun w1 ω01 =>
              debug
                (fun δ1 h1 =>
                 amsg.mk
                 {| debug_asn_program_context := Γ;
                    debug_asn_pathcondition := wco w1;
                    debug_asn_localstore := δ1;
                    debug_asn_heap := h1
                 |})
                (pure tt)
          end.

    End ProduceConsume.

    Section Exec.

      Variable cfg : Config.

      Definition call_contract {Γ Δ τ} (c : SepContract Δ τ) :
        ⊢ SStore Δ -> SHeapSpecM Γ Γ (STerm τ) :=
        match c with
        | MkSepContract _ _ Σe δe req result ens =>
          fun w0 args =>
            ⟨ ω1 ⟩ evars <- angelic_ctx id Σe ;;
            ⟨ ω2 ⟩ _     <- assert_eq_nenv (subst δe evars) args⟨ω1⟩ ;;

            ⟨ ω3 ⟩ _     <- (let we := @MkWorld Σe ctx.nil in
                            consume (w := we)
                              req (@acc_sub we _ evars (fun _ _ => I) ∘ ω2)) ;;
            ⟨ ω4 ⟩ res   <- demonic (Some result) τ;;
            ⟨ ω5 ⟩ _     <- (let we := @MkWorld (Σe ▻ result∷τ) ctx.nil in
                            let evars' := persist (A := Sub _) evars (ω2 ∘ ω3 ∘ ω4) in
                            let ζ      := sub_snoc evars' (result∷τ) res in
                            produce (w := we) ens (@acc_sub we _ ζ (fun _ _ => I))) ;;
            pure res⟨ω5⟩
       end.

      Definition call_lemma {Γ Δ} (lem : Lemma Δ) :
        ⊢ SStore Δ -> SHeapSpecM Γ Γ Unit :=
        match lem with
        | MkLemma _ Σe δe req ens =>
          fun w0 args =>
            ⟨ ω1 ⟩ evars <- angelic_ctx id Σe ;;
            ⟨ ω2 ⟩ _     <- assert_eq_nenv (subst δe evars) args⟨ω1⟩ ;;
            let we := @MkWorld Σe ctx.nil in
            ⟨ ω3 ⟩ _     <- consume (w := we) req (@acc_sub we _ evars (fun _ _ => I) ∘ ω2) ;;
                           (let evars' := persist (A := Sub _) evars (ω2 ∘ ω3) in
                            produce (w := we) ens (@acc_sub we _ evars' (fun _ _ => I)))
        end.

      Definition call_contract_debug {Γ Δ τ} (f : 𝑭 Δ τ) (c : SepContract Δ τ) :
        ⊢ SStore Δ -> SHeapSpecM Γ Γ (STerm τ) :=
        fun w0 δΔ =>
          let o := call_contract c δΔ in
          if config_debug_function cfg f
          then
            debug
              (fun δ h => amsg.mk
                          {| debug_call_function_parameters := Δ;
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
            | stm_read_register reg =>
                ⟨ ω01 ⟩ t <- angelic None _ ;;
                ⟨ ω12 ⟩ _ <- T (consume (asn.chunk (chunk_ptsreg reg t))) ;;
                ⟨ ω23 ⟩ _ <- T (produce (asn.chunk (chunk_ptsreg reg (persist__term t ω12))));;
                pure (persist__term t (ω12 ∘ ω23))
            | stm_write_register reg e =>
                ⟨ ω01 ⟩ told <- angelic None _ ;;
                ⟨ ω12 ⟩ _    <- T (consume (asn.chunk (chunk_ptsreg reg told))) ;;
                ⟨ ω23 ⟩ tnew <- eval_exp e (w:=_) ;;
                ⟨ ω34 ⟩ _ <- T (produce (asn.chunk (chunk_ptsreg reg tnew))) ;;
                pure (persist__term tnew ω34)
            | stm_pattern_match s pat rhs =>
                ⟨ ω1 ⟩ v  <- exec_aux s ;;
                demonic_pattern_match
                  PVartoLVar pat v
                  (fun pc w2 ω2 vs =>
                     pushspops vs (exec_aux (rhs pc)))
                (* ⟨ r1 ⟩ v  <- exec_aux s ;; *)
                (* ⟨ r2 ⟩ '(existT pc vs) <- wip_pattern_match PVartoLVar pat v ;; *)
                (* pushspops vs (exec_aux (rhs pc)) *)
            | stm_bind _ _ =>
                error
                  (fun δ h =>
                     amsg.mk
                     {| msg_function := "SHeapSpecM.exec";
                        msg_message := "stm_bind not supported";
                        msg_program_context := _;
                        msg_localstore := δ;
                        msg_heap := h;
                        msg_pathcondition := wco w0
                  |})
            | stm_debugk k =>
                debug
                  (fun (δ0 : SStore Γ w0) (h0 : SHeap w0) =>
                     amsg.mk
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
        | O   => fun _ _ _ _ =>
                   error
                     (fun δ h =>
                        amsg.mk
                        {| msg_function := "SHeapSpecM.exec";
                           msg_message := "out of fuel for inlining";
                           msg_program_context := _;
                           msg_localstore := δ;
                           msg_heap := h;
                           msg_pathcondition := wco _
                        |})
        | S n => @exec_aux (@exec n)
        end.
      Global Arguments exec _ {_ _} _ {w} _ _ _.

      Import Notations.

      Variable inline_fuel : nat.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
        SHeapSpecM Δ Δ Unit {| wctx := sep_contract_logic_variables c; wco := ctx.nil |} :=
        match c with
        | MkSepContract _ _ _ _ req result ens =>
          ⟨ ω01 ⟩ _   <- produce (w:=@MkWorld _ _) req acc_refl ;;
          ⟨ ω12 ⟩ res <- exec inline_fuel s ;;
          consume
            (w:=wsnoc (@MkWorld _ ctx.nil) (result∷τ)%ctx)
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

    Definition ValidContractWithFuel {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition
        (postprocess
           (vcgen default_config fuel c body)).

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      (* Use inline_fuel = 1 by default. *)
      ValidContractWithFuel 1 c body.

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

    Definition ValidContractReflectWithFuel {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      is_true (ok (postprocess (vcgen default_config fuel c body))).

    Definition ValidContractReflect {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      ValidContractReflectWithFuel 1 c body.

    Lemma validcontract_reflect_fuel_sound {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractReflectWithFuel fuel c body ->
      ValidContractWithFuel fuel c body.
    Proof.
      unfold ValidContractReflectWithFuel, ValidContractWithFuel. intros Hok.
      apply (ok_sound _ env.nil) in Hok. now constructor.
    Qed.

    Lemma validcontract_reflect_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractReflect c body ->
      ValidContract c body.
    Proof.
      eapply validcontract_reflect_fuel_sound.
    Qed.

    Definition VcGenErasure {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Erasure.ESymProp :=
      Erasure.erase_symprop (postprocess (vcgen default_config 1 c body)).

    Definition ValidContractWithErasure {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationConditionWithErasure (VcGenErasure c body).

    Lemma verification_condition_with_erasure_sound (p : 𝕊 ctx.nil) :
      VerificationConditionWithErasure (Erasure.erase_symprop p) ->
      VerificationCondition p.
    Proof. intros [H]. constructor. now rewrite <- Erasure.erase_safe. Qed.

    Lemma validcontract_with_erasure_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractWithErasure c body ->
      ValidContract c body.
    Proof. apply verification_condition_with_erasure_sound. Qed.

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
                   sep_contract_postcondition   := asn.sep post asn.debug;
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

  Module Replay.

    Import SPureSpecM.
    Import SPureSpecM.notations.

    Definition replay_aux : forall {Σ} (s : 𝕊 Σ) {w : World},
        MkWorld Σ ctx.nil ⊒ w -> SPureSpecM Unit w :=
      fix replay {Σ} s {w} {struct s} :=
        match s with
        | SymProp.angelic_binary o1 o2 =>
            fun r => angelic_binary (replay o1 r) (replay o2 r)
        | SymProp.demonic_binary o1 o2 =>
            fun r => demonic_binary (replay o1 r) (replay o2 r)
        | SymProp.block =>
            fun r => block
        | SymProp.error msg =>
            fun r => error msg⟨r⟩
        | assertk fml msg k =>
            fun r01 =>
              ⟨ r12 ⟩ _ <- assert_formula msg⟨r01⟩ fml⟨r01⟩ ;;
              replay k (r01 ∘ r12)
        | assumek fml k =>
            fun r01 =>
              ⟨ r12 ⟩ _ <- assume_formula fml⟨r01⟩ ;;
              replay k (r01 ∘ r12)
        | angelicv b k =>
            fun r01 P =>
              angelicv b
                (replay k
                   (@acc_sub (MkWorld (Σ▻b) ctx.nil) (wsnoc w b)
                      (sub_up1 (sub_acc r01))
                      entails_nil)
                   (four P acc_snoc_right))
        | demonicv b k =>
            fun r01 P =>
              demonicv b
                (replay k
                   (@acc_sub (MkWorld (Σ▻b) ctx.nil) (wsnoc w b)
                      (sub_up1 (sub_acc r01))
                      entails_nil)
                   (four P acc_snoc_right))
        | @assert_vareq _ x σ xIn t msg k =>
            fun r01 =>
              let ζ    := subst (sub_shift xIn) (sub_acc r01) in
              let msg1 := subst msg ζ in
              let x1   := subst (T := fun Σ => Term Σ _) (term_var x) (sub_acc r01) in
              let t1   := subst (T := fun Σ => Term Σ _) t ζ in
              ⟨ r12 ⟩ _ <- assert_formula msg1 (formula_relop bop.eq x1 t1) ;;
              replay k (@acc_sub (MkWorld (Σ-x∷σ) ctx.nil) _ ζ entails_nil ∘ r12)
        | @assume_vareq _ x σ xIn t k =>
            fun r01 =>
              let ζ    := subst (sub_shift xIn) (sub_acc r01) in
              let x1   := subst (T := fun Σ => Term Σ _) (term_var x) (sub_acc r01) in
              let t1   := subst (T := fun Σ => Term Σ _) t ζ in
              ⟨ r12 ⟩ _ <- assume_formula (formula_relop bop.eq x1 t1) ;;
              replay k (@acc_sub (MkWorld (Σ-x∷σ) ctx.nil) _ ζ entails_nil ∘ r12)
        | SymProp.pattern_match s pat rhs => fun r P => SymProp.block (* FIXME *)
        | SymProp.pattern_match_var x pat rhs => fun r P => SymProp.block (* FIXME *)
        | debug b k => fun r01 P => debug (subst b (sub_acc r01)) (replay k r01 P)
        end.

    Definition replay {Σ} (s : 𝕊 Σ) : 𝕊 Σ :=
      replay_aux s acc_refl (fun _ _ _ => SymProp.block).

  End Replay.

End SymbolicExecOn.

Module MakeExecutor
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SIG  : Signature B)
  (Import SPEC : Specification B PROG SIG)
  (Import SOLV : SolverKit B SIG).

  Include SymbolicExecOn B PROG SIG SPEC SOLV.

End MakeExecutor.
