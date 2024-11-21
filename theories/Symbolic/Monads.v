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
  Classes.Morphisms
  Classes.Morphisms_Prop
  Classes.RelationClasses
  Program.Basics
  Relations.Relation_Definitions.
From Equations Require Import
  Equations.
From Katamaran Require Import
  Prelude
  Base
  (* Sep.Logic *)
  Syntax.Assertions
  Syntax.Chunks
  Syntax.Predicates
  Symbolic.Solver
  Symbolic.Propositions
  Symbolic.Worlds.

Import ctx.notations.
Import env.notations.
Import SignatureNotations.

Set Implicit Arguments.

Module Type SymbolicMonadsOn
  (Import B : Base)
  (Import PK : PredicateKit B)
  (Import WR : WorldsMixin B PK)
  (Import SK : SolverKit B PK WR)
  (Import AS : AssertionsOn B PK WR)
  (Import SP : SymPropOn B PK WR)
  (Import GS : GenericSolverOn B PK WR SK).

  Import ModalNotations.
  Local Open Scope modal.

  Section DebugInfo.

    Import option.notations.

    Record DebugAsn (Σ : LCtx) : Type :=
      MkDebugAsn
        { (* debug_asn_program_context        : PCtx; *)
          debug_asn_pathcondition          : PathCondition Σ;
          (* debug_asn_localstore             : SStore debug_asn_program_context Σ; *)
          debug_asn_heap                   : SHeap Σ;
        }.

    #[export] Instance SubstDebugAsn : Subst DebugAsn :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugAsn pc (* δ *) h =>
          MkDebugAsn (subst pc ζ01) (* (subst δ ζ01) *) (subst h ζ01)
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
        | MkDebugAsn pc (* δ *) h =>
            pc' <- occurs_check xIn pc ;;
            (* δ'  <- occurs_check xIn δ ;; *)
            h'  <- occurs_check xIn h ;;
            Some (MkDebugAsn pc' (* δ' *) h')
        end.

    Record DebugConsumeChunk (Σ : LCtx) : Type :=
      MkDebugConsumeChunk
        { (* debug_consume_chunk_program_context        : PCtx; *)
          debug_consume_chunk_pathcondition          : PathCondition Σ;
          (* debug_consume_chunk_localstore             : SStore debug_consume_chunk_program_context Σ; *)
          debug_consume_chunk_heap                   : SHeap Σ;
          debug_consume_chunk_chunk                  : Chunk Σ;
        }.

    #[export] Instance SubstDebugConsumeChunk : Subst DebugConsumeChunk :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugConsumeChunk pc (* δ *) h c =>
            MkDebugConsumeChunk (subst pc ζ01) (* (subst δ ζ01) *) (subst h ζ01) (subst c ζ01)
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
        | MkDebugConsumeChunk pc (* δ *) h c =>
            pc' <- occurs_check xIn pc ;;
            (* δ'  <- occurs_check xIn δ ;; *)
            h'  <- occurs_check xIn h ;;
            c'  <- occurs_check xIn c ;;
            Some (MkDebugConsumeChunk pc' (* δ' *) h'  c')
        end.

  End DebugInfo.

  #[local] Hint Extern 2 (Persistent (WTerm ?σ)) =>
    refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.
  #[local] Hint Extern 2 (Persistent (fun w : World => NamedEnv (Term (wctx w)) ?Γ)) =>
    refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.
  #[local] Hint Extern 2 (Persistent (fun w : World => @Env _ (fun xt => Term (wctx w) (type  xt)) ?Γ)) =>
    refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.

  Definition symprop_assert_pathcondition :
    ⊢ AMessage -> PathCondition -> □SymProp -> SymProp :=
    fun w0 msg C0 POST =>
      match combined_solver _ C0 with
      | Some (existT w1 (ν , C1)) =>
          (* Assert variable equalities and the residual constraints *)
          SymProp.assert_triangular msg ν
            (fun msg' =>
               SymProp.assert_pathcondition_without_solver msg' C1
                 (* Critical code. Like for assume_pathcondition. *)
                 (four POST (acc_triangular ν) (acc_pathcondition_right w1 C1)))
      | None =>
          (* The new path constraints are inconsistent with the old path
             constraints. *)
          SymProp.error msg
      end.

  Definition symprop_assume_pathcondition :
    ⊢ PathCondition -> □SymProp -> SymProp :=
    fun w0 C0 POST =>
      match combined_solver _ C0 with
      | Some (existT w1 (ν , C1)) =>
          (* Assume variable equalities and the residual constraints *)
          SymProp.assume_triangular ν
            (SymProp.assume_pathcondition_without_solver C1
               (* Run POST in the world with the variable and residual formulas *)
               (* included. This is a critical piece of code since this is the *)
               (* place where we really meaningfully change the world. We *)
               (* changed the type of assume_pathcondition_without_solver just *)
               (* to not forget adding the new path constraints. *)
               (four POST (acc_triangular ν) (acc_pathcondition_right w1 C1)))
      | None =>
          (* The new path constraints are inconsistent with the old path *)
          (* constraints. *)
          SymProp.block
      end.

  Definition SPureSpec (A : TYPE) : TYPE :=
    □(A -> 𝕊) -> 𝕊.

  Module SPureSpec.

    Definition run :
      ⊢ SPureSpec Unit -> 𝕊 :=
      fun w m => m (fun w1 θ1 _ => SymProp.block).

    Definition pure {A : TYPE} :
      ⊢ A -> SPureSpec A :=
      fun w0 a POST => T POST a.

    Definition bind {A B} :
      ⊢ SPureSpec A -> □(A -> SPureSpec B) -> SPureSpec B :=
      fun w0 m f POST => m (fun w1 ω01 a1 => f w1 ω01 a1 (four POST ω01)).
    #[global] Arguments bind {A B} [w] m f _ /.

    Module Import notations.
      Notation "⟨ ω ⟩ ' x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 80, x pattern,
             ma at next level, mb at level 200,
               right associativity).
      Notation "⟨ ω ⟩ x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 80, x at next level,
             ma at next level, mb at level 200,
               right associativity).
      Notation "x ⟨ ω ⟩" := (persist x ω).
    End notations.

    Definition block {A} :
      ⊢ SPureSpec A :=
      fun w POST => SymProp.block.
    #[global] Arguments block {A w}.
    Definition error {A} :
      ⊢ □(AMessage) -> SPureSpec A :=
      fun w msg POST => SymProp.error (T msg).

    Definition angelic (x : option LVar) :
      ⊢ ∀ σ, SPureSpec (STerm σ) :=
      fun w σ k =>
        let y := fresh_lvar w x in
        SymProp.angelicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    #[global] Arguments angelic x [w] σ k : rename.

    Definition demonic (x : option LVar) :
      ⊢ ∀ σ, SPureSpec (STerm σ) :=
      fun w σ k =>
        let y := fresh_lvar w x in
        SymProp.demonicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    #[global] Arguments demonic x [w] σ k : rename.

    Definition angelic_ctx {N : Set} (n : N -> LVar) :
      ⊢ ∀ Δ : NCtx N Ty, SPureSpec (fun w => NamedEnv (Term w) Δ) :=
      fix rec {w} Δ {struct Δ} :=
        match Δ with
        | []%ctx => pure []%env
        | Γ ▻ x∷σ => ⟨ ω1 ⟩ tΔ <- rec Γ;;
                     ⟨ ω2 ⟩ tσ <- angelic (Some (n x)) σ ;;
                     pure (tΔ⟨ω2⟩ ► (x∷σ ↦ tσ))
        end.
    #[global] Arguments angelic_ctx {N} n [w] Δ : rename.

    Definition demonic_ctx {N : Set} (n : N -> LVar) :
      ⊢ ∀ Δ : NCtx N Ty, SPureSpec (fun w => NamedEnv (Term w) Δ) :=
      fix rec {w} Δ {struct Δ} :=
        match Δ with
        | []%ctx  => pure []%env
        | Δ ▻ x∷σ => ⟨ ω1 ⟩ tΔ <- rec Δ;;
                     ⟨ ω2 ⟩ tσ <- demonic (Some (n x)) σ;;
                     pure (tΔ⟨ω2⟩ ► (x∷σ ↦ tσ))
        end%ctx.
    #[global] Arguments demonic_ctx {_} n [w] Δ : rename.

    Definition assert_pathcondition :
      ⊢ □(AMessage) -> PathCondition -> SPureSpec Unit :=
      fun w msg C POST =>
        symprop_assert_pathcondition
          (msg _ acc_refl) C
          (POST <*> (fun w r => tt)).
    Definition assume_pathcondition :
      ⊢ PathCondition -> SPureSpec Unit :=
      fun w C POST => symprop_assume_pathcondition C (POST <*> (fun w r => tt)).

    Definition assert_formula :
      ⊢ □(AMessage) -> Formula -> SPureSpec Unit :=
      fun w0 msg fml0 =>
        assert_pathcondition msg (ctx.nil ▻ fml0 ).
    Definition assume_formula :
      ⊢ Formula -> SPureSpec Unit :=
      fun w F => assume_pathcondition ([ctx] ▻ F).

    Definition angelic_binary {A} :
      ⊢ SPureSpec A -> SPureSpec A -> SPureSpec A :=
      fun w m1 m2 POST =>
        SymProp.angelic_binary (m1 POST) (m2 POST).
    Definition demonic_binary {A} :
      ⊢ SPureSpec A -> SPureSpec A -> SPureSpec A :=
      fun w m1 m2 POST =>
        SymProp.demonic_binary (m1 POST) (m2 POST).

    Definition angelic_list' {A} :
      ⊢ A -> WList A -> SPureSpec A :=
      fun w =>
        fix rec d xs :=
        match xs with
        | nil        => pure d
        | cons x xs  => angelic_binary (pure d) (rec x xs)
        end.
    #[global] Arguments angelic_list' {A} [w].

    Definition angelic_list {A} :
      ⊢ □(AMessage) -> WList A -> SPureSpec A :=
      fun w msg xs =>
        match xs with
        | nil        => error msg
        | cons x xs  => angelic_list' x xs
        end.

    Definition demonic_list' {A} :
      ⊢ A -> WList A -> SPureSpec A :=
      fun w =>
        fix rec d xs :=
        match xs with
        | nil        => pure d
        | cons x xs  => demonic_binary (pure d) (rec x xs)
        end.

    Definition demonic_list {A} :
      ⊢ WList A -> SPureSpec A :=
      fun w xs =>
        match xs with
        | nil        => block
        | cons x xs  => demonic_list' x xs
        end.

    Definition angelic_finite F `{finite.Finite F} :
      ⊢ □(AMessage) -> SPureSpec ⌜F⌝ :=
      fun w msg => angelic_list msg (finite.enum F).
    #[global] Arguments angelic_finite F {_ _ w}.

    Definition demonic_finite F `{finite.Finite F} :
      ⊢ SPureSpec ⌜F⌝ :=
      fun w => demonic_list (finite.enum F).
    #[global] Arguments demonic_finite F {_ _ w}.

    Section PatternMatching.

      Context {N : Set} (n : N -> LVar).

      Definition angelic_pattern_match' {σ} (pat : @Pattern N σ) :
        ⊢ □(AMessage) -> WTerm σ -> SPureSpec (SMatchResult pat) :=
        fun w0 msg t =>
          ⟨ θ1 ⟩ pc <- angelic_finite (PatternCase pat) msg ;;
          ⟨ θ2 ⟩ ts <- angelic_ctx n (PatternCaseCtx pc) ;;
          let θ12 := θ1 ∘ θ2 in
          ⟨ θ3 ⟩ _  <- assert_formula (four msg θ12)
                         (formula_relop bop.eq
                            (pattern_match_term_reverse pat pc ts)
                            t⟨θ12⟩);;
          pure (A := SMatchResult pat) (existT pc ts⟨θ3⟩).
      #[global] Arguments angelic_pattern_match' {σ} pat [w].

      Definition angelic_pattern_match :
        forall {σ} (pat : @Pattern N σ),
          ⊢ □(AMessage) -> WTerm σ -> SPureSpec (SMatchResult pat) :=
        fix angelic (σ : Ty) (pat : Pattern σ) {w0} msg {struct pat} :
          WTerm σ w0 -> SPureSpec (SMatchResult pat) w0 :=
          match pat with
          | pat_var x =>
              fun scr =>
                pure
                  (A := SMatchResult (pat_var x))
                  (existT tt [env].[x∷_ ↦ scr])
          | pat_bool =>
              fun scr =>
                match term_get_val scr with
                | Some v => pure (A := SMatchResult pat_bool)
                              (existT v [env])
                | None => angelic_pattern_match' _ msg scr
                end
          | pat_list _ _ _ =>
              fun scr =>
                angelic_pattern_match' _ msg scr
          | pat_pair x y =>
              fun scr =>
                match term_get_pair scr with
                | Some (tl, tr) =>
                    pure (A := SMatchResult (pat_pair x y))
                      (existT tt [env].[x∷_ ↦ tl].[y∷_ ↦ tr])
                | None => angelic_pattern_match' _ msg scr
                end
          | pat_sum _ _ _ _ =>
              fun scr =>
                match term_get_sum scr with
                | Some (inl tl) => pure (A := SMatchResult (pat_sum _ _ _ _))
                                     (existT true [env].[_∷_ ↦ tl])
                | Some (inr tr) => pure (A := SMatchResult (pat_sum _ _ _ _))
                                     (existT false [env].[_∷_ ↦ tr])
                | None => angelic_pattern_match' _ msg scr
                end
          | pat_unit =>
              fun scr =>
                pure (A := SMatchResult pat_unit) (existT tt [env])
          | pat_enum E =>
              fun scr =>
                match term_get_val scr with
                | Some v => pure (A := SMatchResult (pat_enum E))
                              (existT v [env])
                | None => angelic_pattern_match' _ msg scr
                end
          | pat_bvec_split _ _ _ _ =>
              fun scr =>
                angelic_pattern_match' _ msg scr
          | pat_bvec_exhaustive m =>
              fun scr =>
                match term_get_val scr with
                | Some v => pure (A := SMatchResult (pat_bvec_exhaustive m))
                              (existT v [env])
                | None => angelic_pattern_match' _ msg scr
                end
          | pat_tuple p =>
              fun scr =>
                match term_get_tuple scr with
                | Some a => pure (A := SMatchResult (pat_tuple p))
                              (existT tt (tuple_pattern_match_env p a))
                | None => angelic_pattern_match' (pat_tuple p) msg scr
                end
          | pat_record R Δ p =>
              fun scr =>
                match term_get_record scr with
                | Some a => pure (A := SMatchResult (pat_record R Δ p))
                              (existT tt (record_pattern_match_env p a))
                | None => angelic_pattern_match' (pat_record R Δ p) msg scr
                end
          | pat_union U p =>
              fun scr =>
                match term_get_union scr with
                | Some (existT K scr') =>
                    ⟨ θ1 ⟩ res <- angelic (unionk_ty U K) (p K) msg scr' ;;
                    match res with
                    | existT pc δpc =>
                        pure (A := SMatchResult (pat_union U p))
                          (existT (existT K pc) δpc)
                    end
                | None => angelic_pattern_match' (pat_union U p) msg scr
                end
          end.
      #[global] Arguments angelic_pattern_match {σ} pat [w].

      Definition demonic_pattern_match' {σ} (pat : @Pattern N σ) :
        ⊢ WTerm σ -> SPureSpec (SMatchResult pat) :=
        fun w0 t =>
          ⟨ θ1 ⟩ pc <- demonic_finite (PatternCase pat) ;;
          ⟨ θ2 ⟩ ts <- demonic_ctx n (PatternCaseCtx pc) ;;
          let θ12 := θ1 ∘ θ2 in
          ⟨ θ3 ⟩ _  <- assume_formula
                         (formula_relop bop.eq
                            (pattern_match_term_reverse pat pc ts)
                            t⟨θ12⟩);;
          pure (A := SMatchResult pat) (existT pc ts⟨θ3⟩).
      #[global] Arguments demonic_pattern_match' {σ} pat [w].

      Definition demonic_pattern_match :
        forall {σ} (pat : @Pattern N σ),
          ⊢ WTerm σ -> SPureSpec (SMatchResult pat) :=
        fix demonic (σ : Ty) (pat : Pattern σ) {w0} {struct pat} :
          WTerm σ w0 -> SPureSpec (SMatchResult pat) w0 :=
          match pat with
          | pat_var x =>
              fun scr =>
                pure
                  (A := SMatchResult (pat_var x))
                  (existT tt [env].[x∷_ ↦ scr])
          | pat_bool =>
              fun scr =>
                match term_get_val scr with
                | Some v => pure (A := SMatchResult pat_bool)
                              (existT v [env])
                | None => demonic_pattern_match' _ scr
                end
          | pat_list _ _ _ =>
              fun scr =>
                demonic_pattern_match' _ scr
          | pat_pair x y =>
              fun scr =>
                match term_get_pair scr with
                | Some (tl, tr) =>
                    pure (A := SMatchResult (pat_pair x y))
                      (existT tt [env].[x∷_ ↦ tl].[y∷_ ↦ tr])
                | None => demonic_pattern_match' _ scr
                end
          | pat_sum _ _ _ _ =>
              fun scr =>
                match term_get_sum scr with
                | Some (inl tl) => pure (A := SMatchResult (pat_sum _ _ _ _))
                                     (existT true [env].[_∷_ ↦ tl])
                | Some (inr tr) => pure (A := SMatchResult (pat_sum _ _ _ _))
                                     (existT false [env].[_∷_ ↦ tr])
                | None => demonic_pattern_match' _ scr
                end
          | pat_unit =>
              fun scr =>
                pure (A := SMatchResult pat_unit) (existT tt [env])
          | pat_enum E =>
              fun scr =>
                match term_get_val scr with
                | Some v => pure (A := SMatchResult (pat_enum E))
                              (existT v [env])
                | None => demonic_pattern_match' _ scr
                end
          | pat_bvec_split _ _ _ _ =>
              fun scr =>
                demonic_pattern_match' _ scr
          | pat_bvec_exhaustive m =>
              fun scr =>
                match term_get_val scr with
                | Some v => pure (A := SMatchResult (pat_bvec_exhaustive m))
                              (existT v [env])
                | None => demonic_pattern_match' _ scr
                end
          | pat_tuple p =>
              fun scr =>
                match term_get_tuple scr with
                | Some a => pure (A := SMatchResult (pat_tuple p))
                              (existT tt (tuple_pattern_match_env p a))
                | None => demonic_pattern_match' (pat_tuple p) scr
                end
          | pat_record R Δ p =>
              fun scr =>
                match term_get_record scr with
                | Some a => pure (A := SMatchResult (pat_record R Δ p))
                              (existT tt (record_pattern_match_env p a))
                | None => demonic_pattern_match' (pat_record R Δ p) scr
                end
          | pat_union U p =>
              fun scr =>
                match term_get_union scr with
                | Some (existT K scr') =>
                    ⟨ θ1 ⟩ res <- demonic (unionk_ty U K) (p K) scr' ;;
                    match res with
                    | existT pc δpc =>
                        pure (A := SMatchResult (pat_union U p))
                          (existT (existT K pc) δpc)
                    end
                | None => demonic_pattern_match' (pat_union U p) scr
                end
          end.
      #[global] Arguments demonic_pattern_match {σ} pat [w].

      Definition new_pattern_match_regular {σ} (pat : @Pattern N σ) :
        ⊢ STerm σ -> SPureSpec (SMatchResult pat) :=
        fun w0 scr POST =>
          SymProp.pattern_match scr (freshen_pattern n w0 pat)
            (fun pc : PatternCase _ =>
               let w1 : World   := wmatch w0 scr _ pc in
               let r1 : w0 ⊒ w1 := acc_match_right pc in
               POST w1 r1
                 (existT
                    (unfreshen_patterncase n w0 pat pc)
                    (unfreshen_patterncaseenv n pat pc (sub_cat_right _)))).
      #[global] Arguments new_pattern_match_regular {σ} pat [w] t.

      Definition new_pattern_match_var {σ} (x : LVar) (pat : @Pattern N σ) :
        ⊢ ctx.In (x∷σ) -> SPureSpec (SMatchResult pat) :=
        fun w0 xIn POST =>
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
      #[global] Arguments new_pattern_match_var [σ x] pat [w] xIn : rename.

      Definition new_pattern_match' {σ} (pat : @Pattern N σ) :
        ⊢ STerm σ -> SPureSpec (SMatchResult pat) :=
        fun w0 scr =>
          match scr with
          | @term_var _ x σ xIn => fun pat => new_pattern_match_var pat xIn
          | t => fun pat => new_pattern_match_regular pat t
          end pat.
      #[global] Arguments new_pattern_match' {σ} pat [w] t.

      Fixpoint new_pattern_match {σ} (pat : @Pattern N σ) :
        ⊢ WTerm σ -> SPureSpec (SMatchResult pat) :=
        fun w0 : World =>
          match pat as p in (Pattern t)
                return (forall _ : Term (wctx w0) t,
                           SPureSpec (@SMatchResult N t p) w0) with
          | pat_var x       => fun scr => pure (existT tt [env].[x∷_ ↦ scr])
          | pat_bool        =>
              fun scr => match term_get_val scr with
                         | Some a => pure (existT a [env])
                         | None => new_pattern_match' pat_bool scr
                         end
          | pat_list σ x y  =>
              fun scr => new_pattern_match' (pat_list σ x y) scr
          | pat_pair x y    =>
              fun scr =>
                match term_get_pair scr with
                | Some (a, b) => pure (existT tt [env].[x∷_ ↦ a].[y∷_ ↦ b])
                | None        => new_pattern_match' (pat_pair x y) scr
                end
          | pat_sum σ τ x y =>
              fun scr => match term_get_sum scr with
                         | Some (inl a) => pure (existT true [env].[x∷σ ↦ a])
                         | Some (inr b) => pure (existT false [env].[y∷τ ↦ b])
                         | None => new_pattern_match' (pat_sum σ τ x y) scr
                         end
          | pat_unit        => fun _ => pure (existT tt [env])
          | pat_enum E      =>
              fun scr => match term_get_val scr with
                         | Some a => pure (existT a [env])
                         | None => new_pattern_match' (pat_enum E) scr
                         end
          | pat_bvec_split m k x y =>
              fun scr => new_pattern_match' (pat_bvec_split m k x y) scr
          | pat_bvec_exhaustive m =>
              fun scr =>
                match term_get_val scr with
                | Some a => pure (existT a [env])
                | None => new_pattern_match' (pat_bvec_exhaustive m) scr
                end
          | @pat_tuple _ σs Δ p =>
              fun scr =>
                match term_get_tuple scr with
                | Some a => pure (existT tt (tuple_pattern_match_env p a))
                | None => new_pattern_match' (pat_tuple p) scr
                end
          | pat_record R Δ p =>
              fun scr =>
                match term_get_record scr with
                | Some a => pure (existT tt (record_pattern_match_env p a))
                | None => new_pattern_match' (pat_record R Δ p) scr
                end
          | pat_union U p =>
              fun scr =>
                match term_get_union scr with
                | Some (existT K scr') =>
                    ⟨ θ1 ⟩ '(existT pc ts) <- @new_pattern_match _ (p K) _ scr' ;;
                    pure (@existT (PatternCase (pat_union U p))
                            (fun pc => NamedEnv (Term _) (PatternCaseCtx pc))
                            (existT (P := fun K => PatternCase (p K)) K pc) ts)
                | None => new_pattern_match' (pat_union U p) scr
                end
          end.
      #[global] Arguments new_pattern_match {σ} pat [w].

    End PatternMatching.

    Definition debug {A} : ⊢ □(AMessage) -> SPureSpec A -> SPureSpec A :=
      fun w msg m Φ => SymProp.debug (T msg) (m Φ).

    Equations(noeqns) assert_eq_env :
      let E Δ := fun w : World => Env (Term w) Δ in
      ⊢ ∀ Δ : Ctx Ty, □(AMessage) -> E Δ -> E Δ -> SPureSpec Unit :=
    assert_eq_env msg env.nil          env.nil            := pure tt;
    assert_eq_env msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
      ⟨ θ ⟩ _ <- assert_eq_env msg δ δ' ;;
      assert_formula (four msg θ) (formula_relop bop.eq t t')⟨θ⟩.

    Equations(noeqns) assert_eq_nenv {N} :
      let E Δ := fun w : World => NamedEnv (Term w) Δ in
      ⊢ ∀ Δ : NCtx N Ty, □(AMessage) -> E Δ -> E Δ -> SPureSpec Unit :=
    assert_eq_nenv msg env.nil          env.nil            := pure tt;
    assert_eq_nenv msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
      ⟨ θ ⟩ _ <- assert_eq_nenv msg δ δ' ;;
      assert_formula (four msg θ) (formula_relop bop.eq t t')⟨θ⟩.

    Definition assert_eq_chunk : ⊢ □(AMessage) -> Chunk -> Chunk -> □(SPureSpec Unit) :=
      fix assert_eq w0 msg c1 c2 w1 θ1 {struct c1} :=
        match c1 , c2 with
        | chunk_user p1 vs1 as c1 , chunk_user p2 vs2 as c2 =>
            match eq_dec p1 p2 with
            | left e => assert_eq_env (four msg θ1)
                          (eq_rect p1 (fun p => Env (Term w1) (𝑯_Ty p)) vs1⟨θ1⟩ p2 e)
                          (persist (A := fun w => (fun Σ => Env (Term Σ) _) (wctx w)) vs2 θ1)
            | right _ => error msg⟨θ1⟩
            end
        | chunk_ptsreg r1 v1 as c1 , chunk_ptsreg r2 v2 as c2 =>
            match eq_dec_het r1 r2 with
            | left e => assert_formula (four msg θ1)
                          (formula_relop bop.eq (eq_rect _ (Term w1) v1⟨θ1⟩ _ (f_equal projT1 e)) v2⟨θ1⟩)
            | right _ => error msg⟨θ1⟩
            end
        | chunk_conj c11 c12 , chunk_conj c21 c22 =>
            ⟨ θ2 ⟩ _ <- assert_eq _ msg c11 c21 w1 θ1 ;;
            assert_eq _ msg c12 c22 _ (θ1 ∘ θ2)
        | chunk_wand c11 c12 , chunk_wand c21 c22 =>
            ⟨ θ2 ⟩ _ <- assert_eq _ msg c11 c21 w1 θ1 ;;
            assert_eq _ msg c12 c22 _ (θ1 ∘ θ2)
        | _ , _ => error msg⟨θ1⟩
        end.

  End SPureSpec.
  Export (hints) SPureSpec.

  Definition SHeapSpec (A : TYPE) : TYPE :=
    □(A -> SHeap -> 𝕊) -> SHeap -> 𝕊.

  Module SHeapSpec.

    Definition run : ⊢ SHeapSpec Unit -> 𝕊 :=
      fun w m => m (fun w1 θ1 _ h1 => SymProp.block) List.nil.

    Definition lift_purespec {A : TYPE} :
      ⊢ SPureSpec A -> SHeapSpec A :=
      fun w0 m POST h0 =>
        m (fun w1 ω01 a1 => POST w1 ω01 a1 (persist h0 ω01)).

    Definition bind {A B} : ⊢ SHeapSpec A -> □(A -> SHeapSpec B) -> SHeapSpec B :=
      fun w m f Φ => m (fun w1 θ1 a1 => f w1 θ1 a1 (four Φ θ1)).

    Module Import notations.
      Notation "⟨ ω ⟩ ' x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 80, x pattern,
             ma at next level, mb at level 200,
               right associativity).
      Notation "⟨ ω ⟩ x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 80, x at next level,
             ma at next level, mb at level 200,
               right associativity).
      Notation "x ⟨ ω ⟩" := (persist x ω).
    End notations.

    Definition angelic_binary {A} : ⊢ SHeapSpec A -> SHeapSpec A -> SHeapSpec A :=
      fun w m1 m2 Φ h =>
        SymProp.angelic_binary (m1 Φ h) (m2 Φ h).

    Definition demonic_binary {A} : ⊢ SHeapSpec A -> SHeapSpec A -> SHeapSpec A :=
      fun w m1 m2 Φ h =>
        SymProp.demonic_binary (m1 Φ h) (m2 Φ h).

    Definition debug {A} : ⊢ □(SHeap -> AMessage) -> SHeapSpec A -> SHeapSpec A :=
      fun w msg m Φ h => SymProp.debug (T msg h) (m Φ h).

    Definition pure A w a := lift_purespec (@SPureSpec.pure A w a).

    Definition error {A} : ⊢ □(SHeap -> AMessage) -> SHeapSpec A :=
      fun w msg Φ h => SymProp.error (T msg h).

    Definition block A w                               := lift_purespec (@SPureSpec.block A w).
    Definition angelic o w σ                           := lift_purespec (@SPureSpec.angelic o w σ).
    Definition demonic o w σ                           := lift_purespec (@SPureSpec.demonic o w σ).
    Definition angelic_ctx N n w Δ                     := lift_purespec (@SPureSpec.angelic_ctx N n w Δ).
    Definition demonic_ctx N n w Δ                     := lift_purespec (@SPureSpec.demonic_ctx N n w Δ).

    Definition assert_pathcondition :
      ⊢ □(SHeap -> AMessage) -> PathCondition -> SHeapSpec Unit.
    Proof.
      intros w msg C Φ h.
      apply SPureSpec.assert_pathcondition; auto.
      - intros w1 θ1. apply msg. auto. apply (persist (A := SHeap) h θ1).
      - intros w1 θ1 _. apply Φ. auto. constructor. apply (persist (A := SHeap) h θ1).
    Defined.

    Definition assert_formula :
      ⊢ □(SHeap -> AMessage) -> Formula -> SHeapSpec Unit.
    Proof.
      intros w msg C Φ h.
      apply SPureSpec.assert_formula; auto.
      - intros w1 θ1. apply msg. auto. apply (persist (A := SHeap) h θ1).
      - intros w1 θ1 _. apply Φ. auto. constructor. apply (persist (A := SHeap) h θ1).
    Defined.

    Definition assume_pathcondition w C                := lift_purespec (@SPureSpec.assume_pathcondition w C).
    Definition assume_formula w fml                    := lift_purespec (@SPureSpec.assume_formula w fml).
    Definition angelic_pattern_match N n σ pat w msg t := lift_purespec (@SPureSpec.angelic_pattern_match N n σ pat w msg t).
    Definition demonic_pattern_match N n σ pat w t     := lift_purespec (@SPureSpec.demonic_pattern_match N n σ pat w t).
    Definition new_pattern_match N n σ pat w t         := lift_purespec (@SPureSpec.new_pattern_match N n σ pat w t).

    #[global] Arguments angelic o [w] σ.
    #[global] Arguments demonic o [w] σ.
    #[global] Arguments angelic_ctx [N] n [w] Δ.
    #[global] Arguments demonic_ctx [N] n [w] Δ.
    #[global] Arguments demonic_pattern_match [N] n [σ] pat [w].
    #[global] Arguments angelic_pattern_match [N] n [σ] pat [w].
    #[global] Arguments new_pattern_match [N] n [σ] pat [w].

    Section ProduceConsume.
      Import EqNotations.

      Definition get_heap : ⊢ SHeapSpec SHeap :=
        fun w0 POST h => T POST h h.
      Definition put_heap : ⊢ SHeap -> SHeapSpec Unit :=
        fun w0 h POST _ => T POST tt h.

      Definition produce_chunk :
        ⊢ Chunk -> SHeapSpec Unit :=
        fun w0 c Φ h => T Φ tt (cons (peval_chunk c) h).

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

      Definition try_consume_chunk_precise {Σ} (h : SHeap Σ) (c : Chunk Σ) :
        option (SHeap Σ * PathCondition Σ) :=
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

      Definition consume_chunk : ⊢ Chunk -> SHeapSpec Unit :=
        fun w0 c =>
          ⟨ θ1 ⟩ h <- get_heap (w := _) ;;
          let c1 := peval_chunk c⟨θ1⟩ in
          match try_consume_chunk_exact h c1 with
          | Some h' => put_heap h'
          | None =>
            match try_consume_chunk_precise h c1 with
            | Some (h', Fs) =>
                ⟨ θ2 ⟩ _ <- put_heap h' ;;
                assert_pathcondition
                  (fun w3 θ3 _ =>
                     amsg.mk
                       {| (* debug_consume_chunk_program_context := Γ; *)
                          debug_consume_chunk_pathcondition := wco w3;
                          (* debug_consume_chunk_localstore := δ1; *)
                          debug_consume_chunk_heap := persist (A := SHeap) h (θ2∘θ3) ;
                          debug_consume_chunk_chunk := c1⟨θ2∘θ3⟩;
                       |}
                  )
                  Fs⟨θ2⟩
            | None =>
              error
                (fun w2 θ2 h2 =>
                   amsg.mk
                   {| (* debug_consume_chunk_program_context := Γ; *)
                      debug_consume_chunk_pathcondition := wco _;
                      (* debug_consume_chunk_localstore := δ1; *)
                      debug_consume_chunk_heap := h2;
                      debug_consume_chunk_chunk := c1⟨θ2⟩
                   |})
              end
          end.

      Definition consume_chunk_angelic : ⊢ Chunk -> SHeapSpec Unit :=
        fun w0 c =>
          ⟨ θ1 ⟩ h <- get_heap (w := _) ;;
          let c1 := peval_chunk c⟨θ1⟩ in
          match try_consume_chunk_exact h c1 with
          | Some h' => put_heap h'
          | None =>
            match try_consume_chunk_precise h c1 with
            | Some (h', Fs) =>
                ⟨ θ2 ⟩ _ <- put_heap h' ;;
                assert_pathcondition
                  (fun w3 θ3 _ =>
                     amsg.mk
                       {| (* debug_consume_chunk_program_context := Γ; *)
                          debug_consume_chunk_pathcondition := wco w3;
                          (* debug_consume_chunk_localstore := δ1; *)
                          debug_consume_chunk_heap := persist (A := SHeap) h (θ2∘θ3) ;
                          debug_consume_chunk_chunk := c1⟨θ2∘θ3⟩;
                       |}
                  )
                  Fs⟨θ2⟩
            | None =>
                ⟨ θ2 ⟩ '(c',h') <-
                  lift_purespec
                    (SPureSpec.angelic_list
                       (A := Pair Chunk SHeap)
                       (fun w2 θ2 =>
                          amsg.mk
                            {| (* debug_consume_chunk_program_context := Γ; *)
                              debug_consume_chunk_pathcondition := wco w2;
                              (* debug_consume_chunk_localstore := δ1; *)
                              debug_consume_chunk_heap := persist (A := SHeap) h θ2 ;
                              debug_consume_chunk_chunk := c1⟨θ2⟩;
                            |})
                       (heap_extractions h)) ;;
                let c2 := c1⟨θ2⟩ in
                ⟨ θ3 ⟩ _ <-
                  lift_purespec
                    (SPureSpec.assert_eq_chunk
                       (fun w3 θ3 =>
                          amsg.mk
                            {| (* debug_consume_chunk_program_context := Γ; *)
                              debug_consume_chunk_pathcondition := wco w3;
                              (* debug_consume_chunk_localstore := δ1; *)
                              debug_consume_chunk_heap := persist (A := SHeap) h (θ2 ∘ θ3);
                              debug_consume_chunk_chunk := c2⟨θ3⟩;
                            |}
                       )
                       c2 c' acc_refl) ;;
                put_heap h'⟨θ3⟩
            end
          end.

      Definition read_register {τ} (reg : 𝑹𝑬𝑮 τ) : ⊢ SHeapSpec (WTerm τ) :=
        fun w =>
          ⟨ ω01 ⟩ t <- angelic None _ ;;
          ⟨ ω12 ⟩ _ <- consume_chunk (chunk_ptsreg reg t) ;;
          let t2 := persist__term t ω12 in
          ⟨ ω23 ⟩ _ <- produce_chunk (chunk_ptsreg reg t2) ;;
          pure (persist__term t2 ω23).
      #[global] Arguments read_register {τ} reg {w}.

      Definition write_register {τ} (reg : 𝑹𝑬𝑮 τ) : ⊢ WTerm τ -> SHeapSpec (WTerm τ) :=
        fun w tnew =>
          ⟨ ω01 ⟩ told <- angelic None _ ;;
          ⟨ ω12 ⟩ _    <- consume_chunk (chunk_ptsreg reg told) ;;
          let tnew2 := persist__term tnew (ω01 ∘ ω12) in
          ⟨ ω34 ⟩ _    <- produce_chunk (chunk_ptsreg reg tnew2) ;;
          pure (persist__term tnew2 ω34).

      Definition sproduce :
        forall {Σ} (asn : Assertion Σ), ⊢ Sub Σ -> SHeapSpec Unit :=
      fix sproduce {Σ} asn {w} ζ :=
        match asn with
        | asn.formula fml =>
            assume_formula (subst fml ζ)
        | asn.chunk c =>
            produce_chunk (subst c ζ)
        | asn.chunk_angelic c =>
            produce_chunk (subst c ζ)
        | asn.pattern_match s pat rhs =>
            ⟨ θ ⟩ '(existT pc δpc) <- demonic_pattern_match id pat (subst s ζ) ;;
            sproduce (rhs pc) (persist ζ θ ►► δpc)
        | asn.sep a1 a2 =>
            ⟨ θ ⟩ _ <- sproduce a1 ζ ;;
            sproduce a2 (persist ζ θ)
        | asn.or a1 a2 =>
            demonic_binary (sproduce a1 ζ) (sproduce a2 ζ)
        | asn.exist ς τ a =>
            ⟨ θ ⟩ t <- demonic (Some ς) τ ;;
            sproduce a (env.snoc (persist ζ θ) (ς∷τ) t)
        | asn.debug =>
            debug
              (fun w1 θ1 h1 =>
                 amsg.mk
                   {| (* debug_asn_program_context := Γ; *)
                     debug_asn_pathcondition := wco w1;
                     (* debug_asn_localstore := δ1; *)
                     debug_asn_heap := h1;
                   |})
              (pure tt)
        end.

      Definition sconsume :
        forall {Σ} (asn : Assertion Σ), ⊢ Sub Σ -> SHeapSpec Unit :=
      fix sconsume {Σ} asn {w} ζ :=
        match asn with
        | asn.formula fml =>
            assert_formula (fun _ _ _ => amsg.mk tt) (subst fml ζ)
        | asn.chunk c =>
            consume_chunk (subst c ζ)
        | asn.chunk_angelic c =>
            consume_chunk_angelic (subst c ζ)
        | asn.pattern_match s pat rhs =>
            ⟨ θ ⟩ '(existT pc δpc) <- angelic_pattern_match id pat
                                        (fun _ _ => amsg.mk tt)
                                        (subst s ζ) ;;
            sconsume (rhs pc) (persist ζ θ ►► δpc)
        | asn.sep a1 a2 =>
            ⟨ θ ⟩ _ <- sconsume a1 ζ ;;
            sconsume a2 (persist ζ θ)
        | asn.or a1 a2 =>
            angelic_binary (sconsume a1 ζ) (sconsume a2 ζ)
        | asn.exist ς τ a =>
            ⟨ θ ⟩ t <- angelic (Some ς) τ ;;
            sconsume a (env.snoc (persist ζ θ) (ς∷τ) t)
        | asn.debug =>
            debug
              (fun w1 θ1 h1 =>
                 amsg.mk
                   {| (* debug_asn_program_context := Γ; *)
                     debug_asn_pathcondition := wco w1;
                     (* debug_asn_localstore := δ1; *)
                     debug_asn_heap := h1;
                   |})
              (pure tt)
        end.

      Definition scall_contract {Δ τ} (c : SepContract Δ τ) :
        ⊢ SStore Δ -> SHeapSpec (STerm τ) :=
        fun w0 args =>
          match c with
          | MkSepContract _ _ Σe δe req result ens =>
              ⟨ θ1 ⟩ evars <- angelic_ctx id Σe ;;
              ⟨ θ2 ⟩ _     <- lift_purespec
                                (SPureSpec.assert_eq_nenv (fun _ _ => amsg.mk tt)
                                   (subst δe evars) args⟨θ1⟩) ;;
              let evars2 := persist (A := Sub _) evars θ2 in
              ⟨ θ3 ⟩ _     <- sconsume req evars2 ;;
              ⟨ θ4 ⟩ res   <- demonic (Some result) τ ;;
              let evars4 := persist (A := Sub _) evars2 (θ3 ∘ θ4) in
              ⟨ θ5 ⟩ _     <- sproduce ens (sub_snoc evars4 (result∷τ) res) ;;
              pure res⟨θ5⟩
          end.

      Definition scall_lemma {Δ} (lem : Lemma Δ) :
        ⊢ SStore Δ -> SHeapSpec Unit :=
        fun w0 args =>
          match lem with
          | MkLemma _ Σe δe req ens =>
              ⟨ θ1 ⟩ evars <- angelic_ctx id Σe ;;
              ⟨ θ2 ⟩ _     <- lift_purespec
                                (SPureSpec.assert_eq_nenv (fun _ _ => amsg.mk tt)
                                   (subst δe evars) args⟨θ1⟩) ;;
              let evars2 := persist (A := Sub _) evars θ2 in
              ⟨ θ3 ⟩ _     <- sconsume req evars2 ;;
              let evars3 := persist (A := Sub _) evars2 θ3 in
              sproduce ens evars3
          end.

    End ProduceConsume.

  End SHeapSpec.

  Section Replay.

    Import ModalNotations SPureSpec SPureSpec.notations.

    Definition reuseMsg :
      ⊢ AMessage -> □(AMessage) :=
      fun w msg w1 θ1 => persist msg θ1.

    Definition sreplay :
      forall {Σ} (s : 𝕊 Σ), ⊢ Sub Σ -> SPureSpec Unit :=
      fix replay {Σ} s {w0} δ {struct s} :=
        match s with
        | SymProp.angelic_binary o1 o2 =>
            SPureSpec.angelic_binary (replay o1 δ) (replay o2 δ)
        | SymProp.demonic_binary o1 o2 =>
            SPureSpec.demonic_binary (replay o1 δ) (replay o2 δ)
        | SymProp.block => block
        | SymProp.error msg =>
            error (reuseMsg (subst msg δ))
        | SymProp.assertk fml msg k =>
            ⟨ θ ⟩ _ <- assert_formula
                         (reuseMsg (subst msg δ))
                         (subst fml δ) ;;
            replay k (persist δ θ)
        | SymProp.assumek fml k =>
            ⟨ θ ⟩ _ <- assume_formula (subst fml δ) ;;
            replay k (persist δ θ)
        | SymProp.angelicv b k =>
            ⟨ θ ⟩ t <- angelic (Some (name b)) (type b) ;;
            replay k (env.snoc (persist δ θ) b t)
        | SymProp.demonicv b k =>
            ⟨ θ ⟩ t <- demonic (Some (name b)) (type b) ;;
            replay k (env.snoc (persist δ θ) b t)
        | SymProp.assert_vareq x t msg k =>
            let ζ    := sub_shift (b:=x∷_) _ in
            let msg  := subst msg ζ in
            let fml  := formula_relop bop.eq
                          (subst t ζ)
                          (term_var x) in
            ⟨ θ ⟩ _            <- assert_formula
                                    (reuseMsg (subst msg δ))
                                    (subst fml δ) ;;
            replay k (env.remove (x∷_) δ⟨θ⟩ _)
        | SymProp.assume_vareq x t k =>
            let ζ    := sub_shift (b:=x∷_) _ in
            let fml  := formula_relop bop.eq
                          (subst t ζ)
                          (term_var x) in
            ⟨ θ ⟩ _            <- assume_formula
                                    (subst fml δ) ;;
            replay k (env.remove (x∷_) δ⟨θ⟩ _)
        | SymProp.pattern_match s pat rhs =>
            error (fun _ _ => amsg.mk tt)
        (* FIXME *)
        (* ⟨ θ ⟩ '(existT pc δpc) <- new_pattern_match id pat (subst s δ) ;; *)
        (* replay (rhs pc) (persist δ θ ►► δpc) *)
        | SymProp.pattern_match_var x pat rhs =>
            error (fun _ _ => amsg.mk tt)
        (* FIXME *)
        (* ⟨ θ ⟩ '(existT pc δpc) <- new_pattern_match id pat (subst (term_var x) δ) ;; *)
        (* replay (rhs pc) (env.remove _ (δ⟨θ⟩ ►► δpc) _) *)
        | SymProp.debug msg k =>
            debug (reuseMsg (subst msg δ)) (replay k δ)
        end.

  End Replay.

End SymbolicMonadsOn.
