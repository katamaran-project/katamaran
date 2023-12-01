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
     Classes.Morphisms.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Signature
     Base.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type SymbolicMonadInstancesOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import SOLV : SolverKit B SIG).

  Import ModalNotations.
  Import Postprocessing.

  Local Open Scope modal.

  Local Hint Extern 2 (Persistent (WTerm ?σ)) =>
          refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.
  Local Hint Extern 2 (Persistent (fun w : World => NamedEnv (Term (wctx w)) ?Γ)) =>
          refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.
  Local Hint Extern 2 (Persistent (fun w : World => @Env _ (fun xt => Term (wctx w) (type  xt)) ?Γ)) =>
          refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.


  Section DebugInfo.

    Import option.notations.

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

  Definition symprop_assert_pathcondition :
      ⊢ AMessage -> PathCondition -> □SymProp -> SymProp :=
      fun w0 msg C0 POST =>
        match solver _ C0 with
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
      match solver _ C0 with
      | Some (existT w1 (ν , C1)) =>
          (* Assume variable equalities and the residual constraints *)
          SymProp.assume_triangular ν
            (SymProp.assume_pathcondition_without_solver C1
               (* Run POST in the world with the variable and residual formulas *)
(*                   included. This is a critical piece of code since this is the *)
(*                   place where we really meaningfully change the world. We *)
(*                   changed the type of assume_pathcondition_without_solver just *)
(*                   to not forget adding the new path constraints. *)
               (four POST (acc_triangular ν) (acc_pathcondition_right w1 C1)))
      | None =>
          (* The new path constraints are inconsistent with the old path *)
(*              constraints. *)
          SymProp.block
      end.

  Definition SPureSpec (A : TYPE) : TYPE :=
    □(A -> 𝕊) -> 𝕊.

  Module SPureSpec.

    Import SPureSpecM.

    Definition pure {A : TYPE} :
      ⊢ A -> SPureSpec A :=
      fun w0 a POST => T POST a.

    Definition bind {A B} :
      ⊢ SPureSpec A -> □(A -> SPureSpec B) -> SPureSpec B :=
      fun w0 m f POST => m (fun w1 ω01 a1 => f w1 ω01 a1 (four POST ω01)).
    #[global] Arguments bind {A B} [w] m f _ /.

    #[local] Notation "⟨ ω ⟩ ' x <- ma ;; mb" :=
      (bind ma (fun _ ω x => mb))
        (at level 80, x pattern,
          ma at next level, mb at level 200,
          right associativity).
    #[local] Notation "⟨ ω ⟩ x <- ma ;; mb" :=
      (bind ma (fun _ ω x => mb))
        (at level 80, x at next level,
          ma at next level, mb at level 200,
          right associativity).
    #[local] Notation "x ⟨ ω ⟩" := (persist x ω).

    Definition error {A} :
      ⊢ □(SHeap -> AMessage) -> SPureSpec A := fun w msg POST => SymProp.error (T msg nil).
    Definition block {A} : ⊢ SPureSpec A :=
      fun w POST => SymProp.block.
    #[global] Arguments block {A w}.

    Definition angelic (x : option LVar) :
      ⊢ ∀ σ, SPureSpec (STerm σ) :=
      fun w σ k =>
        let y := fresh_lvar w x in
        SymProp.angelicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    Global Arguments angelic x [w] σ k : rename.

    Definition demonic (x : option LVar) :
      ⊢ ∀ σ, SPureSpec (STerm σ) :=
      fun w σ k =>
        let y := fresh_lvar w x in
        SymProp.demonicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    Global Arguments demonic x [w] σ k : rename.

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
      ⊢ □(SHeap -> AMessage) -> PathCondition -> SPureSpec Unit :=
      fun w msg C POST =>
        symprop_assert_pathcondition (msg _ acc_refl nil) C (POST <*> (fun w r => tt)).

    Definition assume_pathcondition :
      ⊢ PathCondition -> SPureSpec Unit :=
      fun w C POST =>
        symprop_assume_pathcondition C (POST <*> (fun w r => tt)).

    Definition assume_formula :
      ⊢ Formula -> SPureSpec Unit :=
      fun w F => assume_pathcondition ([ctx] ▻ F).

    Definition assert_formula :
      ⊢ □(SHeap -> AMessage) -> Formula -> SPureSpec Unit :=
      fun w0 msg fml0 =>
        assert_pathcondition msg (ctx.nil ▻ fml0 ).

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
      ⊢ □(SHeap -> AMessage) -> WList A -> SPureSpec A :=
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
      ⊢ □(SHeap -> AMessage) -> SPureSpec ⌜F⌝ :=
      fun w msg => angelic_list msg (finite.enum F).
    #[global] Arguments angelic_finite F {_ _ w}.

    Definition demonic_finite F `{finite.Finite F} :
      ⊢ SPureSpec ⌜F⌝ :=
      fun w => demonic_list (finite.enum F).
    #[global] Arguments demonic_finite F {_ _ w}.

    Section PatternMatching.

      Context {N : Set} (n : N -> LVar).

      Definition angelic_pattern_match' {σ} (pat : @Pattern N σ) :
        ⊢ □(SHeap -> AMessage) -> WTerm σ -> SPureSpec (SMatchResult pat) :=
        fun w0 msg t =>
          ⟨ θ1 ⟩ pc <- angelic_finite (PatternCase pat) msg ;;
          ⟨ θ2 ⟩ ts <- angelic_ctx n (PatternCaseCtx pc) ;;
          let θ12 := θ1 ∘ θ2 in
          ⟨ θ3 ⟩ _  <- assert_formula (four msg θ12)
                         (formula_relop bop.eq
                            (pattern_match_term_reverse pat pc ts)
                            t⟨θ12⟩);;
          pure (A := SMatchResult pat) (existT pc ts⟨θ3⟩).
      #[global] Arguments angelic_pattern_match' {σ} _ [w].

      Definition angelic_pattern_match :
        forall {σ} (pat : @Pattern N σ),
          ⊢ □(SHeap -> AMessage) -> WTerm σ -> SPureSpec (SMatchResult pat) :=
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
      #[global] Arguments demonic_pattern_match' {σ} _ [w].

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

      Definition new_pattern_match_var {σ} (pat : @Pattern N σ) :
        ⊢ ∀ x, ctx.In (x∷σ) -> SPureSpec (SMatchResult pat) :=
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
      #[global] Arguments new_pattern_match_var {σ} pat [w x] xIn : rename.

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

    Definition debug {A} : ⊢ □(SHeap -> AMessage) -> SPureSpec A -> SPureSpec A :=
      fun w msg m Φ => SymProp.debug (T msg nil) (m Φ).

    #[export] Instance purespecm : SPureSpecM SPureSpec :=
      {| SPureSpecM.pure                           := @pure;
         SPureSpecM.bind                           := @bind;
         SPureSpecM.error                          := @error;
         SPureSpecM.block                          := @block;
         SPureSpecM.angelic                        := @angelic;
         SPureSpecM.demonic                        := @demonic;
         SPureSpecM.angelic_ctx                    := @angelic_ctx;
         SPureSpecM.demonic_ctx                    := @demonic_ctx;
         SPureSpecM.assert_pathcondition           := @assert_pathcondition;
         SPureSpecM.assert_formula                 := @assert_formula;
         SPureSpecM.assume_pathcondition           := @assume_pathcondition;
         SPureSpecM.assume_formula                 := @assume_formula;
         SPureSpecM.angelic_binary                 := @angelic_binary;
         SPureSpecM.demonic_binary                 := @demonic_binary;
         SPureSpecM.angelic_pattern_match          := @angelic_pattern_match;
         SPureSpecM.demonic_pattern_match          := @demonic_pattern_match;
         SPureSpecM.new_pattern_match              := @new_pattern_match;
         SPureSpecM.debug                          := @debug;
      |}.

  End SPureSpec.
  Export (hints) SPureSpec.

  Definition SHeapSpec (A : TYPE) : TYPE :=
    □(A -> SHeap -> 𝕊) -> SHeap -> 𝕊.
  Bind Scope mut_scope with SHeapSpec.

  (* Local Hint Extern 2 (Persistent (WTerm ?σ)) => *)
  (*   refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances. *)

  Module SHeapSpec.

    Import SPureSpecM SHeapSpecM.

    Definition run : ⊢ SHeapSpec Unit -> 𝕊 :=
      fun w m => m (fun w1 θ1 _ h1 => SymProp.block) List.nil.

    Definition lift_purespec {A : TYPE} :
      ⊢ SPureSpec A -> SHeapSpec A :=
      fun w0 m POST h0 =>
        m (fun w1 ω01 a1 => POST w1 ω01 a1 (persist h0 ω01)).

    Definition bind {A B} :  ⊢ SHeapSpec A -> □(A -> SHeapSpec B) -> SHeapSpec B :=
      fun w m f Φ => m (fun w1 θ1 a1 => f w1 θ1 a1 (four Φ θ1)).

    Definition angelic_binary {A} : ⊢ SHeapSpec A -> SHeapSpec A -> SHeapSpec A :=
      fun w m1 m2 Φ h =>
        SymProp.angelic_binary (m1 Φ h) (m2 Φ h).

    Definition demonic_binary {A} : ⊢ SHeapSpec A -> SHeapSpec A -> SHeapSpec A :=
      fun w m1 m2 Φ h =>
        SymProp.demonic_binary (m1 Φ h) (m2 Φ h).

    Definition debug {A} : ⊢ □(SHeap -> AMessage) -> SHeapSpec A -> SHeapSpec A :=
      fun w msg m Φ h => SymProp.debug (T msg h) (m Φ h).

    #[export] Instance purespecm : SPureSpecM SHeapSpec :=
      {| SPureSpecM.pure  A w a                             := lift_purespec (SPureSpecM.pure a);
         SPureSpecM.bind                                    := @bind;
         SPureSpecM.error A w msg                           := lift_purespec (SPureSpecM.error msg);
         SPureSpecM.block A w                               := lift_purespec SPureSpecM.block;
         SPureSpecM.angelic o w σ                           := lift_purespec (SPureSpecM.angelic o σ);
         SPureSpecM.demonic o w σ                           := lift_purespec (SPureSpecM.demonic o σ);
         SPureSpecM.angelic_ctx N n w Δ                     := lift_purespec (SPureSpecM.angelic_ctx n Δ);
         SPureSpecM.demonic_ctx N n w Δ                     := lift_purespec (SPureSpecM.demonic_ctx n Δ);
         SPureSpecM.assert_pathcondition w msg C            := lift_purespec (SPureSpecM.assert_pathcondition msg C);
         SPureSpecM.assert_formula w msg fml                := lift_purespec (SPureSpecM.assert_formula msg fml);
         SPureSpecM.assume_pathcondition w C                := lift_purespec (SPureSpecM.assume_pathcondition C);
         SPureSpecM.assume_formula w fml                    := lift_purespec (SPureSpecM.assume_formula fml);
         SPureSpecM.angelic_binary                          := @angelic_binary;
         SPureSpecM.demonic_binary                          := @demonic_binary;
         SPureSpecM.angelic_pattern_match N n σ pat w msg t := lift_purespec (SPureSpecM.angelic_pattern_match n pat msg t);
         SPureSpecM.demonic_pattern_match N n σ pat w t     := lift_purespec (SPureSpecM.demonic_pattern_match n pat t);
         SPureSpecM.new_pattern_match N n σ p w t           := lift_purespec (SPureSpecM.new_pattern_match n p t);
         SPureSpecM.debug                                   := @debug;
      |}.

    Section ProduceConsume.
      Import EqNotations.
      Import SPureSpecM.notations.

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
                  (fun w3 θ3 h3 =>
                     amsg.mk
                       {| (* debug_consume_chunk_program_context := Γ; *)
                          debug_consume_chunk_pathcondition := wco w3;
                          (* debug_consume_chunk_localstore := δ1; *)
                          debug_consume_chunk_heap := h3;
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
                  (fun w3 θ3 h3 =>
                     amsg.mk
                       {| (* debug_consume_chunk_program_context := Γ; *)
                          debug_consume_chunk_pathcondition := wco w3;
                          (* debug_consume_chunk_localstore := δ1; *)
                          debug_consume_chunk_heap := h3;
                          debug_consume_chunk_chunk := c1⟨θ2∘θ3⟩;
                       |}
                  )
                  Fs⟨θ2⟩
            | None =>
                ⟨ θ2 ⟩ '(c',h') <-
                  lift_purespec
                    (SPureSpec.angelic_list
                       (A := Pair Chunk SHeap)
                       (fun w2 θ2 h2 =>
                          amsg.mk
                            {| (* debug_consume_chunk_program_context := Γ; *)
                              debug_consume_chunk_pathcondition := wco w2;
                              (* debug_consume_chunk_localstore := δ1; *)
                              debug_consume_chunk_heap := h2;
                              debug_consume_chunk_chunk := c1⟨θ2⟩;
                            |})
                       (heap_extractions h)) ;;
                let c2 := c1⟨θ2⟩ in
                ⟨ θ3 ⟩ _ <-
                  lift_purespec
                    (assert_eq_chunk
                       (fun w3 θ3 h3 =>
                          amsg.mk
                            {| (* debug_consume_chunk_program_context := Γ; *)
                              debug_consume_chunk_pathcondition := wco w3;
                              (* debug_consume_chunk_localstore := δ1; *)
                              debug_consume_chunk_heap := h3;
                              debug_consume_chunk_chunk := c2⟨θ3⟩;
                            |}
                       )
                       c2 c' acc_refl) ;;
                put_heap h'⟨θ3⟩
            end
          end.

      #[export] Instance heapspecm : SHeapSpecM SHeapSpec :=
        {| SHeapSpecM.produce_chunk := produce_chunk;
           SHeapSpecM.consume_chunk := consume_chunk;
           SHeapSpecM.consume_chunk_angelic := consume_chunk_angelic
        |}.

    End ProduceConsume.

  End SHeapSpec.
  Export (hints) SHeapSpec.

End SymbolicMonadInstancesOn.
