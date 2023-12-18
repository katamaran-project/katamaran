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

From Equations Require Import
  Equations.
From Katamaran Require Import
  Prelude
  Base
  Syntax.Chunks
  Syntax.Predicates
  Symbolic.Propositions
  Symbolic.Solver
  Symbolic.Worlds.

Import ctx.notations.
Import env.notations.

#[local] Set Implicit Arguments.

Module Type SymbolicMonadsOn (Import B : Base) (Import P : PredicateKit B)
  (Import W : WorldsMixin B P) (Import SK : SolverKit B P W)
  (Import SP : SymPropOn B P W) (Import GS : GenericSolverOn B P W SK).

  Import ModalNotations.
  #[local] Open Scope modal.

  #[local] Hint Extern 2 (Persistent (WTerm ?σ)) =>
    refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.
  #[local] Hint Extern 2 (Persistent (fun w : World => NamedEnv (Term (wctx w)) ?Γ)) =>
    refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.

  Definition SPureSpec (A : TYPE) : TYPE :=
    □(A -> 𝕊) -> 𝕊.

  Module SPureSpec.

    Definition run : ⊢ SPureSpec Unit -> 𝕊 :=
      fun w m => m (fun w1 θ1 _ => SymProp.block).

    Definition pure {A : TYPE} : ⊢ A -> SPureSpec A :=
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

    Definition block {A} : ⊢ SPureSpec A :=
      fun w POST => SymProp.block.
    #[global] Arguments block {A w}.
    Definition error {A} : ⊢ AMessage -> SPureSpec A :=
      fun w msg POST => SymProp.error msg.

    Definition angelic (x : option LVar) : ⊢ ∀ σ, SPureSpec (STerm σ) :=
      fun w σ k =>
        let y := fresh_lvar w x in
        SymProp.angelicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    #[global] Arguments angelic x [w] σ k : rename.

    Definition demonic (x : option LVar) : ⊢ ∀ σ, SPureSpec (STerm σ) :=
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
      ⊢ AMessage -> PathCondition -> SPureSpec Unit :=
      fun w msg C POST =>
        match combined_solver w C with
        | Some (existT w1 (ν, C1)) =>
            (* Assert variable equalities and the residual constraints *)
            SymProp.assert_triangular msg ν
              (fun msg' =>
                 SymProp.assert_pathcondition_without_solver msg' C1
                   (* Run POST in the world with the variable and residual *)
                   (* formulas included. This is a critical piece of code *)
                   (* since this is the place where we really meaningfully *)
                   (* change the world. We changed the type of *)
                   (* assume_pathcondition_without_solver just to not forget *)
                   (* adding the new path constraints. *)
                   (POST (wpathcondition w1 C1)
                      (acc_triangular ν ∘ acc_pathcondition_right w1 C1) tt))
        | None =>
            (* The new path constraints are inconsistent with the old path
               constraints. *)
            SymProp.error msg
        end.

    Definition assume_pathcondition :
      ⊢ PathCondition -> SPureSpec Unit :=
      fun w C POST =>
        match combined_solver w C with
        | Some (existT w1 (ν, C1)) =>
            (* Assume variable equalities and the residual constraints *)
            SymProp.assume_triangular ν
              (SymProp.assume_pathcondition_without_solver C1
                 (* Critical code. Like for assert_pathcondition. *)
                 (POST (wpathcondition w1 C1)
                    (acc_triangular ν ∘ acc_pathcondition_right w1 C1) tt))
        | None =>
            (* The new path constraints are inconsistent with the old path *)
            (* constraints. *)
            SymProp.block
        end.

    Definition assert_formula :
      ⊢ AMessage -> Formula -> SPureSpec Unit :=
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
      ⊢ AMessage -> WList A -> SPureSpec A :=
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
      ⊢ AMessage -> SPureSpec ⌜F⌝ :=
      fun w msg => angelic_list msg (finite.enum F).
    #[global] Arguments angelic_finite F {_ _ w}.

    Definition demonic_finite F `{finite.Finite F} :
      ⊢ SPureSpec ⌜F⌝ :=
      fun w => demonic_list (finite.enum F).
    #[global] Arguments demonic_finite F {_ _ w}.

    Section PatternMatching.

      Context {N : Set} (n : N -> LVar).

      Definition angelic_pattern_match' {σ} (pat : @Pattern N σ) :
        ⊢ AMessage -> WTerm σ -> SPureSpec (SMatchResult pat) :=
        fun w0 msg t =>
          ⟨ θ1 ⟩ pc <- angelic_finite (PatternCase pat) msg ;;
          ⟨ θ2 ⟩ ts <- angelic_ctx n (PatternCaseCtx pc) ;;
          let θ12 := θ1 ∘ θ2 in
          ⟨ θ3 ⟩ _  <- assert_formula (persist msg θ12)
                         (formula_relop bop.eq
                            (pattern_match_term_reverse pat pc ts)
                            t⟨θ12⟩);;
          pure (A := SMatchResult pat) (existT pc ts⟨θ3⟩).
      #[global] Arguments angelic_pattern_match' {σ} pat [w].

      Definition angelic_pattern_match :
        forall {σ} (pat : @Pattern N σ),
          ⊢ AMessage -> WTerm σ -> SPureSpec (SMatchResult pat) :=
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

    Definition debug {A} : ⊢ AMessage -> SPureSpec A -> SPureSpec A :=
      fun w msg m Φ => SymProp.debug msg (m Φ).

    Equations(noeqns) assert_eq_env :
      let E Δ := fun w : World => Env (Term w) Δ in
      ⊢ ∀ Δ : Ctx Ty, AMessage -> E Δ -> E Δ -> SPureSpec Unit :=
    assert_eq_env msg env.nil          env.nil            := pure tt;
    assert_eq_env msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
      ⟨ θ ⟩ _ <- assert_eq_env msg δ δ' ;;
      assert_formula (persist msg θ) (formula_relop bop.eq t t')⟨θ⟩.

    Equations(noeqns) assert_eq_nenv {N} :
      let E Δ := fun w : World => NamedEnv (Term w) Δ in
      ⊢ ∀ Δ : NCtx N Ty, AMessage -> E Δ -> E Δ -> SPureSpec Unit :=
    assert_eq_nenv msg env.nil          env.nil            := pure tt;
    assert_eq_nenv msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
      ⟨ θ ⟩ _ <- assert_eq_nenv msg δ δ' ;;
      assert_formula (persist msg θ) (formula_relop bop.eq t t')⟨θ⟩.

    Definition assert_eq_chunk : ⊢ AMessage -> Chunk -> Chunk -> □(SPureSpec Unit) :=
      fix assert_eq w0 msg c1 c2 w1 θ1 {struct c1} :=
        match c1 , c2 with
        | chunk_user p1 vs1 , chunk_user p2 vs2 =>
            match eq_dec p1 p2 with
            | left e => assert_eq_env (persist msg θ1)
                          (eq_rect p1 (fun p => Env (Term w1) (𝑯_Ty p)) vs1⟨θ1⟩ p2 e)
                          (persist (A := fun w => (fun Σ => Env (Term Σ) _) (wctx w)) vs2 θ1)
            | right _ => error msg⟨θ1⟩
            end
        | chunk_ptsreg r1 v1 , chunk_ptsreg r2 v2 =>
            match eq_dec_het r1 r2 with
            | left e => assert_formula (persist msg θ1)
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

    Definition replay_aux :
      forall {Σ} (s : 𝕊 Σ), ⊢ Sub Σ -> SPureSpec Unit :=
      fix replay {Σ} s {w0} δ {struct s} :=
        match s with
        | SymProp.angelic_binary o1 o2 =>
            SPureSpec.angelic_binary (replay o1 δ) (replay o2 δ)
        | SymProp.demonic_binary o1 o2 =>
            SPureSpec.demonic_binary (replay o1 δ) (replay o2 δ)
        | SymProp.block => block
        | SymProp.error msg =>
            error (subst msg δ)
        | SymProp.assertk fml msg k =>
            ⟨ θ ⟩ _ <- assert_formula (subst msg δ) (subst fml δ) ;;
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
            let fml  := formula_relop bop.eq (subst t ζ) (term_var x) in
            ⟨ θ ⟩ _ <- assert_formula (subst msg δ) (subst fml δ) ;;
            replay k (env.remove (x∷_) δ⟨θ⟩ _)
        | SymProp.assume_vareq x t k =>
            let ζ    := sub_shift (b:=x∷_) _ in
            let fml  := formula_relop bop.eq (subst t ζ) (term_var x) in
            ⟨ θ ⟩ _ <- assume_formula (subst fml δ) ;;
            replay k (env.remove (x∷_) δ⟨θ⟩ _)
        | SymProp.pattern_match s pat rhs =>
            error (amsg.mk tt)
        (* FIXME *)
        (* ⟨ θ ⟩ '(existT pc δpc) <- new_pattern_match id pat (subst s δ) ;; *)
        (* replay (rhs pc) (persist δ θ ►► δpc) *)
        | SymProp.pattern_match_var x pat rhs =>
            error (amsg.mk tt)
        (* FIXME *)
        (* ⟨ θ ⟩ '(existT pc δpc) <- new_pattern_match id pat (subst (term_var x) δ) ;; *)
        (* replay (rhs pc) (env.remove _ (δ⟨θ⟩ ►► δpc) _) *)
        | SymProp.debug msg k =>
            debug (subst msg δ) (replay k δ)
        end.

    Definition replay : ⊢ 𝕊 -> 𝕊 :=
      fun w P => run (replay_aux P (sub_id w)).

  End SPureSpec.
  Export (hints) SPureSpec.

End SymbolicMonadsOn.
