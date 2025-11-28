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
  Strings.String.
From Equations Require Import
  Equations.
From Katamaran Require Import
  Prelude
  Base
  Syntax.Assertions
  Syntax.Chunks
  Syntax.Predicates
  Symbolic.Propositions
  Symbolic.UnifLogic
  Symbolic.Solver
  Symbolic.Worlds.

Import ctx.notations.
Import env.notations.

#[local] Set Implicit Arguments.

Module Type SymbolicMonadsOn (Import B : Base) (Import P : PredicateKit B)
  (Import W : WorldsMixin B P)
  (Import SK : SolverKit B P W)
  (Import SP : SymPropOn B P W)
  (Import UL : UnifLogicOn B P W)
  (Import LSP : LogSymPropOn B P W SP UL)
  (Import GS : GenericSolverOn B P W SK SP UL LSP)
  (Import A : AssertionsOn B P W).

  Import ModalNotations.
  #[local] Open Scope modal.

  #[local] Hint Extern 2 (Persistent (WTerm ?σ)) =>
    refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.
  #[local] Hint Extern 2 (Persistent (fun w : World => NamedEnv (Term (wctx w)) ?Γ)) =>
    refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.

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

    Record DebugReadRegister (Σ : LCtx) : Type :=
      MkDebugReadRegister
        { debug_read_register_pathcondition : PathCondition Σ;
          debug_read_register_heap          : SHeap Σ;
          debug_read_register_type          : Ty;
          debug_read_register_register      : 𝑹𝑬𝑮 debug_read_register_type;
        }.

    #[export] Instance SubstDebugReadRegister : Subst DebugReadRegister :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugReadRegister pc h r =>
            MkDebugReadRegister (subst pc ζ01) (subst h ζ01) r
        end.

    #[export] Instance SubstLawsDebugReadRegister : SubstLaws DebugReadRegister.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance OccursCheckDebugReadRegister : OccursCheck DebugReadRegister :=
      fun Σ x xIn d =>
        match d with
        | MkDebugReadRegister pc h r =>
            pc' <- occurs_check xIn pc ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugReadRegister pc' h' r)
        end.

    Record DebugWriteRegister (Σ : LCtx) : Type :=
      MkDebugWriteRegister
        { debug_write_register_pathcondition : PathCondition Σ;
          debug_write_register_heap          : SHeap Σ;
          debug_write_register_type          : Ty;
          debug_write_register_register      : 𝑹𝑬𝑮 debug_write_register_type;
          debug_write_register_value         : Term Σ debug_write_register_type;
        }.

    #[export] Instance SubstDebugWriteRegister : Subst DebugWriteRegister :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugWriteRegister pc h r t =>
            MkDebugWriteRegister (subst pc ζ01) (subst h ζ01) r (subst t ζ01)
        end.

    #[export] Instance SubstLawsDebugWriteRegister : SubstLaws DebugWriteRegister.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance OccursCheckDebugWriteRegister : OccursCheck DebugWriteRegister :=
      fun Σ x xIn d =>
        match d with
        | MkDebugWriteRegister pc h r t =>
            pc' <- occurs_check xIn pc ;;
            h'  <- occurs_check xIn h ;;
            t'  <- occurs_check xIn t ;;
            Some (MkDebugWriteRegister pc' h' r t')
        end.

    Record DebugString (Σ : LCtx) : Type :=
      MkDebugString
        { debug_string_pathcondition : PathCondition Σ;
          debug_string_message       : string;
        }.

    #[export] Instance SubstDebugString : Subst DebugString :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugString pc s =>
            MkDebugString (subst pc ζ01) s
        end.

    #[export] Instance SubstLawsDebugString : SubstLaws DebugString.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance OccursCheckDebugString : OccursCheck DebugString :=
      fun Σ x xIn d =>
        match d with
        | MkDebugString pc s =>
            pc' <- occurs_check xIn pc ;;
            Some (MkDebugString pc' s)
        end.

    Record DebugAssertFormula (Σ : LCtx) : Type :=
      MkDebugAssertFormula
        { debug_assert_formula_pathcondition   : PathCondition Σ;
          debug_assert_formula_heap            : SHeap Σ;
          debug_assert_formula_formula         : Formula Σ;
        }.

    #[export] Instance SubstDebugAssertFormula : Subst DebugAssertFormula :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugAssertFormula pc h fml =>
          MkDebugAssertFormula (subst pc ζ01) (subst h ζ01) (subst fml ζ01)
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
        | MkDebugAssertFormula pc h fml =>
            pc' <- occurs_check xIn pc ;;
            h'  <- occurs_check xIn h ;;
            fml'  <- occurs_check xIn fml ;;
            Some (MkDebugAssertFormula pc' h' fml')
        end.

  End DebugInfo.

  Definition SPureSpec (A : TYPE) : TYPE :=
    □(A -> 𝕊) -> 𝕊.

  Module SPureSpec.

    Definition run : ⊢ SPureSpec Unit -> 𝕊 :=
      fun w m => m (fun w1 θ1 _ => SymProp.block).

    Definition pure {A : TYPE} : ⊢ A -> SPureSpec A :=
      fun w0 a Φ => T Φ a.

    Definition bind {A B} :
      ⊢ SPureSpec A -> □(A -> SPureSpec B) -> SPureSpec B :=
      fun w0 m f Φ => m (fun w1 ω01 a1 => f w1 ω01 a1 (four Φ ω01)).
    #[global] Arguments bind {A B} [w] m f _ /.

    Module Import notations.
      Notation "⟨ θ ⟩ ' x <- ma ;; mb" :=
        (bind ma (fun _ θ x => mb))
          (at level 80, x pattern,
             ma at next level, mb at level 200,
               right associativity).
      Notation "⟨ θ ⟩ x <- ma ;; mb" :=
        (bind ma (fun _ θ x => mb))
          (at level 80, x at next level,
             ma at next level, mb at level 200,
               right associativity).
      Notation "x ⟨ θ ⟩" := (persist x θ).
    End notations.

    Definition block {A} : ⊢ SPureSpec A :=
      fun w Φ => SymProp.block.
    #[global] Arguments block {A w}.
    Definition error {A} : ⊢ AMessage -> SPureSpec A :=
      fun w msg Φ => SymProp.error msg.

    Definition angelic (x : option LVar) : ⊢ ∀ σ, SPureSpec (STerm σ) :=
      fun w σ Φ =>
        let y := fresh_lvar w x in
        SymProp.angelicv
          (y∷σ) (Φ (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    #[global] Arguments angelic x [w] σ Φ : rename.

    Definition demonic (x : option LVar) : ⊢ ∀ σ, SPureSpec (STerm σ) :=
      fun w σ Φ =>
        let y := fresh_lvar w x in
        SymProp.demonicv
          (y∷σ) (Φ (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    #[global] Arguments demonic x [w] σ Φ : rename.

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

    Definition assertSecLeak {σ} :
      ⊢ AMessage -> WTerm σ -> SPureSpec Unit :=
      fun w msg t =>
        assert_formula msg (formula_secLeak t).

    Definition assumeSecLeak {σ} :
      ⊢ WTerm σ -> SPureSpec Unit :=
      fun w t => assume_formula (formula_secLeak t).

    Section PatternMatching.

      Context {N : Set} (n : N -> LVar).

      Definition angelic_pattern_match' {σ} (pat : Pattern (N:=N) σ) :
        ⊢ AMessage -> WTerm σ -> SPureSpec (SMatchResult pat) :=
        fun w0 msg t =>
          ⟨ θ ⟩ _ <- assertSecLeak msg t ;;
          ⟨ θ1 ⟩ pc <- angelic_finite (PatternCase pat) msg⟨θ⟩ ;;
          ⟨ θ2 ⟩ ts <- angelic_ctx n (PatternCaseCtx pc) ;;
          let θ12 := θ ∘ θ1 ∘ θ2 in
          ⟨ θ3 ⟩ _  <- assert_formula (persist msg θ12)
                         (formula_propeq
                            (pattern_match_term_reverse pat pc ts)
                            t⟨θ12⟩);;
          pure (A := SMatchResult pat) (existT pc ts⟨θ3⟩).
      #[global] Arguments angelic_pattern_match' {σ} pat [w].

      Definition angelic_pattern_match :
        forall {σ} (pat : Pattern (N:=N) σ),
          ⊢ AMessage -> WTerm σ -> SPureSpec (SMatchResult pat) :=
        fun σ pat => angelic_pattern_match' pat.
        (* fix angelic (σ : Ty) (pat : Pattern σ) {w0} msg {struct pat} : *)
        (*   WTerm σ w0 -> SPureSpec (SMatchResult pat) w0 := *)
        (*   match pat with *)
        (*   | pat_var x => *)
        (*       fun scr => *)
        (*         pure *)
        (*           (A := SMatchResult (pat_var x)) *)
        (*           (existT tt [env].[x∷_ ↦ scr]) *)
        (*   | pat_bool => *)
        (*       fun scr => *)
        (*         match term_get_val scr with *)
        (*         | Some v => pure (A := SMatchResult pat_bool) *)
        (*                       (existT v [env]) *)
        (*         | None => angelic_pattern_match' _ msg scr *)
        (*         end *)
        (*   (* | pat_list _ _ _ => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       angelic_pattern_match' _ msg scr *) *)
        (*   | pat_pair x y => *)
        (*       fun scr => *)
        (*         match term_get_pair scr with *)
        (*         | Some (tl, tr) => *)
        (*             pure (A := SMatchResult (pat_pair x y)) *)
        (*               (existT tt [env].[x∷_ ↦ tl].[y∷_ ↦ tr]) *)
        (*         | None => angelic_pattern_match' _ msg scr *)
        (*         end *)
        (*   (* | pat_sum _ _ _ _ => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_sum scr with *) *)
        (*   (*       | Some (inl tl) => pure (A := SMatchResult (pat_sum _ _ _ _)) *) *)
        (*   (*                            (existT true [env].[_∷_ ↦ tl]) *) *)
        (*   (*       | Some (inr tr) => pure (A := SMatchResult (pat_sum _ _ _ _)) *) *)
        (*   (*                            (existT false [env].[_∷_ ↦ tr]) *) *)
        (*   (*       | None => angelic_pattern_match' _ msg scr *) *)
        (*   (*       end *) *)
        (*   | pat_unit => *)
        (*       fun scr => *)
        (*         pure (A := SMatchResult pat_unit) (existT tt [env]) *)
        (*   (* | pat_enum E => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_val scr with *) *)
        (*   (*       | Some v => pure (A := SMatchResult (pat_enum E)) *) *)
        (*   (*                     (existT v [env]) *) *)
        (*   (*       | None => angelic_pattern_match' _ msg scr *) *)
        (*   (*       end *) *)
        (*   | pat_bvec_split _ _ _ _ => *)
        (*       fun scr => *)
        (*         angelic_pattern_match' _ msg scr *)
        (*   (* | pat_bvec_exhaustive m => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_val scr with *) *)
        (*   (*       | Some v => pure (A := SMatchResult (pat_bvec_exhaustive m)) *) *)
        (*   (*                     (existT v [env]) *) *)
        (*   (*       | None => angelic_pattern_match' _ msg scr *) *)
        (*   (*       end *) *)
        (*   (* | pat_tuple p => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_tuple scr with *) *)
        (*   (*       | Some a => pure (A := SMatchResult (pat_tuple p)) *) *)
        (*   (*                     (existT tt (tuple_pattern_match_env p a)) *) *)
        (*   (*       | None => angelic_pattern_match' (pat_tuple p) msg scr *) *)
        (*   (*       end *) *)
        (*   (* | pat_record R Δ p => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_record scr with *) *)
        (*   (*       | Some a => pure (A := SMatchResult (pat_record R Δ p)) *) *)
        (*   (*                     (existT tt (record_pattern_match_env p a)) *) *)
        (*   (*       | None => angelic_pattern_match' (pat_record R Δ p) msg scr *) *)
        (*   (*       end *) *)
        (*   (* | pat_union U p => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_union scr with *) *)
        (*   (*       | Some (existT K scr') => *) *)
        (*   (*           ⟨ θ1 ⟩ res <- angelic (unionk_ty U K) (p K) msg scr' ;; *) *)
        (*   (*           match res with *) *)
        (*   (*           | existT pc δpc => *) *)
        (*   (*               pure (A := SMatchResult (pat_union U p)) *) *)
        (*   (*                 (existT (existT K pc) δpc) *) *)
        (*   (*           end *) *)
        (*   (*       | None => angelic_pattern_match' (pat_union U p) msg scr *) *)
        (*   (*       end *) *)
        (*   end. *)
      #[global] Arguments angelic_pattern_match {σ} pat [w].

      Definition demonic_pattern_match' {σ} (pat : Pattern (N:=N) σ) :
        ⊢ WTerm σ -> SPureSpec (SMatchResult pat) :=
        fun w0 t =>
          ⟨ θ ⟩ _ <- assertSecLeak (amsg.mk
                                      {| debug_string_pathcondition := wco _;
                                        debug_string_message       :=
                                          "Pattern matched term is not secLeak";
                                      |}) t ;;
          ⟨ θ1 ⟩ pc <- demonic_finite (PatternCase pat) ;;
          ⟨ θ2 ⟩ ts <- demonic_ctx n (PatternCaseCtx pc) ;;
          let θ12 := θ ∘ θ1 ∘ θ2 in
          ⟨ θ3 ⟩ _  <- assume_formula
                         (formula_propeq
                            (pattern_match_term_reverse pat pc ts)
                            t⟨θ12⟩);;
          pure (A := SMatchResult pat) (existT pc ts⟨θ3⟩).
      #[global] Arguments demonic_pattern_match' {σ} pat [w].

      Definition demonic_pattern_match :
        forall {σ} (pat : Pattern (N:=N) σ),
          ⊢ WTerm σ -> SPureSpec (SMatchResult pat) :=
        fun σ pat => demonic_pattern_match' pat.
        (* fix demonic (σ : Ty) (pat : Pattern σ) {w0} {struct pat} : *)
        (*   WTerm σ w0 -> SPureSpec (SMatchResult pat) w0 := *)
        (*   match pat with *)
        (*   | pat_var x => *)
        (*       fun scr => *)
        (*         pure *)
        (*           (A := SMatchResult (pat_var x)) *)
        (*           (existT tt [env].[x∷_ ↦ scr]) *)
        (*   | pat_bool => *)
        (*       fun scr => *)
        (*         match term_get_val scr with *)
        (*         | Some v => pure (A := SMatchResult pat_bool) *)
        (*                       (existT v [env]) *)
        (*         | None => demonic_pattern_match' _ scr *)
        (*         end *)
        (*   (* | pat_list _ _ _ => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       demonic_pattern_match' _ scr *) *)
        (*   | pat_pair x y => *)
        (*       fun scr => *)
        (*         match term_get_pair scr with *)
        (*         | Some (tl, tr) => *)
        (*             pure (A := SMatchResult (pat_pair x y)) *)
        (*               (existT tt [env].[x∷_ ↦ tl].[y∷_ ↦ tr]) *)
        (*         | None => demonic_pattern_match' _ scr *)
        (*         end *)
        (*   (* | pat_sum _ _ _ _ => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_sum scr with *) *)
        (*   (*       | Some (inl tl) => pure (A := SMatchResult (pat_sum _ _ _ _)) *) *)
        (*   (*                            (existT true [env].[_∷_ ↦ tl]) *) *)
        (*   (*       | Some (inr tr) => pure (A := SMatchResult (pat_sum _ _ _ _)) *) *)
        (*   (*                            (existT false [env].[_∷_ ↦ tr]) *) *)
        (*   (*       | None => demonic_pattern_match' _ scr *) *)
        (*   (*       end *) *)
        (*   | pat_unit => *)
        (*       fun scr => *)
        (*         pure (A := SMatchResult pat_unit) (existT tt [env]) *)
        (*   (* | pat_enum E => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_val scr with *) *)
        (*   (*       | Some v => pure (A := SMatchResult (pat_enum E)) *) *)
        (*   (*                     (existT v [env]) *) *)
        (*   (*       | None => demonic_pattern_match' _ scr *) *)
        (*   (*       end *) *)
        (*   | pat_bvec_split _ _ _ _ => *)
        (*       fun scr => *)
        (*         demonic_pattern_match' _ scr *)
        (*   (* | pat_bvec_exhaustive m => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_val scr with *) *)
        (*   (*       | Some v => pure (A := SMatchResult (pat_bvec_exhaustive m)) *) *)
        (*   (*                     (existT v [env]) *) *)
        (*   (*       | None => demonic_pattern_match' _ scr *) *)
        (*   (*       end *) *)
        (*   (* | pat_tuple p => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_tuple scr with *) *)
        (*   (*       | Some a => pure (A := SMatchResult (pat_tuple p)) *) *)
        (*   (*                     (existT tt (tuple_pattern_match_env p a)) *) *)
        (*   (*       | None => demonic_pattern_match' (pat_tuple p) scr *) *)
        (*   (*       end *) *)
        (*   (* | pat_record R Δ p => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_record scr with *) *)
        (*   (*       | Some a => pure (A := SMatchResult (pat_record R Δ p)) *) *)
        (*   (*                     (existT tt (record_pattern_match_env p a)) *) *)
        (*   (*       | None => demonic_pattern_match' (pat_record R Δ p) scr *) *)
        (*   (*       end *) *)
        (*   (* | pat_union U p => *) *)
        (*   (*     fun scr => *) *)
        (*   (*       match term_get_union scr with *) *)
        (*   (*       | Some (existT K scr') => *) *)
        (*   (*           ⟨ θ1 ⟩ res <- demonic (unionk_ty U K) (p K) scr' ;; *) *)
        (*   (*           match res with *) *)
        (*   (*           | existT pc δpc => *) *)
        (*   (*               pure (A := SMatchResult (pat_union U p)) *) *)
        (*   (*                 (existT (existT K pc) δpc) *) *)
        (*   (*           end *) *)
        (*   (*       | None => demonic_pattern_match' (pat_union U p) scr *) *)
        (*         (* end *) *)
        (*   end. *)
      #[global] Arguments demonic_pattern_match {σ} pat [w].

      (* Definition new_pattern_match_regular {σ} (pat : Pattern (N:=N) σ) : *)
      (*   ⊢ STerm σ -> SPureSpec (SMatchResult pat) := *)
      (*   fun w0 scr POST => *)
      (*     SymProp.pattern_match scr (freshen_pattern n w0 pat) *)
      (*       (fun pc : PatternCase _ => *)
      (*          let w1 : World   := wmatch w0 scr _ pc in *)
      (*          let r1 : w0 ⊒ w1 := acc_match_right pc in *)
      (*          POST w1 r1 *)
      (*            (existT *)
      (*               (unfreshen_patterncase n w0 pat pc) *)
      (*               (unfreshen_patterncaseenv n pat pc (sub_cat_right _)))). *)
      (* #[global] Arguments new_pattern_match_regular {σ} pat [w] t. *)

      (* Definition new_pattern_match_var {σ} (x : LVar) (pat : Pattern (N:=N) σ) : *)
      (*   ⊢ ctx.In (x∷σ) -> SPureSpec (SMatchResult pat) := *)
      (*   fun w0 xIn POST => *)
      (*     let pat' := freshen_pattern n w0 pat in *)
      (*     SymProp.pattern_match_var x pat' *)
      (*       (fun pc : PatternCase _ => *)
      (*          POST (wmatchvar w0 xIn pat' pc) (acc_matchvar_right pc) *)
      (*            (existT *)
      (*               (unfreshen_patterncase n w0 pat pc) *)
      (*               (unfreshen_patterncaseenv (D := Term (wmatchvar w0 xIn pat' pc)) n pat pc (wmatchvar_patternvars pc)))). *)
      (* #[global] Arguments new_pattern_match_var [σ x] pat [w] xIn : rename. *)

      (* Definition new_pattern_match' {σ} (pat : Pattern (N:=N) σ) : *)
      (*   ⊢ STerm σ -> SPureSpec (SMatchResult pat) := *)
      (*   fun w0 scr => *)
      (*     match scr with *)
      (*     | @term_var _ x σ xIn => fun pat => new_pattern_match_var pat xIn *)
      (*     | t => fun pat => new_pattern_match_regular pat t *)
      (*     end pat. *)
      (* #[global] Arguments new_pattern_match' {σ} pat [w] t. *)

      (* Definition new_pattern_match {σ} (pat : Pattern (N:=N) σ) : *)
      (*   ⊢ WTerm σ -> SPureSpec (SMatchResult pat) := *)
      (*   fun w0 : World => *)
      (*     match pat as p in (Pattern t) *)
      (*           return (forall _ : Term (wctx w0) t, *)
      (*                      SPureSpec (@SMatchResult N t p) w0) with *)
      (*     | pat_var x       => fun scr => pure (existT tt [env].[x∷_ ↦ scr]) *)
      (*     | pat_bool        => *)
      (*         fun scr => match term_get_val scr with *)
      (*                    | Some a => pure (existT a [env]) *)
      (*                    | None => new_pattern_match' pat_bool scr *)
      (*                    end *)
      (*     (* | pat_list σ x y  => *) *)
      (*     (*     fun scr => new_pattern_match' (pat_list σ x y) scr *) *)
      (*     | pat_pair x y    => *)
      (*         fun scr => *)
      (*           match term_get_pair scr with *)
      (*           | Some (a, b) => pure (existT tt [env].[x∷_ ↦ a].[y∷_ ↦ b]) *)
      (*           | None        => new_pattern_match' (pat_pair x y) scr *)
      (*           end *)
      (*     (* | pat_sum σ τ x y => *) *)
      (*     (*     fun scr => match term_get_sum scr with *) *)
      (*     (*                | Some (inl a) => pure (existT true [env].[x∷σ ↦ a]) *) *)
      (*     (*                | Some (inr b) => pure (existT false [env].[y∷τ ↦ b]) *) *)
      (*     (*                | None => new_pattern_match' (pat_sum σ τ x y) scr *) *)
      (*     (*                end *) *)
      (*     | pat_unit        => fun _ => pure (existT tt [env]) *)
      (*     (* | pat_enum E      => *) *)
      (*     (*     fun scr => match term_get_val scr with *) *)
      (*     (*                | Some a => pure (existT a [env]) *) *)
      (*     (*                | None => new_pattern_match' (pat_enum E) scr *) *)
      (*     (*                end *) *)
      (*     | pat_bvec_split m k x y => *)
      (*         fun scr => new_pattern_match' (pat_bvec_split m k x y) scr *)
      (*     | pat_bvec_exhaustive m => *)
      (*         fun scr => *)
      (*           match term_get_val scr with *)
      (*           | Some a => pure (existT a [env]) *)
      (*           | None => new_pattern_match' (pat_bvec_exhaustive m) scr *)
      (*           end *)
      (*     (* | @pat_tuple _ σs Δ p => *) *)
      (*     (*     fun scr => *) *)
      (*     (*       match term_get_tuple scr with *) *)
      (*     (*       | Some a => pure (existT tt (tuple_pattern_match_env p a)) *) *)
      (*     (*       | None => new_pattern_match' (pat_tuple p) scr *) *)
      (*     (*       end *) *)
      (*     (* | pat_record R Δ p => *) *)
      (*     (*     fun scr => *) *)
      (*     (*       match term_get_record scr with *) *)
      (*     (*       | Some a => pure (existT tt (record_pattern_match_env p a)) *) *)
      (*     (*       | None => new_pattern_match' (pat_record R Δ p) scr *) *)
      (*     (*       end *) *)
      (*     (* | pat_union U p => *) *)
      (*     (*     fun scr => *) *)
      (*     (*       match term_get_union scr with *) *)
      (*     (*       | Some (existT K scr') => *) *)
      (*     (*           ⟨ θ1 ⟩ '(existT pc ts) <- @new_pattern_match _ (p K) _ scr' ;; *) *)
      (*     (*           pure (@existT (PatternCase (pat_union U p)) *) *)
      (*     (*                   (fun pc => NamedEnv (Term _) (PatternCaseCtx pc)) *) *)
      (*     (*                   (existT (P := fun K => PatternCase (p K)) K pc) ts) *) *)
      (*     (*       | None => new_pattern_match' (pat_union U p) scr *) *)
      (*     (*       end *) *)
      (*     end. *)
      (* #[global] Arguments new_pattern_match {σ} pat [w]. *)

    End PatternMatching.

    Definition debug {A} : ⊢ AMessage -> SPureSpec A -> SPureSpec A :=
      fun w msg m Φ => SymProp.debug msg (m Φ).

    Equations(noeqns) assert_eq_env :
      let E Δ := fun w : World => Env (Term w) Δ in
      ⊢ ∀ Δ : Ctx Ty, AMessage -> E Δ -> E Δ -> SPureSpec Unit :=
    assert_eq_env msg env.nil          env.nil            := pure tt;
    assert_eq_env msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
      ⟨ θ ⟩ _ <- assert_eq_env msg δ δ' ;;
      assert_formula (persist msg θ) (formula_propeq t t')⟨θ⟩.

    Equations(noeqns) assert_eq_nenv {N} :
      let E Δ := fun w : World => NamedEnv (Term w) Δ in
      ⊢ ∀ Δ : NCtx N Ty, AMessage -> E Δ -> E Δ -> SPureSpec Unit :=
    assert_eq_nenv msg env.nil          env.nil            := pure tt;
    assert_eq_nenv msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
      ⟨ θ ⟩ _ <- assert_eq_nenv msg δ δ' ;;
      assert_formula (persist msg θ) (formula_propeq t t')⟨θ⟩.

    Definition assert_eq_chunk : ⊢ AMessage -> Chunk -> Chunk -> □(SPureSpec Unit) :=
      fix assert_eq w0 msg c1 c2 w1 θ1 {struct c1} :=
        match c1 , c2 with
        (* | chunk_user p1 vs1 , chunk_user p2 vs2 => *)
        (*     match eq_dec p1 p2 with *)
        (*     | left e => assert_eq_env (persist msg θ1) *)
        (*                   (eq_rect p1 (fun p => Env (Term w1) (𝑯_Ty p)) vs1⟨θ1⟩ p2 e) *)
        (*                   (persist (A := fun w => (fun Σ => Env (Term Σ) _) (wctx w)) vs2 θ1) *)
        (*     | right _ => error msg⟨θ1⟩ *)
        (*     end *)
        | chunk_ptsreg r1 v1 , chunk_ptsreg r2 v2 =>
            match eq_dec_het r1 r2 with
            | left e => assert_formula (persist msg θ1)
                          (formula_propeq (eq_rect _ (Term w1) v1⟨θ1⟩ _ (f_equal projT1 e)) v2⟨θ1⟩)
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
            let fml  := formula_propeq (subst t ζ) (term_var x) in
            ⟨ θ ⟩ _ <- assert_formula (subst msg δ) (subst fml δ) ;;
            replay k (env.remove (x∷_) δ⟨θ⟩ _)
        | SymProp.assume_vareq x t k =>
            let ζ    := sub_shift (b:=x∷_) _ in
            let fml  := formula_propeq (subst t ζ) (term_var x) in
            ⟨ θ ⟩ _ <- assume_formula (subst fml δ) ;;
            replay k (env.remove (x∷_) δ⟨θ⟩ _)
        (* | SymProp.pattern_match s pat rhs => *)
        (*     (* FIXME *) *)
        (*     (* ⟨ θ ⟩ '(existT pc δpc) <- new_pattern_match id pat (subst s δ) ;; *) *)
        (*     (* replay (rhs pc) (persist δ θ ►► δpc) *) *)
        (*     error (amsg.mk *)
        (*              {| debug_string_pathcondition := wco _; *)
        (*                 debug_string_message       := *)
        (*                   "NOT IMPLEMENTED: replay_aux.pattern_match"; *)
        (*              |}) *)
        (* | SymProp.pattern_match_var x pat rhs => *)
        (*     (* FIXME *) *)
        (*     (* ⟨ θ ⟩ '(existT pc δpc) <- new_pattern_match id pat (subst (term_var x) δ) ;; *) *)
        (*     (* replay (rhs pc) (env.remove _ (δ⟨θ⟩ ►► δpc) _) *) *)
        (*     error (amsg.mk *)
        (*              {| debug_string_pathcondition := wco _; *)
        (*                 debug_string_message       := *)
        (*                   "NOT IMPLEMENTED: replay_aux.pattern_match_var"; *)
        (*              |}) *)
        | SymProp.debug msg k =>
            debug (subst msg δ) (replay k δ)
        end.

    Definition replay : ⊢ 𝕊 -> 𝕊 :=
      fun w P => run (replay_aux P (sub_id w)).

    Definition produce_chunk :
      ⊢ Chunk -> SHeap -> SPureSpec SHeap :=
      fun w0 c h => pure (cons (peval_chunk c) h).

    Definition consume_chunk : ⊢ Chunk -> SHeap -> SPureSpec SHeap :=
      fun w0 c h =>
        let c1 := peval_chunk c in
        match try_consume_chunk_exact h c1 with
        | Some h' => pure h'
        | None =>
            match try_consume_chunk_precise h c1 with
            | Some (h', Fs) =>
                ⟨ θ ⟩ _ <-
                  assert_pathcondition
                    (amsg.mk
                       {| debug_consume_chunk_pathcondition := wco _;
                          debug_consume_chunk_heap := h;
                          debug_consume_chunk_chunk := c1;
                       |})
                    Fs ;;
                pure h'⟨θ⟩
            | None =>
                error
                  (amsg.mk
                     {| debug_consume_chunk_pathcondition := wco _;
                        debug_consume_chunk_heap := h;
                        debug_consume_chunk_chunk := c1;
                     |})
            end
        end.

    Definition consume_chunk_angelic : ⊢ Chunk -> SHeap -> SPureSpec SHeap :=
      fun w0 c h =>
        let c1 := peval_chunk c in
        match try_consume_chunk_exact h c1 with
        | Some h' => pure h'
        | None =>
            match try_consume_chunk_precise h c1 with
            | Some (h', Fs) =>
                ⟨ θ ⟩ _ <-
                  assert_pathcondition
                    (amsg.mk
                       {| debug_consume_chunk_pathcondition := wco _;
                          debug_consume_chunk_heap := h;
                          debug_consume_chunk_chunk := c1;
                       |})
                    Fs ;;
                pure h'⟨θ⟩
            | None =>
                ⟨ θ2 ⟩ '(c',h') <-
                  angelic_list
                    (A := Pair Chunk SHeap)
                    (amsg.mk
                       {| debug_consume_chunk_pathcondition := wco _;
                          debug_consume_chunk_heap := h ;
                          debug_consume_chunk_chunk := c1;
                       |})
                    (heap_extractions h) ;;
                let c2 := c1⟨θ2⟩ in
                ⟨ θ3 ⟩ _ <-
                  assert_eq_chunk
                    (amsg.mk
                       {| debug_consume_chunk_pathcondition := wco _;
                          debug_consume_chunk_heap := persist (A := SHeap) h θ2;
                          debug_consume_chunk_chunk := c2;
                       |})
                    c2 c' acc_refl ;;
                pure (persist (A := SHeap) h' θ3)
            end
          end.

    Definition read_register {τ} (reg : 𝑹𝑬𝑮 τ) :
      ⊢ SHeap -> SPureSpec (Pair (STerm τ) SHeap) :=
      fun w h =>
        match find_chunk_ptsreg_precise reg h with
        | Some (t', h') => pure (t', cons (chunk_ptsreg reg t') h')
        | None => error (amsg.mk (MkDebugReadRegister (wco w) h reg))
        end.

    Definition write_register {τ} (reg : 𝑹𝑬𝑮 τ) :
      ⊢ WTerm τ -> SHeap -> SPureSpec (Pair (STerm τ) SHeap) :=
      fun w t h =>
        match find_chunk_ptsreg_precise reg h with
        | Some (_, h') => pure (t, cons (chunk_ptsreg reg t) h')
        | None => error (amsg.mk (MkDebugWriteRegister (wco w) h reg t))
        end.

  End SPureSpec.
  Export (hints) SPureSpec.

  Definition SHeapSpec (A : TYPE) : TYPE :=
    □(A -> SHeap -> 𝕊) -> SHeap -> 𝕊.

  Module SHeapSpec.

    Definition run : ⊢ SHeapSpec Unit -> 𝕊 :=
      fun w m => m (fun w1 θ1 _ h1 => SymProp.block) List.nil.

    Definition lift_purespec {A} : ⊢ SPureSpec A -> SHeapSpec A :=
      fun w0 m Φ h0 =>
        m (fun w1 ω01 a1 => Φ w1 ω01 a1 (persist h0 ω01)).

    Definition pure {A} : ⊢ A -> SHeapSpec A :=
      fun w a Φ h => T Φ a h.

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

    Definition error {A} : ⊢ (SHeap -> AMessage) -> SHeapSpec A :=
      fun w msg Φ h => SymProp.error (msg h).

    Definition angelic (x : option LVar) : ⊢ ∀ σ, SHeapSpec (STerm σ) :=
      fun w σ => lift_purespec (SPureSpec.angelic x σ).
    #[global] Arguments angelic x [w] σ Φ : rename.
    Definition demonic (x : option LVar) : ⊢ ∀ σ, SHeapSpec (STerm σ) :=
      fun w σ => lift_purespec (SPureSpec.demonic x σ).
    #[global] Arguments demonic x [w] σ Φ : rename.

    Definition angelic_ctx {N : Set} (n : N -> LVar) :
      ⊢ ∀ Δ : NCtx N Ty, SHeapSpec (fun w => NamedEnv (Term w) Δ) :=
    fun w Δ => lift_purespec (SPureSpec.angelic_ctx n Δ).
    #[global] Arguments angelic_ctx {N} n [w] Δ : rename.

    Definition demonic_ctx {N : Set} (n : N -> LVar) :
      ⊢ ∀ Δ : NCtx N Ty, SHeapSpec (fun w => NamedEnv (Term w) Δ) :=
    fun w Δ => lift_purespec (SPureSpec.demonic_ctx n Δ).
    #[global] Arguments demonic_ctx {N} n [w] Δ : rename.

    Definition angelic_binary {A} : ⊢ SHeapSpec A -> SHeapSpec A -> SHeapSpec A :=
      fun w m1 m2 Φ h =>
        SymProp.angelic_binary (m1 Φ h) (m2 Φ h).
    Definition demonic_binary {A} : ⊢ SHeapSpec A -> SHeapSpec A -> SHeapSpec A :=
      fun w m1 m2 Φ h =>
        SymProp.demonic_binary (m1 Φ h) (m2 Φ h).

    Definition debug {A} : ⊢ (SHeap -> AMessage) -> SHeapSpec A -> SHeapSpec A :=
      fun w msg m Φ h => SymProp.debug (msg h) (m Φ h).

    Definition assert_formula :
      ⊢ (SHeap -> AMessage) -> Formula -> SHeapSpec Unit :=
      fun w msg C Φ h =>
        SPureSpec.assert_formula (msg h) C
          (fun w1 θ1 x => Φ w1 θ1 x h⟨θ1⟩).
    Definition assume_formula :
      ⊢ Formula -> SHeapSpec Unit :=
      fun w fml => lift_purespec (@SPureSpec.assume_formula w fml).

    Definition produce_chunk : ⊢ Chunk -> SHeapSpec Unit :=
      fun w0 c Φ h => SPureSpec.produce_chunk c h
                        (fun w1 θ1 => Φ w1 θ1 tt).
    Definition consume_chunk : ⊢ Chunk -> SHeapSpec Unit :=
      fun w0 c Φ h => SPureSpec.consume_chunk c h
                        (fun w1 θ1 => Φ w1 θ1 tt).
    Definition consume_chunk_angelic : ⊢ Chunk -> SHeapSpec Unit :=
      fun w0 c Φ h => SPureSpec.consume_chunk_angelic c h
                        (fun w1 θ1 => Φ w1 θ1 tt).

    Definition read_register {τ} (reg : 𝑹𝑬𝑮 τ) : ⊢ SHeapSpec (WTerm τ) :=
      fun w0 Φ h => SPureSpec.read_register reg h
                      (fun w1 θ1 '(t,h') => Φ w1 θ1 t h').
    #[global] Arguments read_register {τ} reg {w}.

    Definition write_register {τ} (reg : 𝑹𝑬𝑮 τ) :
      ⊢ WTerm τ -> SHeapSpec (WTerm τ) :=
      fun w0 t Φ h => SPureSpec.write_register reg t h
                        (fun w1 θ1 '(t',h') => Φ w1 θ1 t' h').

    Definition produce :
      forall {Σ} (asn : Assertion Σ), ⊢ Sub Σ -> SHeapSpec Unit :=
    fix produce {Σ} asn {w} ζ :=
      match asn with
      | asn.formula fml =>
          assume_formula (subst fml ζ)
      | asn.chunk c =>
          produce_chunk (subst c ζ)
      | asn.chunk_angelic c =>
          produce_chunk (subst c ζ)
      | asn.pattern_match s pat rhs =>
          ⟨ θ ⟩ '(existT pc δpc) <-
            lift_purespec
              (SPureSpec.demonic_pattern_match id pat (subst s ζ)) ;;
          produce (rhs pc) (persist ζ θ ►► δpc)
      | asn.sep a1 a2 =>
          ⟨ θ ⟩ _ <- produce a1 ζ ;;
          produce a2 (persist ζ θ)
      | asn.or a1 a2 =>
          demonic_binary (produce a1 ζ) (produce a2 ζ)
      | asn.exist ς τ a =>
          ⟨ θ ⟩ t <- demonic (Some ς) τ ;;
          produce a (env.snoc (persist ζ θ) (ς∷τ) t)
      | asn.debug =>
          debug
            (fun h1 =>
               amsg.mk
                 {| debug_asn_pathcondition := wco _;
                    debug_asn_heap := h1;
                 |})
            (pure tt)
      end.

    Definition consume :
      forall {Σ} (asn : Assertion Σ), ⊢ Sub Σ -> SHeapSpec Unit :=
    fix consume {Σ} asn {w} ζ :=
      match asn with
      | asn.formula fml =>
          let fml := subst fml ζ in
          assert_formula
            (fun h =>
               amsg.mk
                 {| debug_assert_formula_pathcondition := wco _;
                    debug_assert_formula_heap          := h;
                    debug_assert_formula_formula       := fml;
                 |})
            fml
      | asn.chunk c =>
          consume_chunk (subst c ζ)
      | asn.chunk_angelic c =>
          consume_chunk_angelic (subst c ζ)
      | asn.pattern_match s pat rhs =>
          ⟨ θ ⟩ '(existT pc δpc) <-
            lift_purespec
              (SPureSpec.angelic_pattern_match id pat
                 (amsg.mk
                    {| debug_string_pathcondition := wco _;
                       debug_string_message       :=
                        "SHeapSpec.consume.pattern_match";
                    |})
                 (subst s ζ)) ;;
          consume (rhs pc) (persist ζ θ ►► δpc)
      | asn.sep a1 a2 =>
          ⟨ θ ⟩ _ <- consume a1 ζ ;;
          consume a2 (persist ζ θ)
      | asn.or a1 a2 =>
          angelic_binary (consume a1 ζ) (consume a2 ζ)
      | asn.exist ς τ a =>
          ⟨ θ ⟩ t <- angelic (Some ς) τ ;;
          consume a (env.snoc (persist ζ θ) (ς∷τ) t)
      | asn.debug =>
          debug
            (fun h1 =>
               amsg.mk
                 {| debug_asn_pathcondition := wco _;
                    debug_asn_heap := h1;
                 |})
            (pure tt)
      end.

    Definition call_contract {Δ τ} (c : SepContract Δ τ) :
      ⊢ SStore Δ -> SHeapSpec (STerm τ) :=
      fun w0 args =>
        match c with
        | MkSepContract _ _ Σe δe req result ens =>
            ⟨ θ1 ⟩ evars <-
              lift_purespec (SPureSpec.angelic_ctx id Σe) ;;
            ⟨ θ2 ⟩ _     <-
              lift_purespec
                (SPureSpec.assert_eq_nenv
                   (amsg.mk
                      {| debug_string_pathcondition := wco _;
                         debug_string_message       := "SHeapSpec.call_contract";
                      |})
                   (subst δe evars) args⟨θ1⟩) ;;
            let evars2 := persist (A := Sub _) evars θ2 in
            ⟨ θ3 ⟩ _     <- consume req evars2 ;;
            ⟨ θ4 ⟩ res   <- demonic (Some result) τ ;;
            let evars4 := persist (A := Sub _) evars2 (θ3 ∘ θ4) in
            ⟨ θ5 ⟩ _     <- produce ens (sub_snoc evars4 (result∷τ) res) ;;
            pure res⟨θ5⟩
        end.

    Definition call_lemma {Δ} (lem : Lemma Δ) :
      ⊢ SStore Δ -> SHeapSpec Unit :=
      fun w0 args =>
        match lem with
        | MkLemma _ Σe δe req ens =>
            ⟨ θ1 ⟩ evars <-
              lift_purespec (SPureSpec.angelic_ctx id Σe) ;;
            ⟨ θ2 ⟩ _     <-
              lift_purespec
                (SPureSpec.assert_eq_nenv
                   (amsg.mk
                      {| debug_string_pathcondition := wco _;
                         debug_string_message       := "SHeapSpec.call_lemma";
                      |})
                   (subst δe evars) args⟨θ1⟩) ;;
            let evars2 := persist (A := Sub _) evars θ2 in
            ⟨ θ3 ⟩ _     <- consume req evars2 ;;
            let evars3 := persist (A := Sub _) evars2 θ3 in
            produce ens evars3
        end.

  End SHeapSpec.

End SymbolicMonadsOn.
