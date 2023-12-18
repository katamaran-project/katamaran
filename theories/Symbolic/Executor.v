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
     Bitvector
     Signature
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
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG).

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

  Section Configuration.

    Record Config : Type :=
      MkConfig
        { config_debug_function : forall Δ τ, 𝑭 Δ τ -> bool;
        }.

    Definition default_config : Config :=
      {| config_debug_function _ _ f := false;
      |}.

  End Configuration.

  Definition SStoreSpec (Γ1 Γ2 : PCtx) (A : TYPE) : TYPE :=
    □(A -> SStore Γ2 -> SHeap -> 𝕊) -> SStore Γ1 -> SHeap -> 𝕊.
  Bind Scope mut_scope with SStoreSpec.

  Module SStoreSpec.

    Local Hint Extern 2 (Persistent (WTerm ?σ)) =>
      refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.

    Section Basic.

      Definition lift_purem {Γ} {A : TYPE} :
        ⊢ SPureSpec A -> SStoreSpec Γ Γ A :=
        fun w0 m POST δ0 h0 =>
          m (fun w1 ω01 a1 => POST w1 ω01 a1 (persist δ0 ω01) (persist h0 ω01)).

      Definition pure {Γ} {A : TYPE} :
        ⊢ A -> SStoreSpec Γ Γ A := fun _ a k => T k a.

      Definition bind {Γ1 Γ2 Γ3 A B} :
        ⊢ SStoreSpec Γ1 Γ2 A -> □(A -> SStoreSpec Γ2 Γ3 B) -> SStoreSpec Γ1 Γ3 B :=
        fun w0 ma f k => ma (fun w1 ω01 a1 => f w1 ω01 a1 (four k ω01)).

      Definition bind_box {Γ1 Γ2 Γ3 A B} :
        ⊢ □(SStoreSpec Γ1 Γ2 A) -> □(A -> SStoreSpec Γ2 Γ3 B) -> □(SStoreSpec Γ1 Γ3 B) :=
        fun w0 m f => bind <$> m <*> four f.

      Definition error {Γ1 Γ2 A} :
        ⊢ (SStore Γ1 -> SHeap -> AMessage) -> SStoreSpec Γ1 Γ2 A :=
        fun w msg _ δ h => SymProp.error (msg δ h).

      Definition block {Γ1 Γ2 A} :
        ⊢ SStoreSpec Γ1 Γ2 A := fun _ POST δ h => block.

      Definition angelic_binary {Γ1 Γ2 A} :
        ⊢ SStoreSpec Γ1 Γ2 A -> SStoreSpec Γ1 Γ2 A -> SStoreSpec Γ1 Γ2 A :=
        fun w m1 m2 POST δ1 h1 =>
          angelic_binary (m1 POST δ1 h1) (m2 POST δ1 h1).
      Definition demonic_binary {Γ1 Γ2 A} :
        ⊢ SStoreSpec Γ1 Γ2 A -> SStoreSpec Γ1 Γ2 A -> SStoreSpec Γ1 Γ2 A :=
        fun w m1 m2 POST δ1 h1 =>
          demonic_binary (m1 POST δ1 h1) (m2 POST δ1 h1).

      Definition angelic_list {A Γ} :
        ⊢ (SStore Γ -> SHeap -> AMessage) -> WList A -> SStoreSpec Γ Γ A :=
        fun w msg xs POST δ h => lift_purem (SPureSpec.angelic_list (msg δ h) xs) POST δ h.

      Definition angelic_finite F `{finite.Finite F} {Γ} :
        ⊢ (SStore Γ -> SHeap -> AMessage) -> SStoreSpec Γ Γ ⌜F⌝ :=
        fun w msg POST δ h => lift_purem (SPureSpec.angelic_finite F (msg δ h)) POST δ h.
      #[global] Arguments angelic_finite F {_ _ Γ w}.

      Definition angelic {Γ} (x : option LVar) :
        ⊢ ∀ σ, SStoreSpec Γ Γ (STerm σ) :=
        fun w σ => lift_purem (SPureSpec.angelic x σ).
      Global Arguments angelic {Γ} x [w] σ : rename.

      Definition demonic {Γ} (x : option LVar) :
        ⊢ ∀ σ, SStoreSpec Γ Γ (STerm σ) :=
        fun w σ => lift_purem (SPureSpec.demonic x σ).
      Global Arguments demonic {Γ} x [w] σ : rename.

      Definition debug {AT} {Γ1 Γ2} :
        ⊢ (SStore Γ1 -> SHeap -> AMessage) -> (SStoreSpec Γ1 Γ2 AT) -> (SStoreSpec Γ1 Γ2 AT) :=
        fun _ d m POST δ h => SymProp.debug (d δ h) (m POST δ h).

      Definition angelic_ctx {N : Set} (n : N -> LVar) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SStoreSpec Γ Γ (fun w => NamedEnv (Term w) Δ) :=
        fun w Δ => lift_purem (SPureSpec.angelic_ctx n Δ).
      Global Arguments angelic_ctx {N} n {Γ} [w] Δ : rename.

      Definition demonic_ctx {N : Set} (n : N -> LVar) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SStoreSpec Γ Γ (fun w => NamedEnv (Term w) Δ) :=
        fun w Δ => lift_purem (SPureSpec.demonic_ctx n Δ).
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
        ⊢ Formula -> SStoreSpec Γ Γ Unit :=
        fun w0 fml => lift_purem (SPureSpec.assume_formula fml).

      Definition box_assume_formula {Γ} :
        ⊢ Formula -> □(SStoreSpec Γ Γ Unit) :=
        fun w0 fml => assume_formula <$> persist fml.

      Definition assert_formula {Γ} :
        ⊢ Formula -> SStoreSpec Γ Γ Unit :=
        fun w0 fml POST δ0 h0 =>
          lift_purem
            (SPureSpec.assert_formula
               (amsg.mk (MkDebugAssertFormula (wco w0) δ0 h0 fml)) fml)
            POST δ0 h0.

      Definition box_assert_formula {Γ} :
        ⊢ Formula -> □(SStoreSpec Γ Γ Unit) :=
        fun w0 fml => assert_formula <$> persist fml.

      Definition assert_pathcondition {Γ} :
        ⊢ PathCondition -> SStoreSpec Γ Γ Unit :=
        fun w0 fmls POST δ0 h0 =>
          lift_purem
            (SPureSpec.assert_pathcondition
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
        ⊢ E -> E -> SStoreSpec Γ Γ Unit :=
        fun w0 E1 E2 POST δ0 h0 =>
          lift_purem
            (SPureSpec.assert_eq_env
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
        ⊢ E -> E -> SStoreSpec Γ Γ Unit :=
        fun w0 E1 E2 POST δ0 h0 =>
          lift_purem
            (SPureSpec.assert_eq_nenv
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
        ⊢ Chunk -> Chunk -> SStoreSpec Γ Γ Unit :=
        fun w0 c1 c2 POST δ0 h0 =>
          lift_purem
            (T (SPureSpec.assert_eq_chunk
                  (amsg.mk
                     {| msg_function := "SStoreSpec.assert_eq_chunk";
                        msg_message := "Proof obligation";
                        msg_program_context := Γ;
                        msg_localstore := δ0;
                        msg_heap := h0;
                        msg_pathcondition := wco w0
                     |}) c1 c2))
         POST δ0 h0.

    End AssumeAssert.

    Section PatternMatching.

      Definition angelic_pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : @Pattern N σ) :
        ⊢ STerm σ -> SStoreSpec Γ Γ (SMatchResult pat) :=
        fun w0 t Φ δ h =>
          SPureSpec.angelic_pattern_match n pat
            (amsg.mk
               {| msg_function := "SStoreSpec.angelic_pattern_match";
                 msg_message := "pattern match assertion";
                 msg_program_context := Γ;
                 msg_localstore := δ;
                 msg_heap := h;
                 msg_pathcondition := wco w0
               |}) t
            (fun w1 θ1 mr => Φ w1 θ1 mr δ⟨θ1⟩ h⟨θ1⟩).
      #[global] Arguments angelic_pattern_match {N} n {Γ σ} pat [w].

      Definition demonic_pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : @Pattern N σ) :
        ⊢ STerm σ -> SStoreSpec Γ Γ (SMatchResult pat) :=
        fun w0 t Φ δ h =>
          SPureSpec.demonic_pattern_match n pat t
            (fun w1 θ1 mr => Φ w1 θ1 mr δ⟨θ1⟩ h⟨θ1⟩).
      #[global] Arguments demonic_pattern_match {N} n {Γ σ} pat [w].

      Definition pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : @Pattern N σ) :
        ⊢ WTerm σ -> SStoreSpec Γ Γ (SMatchResult pat) :=
        fun w t => lift_purem (SPureSpec.new_pattern_match n pat t).
      #[global] Arguments pattern_match {N} n {Γ σ} pat [w].

    End PatternMatching.

    Section State.

      Definition pushpop {AT Γ1 Γ2 x σ} :
        ⊢ STerm σ -> SStoreSpec (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) AT -> SStoreSpec Γ1 Γ2 AT :=
        fun w0 t m POST δ h =>
          m (fun w1 ω01 a1 δ1 => POST w1 ω01 a1 (env.tail δ1)) δ.[x∷σ↦t] h.

      Definition pushspops {AT Γ1 Γ2 Δ} :
        ⊢ SStore Δ -> SStoreSpec (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT -> SStoreSpec Γ1 Γ2 AT :=
        fun w0 δΔ m POST δ h =>
          m (fun w1 ω01 a1 δ1 => POST w1 ω01 a1 (env.drop Δ δ1)) (δ ►► δΔ) h.

      Definition get_local {Γ} : ⊢ SStoreSpec Γ Γ (SStore Γ) :=
        fun w0 POST δ => T POST δ δ.
      Definition put_local {Γ1 Γ2} : ⊢ SStore Γ2 -> SStoreSpec Γ1 Γ2 Unit :=
        fun w0 δ POST _ => T POST tt δ.
      Definition get_heap {Γ} : ⊢ SStoreSpec Γ Γ SHeap :=
        fun w0 POST δ h => T POST h δ h.
      Definition put_heap {Γ} : ⊢ SHeap -> SStoreSpec Γ Γ Unit :=
        fun w0 h POST δ _ => T POST tt δ h.

      Definition eval_exp {Γ σ} (e : Exp Γ σ) :
        ⊢ SStoreSpec Γ Γ (STerm σ) :=
        fun w POST δ => T POST (peval (seval_exp δ e)) δ.

      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        ⊢ SStoreSpec Γ Γ (SStore σs) :=
        fun w POST δ =>
          T POST (env.map (fun (b : PVar∷Ty) (e : Exp Γ (type b)) => peval (seval_exp δ e)) es) δ.

      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} : ⊢ STerm σ -> SStoreSpec Γ Γ Unit :=
        fun w0 t POST δ => T POST tt (δ ⟪ x ↦ t ⟫).
      Global Arguments assign {Γ} x {σ xIn} [w] v.

    End State.

    Section ProduceConsume.
      Import EqNotations.

      Definition produce_chunk {Γ} :
        ⊢ Chunk -> SStoreSpec Γ Γ Unit :=
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
        ⊢ Chunk -> SStoreSpec Γ Γ Unit :=
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
        ⊢ Chunk -> SStoreSpec Γ Γ Unit :=
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
        ⊢ Assertion -> □(SStoreSpec Γ Γ Unit) :=
        fix produce w0 asn :=
          match asn with
          | asn.formula fml => box_assume_formula fml
          | asn.chunk c => produce_chunk <$> persist c
          | asn.chunk_angelic c => produce_chunk <$> persist c
          | asn.pattern_match s pat rhs =>
             fun w1 θ1 =>
               ⟨ θ2 ⟩ '(existT pc ζ) <- demonic_pattern_match id pat s⟨θ1⟩ ;;
               produce (wcat w0 (PatternCaseCtx pc)) (rhs pc) _ (acc_cat_left (θ1 ∘ θ2) ζ)
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
        ⊢ Assertion -> □(SStoreSpec Γ Γ Unit) :=
        fix consume w0 asn :=
          match asn with
          | asn.formula fml => box_assert_formula fml
          | asn.chunk c => consume_chunk <$> persist c
          | asn.chunk_angelic c => consume_chunk_angelic <$> persist c
          | asn.pattern_match s pat rhs =>
             fun w1 θ1 =>
               ⟨ θ2 ⟩ '(existT pc ζ) <- angelic_pattern_match id pat s⟨θ1⟩ ;;
               consume (wcat w0 (PatternCaseCtx pc)) (rhs pc) _ (acc_cat_left (θ1 ∘ θ2) ζ)
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
        ⊢ SStore Δ -> SStoreSpec Γ Γ (STerm τ) :=
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
        ⊢ SStore Δ -> SStoreSpec Γ Γ Unit :=
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
        ⊢ SStore Δ -> SStoreSpec Γ Γ (STerm τ) :=
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
      Definition Exec := forall Γ τ (s : Stm Γ τ), ⊢ SStoreSpec Γ Γ (STerm τ).

      Section ExecAux.

        (* The executor for "inlining" a call. *)
        Variable rec : Exec.

        (* The openly-recursive executor. *)
        Definition exec_aux : forall {Γ τ} (s : Stm Γ τ), ⊢ SStoreSpec Γ Γ (STerm τ) :=
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
                ⟨ θ1 ⟩ v  <- exec_aux s ;;
                ⟨ θ2 ⟩ '(existT pc vs) <- demonic_pattern_match PVartoLVar pat v ;;
                pushspops vs (exec_aux (rhs pc))
            | stm_bind _ _ =>
                error
                  (fun δ h =>
                     amsg.mk
                     {| msg_function := "SStoreSpec.exec";
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
                        {| msg_function := "SStoreSpec.exec";
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
        SStoreSpec Δ Δ Unit {| wctx := sep_contract_logic_variables c; wco := ctx.nil |} :=
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

  End SStoreSpec.

  Module Symbolic.
    Import SStoreSpec.

    Definition ValidContractWithFuel {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition
        (postprocess (SPureSpec.replay (postprocess (vcgen default_config fuel c body)))).

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
      is_true (ok (postprocess (SPureSpec.replay (postprocess (vcgen default_config fuel c body))))).

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
      unfold ValidContract, ValidContractReflect.
      now apply validcontract_reflect_fuel_sound.
    Qed.

    Definition VcGenErasure {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Erasure.ESymProp :=
      Erasure.erase_symprop (postprocess (SPureSpec.replay (postprocess (vcgen default_config 1 c body)))).

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
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG).

  Include SymbolicExecOn B SIG PROG SPEC .

End MakeExecutor.
