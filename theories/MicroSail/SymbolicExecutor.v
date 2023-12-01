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
  (Import PROG : Program B).

  Import ModalNotations.
  Import SPureSpecM SHeapSpecM.
  #[local] Open Scope modal.
  #[local] Open Scope mut_scope.

  Section DebugInfo.

    Import option.notations.

    Record DebugCall (Σ : LCtx) : Type :=
      MkDebugCall
        { debug_call_function_parameters    : PCtx;
          debug_call_function_result_type   : Ty;
          debug_call_function_name          : 𝑭 debug_call_function_parameters debug_call_function_result_type;
          debug_call_function_contract      : SepContract debug_call_function_parameters debug_call_function_result_type;
          debug_call_function_arguments     : SStore debug_call_function_parameters Σ;
          (* debug_call_program_context        : PCtx; *)
          debug_call_pathcondition          : PathCondition Σ;
          (* debug_call_localstore             : SStore debug_call_program_context Σ; *)
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
        | MkDebugCall f c ts pc (* δ *) h =>
          MkDebugCall f c (subst ts ζ01) (subst pc ζ01) (* (subst δ ζ01) *) (subst h ζ01)
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
        | MkDebugCall f c ts pc (* δ *) h =>
            ts' <- occurs_check xIn ts ;;
            pc' <- occurs_check xIn pc ;;
            (* δ'  <- occurs_check xIn δ ;; *)
            h'  <- occurs_check xIn h ;;
            Some (MkDebugCall f c ts' pc' (* δ' *) h')
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

  #[local] Hint Extern 2 (Persistent (WTerm ?σ)) =>
    refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.
  #[local] Hint Extern 2 (Persistent (fun w : World => NamedEnv (Term (wctx w)) ?Γ)) =>
    refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.
  #[local] Hint Extern 2 (Persistent (fun w : World => @Env _ (fun xt => Term (wctx w) (type  xt)) ?Γ)) =>
    refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.
  #[local] Hint Extern 2 (Persistent (fun w : World => SStore ?Γ (wctx w))) =>
    refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.
  #[local] Hint Extern 2 (Lift (SStore ?Γ) (CStore ?Γ)) =>
    refine (@lift_env (Binding _ _) (fun Σ b => Term Σ (type b)) _ _ Γ) : typeclass_instances.

  Section Exec.

    Context {M : TYPE -> TYPE}
      {pureM : SPureSpecM M}
      {heapM : SHeapSpecM M}.

    Definition SStoreT (Γ1 Γ2 : PCtx) (A : TYPE) : TYPE :=
      SStore Γ1 -> M (WProd A (SStore Γ2)).

    Definition liftM {Γ A} :
      ⊢ M A -> SStoreT Γ Γ A :=
      fun w m δ =>
        SPureSpecM.bind m (fun _ θ a =>
                  SPureSpecM.pure (a, persist (A := SStore Γ) δ θ)).

    Definition evalStoreT {Γ1 Γ2 A} : ⊢ SStoreT Γ1 Γ2 A -> SStore Γ1 -> M A :=
      fun w m δ1 => SPureSpecM.bind (m δ1) (fun _ _ '(a,_) => pure a).

    Definition state {Γ1 Γ2 A} : ⊢ (SStore Γ1 -> WProd A (SStore Γ2)) -> SStoreT Γ1 Γ2 A :=
      fun w f δ => SPureSpecM.pure (f δ).

    Definition pure {Γ A} : ⊢ A -> SStoreT Γ Γ A :=
      fun w a => liftM (SPureSpecM.pure a).

    Definition bind {Γ1 Γ2 Γ3 A B} :
      ⊢ SStoreT Γ1 Γ2 A -> □(A -> SStoreT Γ2 Γ3 B) -> SStoreT Γ1 Γ3 B :=
      fun w m f δ1 => SPureSpecM.bind (m δ1) (fun _ θ '(a,δ2) => f _ θ a δ2).

    Definition error {Γ A} :
       ⊢ □(SStore Γ -> SHeap -> AMessage) -> SStoreT Γ Γ A :=
      fun w msg δ => SPureSpecM.error (fun _ θ => msg _ θ (persist δ θ)).

    Definition debug {Γ A} :
       ⊢ □(SStore Γ -> SHeap -> AMessage) -> SStoreT Γ Γ A -> SStoreT Γ Γ A :=
      fun w msg m δ => SPureSpecM.debug (fun _ θ => msg _ θ (persist δ θ)) (m δ).

    #[local] Notation "⟨ θ ⟩ x <- ma ;; mb" :=
      (bind ma (fun _ θ x => mb))
        (at level 80, x at next level,
          ma at next level, mb at level 200,
          right associativity) : mut_scope.
    #[local] Notation "⟨ θ ⟩ ' x <- ma ;; mb" :=
      (bind ma (fun _ θ x => mb))
        (at level 80, x pattern,
          ma at next level, mb at level 200,
          right associativity) : mut_scope.
    #[local] Notation "x ⟨ θ ⟩" := (persist x θ).

    Definition pushpop {A Γ1 Γ2 x σ} :
      ⊢ STerm σ -> SStoreT (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A -> SStoreT Γ1 Γ2 A :=
      fun _ t m δ1 =>
        SPureSpecM.bind (m δ1.[x∷σ ↦ t])
          (fun _ θ '(a,δ2) => SPureSpecM.pure (a, env.tail δ2)).

    Definition pushspops {A Γ1 Γ2 Δ} :
      ⊢ SStore Δ -> SStoreT (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A -> SStoreT Γ1 Γ2 A :=
      fun _ ts m δ1 =>
        SPureSpecM.bind (m (env.cat δ1 ts))
          (fun _ θ '(a,δ2) => SPureSpecM.pure (a, env.drop Δ δ2)).

    Definition put_local {Γ1 Γ2} :
      ⊢ SStore Γ2 -> SStoreT Γ1 Γ2 (SStore Γ1) :=
      fun _ δ2 => state (fun δ1 => (δ1, δ2)).

    Definition eval_exp {Γ σ} (e : Exp Γ σ) :
      ⊢ SStoreT Γ Γ (STerm σ) :=
      fun _ => state (fun δ => (peval (seval_exp δ e), δ)).
    #[global] Arguments eval_exp {Γ σ} e {w}.

    Definition eval_exps {Γ σs} (es : NamedEnv (Exp Γ) σs) :
      ⊢ SStoreT Γ Γ (SStore σs) :=
      fun _ => state (fun δ => (env.map (fun b e => peval (seval_exp δ e)) es, δ)).
    #[global] Arguments eval_exps {Γ σs} es {w}.

    Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} :
      ⊢ STerm σ -> SStoreT Γ Γ Unit :=
      fun _ t => state (fun δ => (tt, δ ⟪ x ↦ t ⟫)).
    #[global] Arguments assign {Γ} x {σ xIn w} t.

    (* The paper discusses the case that a function call is replaced by
       interpreting the contract instead. However, this is not always
       convenient. We therefore make contracts for functions optional and
       if a function does not have a contract, we continue executing
       the body of the called function. A paramter [inline_fuel] controls the
       number of levels this is allowed before failing execution. Therefore,
       we write the executor in an open-recusion style and [Exec] is the
       closed type of such an executor. *)
    Definition ExecCall := forall Δ τ, 𝑭 Δ τ -> ⊢ SStore Δ -> M (STerm τ).
    Definition ExecCallForeign := forall Δ τ, 𝑭𝑿 Δ τ -> ⊢ SStore Δ -> M (STerm τ).
    Definition ExecLemma := forall Δ, 𝑳 Δ -> ⊢ SStore Δ -> M Unit.
    Definition Exec := forall Γ τ (s : Stm Γ τ), ⊢ SStoreT Γ Γ (STerm τ).

    Definition exec_call_error : ExecCall :=
      fun Δ τ f w _args =>
       SPureSpecM.error
         (fun (w' : World) (_ : w ⊒ w') (h : SHeap w') =>
          amsg.mk
            {|
              msg_function := "Symbolic.Executor.exec_call_xerror";
              msg_message := "out of fuel for inlining";
              msg_program_context := [ctx];
              msg_localstore := [env];
              msg_heap := h;
              msg_pathcondition := wco w'
            |}).

    Section WithExecs.

      Variable exec_call_foreign : ExecCallForeign.
      Variable exec_lemma : ExecLemma.
      Variable exec_call : ExecCall.

      Definition exec_aux : Exec :=
        fix exec_aux {Γ τ} s {w0} :=
          match s with
          | stm_val _ v => pure (term_val τ v)
          | stm_exp e => eval_exp e
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
              ⟨ θ1 ⟩ args <- eval_exps es ;;
              liftM (exec_call f args)
          | stm_call_frame δf s =>
              ⟨ θ1 ⟩ δ1  <- put_local (lift δf) ;;
              ⟨ θ2 ⟩ res <- exec_aux s ;;
              ⟨ θ3 ⟩ _   <- put_local (persist δ1 θ2) ;;
              pure (persist__term res θ3)
          | stm_foreign f es =>
              ⟨ θ1 ⟩ args <- eval_exps es ;;
              liftM (exec_call_foreign f args)
          | stm_lemmak l es k =>
              ⟨ θ1 ⟩ args <- eval_exps es ;;
              ⟨ θ2 ⟩ _    <- liftM (exec_lemma l args) ;;
              exec_aux k
          | stm_seq s1 s2 =>
              ⟨ θ1 ⟩ _ <- exec_aux s1 ;;
              exec_aux s2
          | stm_assertk e _ k =>
              ⟨ ω01 ⟩ t <- eval_exp e ;;
              (* This uses assume_formula for a partial correctness *)
              (* interpretation of the object language failure effect. *)
              ⟨ ω12 ⟩ _ <- liftM (assume_formula (formula_bool t)) ;;
              exec_aux k
          | stm_fail _ _ =>
              (* Same as stm_assert: partial correctness of failure. *)
              liftM (block (w:=w0))
          | stm_read_register reg =>
              ⟨ ω01 ⟩ t <- liftM (angelic None _) ;;
              ⟨ ω12 ⟩ _ <- liftM (consume_chunk (chunk_ptsreg reg t)) ;;
              ⟨ ω23 ⟩ _ <- liftM (produce_chunk (chunk_ptsreg reg (persist__term t ω12))) ;;
              pure (persist__term t (ω12 ∘ ω23))
          | stm_write_register reg e =>
              ⟨ ω01 ⟩ told <- liftM (angelic None _) ;;
              ⟨ ω12 ⟩ _    <- liftM (consume_chunk (chunk_ptsreg reg told)) ;;
              ⟨ ω23 ⟩ tnew <- eval_exp e ;;
              ⟨ ω34 ⟩ _    <- liftM (produce_chunk (chunk_ptsreg reg tnew)) ;;
              pure (persist__term tnew ω34)
          | stm_pattern_match s pat rhs =>
              ⟨ θ1 ⟩ v  <- exec_aux s ;;
              ⟨ θ2 ⟩ '(existT pc δpc) <-
                liftM (demonic_pattern_match PVartoLVar pat v) ;;
              pushspops δpc (exec_aux (rhs pc))
          | stm_bind _ _ =>
              error
                (fun w2 θ2 δ2 h2 =>
                   amsg.mk
                     {| msg_function := "SHeapSpecM.exec";
                       msg_message := "stm_bind not supported";
                       msg_program_context := Γ;
                       msg_localstore := δ2;
                       msg_heap := h2;
                       msg_pathcondition := wco w2;
                     |})
          | stm_debugk k =>
              debug
                (fun w θ δ h =>
                   amsg.mk
                     {| debug_stm_program_context := Γ;
                       debug_stm_statement_type := τ;
                       debug_stm_statement := k;
                       debug_stm_pathcondition := wco w;
                       debug_stm_localstore := δ;
                       debug_stm_heap := h
                     |})
                (exec_aux k)
          end.

    End WithExecs.

    Section WithExec.

      Context (exec : Exec).

      Import SPureSpecM.notations.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : ⊢ M Unit :=
        fun w =>
          match c with
          | MkSepContract _ _ lvars pats req result ens =>
              ⟨ θ1 ⟩ lenv  <- demonic_ctx id lvars ;;
              ⟨ θ2 ⟩ _     <- sproduce req lenv ;;
              let lenv2 := persist lenv θ2 in
              ⟨ θ3 ⟩ res   <- evalStoreT (exec s (w:=_)) (subst pats lenv2) ;;
              sconsume ens (sub_snoc (persist lenv2 θ3) (result∷τ) res)
          end.

    End WithExec.

  End Exec.
  #[global] Arguments SStoreT M Γ1 Γ2 A w : clear implicits.
  #[global] Arguments ExecCallForeign M : clear implicits.
  #[global] Arguments ExecLemma M : clear implicits.
  #[global] Arguments ExecCall M : clear implicits.
  #[global] Arguments Exec M : clear implicits.

End SymbolicExecOn.
