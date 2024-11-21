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
  (* Import SPureSpecM SHeapSpecM. *)
  (* Import SHeapSpec. *)
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

    (* Context {M : TYPE -> TYPE} *)
    (*   {pureM : SPureSpecM M} *)
    (*   {heapM : SHeapSpecM M}. *)
    Notation M := SHeapSpec.

    Definition SStoreSpec (Γ1 Γ2 : PCtx) (A : TYPE) : TYPE :=
      □(A -> SStore Γ2 -> SHeap -> SymProp) -> SStore Γ1 -> SHeap -> SymProp.

    Definition lift_heapspec {Γ A} :
      ⊢ M A -> SStoreSpec Γ Γ A :=
      fun w m Φ δ h =>
        m (fun _ θ a =>
             let δ' := persist (A := SStore Γ) δ θ in
             Φ _ θ a δ') h.

    Definition evalStoreSpec {Γ1 Γ2 A} : ⊢ SStoreSpec Γ1 Γ2 A -> SStore Γ1 -> M A :=
      fun w m δ1 Φ h1 => m (fun _ θ a _ h2 => Φ _ θ a h2) δ1 h1.

    Definition pure {Γ A} : ⊢ A -> SStoreSpec Γ Γ A :=
      fun w a Φ δ h => T Φ a δ h.

    Definition bind {Γ1 Γ2 Γ3 A B} :
      ⊢ SStoreSpec Γ1 Γ2 A -> □(A -> SStoreSpec Γ2 Γ3 B) -> SStoreSpec Γ1 Γ3 B :=
      fun w m f Φ δ1 h1 => m (fun _ θ a δ2 h2 => f _ θ a (four Φ θ) δ2 h2) δ1 h1.

    Definition error {Γ A} :
       ⊢ (SStore Γ -> SHeap -> AMessage) -> SStoreSpec Γ Γ A :=
      fun w msg _ δ h => SymProp.error (msg δ h).

    Definition debug {Γ A} :
       ⊢ (SStore Γ -> SHeap -> AMessage) -> SStoreSpec Γ Γ A -> SStoreSpec Γ Γ A :=
      fun w msg m Φ δ h => SymProp.debug (msg δ h) (m Φ δ h).

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
      ⊢ STerm σ -> SStoreSpec (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A -> SStoreSpec Γ1 Γ2 A :=
      fun w t m Φ δ1 h => m (fun _ θ a δ2 => Φ _ θ a (env.tail δ2)) δ1.[x∷σ ↦ t] h.

    Definition pushspops {A Γ1 Γ2 Δ} :
      ⊢ SStore Δ -> SStoreSpec (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A -> SStoreSpec Γ1 Γ2 A :=
      fun w δΔ m Φ δ1 h => m (fun _ θ a δ2 => Φ _ θ a (env.drop Δ δ2)) (env.cat δ1 δΔ) h.

    Definition eval_exp {Γ σ} (e : Exp Γ σ) :
      ⊢ SStoreSpec Γ Γ (STerm σ) :=
      fun w Φ δ h => T Φ (peval (seval_exp δ e)) δ h.
    #[global] Arguments eval_exp {Γ σ} e {w}.

    Definition eval_exps {Γ σs} (es : NamedEnv (Exp Γ) σs) :
      ⊢ SStoreSpec Γ Γ (SStore σs) :=
      fun w Φ δ h => T Φ (env.map (fun b e => peval (seval_exp δ e)) es) δ h.
    #[global] Arguments eval_exps {Γ σs} es {w}.

    Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} :
      ⊢ STerm σ -> SStoreSpec Γ Γ (STerm σ) :=
      fun w t Φ δ h => T Φ t (δ ⟪ x ↦ t ⟫) h.
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
    Definition Exec := forall Γ τ (s : Stm Γ τ), ⊢ SStoreSpec Γ Γ (STerm τ).

    Definition exec_call_error : ExecCall :=
      fun Δ τ f w _args =>
       SHeapSpec.error
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

      Definition exec_call' {Γ Δ τ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
        ⊢ SStoreSpec Γ Γ (WTerm τ) :=
        fun w =>
          ⟨ θ1 ⟩ args <- eval_exps es ;;
          lift_heapspec (exec_call f args).

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
              assign x t
          | stm_call f es =>
              exec_call' f es (w := _)
              (* ⟨ θ1 ⟩ args <- eval_exps es ;; *)
              (* lift_heapspec (exec_call f args) *)
          | stm_call_frame δf s =>
              lift_heapspec (evalStoreSpec (exec_aux s) (lift δf))
          | stm_foreign f es =>
              ⟨ θ1 ⟩ args <- eval_exps es ;;
              lift_heapspec (exec_call_foreign f args)
          | stm_lemmak l es k =>
              ⟨ θ1 ⟩ args <- eval_exps es ;;
              ⟨ θ2 ⟩ _    <- lift_heapspec (exec_lemma l args) ;;
              exec_aux k
          | stm_seq s1 s2 =>
              ⟨ θ1 ⟩ _ <- exec_aux s1 ;;
              exec_aux s2
          | stm_assertk e _ k =>
              ⟨ ω01 ⟩ t <- eval_exp e ;;
              (* This uses assume_formula for a partial correctness *)
              (* interpretation of the object language failure effect. *)
              ⟨ ω12 ⟩ _ <- lift_heapspec (SHeapSpec.assume_formula (formula_bool t)) ;;
              exec_aux k
          | stm_fail _ _ =>
              (* Same as stm_assert: partial correctness of failure. *)
              lift_heapspec (SHeapSpec.block (w:=w0))
          | stm_read_register reg =>
              lift_heapspec (SHeapSpec.read_register reg)
          | stm_write_register reg e =>
              ⟨ _ ⟩ tnew <- eval_exp e ;;
              lift_heapspec (SHeapSpec.write_register reg tnew)
          | stm_pattern_match s pat rhs =>
              ⟨ θ1 ⟩ v  <- exec_aux s ;;
              ⟨ θ2 ⟩ '(existT pc δpc) <-
                lift_heapspec (SHeapSpec.demonic_pattern_match PVartoLVar pat v) ;;
              pushspops δpc (exec_aux (rhs pc))
          | stm_bind _ _ =>
              error
                (fun δ2 h2 =>
                   amsg.mk
                     {| msg_function := "SHeapSpecM.exec";
                       msg_message := "stm_bind not supported";
                       msg_program_context := Γ;
                       msg_localstore := δ2;
                       msg_heap := h2;
                       msg_pathcondition := wco _;
                     |})
          | stm_debugk k =>
              debug
                (fun δ h =>
                   amsg.mk
                     {| debug_stm_program_context := Γ;
                       debug_stm_statement_type := τ;
                       debug_stm_statement := k;
                       debug_stm_pathcondition := wco _;
                       debug_stm_localstore := δ;
                       debug_stm_heap := h
                     |})
                (exec_aux k)
          end.

      (* Eval cbv [exec_aux write_register SHeapSpec.bind SHeapSpec.angelic SHeapSpec.lift_purespec SHeapSpec.angelic bind eval_exps eval_exp T lift_heapspec pure four pushpop assign SPureSpec.angelic SHeapSpec.pure SPureSpec.pure] in @exec_aux. *)

    End WithExecs.

    Section WithExec.

      Context (exec : Exec).

      Import SHeapSpec.notations.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : ⊢ M Unit :=
        fun w =>
          match c with
          | MkSepContract _ _ lvars pats req result ens =>
              ⟨ θ1 ⟩ lenv  <- SHeapSpec.demonic_ctx id lvars ;;
              ⟨ θ2 ⟩ _     <- SHeapSpec.sproduce req lenv ;;
              let lenv2 := persist lenv θ2 in
              ⟨ θ3 ⟩ res   <- evalStoreSpec (exec s (w:=_)) (subst pats lenv2) ;;
              SHeapSpec.sconsume ens (sub_snoc (persist lenv2 θ3) (result∷τ) res)
          end.

    End WithExec.

  End Exec.
  #[global] Arguments SStoreSpec Γ1 Γ2 A w : clear implicits.
  #[global] Arguments ExecCallForeign : clear implicits.
  #[global] Arguments ExecLemma : clear implicits.
  #[global] Arguments ExecCall : clear implicits.
  #[global] Arguments Exec : clear implicits.

End SymbolicExecOn.
