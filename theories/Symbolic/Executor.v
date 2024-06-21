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

  Module SStoreSpec.

    Local Hint Extern 2 (Persistent (WTerm ?σ)) =>
      refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.

    Section Basic.

      Definition evalStoreSpec {Γ1 Γ2 A} :
        ⊢ SStoreSpec Γ1 Γ2 A -> SStore Γ1 -> SHeapSpec A :=
        fun w m δ Φ => m (fun w1 θ1 a1 _ => Φ w1 θ1 a1) δ.

      Definition lift_purem {Γ} {A : TYPE} :
        ⊢ SPureSpec A -> SStoreSpec Γ Γ A :=
        fun w0 m POST δ0 h0 =>
          m (fun w1 ω01 a1 => POST w1 ω01 a1 (persist δ0 ω01) (persist h0 ω01)).

      Definition pure {Γ} {A : TYPE} :
        ⊢ A -> SStoreSpec Γ Γ A := fun _ a k => T k a.

      Definition bind {Γ1 Γ2 Γ3 A B} :
        ⊢ SStoreSpec Γ1 Γ2 A -> □(A -> SStoreSpec Γ2 Γ3 B) -> SStoreSpec Γ1 Γ3 B :=
        fun w0 ma f k => ma (fun w1 ω01 a1 => f w1 ω01 a1 (four k ω01)).

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

      Definition assert_formula {Γ} :
        ⊢ Formula -> SStoreSpec Γ Γ Unit :=
        fun w0 fml POST δ0 h0 =>
          lift_purem
            (SPureSpec.assert_formula
               (amsg.mk (MkDebugAssertFormula (wco w0) h0 fml)) fml)
            POST δ0 h0.

      Definition assert_pathcondition {Γ} :
        ⊢ PathCondition -> SStoreSpec Γ Γ Unit :=
        fun w0 fmls POST δ0 h0 =>
          lift_purem
            (SPureSpec.assert_pathcondition
               (amsg.mk
                  {| msg_function := "SStoreSpec._assert_pathcondition";
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
                  {| msg_function := "SStoreSpec.assert_eq_env";
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
                  {| msg_function := "SStoreSpec.assert_eq_env";
                     msg_message := "Proof obligation";
                     msg_program_context := Γ;
                     msg_localstore := δ0;
                     msg_heap := h0;
                     msg_pathcondition := wco w0
                  |}) E1 E2)
            POST δ0 h0.

    End AssumeAssert.

    Section PatternMatching.

      Definition demonic_pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : @Pattern N σ) :
        ⊢ STerm σ -> SStoreSpec Γ Γ (SMatchResult pat) :=
        fun w0 t Φ δ h =>
          SPureSpec.demonic_pattern_match n pat t
            (fun w1 θ1 mr => Φ w1 θ1 mr δ⟨θ1⟩ h⟨θ1⟩).
      #[global] Arguments demonic_pattern_match {N} n {Γ σ} pat [w].

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

      Definition eval_exp {Γ σ} (e : Exp Γ σ) :
        ⊢ SStoreSpec Γ Γ (STerm σ) :=
        fun w POST δ => T POST (peval (seval_exp δ e)) δ.

      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        ⊢ SStoreSpec Γ Γ (SStore σs) :=
        fun w POST δ =>
          T POST (seval_exps δ es) δ.

      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} : ⊢ STerm σ -> SStoreSpec Γ Γ Unit :=
        fun w0 t POST δ => T POST tt (δ ⟪ x ↦ t ⟫).
      Global Arguments assign {Γ} x {σ xIn} [w] v.

    End State.

    Section ProduceConsume.

      Definition produce_chunk {Γ} :
        ⊢ Chunk -> SStoreSpec Γ Γ Unit :=
        fun w0 c Φ δ =>
          SHeapSpec.produce_chunk c (fun w1 θ1 u1 => Φ w1 θ1 u1 δ⟨θ1⟩).
      Arguments produce_chunk {Γ} w c Φ δ : simpl never.

      Definition consume_chunk {Γ} :
        ⊢ Chunk -> SStoreSpec Γ Γ Unit :=
        fun w0 c Φ δ =>
          SHeapSpec.consume_chunk c (fun w1 θ1 u1 => Φ w1 θ1 u1 δ⟨θ1⟩).
      Arguments consume_chunk {Γ} w c Φ δ : simpl never.

      Definition consume_chunk_angelic {Γ} :
        ⊢ Chunk -> SStoreSpec Γ Γ Unit :=
        fun w0 c Φ δ =>
          SHeapSpec.consume_chunk_angelic c (fun w1 θ1 u1 => Φ w1 θ1 u1 δ⟨θ1⟩).

      Definition produce {Γ} :
        ⊢ Assertion -> □(SStoreSpec Γ Γ Unit) :=
        fun w0 asn w1 θ1 Φ δ =>
          SHeapSpec.produce asn (sub_acc θ1) (fun w2 θ2 u2 => Φ w2 θ2 u2 δ⟨θ2⟩).

      Definition consume {Γ} :
        ⊢ Assertion -> □(SStoreSpec Γ Γ Unit) :=
        fun w0 asn w1 θ1 Φ δ =>
       SHeapSpec.consume asn (sub_acc θ1) (fun w2 θ2 u2 => Φ w2 θ2 u2 δ⟨θ2⟩).

      Definition read_register {Γ τ} (r : 𝑹𝑬𝑮 τ) :
        ⊢ SStoreSpec Γ Γ (WTerm τ) :=
        fun w Φ δ =>
          SHeapSpec.read_register r (fun w1 θ1 t' => Φ w1 θ1 t' δ⟨θ1⟩).
      #[global] Arguments read_register {Γ τ} r {w}.

      Definition write_register {Γ τ} (r : 𝑹𝑬𝑮 τ) :
        ⊢ WTerm τ -> SStoreSpec Γ Γ (WTerm τ) :=
        fun w t Φ δ =>
          SHeapSpec.write_register r t (fun w1 θ1 t' => Φ w1 θ1 t' δ⟨θ1⟩).

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
                read_register reg
            | stm_write_register reg e =>
                ⟨ _ ⟩ tnew <- eval_exp e (w:=_) ;;
                write_register reg tnew
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
      Arguments exec_aux rec {Γ τ} !s.

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
      Global Arguments exec _ {_ _} s {w} : simpl never.

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
