(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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
     Bool.Bool
     Classes.Morphisms
     Lists.List
     NArith.NArith
     Program.Basics
     Program.Tactics
     Strings.String
     Relations.Relation_Definitions
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations
     Prelude
     Signature
     Symbolic.Propositions
     Specification.

From stdpp Require base list option.

Import ctx.notations.
Import env.notations.
Import ListNotations.
Import SignatureNotations.

Set Implicit Arguments.

Module Type ShallowExecOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG).

  (* The main specification monad that we use for execution. It is indexed by
     two program variable contexts Γ1 Γ2 that encode the shape of the program
     variable store before and after execution. *)
  Definition CStoreSpec (Γ1 Γ2 : PCtx) (A : Type) : Type :=
    (A -> CStore Γ2 -> SCHeap -> Prop) -> CStore Γ1 -> SCHeap -> Prop.

  Definition MStoreSpec (Γ1 Γ2 : PCtx) [A] (MA : relation A) :
    relation (CStoreSpec Γ1 Γ2 A) :=
    (MA ==> CStore Γ2 ::> SCHeap ::> impl) ==> CStore Γ1 ::> SCHeap ::> impl.
  #[global] Arguments MStoreSpec Γ1 Γ2 [A] MA.

  (* The paper discusses the case that a function call is replaced by
     interpreting the contract instead. However, this is not always
     convenient. We therefore parameterize the executor by other functions
     that interpret function calls and lemma applications. The following
     types describe the executor and the parameters. *)
  Definition ExecCall := forall Δ τ, 𝑭 Δ τ -> CStore Δ -> CHeapSpec (Val τ).
  Definition ExecCallForeign := forall Δ τ, 𝑭𝑿 Δ τ -> CStore Δ -> CHeapSpec (Val τ).
  Definition ExecLemma := forall Δ, 𝑳 Δ -> CStore Δ -> CHeapSpec unit.
  Definition Exec := forall Γ τ (s : Stm Γ τ), CStoreSpec Γ Γ (Val τ).

  Notation MonotonicExecCall exec_call :=
    (forall Δ τ (f : 𝑭 Δ τ) (δ : CStore Δ),
       Monotonic (MHeapSpec eq) (exec_call Δ τ f δ)).
  Notation MonotonicExecCallForeign exec_call_foreign :=
    (forall Δ τ (f : 𝑭𝑿 Δ τ) (δ : CStore Δ),
       Monotonic (MHeapSpec eq) (exec_call_foreign Δ τ f δ)).
  Notation MonotonicExecLemma exec_lemma :=
    (forall Δ (l : 𝑳 Δ) (δ : CStore Δ),
       Monotonic (MHeapSpec eq) (exec_lemma Δ l δ)).
  Notation MonotonicExec exec :=
    (forall Γ τ (s : Stm Γ τ),
       Monotonic (MStoreSpec Γ Γ eq) (exec Γ τ s)).

  Module CStoreSpec.

    Import (hints) CHeapSpec.

    Section Basic.

      Definition evalStoreSpec {Γ1 Γ2 A} :
        CStoreSpec Γ1 Γ2 A -> CStore Γ1 -> CHeapSpec A :=
        fun m δ Φ => m (fun a1 _ => Φ a1) δ.

      Definition lift_purespec {Γ} {A : Type} :
        CPureSpec A -> CStoreSpec Γ Γ A :=
        fun m POST δ h => m (fun a => POST a δ h).
      Definition lift_heapspec {Γ} {A : Type} :
        CHeapSpec A -> CStoreSpec Γ Γ A :=
        fun m POST δ => m (fun a => POST a δ).

      Definition pure {Γ A} (a : A) : CStoreSpec Γ Γ A :=
        fun POST => POST a.
      Definition bind {Γ1 Γ2 Γ3 A B} (ma : CStoreSpec Γ1 Γ2 A) (f : A -> CStoreSpec Γ2 Γ3 B) : CStoreSpec Γ1 Γ3 B :=
        fun POST => ma (fun a => f a POST).

      Definition error {Γ1 Γ2 A} : CStoreSpec Γ1 Γ2 A :=
        fun POST δ h => FALSE.
      Definition block {Γ1 Γ2 A} : CStoreSpec Γ1 Γ2 A :=
        fun POST δ h => TRUE.

      Definition demonic_binary {Γ1 Γ2 A} (m1 m2 : CStoreSpec Γ1 Γ2 A) : CStoreSpec Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h /\ m2 POST δ h.
      Definition angelic_binary {Γ1 Γ2 A} (m1 m2 : CStoreSpec Γ1 Γ2 A) : CStoreSpec Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h \/ m2 POST δ h.

      Definition demonic {Γ} (σ : Ty) : CStoreSpec Γ Γ (Val σ) :=
        lift_purespec (CPureSpec.demonic σ).
      Definition angelic {Γ} (σ : Ty) : CStoreSpec Γ Γ (Val σ) :=
        lift_purespec (CPureSpec.angelic σ).

      Definition angelic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CStoreSpec Γ Γ (NamedEnv Val Δ) :=
        fun Δ => lift_purespec (CPureSpec.angelic_ctx Δ).
      #[global] Arguments angelic_ctx {N Γ} Δ.

      Definition demonic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CStoreSpec Γ Γ (NamedEnv Val Δ) :=
        fun Δ => lift_purespec (CPureSpec.demonic_ctx Δ).
      #[global] Arguments demonic_ctx {N Γ} Δ.

      Lemma mon_evalStoreSpec' {Γ1 Γ2} `{MA : relation A} :
        Monotonic (MStoreSpec Γ1 Γ2 MA ==> CStore Γ1 ::> MHeapSpec MA) evalStoreSpec.
      Proof. intros ? ? rm δ ? ? rΦ. apply rm. intros ? ? ? _. now apply rΦ. Qed.

      #[export] Instance mon_evalStoreSpec {Γ1 Γ2} `{MA : relation A} ma δ1 :
        Monotonic (MStoreSpec Γ1 Γ2 MA) ma ->
        Monotonic (MHeapSpec MA) (evalStoreSpec ma δ1).
      Proof. intros rma. now apply mon_evalStoreSpec'. Qed.

      Lemma mon_lift_purespec' `{MA : relation A} {Γ} :
        Monotonic (MPureSpec MA ==> MStoreSpec Γ Γ MA) lift_purespec.
      Proof. intros ? ? rm ? ? rΦ ? ?. apply rm. intros ? ? ?. now apply rΦ. Qed.

      #[export] Instance mon_lift_purespec `{MA : relation A} {Γ} m :
        Monotonic (MPureSpec MA) m -> Monotonic (MStoreSpec Γ Γ MA) (lift_purespec m).
      Proof. intros rm. now apply mon_lift_purespec'. Qed.

      Lemma mon_lift_heapspec' `{MA : relation A} {Γ} :
        Monotonic (MHeapSpec MA ==> MStoreSpec Γ Γ MA) lift_heapspec.
      Proof. intros ? ? rm ? ? rΦ ?. apply rm. intros ? ? ?. now apply rΦ. Qed.

      #[export] Instance mon_lift_heapspec `{MA : relation A} {Γ} m :
        Monotonic (MHeapSpec MA) m -> Monotonic (MStoreSpec Γ Γ MA) (lift_heapspec m).
      Proof. intros rm. now apply mon_lift_heapspec'. Qed.

      Lemma mon_pure' `{MA : relation A} {Γ} :
        Monotonic (MA ==> MStoreSpec Γ Γ MA) pure.
      Proof. unfold pure. firstorder. Qed.

      #[export] Instance mon_pure `{MA : relation A} {Γ}  x :
        Monotonic MA x -> Monotonic (MStoreSpec Γ Γ MA) (pure x).
      Proof. unfold pure. firstorder. Qed.

      Lemma mon_bind' `{MA : relation A, RB : relation B} {Γ1 Γ2 Γ3} :
        Monotonic (MStoreSpec Γ1 Γ2 MA ==> (MA ==> MStoreSpec Γ2 Γ3 RB) ==> MStoreSpec Γ1 Γ3 RB) bind.
      Proof.
        intros ? ? rm ? ? rf ? ? rΦ. apply rm.
        intros ? ? ra. apply rf. apply ra. apply rΦ.
      Qed.

      #[export] Instance mon_bind `{MA : relation A, RB : relation B} {Γ1 Γ2 Γ3}
        (m : CStoreSpec Γ1 Γ2 A) (f : A -> CStoreSpec Γ2 Γ3 B) :
        Monotonic (MStoreSpec Γ1 Γ2 MA) m ->
        Monotonic (MA ==> MStoreSpec Γ2 Γ3 RB) f ->
        Monotonic (MStoreSpec Γ1 Γ3 RB) (bind m f).
      Proof. intros rm rf. eapply mon_bind'; eauto. Qed.

      #[export] Instance mon_error `{MA : relation A} {Γ1 Γ2} :
        Monotonic (MStoreSpec Γ1 Γ2 MA) error.
      Proof. easy. Qed.

      #[export] Instance mon_block `{MA : relation A} {Γ1 Γ2} :
        Monotonic (MStoreSpec Γ1 Γ2 MA) block.
      Proof. easy. Qed.

    End Basic.

    Module CStoreSpecNotations.

      Infix "⊗" := demonic_binary (at level 40, left associativity) : mut_scope.
      Infix "⊕" := angelic_binary (at level 50, left associativity) : mut_scope.

      Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
           format "' x  <-  ma  ;;  mb") : mut_scope.
      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at level 90, mb at level 200, right associativity) : mut_scope.
      Notation "ma ;; mb" := (bind ma (fun _ => mb)) : mut_scope.

    End CStoreSpecNotations.
    Import CStoreSpecNotations.
    Local Open Scope mut_scope.

    Section PatternMatching.

      Definition demonic_pattern_match {N : Set} {Γ σ} (pat : @Pattern N σ) (v : Val σ) :
        CStoreSpec Γ Γ (MatchResult pat) :=
        lift_purespec (CPureSpec.demonic_pattern_match pat v).
      #[global] Arguments demonic_pattern_match {N Γ σ} pat v.

      Lemma wp_demonic_pattern_match {N : Set} {Γ σ} (pat : @Pattern N σ) (v : Val σ)
        (Φ : MatchResult pat -> CStore Γ -> SCHeap -> Prop) (δ : CStore Γ) (h : SCHeap) :
        demonic_pattern_match pat v Φ δ h <-> Φ (pattern_match_val pat v) δ h.
      Proof.
        unfold demonic_pattern_match, lift_purespec.
        now rewrite CPureSpec.wp_demonic_pattern_match.
      Qed.

    End PatternMatching.

    Section State.

      Definition pushpop {A Γ1 Γ2 x σ} (v : Val σ)
        (d : CStoreSpec (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) : CStoreSpec Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.tail δ1)) (δ0 ► (x∷σ ↦ v)).
      Definition pushspops {A} {Γ1 Γ2 Δ} (δΔ : CStore Δ)
        (d : CStoreSpec (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) : CStoreSpec Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.drop Δ δ1)) (δ0 ►► δΔ).
      Definition get_local {Γ} : CStoreSpec Γ Γ (CStore Γ) :=
        fun POST δ => POST δ δ.
      Definition put_local {Γ1 Γ2} (δ : CStore Γ2) : CStoreSpec Γ1 Γ2 unit :=
        fun POST _ => POST tt δ.

      Definition eval_exp {Γ σ} (e : Exp Γ σ) : CStoreSpec Γ Γ (Val σ) :=
        fun POST δ => POST (eval e δ) δ.
      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) : CStoreSpec Γ Γ (CStore σs) :=
        fun POST δ => POST (evals es δ) δ.
      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : Val σ) : CStoreSpec Γ Γ unit :=
        fun POST δ => POST tt (δ ⟪ x ↦ v ⟫).
      Global Arguments assign {Γ} x {σ xIn} v.

      #[export] Instance mon_pushpop `{MA : relation A} {Γ1 Γ2 x σ} (v : Val σ)
        (d : CStoreSpec (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) :
        Monotonic (MStoreSpec (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) MA) d ->
        Monotonic (MStoreSpec Γ1 Γ2 MA) (pushpop v d).
      Proof. intros md P Q PQ ?. apply md. intros ? ? ma ?. now apply PQ. Qed.

      #[export] Instance mon_pushspops `{MA : relation A} {Γ1 Γ2 Δ} (δΔ : CStore Δ)
        (d : CStoreSpec (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) :
        Monotonic (MStoreSpec (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) MA) d ->
        Monotonic (MStoreSpec Γ1 Γ2 MA) (pushspops δΔ d).
      Proof. intros md P Q PQ ?. apply md. intros ? ? ma ?. now apply PQ. Qed.

      #[export] Instance mon_get_local {Γ} :
        Monotonic (MStoreSpec Γ Γ eq) get_local.
      Proof. intros P Q PQ ?. now apply PQ. Qed.

      #[export] Instance mon_put_local {Γ1 Γ2} (δ : CStore Γ2) :
        Monotonic (MStoreSpec Γ1 Γ2 eq) (put_local δ).
      Proof. intros P Q PQ ?. now apply PQ. Qed.

      #[export] Instance mon_eval_exp {Γ σ} (e : Exp Γ σ) :
        Monotonic (MStoreSpec Γ Γ eq) (eval_exp e).
      Proof. intros P Q PQ ?. now apply PQ. Qed.

      #[export] Instance mon_eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        Monotonic (MStoreSpec Γ Γ eq) (eval_exps es).
      Proof. intros P Q PQ ?. now apply PQ. Qed.

      #[export] Instance mon_assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : Val σ) :
        Monotonic (MStoreSpec Γ Γ eq) (assign x v).
      Proof. intros P Q PQ ?. now apply PQ. Qed.

    End State.

    Section ExecAux.

      Variable exec_call_foreign : ExecCallForeign.
      Variable exec_lemma : ExecLemma.
      Variable exec_call : ExecCall.

      (* The openly-recursive executor. *)
      Definition exec_aux : Exec :=
        fix exec_aux {Γ τ} (s : Stm Γ τ) : CStoreSpec Γ Γ (Val τ) :=
          match s with
          | stm_val _ l => pure l
          | stm_exp e => eval_exp e
          | stm_let x σ s k =>
              v <- exec_aux s ;;
              pushpop v (exec_aux k)
          | stm_block δ k =>
              pushspops δ (exec_aux k)
          | stm_assign x e =>
              v <- exec_aux e ;;
              _ <- assign x v ;;
              pure v
          | stm_call f es =>
              args <- eval_exps es ;;
              lift_heapspec (exec_call f args)
          | stm_foreign f es =>
              ts <- eval_exps es ;;
              lift_heapspec (exec_call_foreign f ts)
          | stm_lemmak l es k =>
              ts <- eval_exps es ;;
              _  <- lift_heapspec (exec_lemma l ts) ;;
              exec_aux k
          | stm_call_frame δ' s =>
              δ <- get_local ;;
              _ <- put_local δ' ;;
              v <- exec_aux s ;;
              _ <- put_local δ ;;
              pure v
          | stm_seq e k => _ <- exec_aux e ;; exec_aux k
          | stm_assertk e1 _ k =>
              v <- eval_exp e1 ;;
              _ <- lift_heapspec (CHeapSpec.assume_formula (v = true)) ;;
              exec_aux k
          | stm_fail _ s =>
              block
          | stm_pattern_match s pat rhs =>
              v  <- exec_aux s ;;
              '(existT pc δpc) <- demonic_pattern_match pat v ;;
              pushspops δpc (exec_aux (rhs pc))
          | stm_read_register reg =>
              lift_heapspec (CHeapSpec.read_register reg)
          | stm_write_register reg e =>
              v__new <- eval_exp e ;;
              lift_heapspec (CHeapSpec.write_register reg v__new)
          | stm_bind s k =>
              v <- exec_aux s ;;
              exec_aux (k v)
          | stm_debugk k =>
              exec_aux k
          end.

      Context
        (mexec_call_foreign : MonotonicExecCallForeign exec_call_foreign)
        (mexec_lemma : MonotonicExecLemma exec_lemma)
        (mexec_call : MonotonicExecCall exec_call).

      #[export] Instance mon_exec_aux : MonotonicExec exec_aux.
      Proof. induction s; typeclasses eauto. Qed.

    End ExecAux.
    #[global] Arguments exec_aux _ _ _ [Γ τ] !s.

    Section WithExec.

      Context (exec : Exec) (mexec : MonotonicExec exec).

      Import CHeapSpec.notations.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : CHeapSpec unit :=
        match c with
        | MkSepContract _ _ lvars pats req result ens =>
            lenv <- CHeapSpec.demonic_ctx lvars ;;
            _    <- CHeapSpec.produce req lenv ;;
            v    <- evalStoreSpec (exec s) (inst pats lenv) ;;
            CHeapSpec.consume ens (env.snoc lenv (result∷τ) v)
        end.

      Definition vcgen {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        CHeapSpec.run (exec_contract c body).

      Lemma mon_exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
        Monotonic (MHeapSpec eq) (exec_contract c s).
      Proof. destruct c. typeclasses eauto. Qed.

    End WithExec.

  End CStoreSpec.

  Section WithSpec.

    Definition exec_call_error : ExecCall :=
      fun Δ τ f args => CHeapSpec.lift_purespec CPureSpec.error.

    Definition cexec_call_foreign : ExecCallForeign :=
      fun Δ τ f args =>
        CHeapSpec.call_contract (CEnvEx f) args.

    Definition cexec_lemma : ExecLemma :=
      fun Δ l args =>
        CHeapSpec.call_lemma (LEnv l) args.

    Import CHeapSpec.notations.

    Definition debug_call [Δ τ] (f : 𝑭 Δ τ) (args : CStore Δ) : CHeapSpec unit :=
      CHeapSpec.pure tt.

    (* If a function does not have a contract, we continue executing the body of
       the called function. A parameter [inline_fuel] bounds the number of
       allowed levels before failing execution. *)
    Fixpoint cexec_call (inline_fuel : nat) : ExecCall :=
      fun Δ τ f args =>
        _ <- debug_call f args ;;
        (* Let's first see if we have a contract defined for function [f]
           and then if we have enough fuel for inlining. *)
        match CEnv f , inline_fuel with
        | Some c , _ =>
            (* YES: Execute the call by interpreting the contract. *)
            CHeapSpec.call_contract c args
        | None   , 0 =>
            (* Out of fuel *)
            exec_call_error f args
        | None   , S n =>
            CStoreSpec.evalStoreSpec
              (CStoreSpec.exec_aux cexec_call_foreign cexec_lemma (cexec_call n) (FunDef f))
              args
        end.

    Definition cexec (inline_fuel : nat) : Exec :=
      @CStoreSpec.exec_aux cexec_call_foreign cexec_lemma (cexec_call inline_fuel).
    #[global] Arguments cexec _ [_ _] s _ _ _ : simpl never.

    Import (hints) CStoreSpec.

    Lemma mon_exec_call_error : MonotonicExecCall exec_call_error.
    Proof. typeclasses eauto. Qed.

    Lemma mon_cexec_call_foreign : MonotonicExecCallForeign cexec_call_foreign.
    Proof. typeclasses eauto. Qed.

    Lemma mon_cexec_lemma : MonotonicExecLemma cexec_lemma.
    Proof. typeclasses eauto. Qed.

    #[export] Instance mon_cexec_call (fuel : nat) : MonotonicExecCall (cexec_call fuel).
    Proof. induction fuel; intros; cbn; destruct CEnv; typeclasses eauto. Qed.

    Lemma mon_cexec (fuel : nat) : MonotonicExec (cexec fuel).
    Proof. typeclasses eauto. Qed.

  End WithSpec.

  Module Shallow.

    Definition ValidContractWithFuel {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      CStoreSpec.vcgen (cexec fuel) c body.

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      (* Use inline_fuel = 1 by default. *)
      ValidContractWithFuel 1 c body.

    Module Statistics.

      Ltac calc fnc :=
        let P := eval compute - [FALSE TRUE FINISH
                                 negb Z.mul Z.opp Z.compare Z.add Z.geb Z.eqb
                                 Z.leb Z.gtb Z.ltb Z.le Z.lt Z.gt Z.ge Z.of_nat
                                 List.app List.length rev rev_append
            ] in
                   (match CEnv fnc with
                    | Some c => Shallow.ValidContract c (FunDef fnc)
                    | None => False
                    end) in
        let s := eval compute in (CStatistics.stats P) in s.

    End Statistics.

  End Shallow.

End ShallowExecOn.

Module MakeShallowExecutor
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG).

  Include ShallowExecOn B SIG PROG SPEC.

End MakeShallowExecutor.
