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

  Definition Exec := forall Γ τ (s : Stm Γ τ), CStoreSpec Γ Γ (Val τ).

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

    Section AssumeAssert.

      Definition assume_formula {Γ} (fml : Prop) : CStoreSpec Γ Γ unit :=
        lift_purespec (CPureSpec.assume_formula fml).
      Definition assert_formula {Γ} (fml : Prop) : CStoreSpec Γ Γ unit :=
        lift_purespec (CPureSpec.assert_formula fml).
      Definition assert_pathcondition {Γ} (fml : Prop) : CStoreSpec Γ Γ unit :=
        lift_purespec (CPureSpec.assert_pathcondition fml).
      Definition assert_eq_env {Γ} {Δ : Ctx Ty} (δ δ' : Env Val Δ) : CStoreSpec Γ Γ unit :=
        lift_purespec (CPureSpec.assert_eq_env δ δ').
      Definition assert_eq_nenv {N Γ} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) : CStoreSpec Γ Γ unit :=
        lift_purespec (CPureSpec.assert_eq_nenv δ δ').

      #[export] Instance mon_assume_formula {Γ} (fml : Prop) :
        Monotonic (MStoreSpec Γ Γ eq) (assume_formula fml).
      Proof. typeclasses eauto. Qed.

      #[export] Instance mon_assert_formula {Γ} (fml : Prop) :
        Monotonic (MStoreSpec Γ Γ eq) (assert_formula fml).
      Proof. typeclasses eauto. Qed.

      #[export] Instance mon_assert_pathcondition {Γ} (fml : Prop) :
        Monotonic (MStoreSpec Γ Γ eq) (assert_pathcondition fml).
      Proof. typeclasses eauto. Qed.

      #[export] Instance mon_assert_eq_env {Γ} {Δ : Ctx Ty} (δ δ' : Env Val Δ) :
        Monotonic (MStoreSpec Γ Γ eq) (assert_eq_env δ δ').
      Proof. typeclasses eauto. Qed.

      #[export] Instance mon_assert_eq_nenv {N Γ} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) :
        Monotonic (MStoreSpec Γ Γ eq) (assert_eq_nenv δ δ').
      Proof. typeclasses eauto. Qed.

    End AssumeAssert.

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

    Section ProduceConsume.

      Definition produce {Γ Σ} (asn : Assertion Σ) (ι : Valuation Σ) : CStoreSpec Γ Γ unit :=
        lift_heapspec (CHeapSpec.produce asn ι).
      Definition consume {Γ Σ} (asn : Assertion Σ) (ι : Valuation Σ) : CStoreSpec Γ Γ unit :=
        lift_heapspec (CHeapSpec.consume asn ι).

      Definition produce_chunk {Γ} (c : SCChunk) : CStoreSpec Γ Γ unit :=
        lift_heapspec (CHeapSpec.produce_chunk c).
      Definition consume_chunk {Γ} (c : SCChunk) : CStoreSpec Γ Γ unit :=
        lift_heapspec (CHeapSpec.consume_chunk c).

      Definition read_register {Γ τ} (r : 𝑹𝑬𝑮 τ) : CStoreSpec Γ Γ (Val τ) :=
        lift_heapspec (CHeapSpec.read_register r).
      Definition write_register {Γ τ} (r : 𝑹𝑬𝑮 τ) (v : Val τ) : CStoreSpec Γ Γ (Val τ) :=
        lift_heapspec (CHeapSpec.write_register r v).

      Lemma mon_produce {Γ Σ} (asn : Assertion Σ) (ι : Valuation Σ) :
        Monotonic (MStoreSpec Γ Γ eq) (produce asn ι).
      Proof. typeclasses eauto. Qed.

      Lemma mon_consume {Γ Σ} (asn : Assertion Σ) (ι : Valuation Σ) :
        Monotonic (MStoreSpec Γ Γ eq) (consume asn ι).
      Proof. typeclasses eauto. Qed.

      Lemma mon_produce_chunk {Γ} (c : SCChunk) :
        Monotonic (MStoreSpec Γ Γ eq) (produce_chunk c).
      Proof. typeclasses eauto. Qed.

      Lemma mon_consume_chunk {Γ} (c : SCChunk) :
        Monotonic (MStoreSpec Γ Γ eq) (consume_chunk c).
      Proof. typeclasses eauto. Qed.

      #[export] Instance mon_read_register {Γ τ} (r : 𝑹𝑬𝑮 τ) :
        Monotonic (MStoreSpec Γ Γ eq) (read_register r).
      Proof. typeclasses eauto. Qed.

      #[export] Instance mon_write_register {Γ τ} (r : 𝑹𝑬𝑮 τ) (v : Val τ) :
        Monotonic (MStoreSpec Γ Γ eq) (write_register (Γ := Γ) r v).
      Proof. apply mon_lift_heapspec, CHeapSpec.mon_write_register. Qed.

    End ProduceConsume.

    Section Exec.

      Definition call_contract {Γ Δ τ} (contract : SepContract Δ τ) (args : CStore Δ) : CStoreSpec Γ Γ (Val τ) :=
        lift_heapspec (CHeapSpec.call_contract contract args).
      Arguments call_contract {Γ Δ τ} !contract args.

      Definition call_lemma {Γ Δ} (lem : Lemma Δ) (vs : CStore Δ) : CStoreSpec Γ Γ unit :=
        lift_heapspec (CHeapSpec.call_lemma lem vs).
      Arguments call_lemma {Γ Δ} !lem vs.

      (* The paper discusses the case that a function call is replaced by
         interpreting the contract instead. However, this is not always
         convenient. We therefore make contracts for functions optional and if a
         function does not have a contract, we continue executing the body of
         the called function. A parameter [inline_fuel] bounds the number of
         allowed levels before failing execution. Therefore, we write the
         executor in an open-recusion style and [Exec] is the closed type of
         such an executor. *)
      Definition Exec := forall Γ τ (s : Stm Γ τ), CStoreSpec Γ Γ (Val τ).

      Section ExecAux.

        (* The executor for "inlining" a call. *)
        Variable rec : Exec.

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
              match CEnv f with
              | Some c => call_contract c args
              | None   => fun POST δ => rec (FunDef f) (fun v _ => POST v δ) args
              end
            | stm_foreign f es =>
              ts <- eval_exps es ;;
              call_contract (CEnvEx f) ts
            | stm_lemmak l es k =>
              ts <- eval_exps es ;;
              _  <- call_lemma (LEnv l) ts ;;
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
              _ <- assume_formula (v = true) ;;
              exec_aux k
            | stm_fail _ s =>
              block
            | stm_pattern_match s pat rhs =>
              v  <- exec_aux s ;;
              '(existT pc δpc) <- demonic_pattern_match pat v ;;
              pushspops δpc (exec_aux (rhs pc))
            | stm_read_register reg =>
                read_register reg
            | stm_write_register reg e =>
                v__new <- eval_exp e ;;
                write_register reg v__new
            | stm_bind s k =>
              v <- exec_aux s ;;
              exec_aux (k v)
            | stm_debugk k =>
              exec_aux k
            end.

        Context {mon_rec : MonotonicExec rec}.

        #[export] Instance mon_exec_aux : MonotonicExec exec_aux.
        Proof.
          intros Γ τ s. induction s; cbn - [Val]; try typeclasses eauto.
          destruct CEnv.
          - typeclasses eauto.
          - intros P Q PQ ? ?. apply mon_rec.
            intros ? ? ? ?. now apply PQ.
        Qed.

      End ExecAux.
      Arguments exec_aux rec {Γ τ} !s.

      (* The constructed closed executor. *)
      Fixpoint exec (inline_fuel : nat) : Exec :=
        match inline_fuel with
        | O   => fun _ _ _ => error
        | S n => @exec_aux (@exec n)
        end.

      #[export] Instance mon_exec fuel : MonotonicExec (exec fuel).
      Proof. induction fuel; cbn; typeclasses eauto. Qed.

    End Exec.
    #[global] Arguments exec _ {_ _} s : simpl never.

    Section WithFuel.

      Variable inline_fuel : nat.

      Import CHeapSpec.notations.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : CHeapSpec unit :=
        match c with
        | MkSepContract _ _ lvars pats req result ens =>
            lenv <- CHeapSpec.demonic_ctx lvars ;;
            _    <- CHeapSpec.produce req lenv ;;
            v    <- evalStoreSpec (exec inline_fuel s) (inst pats lenv) ;;
            CHeapSpec.consume ens (env.snoc lenv (result∷τ) v)
        end.

      Definition vcgen {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        CHeapSpec.run (exec_contract c body).

      Lemma mon_exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
        Monotonic (MHeapSpec eq) (exec_contract c s).
      Proof. destruct c. typeclasses eauto. Qed.

    End WithFuel.

  End CStoreSpec.

  Module Shallow.

    Definition ValidContractWithFuel {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      CStoreSpec.vcgen fuel c body.

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
