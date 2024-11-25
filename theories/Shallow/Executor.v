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
     Lists.List
     NArith.NArith
     Program.Tactics
     Strings.String
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

  Module CStoreSpec.

    Section Basic.

      Definition evalStoreSpec {Γ1 Γ2 A} :
        CStoreSpec Γ1 Γ2 A -> CStore Γ1 -> CHeapSpec A :=
        fun m δ Φ => m (fun a1 _ => Φ a1) δ.

      Definition lift_purem {Γ} {A : Type} :
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
        lift_purem (CPureSpec.demonic σ).
      Definition angelic {Γ} (σ : Ty) : CStoreSpec Γ Γ (Val σ) :=
        lift_purem (CPureSpec.angelic σ).

      Definition angelic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CStoreSpec Γ Γ (NamedEnv Val Δ) :=
        fun Δ => lift_purem (CPureSpec.angelic_ctx Δ).
      #[global] Arguments angelic_ctx {N Γ} Δ.

      Definition demonic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CStoreSpec Γ Γ (NamedEnv Val Δ) :=
        fun Δ => lift_purem (CPureSpec.demonic_ctx Δ).
      #[global] Arguments demonic_ctx {N Γ} Δ.

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
        lift_purem (CPureSpec.assume_formula fml).
      Definition assert_formula {Γ} (fml : Prop) : CStoreSpec Γ Γ unit :=
        lift_purem (CPureSpec.assert_formula fml).
      Definition assert_pathcondition {Γ} (fml : Prop) : CStoreSpec Γ Γ unit :=
        lift_purem (CPureSpec.assert_pathcondition fml).
      Definition assert_eq_env {Γ} {Δ : Ctx Ty} (δ δ' : Env Val Δ) : CStoreSpec Γ Γ unit :=
        lift_purem (CPureSpec.assert_eq_env δ δ').
      Definition assert_eq_nenv {N Γ} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) : CStoreSpec Γ Γ unit :=
        lift_purem (CPureSpec.assert_eq_nenv δ δ').

    End AssumeAssert.

    Section PatternMatching.

      Definition demonic_pattern_match {N : Set} {Γ σ} (pat : @Pattern N σ) (v : Val σ) :
        CStoreSpec Γ Γ (MatchResult pat) :=
        lift_purem (CPureSpec.demonic_pattern_match pat v).
      #[global] Arguments demonic_pattern_match {N Γ σ} pat v.

      Lemma wp_demonic_pattern_match {N : Set} {Γ σ} (pat : @Pattern N σ) (v : Val σ)
        (Φ : MatchResult pat -> CStore Γ -> SCHeap -> Prop) (δ : CStore Γ) (h : SCHeap) :
        demonic_pattern_match pat v Φ δ h <-> Φ (pattern_match_val pat v) δ h.
      Proof.
        unfold demonic_pattern_match, lift_purem.
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

      End ExecAux.
      Arguments exec_aux rec {Γ τ} !s.

      (* The constructed closed executor. *)
      Fixpoint exec (inline_fuel : nat) : Exec :=
        match inline_fuel with
        | O   => fun _ _ _ => error
        | S n => @exec_aux (@exec n)
        end.
      Global Arguments exec _ {_ _} s _ _ _ : simpl never.

    End Exec.

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
