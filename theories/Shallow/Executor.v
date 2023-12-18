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
  Definition CHeapSpecM (Γ1 Γ2 : PCtx) (A : Type) : Type :=
    (A -> CStore Γ2 -> SCHeap -> Prop) -> CStore Γ1 -> SCHeap -> Prop.
  Bind Scope mut_scope with CHeapSpecM.

  Local Open Scope mut_scope.

  Module CHeapSpecM.

    Section Basic.

      Definition lift_purem {Γ} {A : Type} :
        CPureSpec A -> CHeapSpecM Γ Γ A :=
        fun m POST δ h => m (fun a => POST a δ h).

      Definition pure {Γ A} (a : A) : CHeapSpecM Γ Γ A :=
        fun POST => POST a.
      Definition bind {Γ1 Γ2 Γ3 A B} (ma : CHeapSpecM Γ1 Γ2 A) (f : A -> CHeapSpecM Γ2 Γ3 B) : CHeapSpecM Γ1 Γ3 B :=
        fun POST => ma (fun a => f a POST).

      Definition error {Γ1 Γ2 A} : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ h => FALSE.
      Definition block {Γ1 Γ2 A} : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ h => TRUE.

      Definition demonic_binary {Γ1 Γ2 A} (m1 m2 : CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h /\ m2 POST δ h.
      Definition angelic_binary {Γ1 Γ2 A} (m1 m2 : CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h \/ m2 POST δ h.

      Definition demonic {Γ} (σ : Ty) : CHeapSpecM Γ Γ (Val σ) :=
        lift_purem (CPureSpec.demonic σ).
      Definition angelic {Γ} (σ : Ty) : CHeapSpecM Γ Γ (Val σ) :=
        lift_purem (CPureSpec.angelic σ).

      Definition angelic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CHeapSpecM Γ Γ (NamedEnv Val Δ) :=
        fun Δ => lift_purem (CPureSpec.angelic_ctx Δ).
      #[global] Arguments angelic_ctx {N Γ} Δ.

      Definition angelic_list {A Γ} (xs : list A) : CHeapSpecM Γ Γ A :=
        lift_purem (CPureSpec.angelic_list xs).

      Definition angelic_finite F `{finite.Finite F} {Γ} : CHeapSpecM Γ Γ F :=
        lift_purem (CPureSpec.angelic_finite F).
      #[global] Arguments angelic_finite F {_ _ Γ}.

      Definition demonic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CHeapSpecM Γ Γ (NamedEnv Val Δ) :=
        fun Δ => lift_purem (CPureSpec.demonic_ctx Δ).
      #[global] Arguments demonic_ctx {N Γ} Δ.

    End Basic.

    Module CHeapSpecMNotations.

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

    End CHeapSpecMNotations.
    Import CHeapSpecMNotations.
    Local Open Scope mut_scope.

    Section AssumeAssert.

      Definition assume_formula {Γ} (fml : Prop) : CHeapSpecM Γ Γ unit :=
        lift_purem (CPureSpec.assume_formula fml).
      Definition assert_formula {Γ} (fml : Prop) : CHeapSpecM Γ Γ unit :=
        lift_purem (CPureSpec.assert_formula fml).
      Definition assert_eq_env {Γ} {Δ : Ctx Ty} (δ δ' : Env Val Δ) : CHeapSpecM Γ Γ unit :=
        lift_purem (CPureSpec.assert_eq_env δ δ').
      Definition assert_eq_nenv {N Γ} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) : CHeapSpecM Γ Γ unit :=
        lift_purem (CPureSpec.assert_eq_nenv δ δ').
      Definition assert_eq_chunk {Γ} (c c' : SCChunk) : CHeapSpecM Γ Γ unit :=
        lift_purem (CPureSpec.assert_eq_chunk c c').

    End AssumeAssert.

    Section PatternMatching.

      Definition angelic_pattern_match {N : Set} {Γ σ} (pat : @Pattern N σ) (v : Val σ) :
        CHeapSpecM Γ Γ (MatchResult pat) :=
        lift_purem (CPureSpec.angelic_pattern_match pat v).
      #[global] Arguments angelic_pattern_match {N Γ σ} pat v.

      Definition demonic_pattern_match {N : Set} {Γ σ} (pat : @Pattern N σ) (v : Val σ) :
        CHeapSpecM Γ Γ (MatchResult pat) :=
        lift_purem (CPureSpec.demonic_pattern_match pat v).
      #[global] Arguments demonic_pattern_match {N Γ σ} pat v.

      Lemma wp_angelic_pattern_match {N : Set} {Γ σ} (pat : @Pattern N σ) (v : Val σ)
        (Φ : MatchResult pat -> CStore Γ -> SCHeap -> Prop) (δ : CStore Γ) (h : SCHeap) :
        angelic_pattern_match pat v Φ δ h <-> Φ (pattern_match_val pat v) δ h.
      Proof.
        unfold angelic_pattern_match, lift_purem.
        now rewrite CPureSpec.wp_angelic_pattern_match.
      Qed.

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
        (d : CHeapSpecM (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.tail δ1)) (δ0 ► (x∷σ ↦ v)).
      Definition pushspops {A} {Γ1 Γ2 Δ} (δΔ : CStore Δ)
        (d : CHeapSpecM (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.drop Δ δ1)) (δ0 ►► δΔ).
      Definition get_local {Γ} : CHeapSpecM Γ Γ (CStore Γ) :=
        fun POST δ => POST δ δ.
      Definition put_local {Γ1 Γ2} (δ : CStore Γ2) : CHeapSpecM Γ1 Γ2 unit :=
        fun POST _ => POST tt δ.
      Definition get_heap {Γ} : CHeapSpecM Γ Γ SCHeap :=
        fun POST δ h => POST h δ h.
      Definition put_heap {Γ} (h : SCHeap) : CHeapSpecM Γ Γ unit :=
        fun POST δ _ => POST tt δ h.

      Definition eval_exp {Γ σ} (e : Exp Γ σ) : CHeapSpecM Γ Γ (Val σ) :=
        fun POST δ => POST (eval e δ) δ.
      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) : CHeapSpecM Γ Γ (CStore σs) :=
        fun POST δ => POST (evals es δ) δ.
      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : Val σ) : CHeapSpecM Γ Γ unit :=
        fun POST δ => POST tt (δ ⟪ x ↦ v ⟫).
      Global Arguments assign {Γ} x {σ xIn} v.

    End State.

    Section ProduceConsume.

      Definition produce_chunk {Γ} (c : SCChunk) : CHeapSpecM Γ Γ unit :=
        fun POST δ h => POST tt δ (cons c h).

      Definition consume_chunk {Γ} (c : SCChunk) : CHeapSpecM Γ Γ unit :=
        h         <- get_heap ;;
        '(c', h') <- angelic_list (heap_extractions h) ;;
        assert_eq_chunk c c' ;;
        put_heap h'.

      Global Arguments produce_chunk {Γ} _.
      Global Arguments consume_chunk {Γ} _.

      Fixpoint produce {Γ Σ} (ι : Valuation Σ) (asn : Assertion Σ) : CHeapSpecM Γ Γ unit :=
        match asn with
        | asn.formula fml => assume_formula (instprop fml ι)
        | asn.chunk c     => produce_chunk (inst c ι)
        | asn.chunk_angelic c => produce_chunk (inst c ι)
        | asn.pattern_match s pat rhs =>
            let v := (inst (T := fun Σ => Term Σ _) s ι) in
            '(existT pc vs) <- demonic_pattern_match pat v ;;
            produce (ι ►► vs) (rhs pc)
        | asn.sep a1 a2   => _ <- produce ι a1 ;; produce ι a2
        | asn.or a1 a2 =>
          demonic_binary (produce ι a1)
                         (produce ι a2)
        | asn.exist ς τ a =>
          v <- demonic τ ;;
          produce (env.snoc ι (ς∷τ) v) a
        | asn.debug => pure tt
        end.

      Fixpoint consume {Γ Σ} (ι : Valuation Σ) (asn : Assertion Σ) : CHeapSpecM Γ Γ unit :=
        match asn with
        | asn.formula fml => assert_formula (instprop fml ι)
        | asn.chunk c     => consume_chunk (inst c ι)
        | asn.chunk_angelic c     => consume_chunk (inst c ι)
        | asn.pattern_match s pat rhs =>
            let v := (inst (T := fun Σ => Term Σ _) s ι) in
            '(existT pc vs) <- angelic_pattern_match pat v ;;
            consume (ι ►► vs) (rhs pc)
        | asn.sep a1 a2   => _ <- consume ι a1;; consume ι a2
        | asn.or a1 a2 =>
          angelic_binary (consume ι a1)
                         (consume ι a2)
        | asn.exist ς τ a =>
          v <- angelic τ ;;
          consume (env.snoc ι (ς∷τ) v) a
        | asn.debug => pure tt
        end.

    End ProduceConsume.

    Section Exec.

      Definition call_contract {Γ Δ τ} (contract : SepContract Δ τ) (args : CStore Δ) : CHeapSpecM Γ Γ (Val τ) :=
        match contract with
        | MkSepContract _ _ Σe δ req result ens =>
          ι <- angelic_ctx Σe ;;
          assert_eq_nenv (inst δ ι) args ;;
          consume ι req  ;;
          v <- demonic τ ;;
          produce (env.snoc ι (result∷τ) v) ens ;;
          pure v
        end.

      Definition call_lemma {Γ Δ} (lem : Lemma Δ) (vs : CStore Δ) : CHeapSpecM Γ Γ unit :=
        match lem with
        | MkLemma _ Σe δ req ens =>
          ι <- angelic_ctx Σe ;;
          assert_eq_nenv (inst δ ι) vs ;;
          consume ι req ;;
          produce ι ens
        end.

      (* The paper discusses the case that a function call is replaced by
         interpreting the contract instead. However, this is not always
         convenient. We therefore make contracts for functions optional and if a
         function does not have a contract, we continue executing the body of
         the called function. A parameter [inline_fuel] bounds the number of
         allowed levels before failing execution. Therefore, we write the
         executor in an open-recusion style and [Exec] is the closed type of
         such an executor. *)
      Definition Exec := forall Γ τ (s : Stm Γ τ), CHeapSpecM Γ Γ (Val τ).

      Section ExecAux.

        (* The executor for "inlining" a call. *)
        Variable rec : Exec.

        (* The openly-recursive executor. *)
        Definition exec_aux : Exec :=
          fix exec_aux {Γ τ} (s : Stm Γ τ) : CHeapSpecM Γ Γ (Val τ) :=
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
              v <- angelic τ ;;
              let c := scchunk_ptsreg reg v in
              _ <- consume_chunk c ;;
              _ <- produce_chunk c ;;
              pure v
            | stm_write_register reg e =>
              v__old <- angelic τ ;;
              _    <- consume_chunk (scchunk_ptsreg reg v__old) ;;
              v__new <- eval_exp e ;;
              _    <- produce_chunk (scchunk_ptsreg reg v__new) ;;
              pure v__new
            | stm_bind s k =>
              v <- exec_aux s ;;
              exec_aux (k v)
            | stm_debugk k =>
              exec_aux k
            end.

      End ExecAux.

      (* The constructed closed executor. *)
      Fixpoint exec (inline_fuel : nat) : Exec :=
        match inline_fuel with
        | O   => fun _ _ _ => error
        | S n => @exec_aux (@exec n)
        end.
      Global Arguments exec _ {_ _} s _ _ _.

    End Exec.

    Section WithFuel.

      Variable inline_fuel : nat.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
       Valuation (sep_contract_logic_variables c) -> CHeapSpecM Δ Δ unit :=
        match c with
        | MkSepContract _ _ _ _ req result ens =>
          fun ι =>
          _ <- produce ι req ;;
          v <- exec inline_fuel s ;;
          consume (env.snoc ι (result∷τ) v) ens
        end%mut.

      Definition vcgen {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        ForallNamed (fun ι : Valuation (sep_contract_logic_variables c) =>
          let δΔ : CStore Δ := inst (sep_contract_localstore c) ι in
          (* We use the FINISH alias of True for the purpose of counting
             nodes in a shallowly-generated VC. *)
          exec_contract c body ι (fun _ _ _ => FINISH) δΔ nil).

    End WithFuel.

  End CHeapSpecM.

  Module Replay.
    Import SymProp.
    Import CPureSpec.

    Definition replay_aux : forall {Σ} (ι : Valuation Σ) (s : 𝕊 Σ),
        CPureSpec unit :=
      fix replay {Σ} ι s :=
        match s with
        | SymProp.angelic_binary o1 o2 =>
            angelic_binary (replay ι o1) (replay ι o2)
        | SymProp.demonic_binary o1 o2 =>
            demonic_binary (replay ι o1) (replay ι o2)
        | SymProp.block =>
            block
        | SymProp.error msg =>
            error
        | SymProp.assertk fml msg k =>
            bind (assert_formula (instprop fml ι))
              (fun _ => replay ι k)
        | SymProp.assumek fml k =>
            bind (assume_formula (instprop fml ι))
              (fun _ => replay ι k)
        | SymProp.angelicv b k =>
            bind (angelic _)
              (fun v => replay (env.snoc ι b v) k)
        | SymProp.demonicv b k =>
            bind (demonic _)
              (fun v => replay (env.snoc ι b v ) k)
        | @SymProp.assert_vareq _ x σ xIn t msg k =>
            let ι' := env.remove (x ∷ σ) ι xIn in
            let x' := ι.[? x∷σ] in
            let t' := inst t ι' in
            bind (assert_formula (x' = t'))
                 (fun _ => replay ι' k)
        | @SymProp.assume_vareq _ x σ xIn t k =>
            let ι' := env.remove (x ∷ σ) ι xIn in
            let x' := ι.[? x∷σ] in
            let t' := inst t ι' in
            bind (assume_formula (x' = t'))
                 (fun _ => replay ι' k)
        | SymProp.pattern_match s pat rhs =>
            error
        | SymProp.pattern_match_var x pat rhs =>
            error
        | SymProp.debug b k =>
            replay ι k
        end.

    Definition replay {Σ} (ι : Valuation Σ) (s : 𝕊 Σ) : Prop :=
      replay_aux ι s (fun _ => TRUE).
  End Replay.

  Module Shallow.

    Definition ValidContractWithFuel {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      CHeapSpecM.vcgen fuel c body.

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      (* Use inline_fuel = 1 by default. *)
      ValidContractWithFuel 1 c body.

    Module Statistics.

      Inductive PropShape : Type :=
      | psfork (P Q : PropShape)
      | psquant (P : PropShape)
      | pspruned
      | psfinish
      | psother.

      Fixpoint shape_to_stats (s : PropShape) : Stats :=
        match s with
        | psfork p q => plus_stats (shape_to_stats p) (shape_to_stats q)
        | psquant p  => shape_to_stats p
        | pspruned   => {| branches := 1; pruned := 1 |}
        | psfinish   => {| branches := 1; pruned := 0 |}
        | psother     => {| branches := 0; pruned := 0 |}
        end.

      (* See: Building a Reification Tactic that Recurses Under Binders
         http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html

         This calculates a deeply-embedded PropShape for a given Prop P
         for which we can then run shape_to_stats to calculate the
         number of different kinds of execution paths. *)
      Ltac reifyProp P :=
        match eval simpl in P with
        | forall (x : ?T), TRUE => pspruned
        | forall (x : ?T), FALSE => pspruned
        | forall (x : ?T), FINISH => psfinish
        | forall (x : ?T), True => psother
        | forall (x : ?T), False => psother
        | forall (x : ?T), @?P1 x /\ @?P2 x =>
          let t1 := reifyProp (forall x : T, P1 x) in
          let t2 := reifyProp (forall x : T, P2 x) in
            constr:(psfork t1 t2)
        | forall (x : ?T), @?P1 x \/ @?P2 x =>
          let t1 := reifyProp (forall x : T, P1 x) in
          let t2 := reifyProp (forall x : T, P2 x) in
            constr:(psfork t1 t2)
        | forall (x : ?T), @?P1 x -> @?P2 x =>
          let t1 := reifyProp (forall x : T, P1 x) in
          let t2 := reifyProp (forall x : T, P2 x) in
            constr:(psfork t1 t2)
        | forall (x : ?T), forall (v : ?U), @?P x v =>
          let t := reifyProp (forall xv : T * U, P (fst xv) (snd xv)) in
            constr:(psquant t)
        | forall (x : ?T), exists (v : ?U), @?P x v =>
          let t := reifyProp (forall xv : T * U, P (fst xv) (snd xv)) in
            constr:(psquant t)
        | forall (x : ?T), _ = _ => psother
        | forall (x : ?T), Z.le _ _ => psother
        (* | _ => constr:(sprop P) *)
        end.

      (* This typeclass approach seems to be much faster than the reifyProp
      tactic above. *)
      Class ShallowStats (P : Prop) :=
        stats : Stats.
      Arguments stats P {_}.

      (* We make these instances global so that users can simply use the
         calc tactic qualified without importing the rest of this module. *)
      #[global] Instance stats_true : ShallowStats TRUE :=
        {| branches := 1; pruned := 1 |}.
      #[global] Instance stats_false : ShallowStats FALSE :=
        {| branches := 1; pruned := 1 |}.
      #[global] Instance stats_finish : ShallowStats FINISH :=
        {| branches := 1; pruned := 0 |}.
      (* We do not count regular True and False towards the statistics
         because they do not (should not) represent leaves of the shallow
         execution. *)
      #[global] Instance stats_true' : ShallowStats True :=
        {| branches := 0; pruned := 0 |}.
      #[global] Instance stats_false' : ShallowStats False :=
        {| branches := 0; pruned := 0 |}.

      #[global] Instance stats_eq {A} {x y : A} : ShallowStats (x = y) :=
        {| branches := 0; pruned := 0 |}.
      #[global] Instance stats_zle {x y : Z} : ShallowStats (Z.le x y) :=
        {| branches := 0; pruned := 0 |}.

      #[global] Instance stats_and `{ShallowStats P, ShallowStats Q} :
        ShallowStats (P /\ Q) := plus_stats (stats P) (stats Q).
      #[global] Instance stats_or `{ShallowStats P, ShallowStats Q} :
        ShallowStats (P \/ Q) := plus_stats (stats P) (stats Q).
      #[global] Instance stats_impl `{ShallowStats P, ShallowStats Q} :
        ShallowStats (P -> Q) := plus_stats (stats P) (stats Q).

      Axiom undefined : forall A, A.

      #[global] Instance stats_forall {A} {B : A -> Prop} {SP : forall a, ShallowStats (B a)} :
        ShallowStats (forall a : A, B a) := SP (undefined A).
      #[global] Instance stats_exists {A} {B : A -> Prop} {SP : forall a, ShallowStats (B a)} :
        ShallowStats (exists a : A, B a) := SP (undefined A).

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
        let s := eval compute in (stats P) in s.

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
