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
(* TO, THE IMPLIED WARRANTgIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
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
     Classes.RelationClasses
     Classes.Morphisms
     Program.Basics
     Relations.Relation_Definitions.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Base
     Syntax.Assertions
     Syntax.Chunks
     Syntax.Formulas
     Syntax.Predicates.

Import ctx.notations.
Import env.notations.
Import SignatureNotations.

Set Implicit Arguments.

(* A copy of [Proper] to be used in monotonicity proofs. Most of the instances
   we define allow for more automation, but are weaker than what one would
   normally use for [Proper] instances, hence the different type class. *)
Section Monotonic.
  Let U := Type.
  Context {A B : U}.

  Class Monotonic (R : relation A) (m : A) : Prop :=
    monotonic_prf : R m m.
End Monotonic.

#[export] Hint Extern 1 (Monotonic _ (match ?p with existT _ _ => _ end)) =>
  destruct p : typeclass_instances.

#[export] Instance monotonic_specialize_eq_refl
  {A B} {RB : relation B} {f : A -> B} :
  (forall a, Monotonic RB (f a)) -> Monotonic (eq ==> RB) f.
Proof. unfold Monotonic. intros pf ? ? <-. auto. Qed.

#[export] Instance monotonic_eq_refl {A} {a : A} :
  Monotonic eq a.
Proof. easy. Qed.

Class RelM (M : Type -> Type) :=
  RM : forall {A}, relation A -> relation (M A).
Arguments RM {_ _ _} _%signature_scope.

Module Type ShallowMonadInterfaceOn
  (Import B : Base)
  (Import PK   : PredicateKit B)
  (Import FML  : FormulasOn B PK)
  (Import CHK  : ChunksOn B PK)
  (Import ASN  : AssertionsOn B PK FML CHK).

  (* This is used by potentially multiple instances, but ultimately should be
     moved somewhere else. *)
  Section WithBI.

    Import iris.bi.interface iris.bi.extensions iris.bi.derived_laws.

    Context {L} {biA : BiAffine L} {PI : PredicateDef L}.

    Lemma scchunk_duplicate (c : SCChunk) :
      is_duplicable c = true ->
      interpret_scchunk c ⊣⊢@{L} interpret_scchunk c ∗ interpret_scchunk c.
    Proof.
      destruct c; cbn; try discriminate; intros H.
      apply bi.entails_anti_sym.
      - now apply lduplicate.
      - transitivity (luser p vs ∗ emp)%I.
        + apply bi.sep_mono'; auto.
        + now rewrite bi.sep_emp.
    Qed.

    Lemma in_heap_extractions {h : SCHeap} {c1 h1}
      (hyp : List.In (c1 , h1) (heap_extractions h)) :
      interpret_scheap h ⊣⊢@{L} interpret_scchunk c1 ∗ interpret_scheap h1.
    Proof.
      revert c1 h1 hyp.
      induction h; cbn -[is_duplicable]; intros.
      - contradict hyp.
      - destruct hyp as [hyp|hyp].
        + destruct (is_duplicable a) eqn:Heqdup;
            inversion hyp; subst; clear hyp; cbn.
          * rewrite bi.sep_assoc -scchunk_duplicate; auto.
          * reflexivity.
        + cbn in *.
          apply List.in_map_iff in hyp.
          destruct hyp as [[c2 h2] [H1 H2]].
          inversion H1; subst; clear H1; cbn.
          apply IHh in H2; rewrite H2; clear IHh H2.
          rewrite !bi.sep_assoc.
          apply bi.sep_proper; [|easy].
          now rewrite bi.sep_comm.
    Qed.

  End WithBI.

  Module Import CPureSpecM.

    Class CPureSpecM (M : Type -> Type) : Type :=
      { pure {A} :  A -> M A;
        bind {A B} : M A -> (A -> M B) -> M B;
        error {A} : M A;
        block {A} : M A;
        angelic (σ : Ty) : M (Val σ);
        demonic (σ : Ty) : M (Val σ);
        angelic_ctx {N : Set} (Δ : NCtx N Ty) : M (NamedEnv Val Δ);
        demonic_ctx {N : Set} (Δ : NCtx N Ty) : M (NamedEnv Val Δ);
        assert_pathcondition : Prop -> M unit;
        assert_formula : Prop -> M unit;
        assume_pathcondition : Prop -> M unit;
        assume_formula : Prop -> M unit;
        angelic_binary {A} : M A -> M A -> M A;
        demonic_binary {A} : M A -> M A -> M A;
        angelic_pattern_match {N σ} (pat : @Pattern N σ) :
          Val σ -> M (MatchResult pat);
        demonic_pattern_match {N σ} (pat : @Pattern N σ) :
          Val σ -> M (MatchResult pat);
        new_pattern_match {N σ} (pat : @Pattern N σ) :
          Val σ -> M (MatchResult pat);
        debug {A} : M A -> M A;
      }.

    #[global] Arguments pure {M CPureSpecM A} _.
    #[global] Arguments bind {M CPureSpecM A B} m f.
    #[global] Arguments block {M CPureSpecM A}.
    #[global] Arguments angelic {M CPureSpecM} σ.
    #[global] Arguments demonic {M CPureSpecM} σ.
    #[global] Arguments angelic_binary {M CPureSpecM A} _ _.
    #[global] Arguments demonic_binary {M CPureSpecM A} _ _.

    Module Import notations.
      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at level 90, mb at level 200, right associativity).
      Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, x pattern,
           ma at next level, mb at level 200,
           right associativity).
      Notation "ma ;; mb" := (bind ma (fun _ => mb)).
    End notations.

    Class MPureSpecM M {pureM : CPureSpecM M} {relM : RelM M} : Type :=
      { mon_pure `{RA : relation A} ::
          Monotonic (RA ==> RM RA) pure;
        mon_bind `{RA : relation A, RB : relation B} ::
          Monotonic (RM RA ==> (RA ==> RM RB) ==> RM RB) bind;
        mon_error `{RA : relation A} ::
          Monotonic (RM RA) error;
        mon_block `{RA : relation A} ::
          Monotonic (RM RA) block;
        mon_angelic (σ : Ty) ::
          Monotonic (RM eq) (angelic σ);
        mon_demonic (σ : Ty) ::
          Monotonic (RM eq) (demonic σ);
        mon_angelic_ctx {N : Set} {Δ} ::
          Monotonic (RM eq) (@angelic_ctx _ _ N Δ);
        mon_demonic_ctx {N : Set} {Δ} ::
          Monotonic (RM eq) (@demonic_ctx _ _ N Δ);
        mon_assert_pathcondition pc ::
          Monotonic (RM eq) (assert_pathcondition pc);
        mon_assert_formula fml ::
          Monotonic (RM eq) (assert_formula fml);
        mon_assume_pathcondition pc ::
          Monotonic (RM eq) (assume_pathcondition pc);
        mon_assume_formula fml ::
          Monotonic (RM eq) (assume_formula fml);
        mon_angelic_binary `{RA : relation A} m1 m2 ::
          Monotonic (RM RA) m1 -> Monotonic (RM RA) m2 ->
           Monotonic (RM RA) (angelic_binary m1 m2);
        mon_demonic_binary `{RA : relation A} m1 m2 ::
          Monotonic (RM RA) m1 -> Monotonic (RM RA) m2 ->
          Monotonic (RM RA) (demonic_binary m1 m2);
        mon_angelic_pattern_match {N σ} (pat : @Pattern N σ) (v : Val σ) ::
          Monotonic (RM eq) (angelic_pattern_match pat v);
        mon_demonic_pattern_match {N σ} (pat : @Pattern N σ) (v : Val σ) ::
          Monotonic (RM eq) (demonic_pattern_match pat v);
        mon_new_pattern_match {N σ} (pat : @Pattern N σ) (v : Val σ) ::
          Monotonic (RM eq) (new_pattern_match pat v);
        mon_debug `{RA : relation A} m ::
          Monotonic (RM RA) m -> Monotonic (RM RA) (debug m);
      }.
    #[global] Arguments MPureSpecM _ {_ _}.

    #[export] Instance mon_pure' `{MPureSpecM M, RA : relation A} (a : A) :
      Monotonic RA a -> Monotonic (RM RA) (pure a).
    Proof. intros ra. now apply mon_pure. Qed.

    #[export] Instance mon_bind' `{MPureSpecM M, RA : relation A, RB : relation B}
      (m : M A) (f : A -> M B) :
      Monotonic (RM RA) m -> Monotonic (RA ==> RM RB) f -> Monotonic (RM RB) (bind m f).
    Proof. intros rm rf. eapply mon_bind; eauto. Qed.

    Section Derived.
      Context {M} {pureM : CPureSpecM M}.

      (* The paper uses asserted equalities between multiple types, but the
       symbolic executor can in fact only assert equalities between symbolic
       terms. We mirror the structure of the symbolic execution and also
       traverse (the statically known parts) of other data structures. *)
      Equations(noeqns) assert_eq_env [Δ : Ctx Ty]
        (δ δ' : Env Val Δ) : M unit :=
        assert_eq_env env.nil          env.nil            := pure tt;
        assert_eq_env (env.snoc δ _ t) (env.snoc δ' _ t') :=
          bind (assert_eq_env δ δ') (fun _ => assert_formula (t = t')).

      Equations(noeqns) assert_eq_nenv {N : Set} [Δ : NCtx N Ty]
        (δ δ' : NamedEnv Val Δ) : M unit :=
        assert_eq_nenv env.nil          env.nil            := pure tt;
        assert_eq_nenv (env.snoc δ _ t) (env.snoc δ' _ t') :=
          bind (assert_eq_nenv δ δ') (fun _ => assert_formula (t = t')).

      Equations(noeqns) assume_eq_env [Δ : Ctx Ty]
        (δ δ' : Env Val Δ) : M unit :=
        assume_eq_env env.nil          env.nil            := pure tt;
        assume_eq_env (env.snoc δ _ t) (env.snoc δ' _ t') :=
          bind (assume_eq_env δ δ') (fun _ => assume_formula (t = t')).

      Equations(noeqns) assume_eq_nenv {N : Set} [Δ : NCtx N Ty]
        (δ δ' : NamedEnv Val Δ) : M unit :=
        assume_eq_nenv env.nil          env.nil            := pure tt;
        assume_eq_nenv (env.snoc δ _ t) (env.snoc δ' _ t') :=
          bind (assume_eq_nenv δ δ') (fun _ => assume_formula (t = t')).

      Fixpoint assert_eq_chunk (c1 c2 : SCChunk) : M unit :=
        match c1 , c2 with
        | scchunk_user p1 vs1 , scchunk_user p2 vs2 =>
            match eq_dec p1 p2 with
            | left e => assert_eq_env (eq_rect p1 (fun p => Env Val (𝑯_Ty p)) vs1 p2 e) vs2
            | right _ => error
            end
        | scchunk_ptsreg r1 v1 , scchunk_ptsreg r2 v2 =>
            match eq_dec_het r1 r2 with
            | left e => assert_formula (eq_rect _ Val v1 _ (f_equal projT1 e) = v2)
            | right _ => error
            end
        | scchunk_conj c11 c12 , scchunk_conj c21 c22 =>
            assert_eq_chunk c11 c21 ;; assert_eq_chunk c12 c22
        | scchunk_wand c11 c12 , scchunk_wand c21 c22 =>
            assert_eq_chunk c11 c21 ;; assert_eq_chunk c12 c22
        | _ , _ => error
        end.

      Context {relM : RelM M} {rpureM : MPureSpecM M}.

      #[export] Instance mon_assert_eq_env {Δ E1 E2} :
        Monotonic (RM eq) (@assert_eq_env Δ E1 E2).
      Proof. induction E1; env.destroy E2; cbn; typeclasses eauto. Qed.

      #[export] Instance mon_assert_eq_nenv {N Δ E1 E2} :
        Monotonic (RM eq) (@assert_eq_nenv N Δ E1 E2).
      Proof. induction E1; env.destroy E2; cbn; typeclasses eauto. Qed.

      #[export] Instance mon_assume_eq_env {Δ E1 E2} :
        Monotonic (RM eq) (@assume_eq_env Δ E1 E2).
      Proof. induction E1; env.destroy E2; cbn; typeclasses eauto. Qed.

      #[export] Instance mon_assume_eq_nenv {N Δ E1 E2} :
        Monotonic (RM eq) (@assume_eq_nenv N Δ E1 E2).
      Proof. induction E1; env.destroy E2; cbn; typeclasses eauto. Qed.

      #[export] Instance mon_assert_eq_chunk {c1 c2} :
        Monotonic (RM eq) (@assert_eq_chunk c1 c2).
      Proof.
        revert c2; induction c1; intros []; cbn;
          try match goal with
            | |- context[eq_dec ?p ?q] =>
                destruct (eq_dec p q); subst; cbn
            | |- context[eq_dec_het ?p ?q] =>
                destruct (eq_dec_het p q)
            end; typeclasses eauto.
      Qed.

    End Derived.

  End CPureSpecM.
  Export CPureSpecM (CPureSpecM).

  Module Import CHeapSpecM.

    Import CPureSpecM CPureSpecM.notations.

    Class CHeapSpecM (M : Type -> Type) : Type :=
      { produce_chunk : SCChunk -> M unit;
        consume_chunk : SCChunk -> M unit;
      }.

    Class MHeapSpecM M {heapM : CHeapSpecM M} {relM : RelM M} : Type :=
      { mon_produce_chunk c :: Monotonic (RM eq) (produce_chunk c);
        mon_consume_chunk c :: Monotonic (RM eq) (consume_chunk c);
      }.
    #[global] Arguments MHeapSpecM M {_ _}.

  End CHeapSpecM.
  Export CHeapSpecM (CHeapSpecM).

  Module CReaderT.
    Section WithRM.

      Context {R : Type} `{pureM : CPureSpecM M}.

      Definition CReaderT (A : Type) : Type :=
        R -> M A.

      Definition evalCReaderT {A} : CReaderT A -> R -> M A :=
        fun m => m.

      Definition liftM {A} :
        M A -> CReaderT A := fun m _ => m.

      #[export] Instance purespecm : CPureSpecM CReaderT :=
        {| pure A a                        := liftM (pure a);
           bind A B m f r                  := bind (m r) (fun a : A => f a r);
           error A                         := liftM error;
           block A                         := liftM block;
           angelic σ                       := liftM (angelic σ);
           demonic σ                       := liftM (demonic σ);
           angelic_ctx N Δ                 := liftM (angelic_ctx Δ);
           demonic_ctx N Δ                 := liftM (demonic_ctx Δ);
           assert_pathcondition C          := liftM (assert_pathcondition C);
           assert_formula fml              := liftM (assert_formula fml);
           assume_pathcondition C          := liftM (assume_pathcondition C);
           assume_formula fml              := liftM (assume_formula fml);
           angelic_binary A m1 m2 r        := angelic_binary (m1 r) (m2 r);
           demonic_binary A m1 m2 r        := demonic_binary (m1 r) (m2 r);
           angelic_pattern_match N σ pat t := liftM (angelic_pattern_match pat t);
           demonic_pattern_match N σ pat t := liftM (demonic_pattern_match pat t);
           new_pattern_match N σ p t       := liftM (new_pattern_match p t);
           debug A m                       := m;
        |}.

      Context {heapM : CHeapSpecM M}.

      #[export] Instance heapspecm : CHeapSpecM CReaderT :=
        {| produce_chunk c := liftM (produce_chunk c);
           consume_chunk c := liftM (consume_chunk c);
        |}.

      Context {relM : RelM M} {rpureM : MPureSpecM M}.

      #[export] Instance MReaderT : RelM CReaderT :=
        fun A RA => pointwise_relation R (RM RA).

      #[export] Instance mon_evalCReaderT `{RA : relation A} m r :
        Monotonic (RM RA) m -> Monotonic (RM RA) (evalCReaderT m r).
      Proof. intros mon_m. apply mon_m. Qed.

      #[export] Instance mon_liftM `{RA : relation A} :
        Monotonic (RM RA ==> RM RA) liftM.
      Proof. intros m1 m2 mon_m ?. exact mon_m. Qed.

      #[export] Instance mon_liftM' `{RA : relation A} (m : M A) :
        Monotonic (RM RA) m -> Monotonic (RM RA) (liftM m).
      Proof. intros rm ?. exact rm. Qed.

      #[export] Instance mon_purespecm : MPureSpecM CReaderT.
      Proof.
        constructor; cbn; intros *; try typeclasses eauto.
        - intros ? ? ra. now apply mon_liftM, mon_pure.
        - intros m1 m2 mon_m f1 f2 mon_f r. eapply mon_bind.
          apply mon_m. intros ? ? mon_a. now apply mon_f.
        - intros * mon_m1 mon_m2 r. apply mon_angelic_binary.
          apply mon_m1. apply mon_m2.
        - intros * mon_m1 mon_m2 r. apply mon_demonic_binary.
          apply mon_m1. apply mon_m2.
      Qed.

    End WithRM.
    #[global] Arguments CReaderT R M A : clear implicits.
  End CReaderT.
  Export (hints) CReaderT.
  Export CReaderT (CReaderT, evalCReaderT).

  Module CProduceConsumeReader.
  Section CProduceConsumeReader.

    Context {M} {pureM : CPureSpecM M} {heapM : CHeapSpecM M}.
    Import CPureSpecM.notations.

    Definition pureInst {Σ} `{Inst AT A} (a : AT Σ) : CReaderT (Valuation Σ) M A :=
      fun ι => pure (inst a ι).
    #[global] Arguments pureInst {Σ AT A _} a.

    Definition pureInstProp {Σ} `{InstProp A} (a : A Σ) : CReaderT (Valuation Σ) M Prop :=
      fun ι => pure (instprop a ι).
    #[global] Arguments pureInstProp {Σ A _} a.

    Definition cpush {A Σ x σ} :
      Val σ -> CReaderT (Valuation (Σ ▻ x∷σ)) M A -> CReaderT (Valuation Σ) M A :=
      fun v m δ1 => m δ1.[x∷σ ↦ v].

    Definition cpushs {A Σ Δ} :
      Valuation Δ -> CReaderT (Valuation (Σ ▻▻ Δ)) M A -> CReaderT (Valuation Σ) M A :=
      fun δΔ m δΣ => m (δΣ ►► δΔ).

    Fixpoint cproduce {Σ} (asn : Assertion Σ) : CReaderT (Valuation Σ) M unit :=
      match asn with
      | asn.formula fml =>
          fml' <- pureInstProp fml;;
          assume_formula fml'
      | asn.chunk c =>
          c' <- pureInst c;;
          produce_chunk c'
      | asn.chunk_angelic c =>
          c' <- pureInst c;;
          produce_chunk c'
      | asn.pattern_match s pat rhs =>
          s'               <- pureInst s;;
          '(existT pc δpc) <- demonic_pattern_match pat s' ;;
          cpushs δpc (cproduce (rhs pc))
      | asn.sep a1 a2 =>
          _ <- cproduce a1 ;;
          cproduce a2
      | asn.or a1 a2 =>
          demonic_binary (cproduce a1) (cproduce a2)
      | asn.exist ς τ a =>
          t <- demonic τ;;
          cpush t (cproduce a)
      | asn.debug =>
          debug
            (pure tt)
      end.

    Fixpoint cconsume {Σ} (asn : Assertion Σ) : CReaderT (Valuation Σ) M unit :=
      match asn with
      | asn.formula fml =>
          fml' <- pureInstProp fml;;
          assert_formula fml'
      | asn.chunk c =>
          c' <- pureInst c;;
          consume_chunk c'
      | asn.chunk_angelic c =>
          c' <- pureInst c;;
          consume_chunk c'
      | asn.pattern_match s pat rhs =>
          s'               <- pureInst s;;
          '(existT pc δpc) <- angelic_pattern_match pat s' ;;
          cpushs δpc (cconsume (rhs pc))
      | asn.sep a1 a2 =>
          _ <- cconsume a1 ;;
          cconsume a2
      | asn.or a1 a2 =>
          angelic_binary (cconsume a1) (cconsume a2)
      | asn.exist ς τ a =>
          t <- angelic τ;;
          cpush t (cconsume a)
      | asn.debug =>
          debug
            (pure tt)
      end.

    Definition ccall_contract [Δ τ] (c : SepContract Δ τ) (args : CStore Δ) : M (Val τ) :=
      match c with
      | MkSepContract _ _ Σe δ req result ens =>
          ι <- angelic_ctx Σe ;;
          assert_eq_nenv (inst δ ι) args ;;
          evalCReaderT (cconsume req) ι ;;
          v <- demonic τ ;;
          evalCReaderT (cproduce ens) (env.snoc ι (result∷τ) v) ;;
          pure v
      end.

    Definition ccall_lemma [Δ] (lem : Lemma Δ) (vs : CStore Δ) : M unit :=
      match lem with
      | MkLemma _ Σe δ req ens =>
          ι <- angelic_ctx Σe ;;
          assert_eq_nenv (inst δ ι) vs ;;
          evalCReaderT (cconsume req) ι ;;
          evalCReaderT (cproduce ens) ι
      end.

    Context {relM : RelM M} {mpureM : MPureSpecM M} {mheapM : MHeapSpecM M}.

    #[export] Instance mon_pureInstProp {Σ} `{InstProp A} (a : A Σ) :
      Monotonic (RM eq) (pureInstProp a).
    Proof. intros ι. now apply mon_pure. Qed.

    #[export] Instance mon_pureInst {Σ} `{Inst AT A} (a : AT Σ) :
      Monotonic (RM eq) (pureInst a).
    Proof. intros ι. now apply mon_pure. Qed.

    #[export] Instance mon_push `{RA : relation A} {Σ x σ} (v : Val σ) :
      Monotonic (RM RA ==> RM RA) (cpush (Σ := Σ) (x := x) v).
    Proof. intros ? ? rm δΣ. apply rm. Qed.

    #[export] Instance mon_push' `{RA : relation A} {Σ x σ} (v : Val σ) m :
      Monotonic (RM RA) m -> Monotonic (RM RA) (cpush (Σ := Σ) (x := x) v m).
    Proof. intros rm δΣ. apply rm. Qed.

    #[export] Instance mon_pushs `{RA : relation A} {Σ Δ} (δΔ : Valuation Δ) :
      Monotonic (RM RA ==> RM RA) (cpushs (Σ := Σ) δΔ).
    Proof. intros ? ? rm δΣ. apply rm. Qed.

    #[export] Instance mon_pushs' `{RA : relation A} {Σ Δ} (δΔ : Valuation Δ) m :
      Monotonic (RM RA) m -> Monotonic (RM RA) (cpushs (Σ := Σ) δΔ m).
    Proof. intros rm δΣ. apply rm. Qed.

    #[export] Instance mon_produce {Σ} (asn : Assertion Σ) :
      Monotonic (RM eq) (cproduce asn).
    Proof. induction asn; typeclasses eauto. Qed.

    #[export] Instance mon_consume {Σ} (asn : Assertion Σ) :
      Monotonic (RM eq) (cconsume asn).
    Proof. induction asn; typeclasses eauto. Qed.

    #[export] Instance mon_call_contract
      [Δ τ] (c : SepContract Δ τ) (args : CStore Δ) :
      Monotonic (RM eq) (ccall_contract c args).
    Proof. destruct c; typeclasses eauto. Qed.

    #[export] Instance mon_call_lemma
      [Δ] (lem : Lemma Δ) (vs : CStore Δ) :
      Monotonic (RM eq) (ccall_lemma lem vs).
    Proof. destruct lem; typeclasses eauto. Qed.

  End CProduceConsumeReader.
  End CProduceConsumeReader.

  Section ProduceConsume.

    Context {M} {pureM : CPureSpecM M} {heapM : CHeapSpecM M}.
    Import CPureSpecM.notations.

    Fixpoint cproduce {Σ} (asn : Assertion Σ) (ι : Valuation Σ) : M unit :=
      match asn with
      | asn.formula fml =>
          assume_formula (instprop fml ι)
      | asn.chunk c =>
          produce_chunk (inst c ι)
      | asn.chunk_angelic c =>
          produce_chunk (inst c ι)
      | asn.pattern_match s pat rhs =>
          '(existT pc δpc) <- demonic_pattern_match pat (inst s ι) ;;
          cproduce (rhs pc) (ι ►► δpc)
      | asn.sep a1 a2 =>
          _ <- cproduce a1 ι ;;
          cproduce a2 ι
      | asn.or a1 a2 =>
          demonic_binary (cproduce a1 ι) (cproduce a2 ι)
      | asn.exist ς τ a =>
          t <- demonic τ;;
          cproduce a (env.snoc ι (ς∷τ) t)
      | asn.debug =>
          debug
            (pure tt)
      end.

    Fixpoint cconsume {Σ} (asn : Assertion Σ) (ι : Valuation Σ) : M unit :=
      match asn with
      | asn.formula fml =>
          assert_formula (instprop fml ι)
      | asn.chunk c =>
          consume_chunk (inst c ι)
      | asn.chunk_angelic c =>
          consume_chunk (inst c ι)
      | asn.pattern_match s pat rhs =>
          '(existT pc δpc) <- angelic_pattern_match pat (inst s ι) ;;
          cconsume (rhs pc) (ι ►► δpc)
      | asn.sep a1 a2 =>
          _ <- cconsume a1 ι ;;
          cconsume a2 ι
      | asn.or a1 a2 =>
          angelic_binary (cconsume a1 ι) (cconsume a2 ι)
      | asn.exist ς τ a =>
          t <- angelic τ;;
          cconsume a (env.snoc ι (ς∷τ) t)
      | asn.debug =>
          debug
            (pure tt)
      end.

    Definition ccall_contract [Δ τ] (c : SepContract Δ τ) (args : CStore Δ) : M (Val τ) :=
      match c with
      | MkSepContract _ _ Σe δ req result ens =>
          ι <- angelic_ctx Σe ;;
          assert_eq_nenv (inst δ ι) args ;;
          cconsume req ι ;;
          v <- demonic τ ;;
          cproduce ens (env.snoc ι (result∷τ) v) ;;
          pure v
      end.

    Definition ccall_lemma [Δ] (lem : Lemma Δ) (vs : CStore Δ) : M unit :=
      match lem with
      | MkLemma _ Σe δ req ens =>
          ι <- angelic_ctx Σe ;;
          assert_eq_nenv (inst δ ι) vs ;;
          cconsume req ι ;;
          cproduce ens ι
      end.

    Context {relM : RelM M} {mpureM : MPureSpecM M} {mheapM : MHeapSpecM M}.

    #[export] Instance mon_produce {Σ} (asn : Assertion Σ) ι :
      Monotonic (RM eq) (cproduce asn ι).
    Proof. induction asn; typeclasses eauto. Qed.

    #[export] Instance mon_consume {Σ} (asn : Assertion Σ) ι :
      Monotonic (RM eq) (cconsume asn ι).
    Proof. induction asn; typeclasses eauto. Qed.

    #[export] Instance mon_call_contract
      [Δ τ] (c : SepContract Δ τ) (args : CStore Δ) :
      Monotonic (RM eq) (ccall_contract c args).
    Proof. destruct c; typeclasses eauto. Qed.

    #[export] Instance mon_call_lemma
      [Δ] (lem : Lemma Δ) (vs : CStore Δ) :
      Monotonic (RM eq) (ccall_lemma lem vs).
    Proof. destruct lem; typeclasses eauto. Qed.

  End ProduceConsume.

End ShallowMonadInterfaceOn.
