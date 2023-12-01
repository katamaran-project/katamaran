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
     Classes.Morphisms.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Base
     Syntax.Assertions
     Syntax.Chunks
     Syntax.Formulas
     Syntax.Predicates
     Symbolic.Worlds.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type SymbolicMonadInterfaceOn
  (Import B    : Base)
  (Import PK   : PredicateKit B)
  (Import FML  : FormulasOn B PK)
  (Import CHK  : ChunksOn B PK)
  (Import ASN  : AssertionsOn B PK FML CHK)
  (Import WRLD : WorldsOn B PK FML CHK).

  Import ModalNotations.
  Local Open Scope modal.

  (* Unused, but don't let it bitrot. *)
  Module WorldInstance.

    Record WInstance (w : World) : Set :=
      MkWInstance
        { ιassign :> Valuation w;
          ιvalid  : instprop (wco w) ιassign;
        }.

    Program Definition winstance_formula {w} (ι : WInstance w) (fml : Formula w) (p : instprop fml ι) :
      WInstance (wformula w fml) :=
      {| ιassign := ι; |}.
    Next Obligation.
    Proof. intros. cbn. split; auto. apply ιvalid. Qed.

    Program Definition winstance_snoc {w} (ι : WInstance w) {b : LVar ∷ Ty} (v : Val (type b)) :
      WInstance (wsnoc w b) :=
      {| ιassign := env.snoc (ιassign ι) b v; |}.
    Next Obligation.
    Proof.
      intros. unfold wsnoc. cbn [wctx wco].
      rewrite instprop_subst, inst_sub_wk1.
      apply ιvalid.
    Qed.

    Program Definition winstance_subst {w} (ι : WInstance w) {x σ} {xIn : x∷σ ∈ w}
      (t : Term (w - x∷σ) σ) (p : inst t (env.remove (x∷σ) (ιassign ι) xIn) = env.lookup (ιassign ι) xIn) :
      WInstance (wsubst w x t) :=
      @MkWInstance (wsubst w x t) (env.remove _ (ιassign ι) xIn) _.
    Next Obligation.
      intros * p. cbn. rewrite instprop_subst, <- inst_sub_shift in *.
      rewrite inst_sub_single_shift; auto using ιvalid.
    Qed.

    Program Definition instacc {w0 w1} (ω01 : w0 ⊒ w1) : WInstance w1 -> WInstance w0 :=
      match ω01 in (_ ⊒ w) return (WInstance w -> WInstance w0) with
      | acc_refl            => fun ι => ι
      | @acc_sub _ w1 ζ ent => fun ι1 => {| ιassign := inst ζ ι1; |}
      end.
    Next Obligation.
    Proof.
      intros. specialize (ent ι1).
      rewrite <- instprop_subst.
      apply ent.
      apply ιvalid.
    Qed.

  End WorldInstance.

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

  End DebugInfo.

  Local Hint Extern 2 (Persistent (WTerm ?σ)) =>
          refine (@persistent_subst (STerm σ) (@SubstTerm σ)) : typeclass_instances.
  Local Hint Extern 2 (Persistent (fun w : World => NamedEnv (Term (wctx w)) ?Γ)) =>
          refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.
  Local Hint Extern 2 (Persistent (fun w : World => @Env _ (fun xt => Term (wctx w) (type  xt)) ?Γ)) =>
          refine (@persistent_subst (fun Σ : LCtx => NamedEnv (Term Σ) Γ) _) : typeclass_instances.

  Module Import SPureSpecM.

    Class SPureSpecM (M : TYPE -> TYPE) : Type :=
      { pure {A} : ⊢ A -> M A;
        bind {A B} : ⊢ M A -> □(A -> M B) -> M B;
        error {A} : ⊢ □(SHeap -> AMessage) -> M A;
        block {A} : ⊢ M A;
        angelic (x : option LVar) : ⊢ ∀ σ, M (STerm σ);
        demonic (x : option LVar) : ⊢ ∀ σ, M (STerm σ);
        angelic_ctx {N : Set} (n : N -> LVar) :
          ⊢ ∀ Δ : NCtx N Ty, M (fun w => NamedEnv (Term w) Δ);
        demonic_ctx {N : Set} (n : N -> LVar) :
          ⊢ ∀ Δ : NCtx N Ty, M (fun w => NamedEnv (Term w) Δ);
        assert_pathcondition : ⊢ □(SHeap -> AMessage) -> PathCondition -> M Unit;
        assert_formula : ⊢ □(SHeap -> AMessage) -> Formula -> M Unit;
        assume_pathcondition : ⊢ PathCondition -> M Unit;
        assume_formula : ⊢ Formula -> M Unit;
        angelic_binary {A} : ⊢ M A -> M A -> M A;
        demonic_binary {A} : ⊢ M A -> M A -> M A;
        demonic_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) :
          ⊢ STerm σ -> M (SMatchResult pat);
        angelic_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) :
          ⊢ □(SHeap -> AMessage) -> STerm σ -> M (SMatchResult pat);
        new_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) :
          ⊢ STerm σ -> M (SMatchResult pat);
        debug {A} : ⊢ □(SHeap -> AMessage) -> M A -> M A;
      }.

    #[global] Arguments pure {M SPureSpecM A} [w] _.
    #[global] Arguments angelic {M SPureSpecM} x [w] i.
    #[global] Arguments bind {M SPureSpecM A B} [w] m f.
    #[global] Arguments block {M SPureSpecM A w}.
    #[global] Arguments angelic {M SPureSpecM} x [w] σ : rename.
    #[global] Arguments demonic {M SPureSpecM} x [w] σ : rename.
    #[global] Arguments angelic_ctx {_ _ _} n%function_scope [w] Δ : rename.
    #[global] Arguments demonic_ctx {_ _ _} n%function_scope [w] Δ : rename.
    #[global] Arguments angelic_binary {M SPureSpecM A} [w] _ _.
    #[global] Arguments demonic_binary {M SPureSpecM A} [w] _ _.
    #[global] Arguments debug {M SPureSpecM A} [w] _ _.

    Module Import notations.
      Notation "⟨ ω ⟩ x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 80, x at next level,
            ma at next level, mb at level 200,
            right associativity).
      Notation "⟨ ω ⟩ ' x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 80, x pattern,
           ma at next level, mb at level 200,
           right associativity).
      (* Notation "⟨ w , ω ⟩ x <- ma ;; mb" := *)
      (*   (bind ma (fun w ω x => mb)) *)
      (*     (at level 80, x at next level, *)
      (*       ma at next level, mb at level 200, *)
      (*       right associativity, only printing). *)
      Notation "x ⟨ ω ⟩" := (persist x ω).
    End notations.

    Section Derived.
      Context {M} {pureSpecM : SPureSpecM M}.

      Equations(noeqns) assert_eq_env :
        let E Δ := fun w : World => Env (Term w) Δ in
        ⊢ ∀ Δ : Ctx Ty, □(SHeap -> AMessage) -> E Δ -> E Δ -> M Unit :=
        assert_eq_env msg env.nil          env.nil            := pure tt;
        assert_eq_env msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
          ⟨ θ ⟩ _ <- assert_eq_env msg δ δ' ;;
          assert_formula (four msg θ) (formula_relop bop.eq t t')⟨θ⟩.

      Equations(noeqns) assert_eq_nenv {N} :
        let E Δ := fun w : World => NamedEnv (Term w) Δ in
        ⊢ ∀ Δ : NCtx N Ty, □(SHeap -> AMessage) -> E Δ -> E Δ -> M Unit :=
        assert_eq_nenv msg env.nil          env.nil            := pure tt;
        assert_eq_nenv msg (env.snoc δ _ t) (env.snoc δ' _ t') :=
          ⟨ θ ⟩ _ <- assert_eq_nenv msg δ δ' ;;
          assert_formula (four msg θ) (formula_relop bop.eq t t')⟨θ⟩.

      Definition assert_eq_chunk : ⊢ □(SHeap -> AMessage) -> Chunk -> Chunk -> □(M Unit) :=
        fix assert_eq w0 msg c1 c2 w1 θ1 {struct c1} :=
          match c1 , c2 with
          | chunk_user p1 vs1 as c1 , chunk_user p2 vs2 as c2 =>
              match eq_dec p1 p2 with
              | left e => assert_eq_env (four msg θ1)
                            (eq_rect p1 (fun p => Env (Term w1) (𝑯_Ty p)) vs1⟨θ1⟩ p2 e)
                            (persist (A := fun w => (fun Σ => Env (Term Σ) _) (wctx w)) vs2 θ1)
              | right _ => error msg⟨θ1⟩
              end
          | chunk_ptsreg r1 v1 as c1 , chunk_ptsreg r2 v2 as c2 =>
              match eq_dec_het r1 r2 with
              | left e => assert_formula (four msg θ1)
                            (formula_relop bop.eq (eq_rect _ (Term w1) v1⟨θ1⟩ _ (f_equal projT1 e)) v2⟨θ1⟩)
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

    End Derived.

  End SPureSpecM.
  Export (hints) SPureSpecM.
  Export SPureSpecM (SPureSpecM).

  Module Import SHeapSpecM.

    Import SPureSpecM SPureSpecM.notations.

    Class SHeapSpecM (M : TYPE -> TYPE) : Type :=
      { produce_chunk : ⊢ Chunk -> M Unit;
        consume_chunk : ⊢ Chunk -> M Unit;
        consume_chunk_angelic : ⊢ Chunk -> M Unit;
      }.

  End SHeapSpecM.
  Export (hints) SHeapSpecM.
  Export SHeapSpecM (SHeapSpecM).

  Module ReaderT.
    Section ReaderT.

      Context `{persR : Persistent R, pureM : SPureSpecM M}.

      Definition ReaderT (A : TYPE) : TYPE :=
        R -> M A.

      Definition evalReaderT {A} : ⊢ ReaderT A -> R -> M A :=
        fun w m => m.

      Definition bind {A B} :
        ⊢ ReaderT A -> □(A -> ReaderT B) -> ReaderT B :=
        fun w m f r =>
          bind (m r) (fun _ θ a => f _ θ a (persist r θ)).

      Definition angelic_binary {A} :
        ⊢ ReaderT A -> ReaderT A -> ReaderT A :=
        fun w m1 m2 r => angelic_binary (m1 r) (m2 r).

      Definition demonic_binary {A} :
        ⊢ ReaderT A -> ReaderT A -> ReaderT A :=
        fun w m1 m2 r => demonic_binary (m1 r) (m2 r).

      Definition debug {A} :
        ⊢ □(SHeap -> AMessage) -> ReaderT A -> ReaderT A :=
        fun w msg m r => debug msg (m r).

      Definition liftM {A} :
        ⊢ M A -> ReaderT A := fun w m _ => m.

      #[export] Instance purespecm : SPureSpecM ReaderT :=
        {| SPureSpecM.pure  A w a                             := liftM (pure a);
           SPureSpecM.bind                                    := @bind;
           SPureSpecM.error A w msg                           := liftM (error msg);
           SPureSpecM.block A w                               := liftM block;
           SPureSpecM.angelic o w σ                           := liftM (angelic o σ);
           SPureSpecM.demonic o w σ                           := liftM (demonic o σ);
           SPureSpecM.angelic_ctx N n w Δ                     := liftM (angelic_ctx n Δ);
           SPureSpecM.demonic_ctx N n w Δ                     := liftM (demonic_ctx n Δ);
           SPureSpecM.assert_pathcondition w msg C            := liftM (assert_pathcondition msg C);
           SPureSpecM.assert_formula w msg fml                := liftM (assert_formula msg fml);
           SPureSpecM.assume_pathcondition w C                := liftM (assume_pathcondition C);
           SPureSpecM.assume_formula w fml                    := liftM (assume_formula fml);
           SPureSpecM.angelic_binary                          := @angelic_binary;
           SPureSpecM.demonic_binary                          := @demonic_binary;
           SPureSpecM.angelic_pattern_match N n σ pat w msg t := liftM (angelic_pattern_match n pat msg t);
           SPureSpecM.demonic_pattern_match N n σ pat w t     := liftM (demonic_pattern_match n pat t);
           SPureSpecM.new_pattern_match N n σ p w t           := liftM (new_pattern_match n p t);
           SPureSpecM.debug                                   := @debug;
        |}.

      Context {heapM : SHeapSpecM M}.

      #[export] Instance heapspecm : SHeapSpecM ReaderT :=
        {| produce_chunk w c := liftM (produce_chunk c);
           consume_chunk w c := liftM (consume_chunk c);
           consume_chunk_angelic w c := liftM (consume_chunk_angelic c);
        |}.

    End ReaderT.
    #[global] Arguments ReaderT R M A : clear implicits.
  End ReaderT.
  Export (hints) ReaderT.
  Export ReaderT (ReaderT, evalReaderT).

  Module ProduceConsumeReader.
  Section ProduceConsumeReader.

    Context {M} {pureM : SPureSpecM M} {heapM : SHeapSpecM M}.
    Import SPureSpecM.notations.

    Definition pureSubst {Σ} `{Subst A} (a : A Σ) : ⊢ ReaderT (Sub Σ) M A :=
      fun w δ => pure (subst a δ).
    #[global] Arguments pureSubst {Σ A _} a {w}.

    Definition push {A Σ x σ} :
      ⊢ STerm σ -> ReaderT (Sub (Σ ▻ x∷σ)) M A -> ReaderT (Sub Σ) M A :=
      fun _ t m δ1 => m δ1.[x∷σ ↦ t].

    Definition pushs {A Σ Δ} :
      ⊢ Sub Δ -> ReaderT (Sub (Σ ▻▻ Δ)) M A -> ReaderT (Sub Σ) M A :=
      fun _ δΔ m δΣ => m (δΣ ►► δΔ).

    Definition produce :
      forall {Σ} (asn : Assertion Σ), ⊢ ReaderT (Sub Σ) M Unit :=
      fix produce {Σ} asn {w} :=
        match asn with
        | asn.formula fml =>
            ⟨ _ ⟩ fml' <- pureSubst fml;;
            assume_formula fml'
        | asn.chunk c =>
            ⟨ _ ⟩ c' <- pureSubst c;;
            produce_chunk c'
        | asn.chunk_angelic c =>
            ⟨ _ ⟩ c' <- pureSubst c;;
            produce_chunk c'
        | asn.pattern_match s pat rhs =>
            ⟨ θ1 ⟩ s'               <- pureSubst s;;
            ⟨ θ2 ⟩ '(existT pc δpc) <- demonic_pattern_match id pat s' ;;
            pushs δpc (produce (rhs pc))
        | asn.sep a1 a2 =>
              ⟨ _ ⟩ _ <- produce a1 ;;
              produce a2
        | asn.or a1 a2 =>
            demonic_binary (produce a1) (produce a2)
        | asn.exist ς τ a =>
            ⟨ _ ⟩ t <- demonic (Some ς) τ;;
            push t (produce a)
        | asn.debug =>
            debug
              (fun w1 θ1 h1 =>
                 amsg.mk
                   {| (* debug_asn_program_context := Γ; *)
                      debug_asn_pathcondition := wco w1;
                      (* debug_asn_localstore := δ1; *)
                      debug_asn_heap := h1;
                   |})
              (pure tt)
        end.

    Definition consume :
      forall {Σ} (asn : Assertion Σ), ⊢ ReaderT (Sub Σ) M Unit :=
      fix consume {Σ} asn {w} :=
        match asn with
        | asn.formula fml =>
            ⟨ _ ⟩ fml' <- pureSubst fml;;
            assert_formula (fun _ _ _ => amsg.mk tt) fml'
        | asn.chunk c =>
            ⟨ _ ⟩ c' <- pureSubst c;;
            consume_chunk c'
        | asn.chunk_angelic c =>
            ⟨ _ ⟩ c' <- pureSubst c;;
            consume_chunk_angelic c'
        | asn.pattern_match s pat rhs =>
            ⟨ θ1 ⟩ s'               <- pureSubst s;;
            ⟨ θ2 ⟩ '(existT pc δpc) <- angelic_pattern_match id pat
                                         (fun _ _ _ => amsg.mk tt) s' ;;
            pushs δpc (consume (rhs pc))
        | asn.sep a1 a2 =>
              ⟨ _ ⟩ _ <- consume a1 ;;
              consume a2
        | asn.or a1 a2 =>
            angelic_binary (consume a1) (consume a2)
        | asn.exist ς τ a =>
            ⟨ _ ⟩ t <- angelic (Some ς) τ;;
            push t (consume a)
        | asn.debug =>
            debug
              (fun w1 θ1 h1 =>
                 amsg.mk
                   {| (* debug_asn_program_context := Γ; *)
                      debug_asn_pathcondition := wco w1;
                      (* debug_asn_localstore := δ1; *)
                      debug_asn_heap := h1;
                   |})
              (pure tt)
        end.

    Definition call_contract {Δ τ} (c : SepContract Δ τ) :
      ⊢ SStore Δ -> M (STerm τ) :=
      fun w0 args =>
        match c with
        | MkSepContract _ _ Σe δe req result ens =>
            ⟨ θ1 ⟩ evars <- angelic_ctx id Σe ;;
            ⟨ θ2 ⟩ _     <- assert_eq_nenv (fun _ _ _ => amsg.mk tt)
                              (subst δe evars) args⟨θ1⟩ ;;
            let evars2 := persist evars θ2 in
            ⟨ θ3 ⟩ _     <- consume req evars2 ;;
            ⟨ θ4 ⟩ res   <- demonic (Some result) τ ;;
            let evars4 := persist evars2 (θ3 ∘ θ4) in
            ⟨ θ5 ⟩ _     <- produce ens (sub_snoc evars4 (result∷τ) res) ;;
            pure res⟨θ5⟩
        end.

    Definition call_lemma {Δ} (lem : Lemma Δ) :
      ⊢ SStore Δ -> M Unit :=
      fun w0 args =>
        match lem with
        | MkLemma _ Σe δe req ens =>
            ⟨ θ1 ⟩ evars <- angelic_ctx id Σe ;;
            ⟨ θ2 ⟩ _     <- assert_eq_nenv (fun _ _ _ => amsg.mk tt)
                              (subst δe evars) args⟨θ1⟩ ;;
            let evars2 := persist evars θ2 in
            ⟨ θ3 ⟩ _     <- consume req evars2 ;;
            let evars3 := persist evars2 θ3 in
            produce ens evars3
        end.

  End ProduceConsumeReader.
  End ProduceConsumeReader.

  Section ProduceConsume.

    Context {M} {pureM : SPureSpecM M} {heapM : SHeapSpecM M}.
    Import SPureSpecM.notations.

    Definition sproduce :
      forall {Σ} (asn : Assertion Σ), ⊢ Sub Σ -> M Unit :=
      fix sproduce {Σ} asn {w} ζ :=
        match asn with
        | asn.formula fml =>
            assume_formula (subst fml ζ)
        | asn.chunk c =>
            produce_chunk (subst c ζ)
        | asn.chunk_angelic c =>
            produce_chunk (subst c ζ)
        | asn.pattern_match s pat rhs =>
            ⟨ θ ⟩ '(existT pc δpc) <- demonic_pattern_match id pat (subst s ζ) ;;
            sproduce (rhs pc) (persist ζ θ ►► δpc)
        | asn.sep a1 a2 =>
            ⟨ θ ⟩ _ <- sproduce a1 ζ ;;
            sproduce a2 (persist ζ θ)
        | asn.or a1 a2 =>
            demonic_binary (sproduce a1 ζ) (sproduce a2 ζ)
        | asn.exist ς τ a =>
            ⟨ θ ⟩ t <- demonic (Some ς) τ;;
            sproduce a (env.snoc (persist ζ θ) (ς∷τ) t)
        | asn.debug =>
            debug
              (fun w1 θ1 h1 =>
                 amsg.mk
                   {| (* debug_asn_program_context := Γ; *)
                      debug_asn_pathcondition := wco w1;
                      (* debug_asn_localstore := δ1; *)
                      debug_asn_heap := h1;
                   |})
              (pure tt)
        end.

    Definition sconsume :
      forall {Σ} (asn : Assertion Σ), ⊢ Sub Σ -> M Unit :=
      fix sconsume {Σ} asn {w} ζ :=
        match asn with
        | asn.formula fml =>
            assert_formula (fun _ _ _ => amsg.mk tt) (subst fml ζ)
        | asn.chunk c =>
            consume_chunk (subst c ζ)
        | asn.chunk_angelic c =>
            consume_chunk_angelic (subst c ζ)
        | asn.pattern_match s pat rhs =>
            ⟨ θ ⟩ '(existT pc δpc) <- angelic_pattern_match id pat
                                         (fun _ _ _ => amsg.mk tt)
                                         (subst s ζ) ;;
            sconsume (rhs pc) (persist ζ θ ►► δpc)
        | asn.sep a1 a2 =>
            ⟨ θ ⟩ _ <- sconsume a1 ζ ;;
            sconsume a2 (persist ζ θ)
        | asn.or a1 a2 =>
            angelic_binary (sconsume a1 ζ) (sconsume a2 ζ)
        | asn.exist ς τ a =>
            ⟨ θ ⟩ t <- angelic (Some ς) τ ;;
            sconsume a (env.snoc (persist ζ θ) (ς∷τ) t)
        | asn.debug =>
            debug
              (fun w1 θ1 h1 =>
                 amsg.mk
                   {| (* debug_asn_program_context := Γ; *)
                      debug_asn_pathcondition := wco w1;
                      (* debug_asn_localstore := δ1; *)
                      debug_asn_heap := h1;
                   |})
              (pure tt)
        end.

    Definition scall_contract {Δ τ} (c : SepContract Δ τ) :
      ⊢ SStore Δ -> M (STerm τ) :=
      fun w0 args =>
        match c with
        | MkSepContract _ _ Σe δe req result ens =>
            ⟨ θ1 ⟩ evars <- angelic_ctx id Σe ;;
            ⟨ θ2 ⟩ _     <- assert_eq_nenv (fun _ _ _ => amsg.mk tt)
                              (subst δe evars) args⟨θ1⟩ ;;
            let evars2 := persist (A := Sub _) evars θ2 in
            ⟨ θ3 ⟩ _     <- sconsume req evars2 ;;
            ⟨ θ4 ⟩ res   <- demonic (Some result) τ ;;
            let evars4 := persist (A := Sub _) evars2 (θ3 ∘ θ4) in
            ⟨ θ5 ⟩ _     <- sproduce ens (sub_snoc evars4 (result∷τ) res) ;;
            pure res⟨θ5⟩
        end.

    Definition scall_lemma {Δ} (lem : Lemma Δ) :
      ⊢ SStore Δ -> M Unit :=
      fun w0 args =>
        match lem with
        | MkLemma _ Σe δe req ens =>
            ⟨ θ1 ⟩ evars <- angelic_ctx id Σe ;;
            ⟨ θ2 ⟩ _     <- assert_eq_nenv (fun _ _ _ => amsg.mk tt)
                              (subst δe evars) args⟨θ1⟩ ;;
            let evars2 := persist (A := Sub _) evars θ2 in
            ⟨ θ3 ⟩ _     <- sconsume req evars2 ;;
            let evars3 := persist (A := Sub _) evars2 θ3 in
            sproduce ens evars3
        end.

  End ProduceConsume.

End SymbolicMonadInterfaceOn.
