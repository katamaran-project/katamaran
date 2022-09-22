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
     Classes.RelationClasses
     Lists.List
     NArith.NArith
     Program.Tactics
     Relations.Relation_Definitions
     Strings.String
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations
     Prelude
     Sep.Logic
     Signature
     Specification.

From stdpp Require base list option.

Import ctx.notations.
Import env.notations.
Import ListNotations.
Import SigTNotations.

Set Implicit Arguments.

Local Notation "A ::> R" :=
  (pointwise_relation A R)
    (at level 55, right associativity)
    : signature_scope.
Local Notation "'∀' x .. y , R " :=
  (forall_relation (fun x => .. (forall_relation (fun y => R)) ..))
    (at level 99, x binder, y binder, right associativity,
      format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' R ']'")
    : signature_scope.

Open Scope signature_scope.

Module Type NewShallowExecOn
  (Import B : Base)
  (Import PROG : Program B)
  (Import SIG : Signature B)
  (Import SPEC : Specification B PROG SIG).

  Import sep.
  Import sep.instances.
  Import sep.notations.

  Module CPureSpecM.
  Section WithProp.

    Context {L} {PI : PredicateDef L}.

    (* The pure backwards predicate transformer monad. We use this monad in some
       of the definition of primitives that do no need access to the store and
       that can later be lifted to the proper monad. *)
    Definition CPureSpecM (A : Type) : Type :=
      (A -> L) -> L.

    Definition Monotonic {A} : relation (CPureSpecM A) :=
      (A ::> lentails) ==> lentails.

    #[export] Instance monotonic_transitive {A} : Transitive (@Monotonic A).
    Proof.
      intros f g h fg gh P Q PQ. transitivity (g Q).
      apply fg. assumption. apply gh. reflexivity.
    Qed.

    Local Ltac solve_wp :=
      repeat
        (try progress subst;
         lazymatch goal with
         (* These first rules do not change the provability if the goal, i.e.
            these steps are always complete. *)
         | x : NamedEnv Val [ctx] |- _ => destruct (env.nilView x)
         | x: NamedEnv Val (_ ▻ _) |- _ => destruct (env.snocView x)
         | |- _ ⊣⊢ _ => split
         | |- context[_ ∧ !! _] => rewrite lprop_float
         | |- !! ?P ∧ ?Q ⊢ ?R => apply (land_prop_left (P := P) (Q := Q) (R := R)); intros ?
         (* | |- !! ?P ⊢ _ => apply lprop_left; intros ? *)
         | |- (∃ x : _, _) ⊢ _ => apply lex_left; intros ?
         | |- _ ⊢ ∀ x : _, _ => apply lall_right; intros ?
         | |- ?P ⊢ ?P ∨ _ => apply lor_right1; reflexivity
         | |- ?P ∧ _ ⊢ ?P => apply land_left1
         | H : ?P |- _ ⊢ !! ?P => apply lprop_right; exact H
         | |- _ ⊢ !! (?x = ?x) => apply lprop_right; reflexivity
         | |- _ ⊢ !! _ → _ => apply lprop_intro_impl; intro
         | |- _ ⊢ !! _ -∗ _ => apply lprop_intro_wand; intro
         | H : _ \/ _ |- _ => destruct H
         | |- _ ∨ _ ⊢ _ => apply lor_left
         | |- _ ⊢ _ ∧ _ => apply land_right
         (* Everything below is incomplete. *)
         | |- _ ⊢ ∃ x : _, _ => eapply lex_right
         | |- (∀ x : _, _) ⊢ _ => eapply lall_left
         | |- _ ⊢ !! ?P  => is_ground P; apply lprop_right; auto; fail
         | _ => easy
         end).

    Section Basic.
      Definition pure {A : Type} :
        A -> CPureSpecM A :=
        fun a POST => POST a.

      Definition map {A B} :
        (A -> B) -> CPureSpecM A -> CPureSpecM B :=
        fun f m POST => m (Basics.compose POST f).

      Definition bind {A B} :
        CPureSpecM A -> (A -> CPureSpecM B) -> CPureSpecM B :=
        fun m f POST => m (fun a1 => f a1 POST).
      #[global] Arguments bind {A B} ma f _ /.

      (* For counting the different execution paths of the shallow executor we use
         different aliases for False and True to distinguish between them. TRUE
         and FALSE represent execution paths that are pruned, i.e. do not reach
         the end of a function, and FINISH encodes the successful execution
         case. *)
      Definition FALSE : L := lprop False.
      Definition TRUE : L := lprop True.
      Definition FINISH : L := lprop True.
      Global Typeclasses Opaque TRUE.
      Global Typeclasses Opaque FALSE.
      Global Typeclasses Opaque FINISH.

      Definition error {A} : CPureSpecM A :=
        fun POST => FALSE.
      Definition block {A} : CPureSpecM A :=
        fun POST => TRUE.

    End Basic.
    Local Notation "x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, ma at level 90, mb at level 200, right associativity).
    Local Notation "ma ;; mb" := (bind ma (fun _ => mb)).

    Section Nondeterminism.

      Definition angelic (σ : Ty) : CPureSpecM (Val σ) :=
        fun POST => ∃ v : Val σ, POST v.

      Definition angelic_ctx {N : Set} :
        forall Δ : NCtx N Ty, CPureSpecM (NamedEnv Val Δ) :=
        fix rec Δ {struct Δ} :=
          match Δ with
          | []%ctx  => pure []
          | Δ ▻ x∷σ => vs <- rec Δ;;
                       v  <- angelic σ;;
                       pure (vs ► (x∷σ ↦ v))
          end.
      #[global] Arguments angelic_ctx {N} Δ.

      Definition demonic σ : CPureSpecM (Val σ) :=
        fun POST => ∀ v : Val σ, POST v.

      Definition demonic_ctx {N : Set} :
        forall Δ : NCtx N Ty, CPureSpecM (NamedEnv Val Δ) :=
        fix rec Δ {struct Δ} :=
          match Δ with
          | []      => pure env.nil
          | Δ ▻ x∷σ => vs <- rec Δ;;
                       v  <- demonic σ;;
                       pure (vs ► (x∷σ ↦ v))
          end%ctx.
      #[global] Arguments demonic_ctx {N} Δ.

      Definition angelic_binary {A} :
        CPureSpecM A -> CPureSpecM A -> CPureSpecM A :=
        fun m1 m2 POST =>
          m1 POST ∨ m2 POST.
      Definition demonic_binary {A} :
        CPureSpecM A -> CPureSpecM A -> CPureSpecM A :=
        fun m1 m2 POST =>
          m1 POST ∧ m2 POST.

      Definition angelic_list {A} :
        list A -> CPureSpecM A :=
        fix rec xs :=
          match xs with
          | nil        => error
          | cons x xs  => angelic_binary (pure x) (rec xs)
          end.

      Definition demonic_list {A} :
        list A -> CPureSpecM A :=
        fix rec xs :=
          match xs with
          | nil        => block
          | cons x xs  => demonic_binary (pure x) (rec xs)
          end.

      Definition angelic_finite F `{finite.Finite F} :
        CPureSpecM F :=
        angelic_list (finite.enum F).
      #[global] Arguments angelic_finite F {_ _}.

      Definition demonic_finite F `{finite.Finite F} :
        CPureSpecM F :=
        demonic_list (finite.enum F).
      #[global] Arguments demonic_finite F {_ _}.

      Lemma wp_angelic_ctx {N : Set} {Δ : NCtx N Ty} (POST : NamedEnv Val Δ -> L) :
        angelic_ctx Δ POST ⊣⊢ ∃ vs : NamedEnv Val Δ, POST vs.
      Proof.
        induction Δ; cbn; cbv [bind angelic pure].
        - solve_wp.
        - setoid_rewrite IHΔ. clear IHΔ. solve_wp.
      Qed.

      Lemma wp_demonic_ctx {N : Set} {Δ : NCtx N Ty} (POST : NamedEnv Val Δ -> L) :
        demonic_ctx Δ POST ⊣⊢ ∀ vs : NamedEnv Val Δ, POST vs.
      Proof.
        induction Δ; cbn; cbv [demonic bind pure].
        - solve_wp.
        - setoid_rewrite IHΔ. clear IHΔ. solve_wp.
      Qed.

      Lemma wp_angelic_list {A} (xs : list A) (POST : A -> L) :
        angelic_list xs POST ⊣⊢ ∃ x : A, !! List.In x xs ∧ POST x.
      Proof.
        induction xs; cbn; cbv [angelic_binary pure].
        - setoid_rewrite lfalse_and. now rewrite lex_false.
        - rewrite IHxs. clear IHxs. repeat solve_wp.
          apply lor_right2. repeat solve_wp.
      Qed.

      Lemma wp_demonic_list {A} (xs : list A) (POST : A -> L) :
        demonic_list xs POST ⊣⊢ ∀ x : A, !! List.In x xs → POST x.
      Proof.
        induction xs; cbn; cbv [demonic_binary pure].
        - setoid_rewrite limpl_false. now rewrite lall_true.
        - rewrite IHxs. clear IHxs. split.
          + repeat solve_wp.
            apply land_left2. apply (lall_left v).
              now apply lentails_apply, lprop_right.
          + apply land_right.
            * apply (lall_left a), lentails_apply, lprop_right. now left.
            * apply proper_lall_entails; intros x.
              apply proper_limpl_entails; [|easy].
              apply proper_lprop_entails. now right.
      Qed.

    End Nondeterminism.

    Section Guards.

      Definition assume_formula (fml : Prop) : CPureSpecM unit :=
        fun POST => !! fml → POST tt.
      #[global] Arguments assume_formula _ _ /.
      Definition assert_formula (fml : Prop) : CPureSpecM unit :=
        fun POST => !! fml ∧ POST tt.
      #[global] Arguments assert_formula _ _ /.
      Definition produce_chunk (c : SCChunk) : CPureSpecM unit :=
        fun POST => interpret_scchunk c -∗ POST tt.
      #[global] Arguments produce_chunk c _ /.
      Definition consume_chunk (c : SCChunk) : CPureSpecM unit :=
        fun POST => interpret_scchunk c ∗ POST tt.
      #[global] Arguments consume_chunk c _/.

      (* The paper uses asserted equalities between multiple types, but the
         symbolic executor can in fact only assert equalities between symbolic
         terms. We mirror the structure of the symbolic execution and also
         traverse (the statically known parts) of other data structures. *)
      Equations(noeqns) assert_eq_env {Δ : Ctx Ty}
        (δ δ' : Env Val Δ) : CPureSpecM unit :=
        assert_eq_env env.nil          env.nil            := pure tt;
        assert_eq_env (env.snoc δ _ t) (env.snoc δ' _ t') :=
          bind (assert_eq_env δ δ') (fun _ => assert_formula (t = t')).

      Equations(noeqns) assert_eq_nenv {N : Set} {Δ : NCtx N Ty}
        (δ δ' : NamedEnv Val Δ) : CPureSpecM unit :=
        assert_eq_nenv env.nil          env.nil            := pure tt;
        assert_eq_nenv (env.snoc δ _ t) (env.snoc δ' _ t') :=
          bind (assert_eq_nenv δ δ') (fun _ => assert_formula (t = t')).

      Lemma wp_assert_formula {F : Prop} (POST : unit -> L) :
        assert_formula F POST ⊣⊢ (!! F ∧ lemp) ∗ POST tt.
      Proof. now rewrite lemp_true, land_true, lprop_sep_and. Qed.
      Lemma wp_assume_formula {F : Prop} (POST : unit -> L) :
        assume_formula F POST ⊣⊢ ((!! F ∧ lemp) -∗ POST tt).
      Proof. now rewrite lemp_true, land_true, lprop_wand_impl. Qed.

      Lemma wp_assert_eq_env {Δ : Ctx Ty} (δ δ' : Env Val Δ) :
        forall POST,
          assert_eq_env δ δ' POST ⊣⊢ !! (δ = δ') ∧ POST tt.
      Proof.
        induction δ; intros POST; env.destroy δ'; cbn;
          cbv [bind assert_formula pure].
        - solve_wp.
        - rewrite IHδ, env.inversion_eq_snoc. clear IHδ.
          solve_wp; now apply lprop_right.
      Qed.

      Lemma wp_assert_eq_nenv {N} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) :
        forall POST,
          assert_eq_nenv δ δ' POST ⊣⊢ !! (δ = δ') ∧ POST tt.
      Proof.
        unfold NamedEnv.
        induction δ; intros POST; env.destroy δ'; cbn; cbv [bind assert_formula].
        - solve_wp.
        - rewrite IHδ, env.inversion_eq_snoc.
          rewrite <- lprop_and_distr, land_assoc.
          solve_wp.
      Qed.

      (* Lemma monotonic_assert_eq_env {Δ} (δ δ' : Env Val Δ) : *)
      (*   Proper Monotonic (assert_eq_env δ δ'). *)
      (* Proof. *)
      (*   intros P Q PQ. rewrite !wp_assert_eq_env. *)
      (*   now apply proper_land_entails. *)
      (* Qed. *)

      (* Lemma monotonic_assert_eq_nenv {N} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) : *)
      (*   Proper Monotonic (assert_eq_nenv δ δ'). *)
      (* Proof. *)
      (*   intros P Q PQ. rewrite !wp_assert_eq_nenv. *)
      (*   now apply proper_land_entails. *)
      (* Qed. *)

    End Guards.

    Section PatternMatching.

      Definition match_bool {A} (v : Val ty.bool) (kt kf : CPureSpecM A) : CPureSpecM A :=
        fun POST => if v then kt POST else kf POST.
      #[global] Arguments match_bool {A} v kt kf _ /.

      Definition match_enum {A E} (v : Val (ty.enum E))
        (cont : enumt E -> CPureSpecM A) : CPureSpecM A :=
        cont v.
      #[global] Arguments match_enum {A E} v cont _ /.

      Definition match_sum {A σ τ} (v : Val (ty.sum σ τ))
        (kinl : Val σ -> CPureSpecM A) (kinr : Val τ -> CPureSpecM A) :
        CPureSpecM A :=
        fun POST =>
          match v with
          | inl v1 => kinl v1 POST
          | inr v2 => kinr v2 POST
          end.
      #[global] Arguments match_sum {A σ τ} v kinl kinr _ /.

      Definition match_prod {A σ τ} (v : Val (ty.prod σ τ)) (k : Val σ -> Val τ -> CPureSpecM A) : CPureSpecM A :=
        fun POST =>
          match v with
          | pair v1 v2 => k v1 v2 POST
          end.
      #[global] Arguments match_prod {A σ τ} v k _ /.

      Definition match_list {A σ} (v : Val (ty.list σ)) (knil : CPureSpecM A)
        (kcons : Val σ -> Val (ty.list σ) -> CPureSpecM A) :
        CPureSpecM A :=
        fun POST =>
          match v with
          | nil       => knil POST
          | cons x xs => kcons x xs POST
          end.
      #[global] Arguments match_list {A σ} v knil kcons _ /.

      Definition match_record {N : Set} {A R} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ)
        (v : Val (ty.record R)) (k : NamedEnv Val Δ -> CPureSpecM A) :
        CPureSpecM A := k (record_pattern_match_val p v).
      #[global] Arguments match_record {_ _ _ _} p v k _ /.

      Definition match_tuple {N : Set} {A σs} {Δ : NCtx N Ty}
        (p : TuplePat σs Δ) (v : Val (ty.tuple σs))
        (k : NamedEnv Val Δ -> CPureSpecM A) :
        CPureSpecM A := k (tuple_pattern_match_val p v).
      #[global] Arguments match_tuple {_ _ _ _} p v k _ /.

      Definition match_union {N : Set} {A U} {Δ : unionk U -> NCtx N Ty}
        (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K)) (v : Val (ty.union U))
        (k : forall K, NamedEnv Val (Δ K) -> CPureSpecM A) : CPureSpecM A :=
        fun POST =>
          let (UK , vf) := unionv_unfold U v in
          k UK (pattern_match_val (p UK) vf) POST.
      #[global] Arguments match_union {_ _ _ _} p v k _ /.

      Definition match_bvec {A n} (v : Val (ty.bvec n))
        (k : bv n -> CPureSpecM A) : CPureSpecM A :=
        k v.
      #[global] Arguments match_bvec {_ _} v k _ /.

      Definition match_bvec_split {A m n} (v : Val (ty.bvec (m + n)))
        (k : bv m -> bv n -> CPureSpecM A) : CPureSpecM A :=
        fun POST =>
          match bv.appView m n v with
          | bv.isapp xs ys => k xs ys POST
          end.
      #[global] Arguments match_bvec_split {_ _ _} v k _ /.

      Definition newpattern_match {N : Set} {A σ} (v : Val σ) (pat : @PatternShape N σ)
        (k : forall (pc : PatternCase pat), NamedEnv Val (PatternCaseCtx pc) -> CPureSpecM A) :
        CPureSpecM A :=
        fun POST => let (pc,δpc) := newpattern_match_val pat v in k pc δpc POST.
      #[global] Arguments newpattern_match {N A σ} v pat  _ /.

    End PatternMatching.

    Section ProduceConsume.

      Fixpoint produce {Σ} (ι : Valuation Σ) (asn : Assertion Σ) : CPureSpecM unit :=
        match asn with
        | asn.formula fml => assume_formula (inst fml ι)
        | asn.chunk c     => produce_chunk (inst c ι)
        | asn.chunk_angelic c => produce_chunk (inst c ι)
        | asn.newpattern_match s pat rhs =>
            newpattern_match
              (inst (T := fun Σ => Term Σ _) s ι)
              pat
              (fun pc δpc => produce (ι ►► δpc) (rhs pc))
        | asn.sep a1 a2   => _ <- produce ι a1 ;; produce ι a2
        | asn.or a1 a2 =>
          demonic_binary (produce ι a1)
                         (produce ι a2)
        | asn.exist ς τ a =>
          v <- demonic τ ;;
          produce (env.snoc ι (ς∷τ) v) a
        | asn.debug => pure tt
        end.

      Fixpoint consume {Σ} (ι : Valuation Σ) (asn : Assertion Σ) : CPureSpecM unit :=
        match asn with
        | asn.formula fml => assert_formula (inst fml ι)
        | asn.chunk c     => consume_chunk (inst c ι)
        | asn.chunk_angelic c     => consume_chunk (inst c ι)
        | asn.newpattern_match s pat rhs =>
            newpattern_match
              (inst (T := fun Σ => Term Σ _) s ι)
              pat
              (fun pc δpc => consume (ι ►► δpc) (rhs pc))
        | asn.sep a1 a2   => _ <- consume ι a1;; consume ι a2
        | asn.or a1 a2 =>
          angelic_binary (consume ι a1)
                         (consume ι a2)
        | asn.exist ς τ a =>
          v <- angelic τ ;;
          consume (env.snoc ι (ς∷τ) v) a
        | asn.debug => pure tt
        end.

      Lemma wp_produce {Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : unit -> L) :
        produce ι asn POST ⊣⊢ (asn.interpret asn ι -∗ POST tt).
      Proof.
        revert POST. induction asn; cbn - [inst inst_term]; intros POST.
        - apply wp_assume_formula.
        - unfold produce_chunk; now rewrite interpret_scchunk_inst.
        - unfold produce_chunk; now rewrite interpret_scchunk_inst.
        - destruct newpattern_match_val; auto.
        - now rewrite IHasn1, IHasn2, lwand_curry.
        - unfold demonic_binary. now rewrite IHasn1, IHasn2, lwand_disj_distr.
        - unfold demonic. rewrite lwand_exists_comm.
          now apply proper_lall_equiv.
        - now rewrite lwand_emp.
      Qed.

      Lemma wp_consume {Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : unit -> L) :
        consume ι asn POST ⊣⊢ asn.interpret asn ι ∗ POST tt.
      Proof.
        revert POST. induction asn; cbn - [inst inst_term]; intros POST.
        - apply wp_assert_formula.
        - unfold consume_chunk; now rewrite interpret_scchunk_inst.
        - unfold consume_chunk; now rewrite interpret_scchunk_inst.
        - destruct newpattern_match_val; auto.
        - now rewrite IHasn1, IHasn2, <- lsep_assoc.
        - rewrite lsep_disj_distr. now apply proper_lor_equiv.
        - rewrite lsep_exists_comm. now apply proper_lex_equiv.
        - now rewrite lsep_comm, lsep_emp.
      Qed.

    End ProduceConsume.

    Section Calls.

      Definition call_contract {Δ τ} (ctr : SepContract Δ τ) (args : CStore Δ) :
        CPureSpecM (Val τ) :=
          match ctr with
          | MkSepContract _ _ Σe δ req result ens =>
            ι <- angelic_ctx Σe ;;
            assert_eq_nenv args (inst δ ι) ;;
            consume ι req  ;;
            v <- demonic τ ;;
            produce (env.snoc ι (result∷τ) v) ens ;;
            pure v
          end.

      Definition call_contract' {Δ τ} (ctr : SepContract Δ τ) (args : CStore Δ) :
        CPureSpecM (Val τ) :=
        fun POST =>
          match ctr with
          | MkSepContract _ _ Σe δ req result ens =>
              ∃ ι : Valuation Σe, !! (args = inst δ ι) ∧
              asn.interpret req ι ∗ (∀ v : Val τ, asn.interpret ens ι.[result∷τ ↦ v] -∗ POST v)
          end.

      Definition call_lemma {Δ} (lem : Lemma Δ) (args : CStore Δ) : CPureSpecM unit :=
          match lem with
          | MkLemma _ Σe δ req ens =>
            ι <- angelic_ctx Σe ;;
            assert_eq_nenv args (inst δ ι) ;;
            consume ι req ;;
            produce ι ens
          end.

      Definition call_lemma' {Δ} (lem : Lemma Δ) (args : CStore Δ) : CPureSpecM (Val ty.unit) :=
        fun POST =>
          match lem with
          | MkLemma _ Σe δ req ens =>
              ∃ ι : Valuation Σe, !! (args = inst δ ι) ∧
              asn.interpret req ι ∗ (asn.interpret ens ι -∗ POST tt)
          end.

      Lemma equiv_call_contract {Δ τ} (ctr : SepContract Δ τ) (args : CStore Δ) :
        forall (POST : Val τ -> L),
          call_contract ctr args POST ⊣⊢ call_contract' ctr args POST.
      Proof.
        intros POST; destruct ctr as [Σe δΔ req res ens].
        cbv [call_contract call_contract' bind demonic].
        rewrite wp_angelic_ctx. apply proper_lex_equiv. intros ι.
        rewrite wp_assert_eq_nenv. apply proper_land_equiv; [easy|].
        rewrite wp_consume. apply proper_lsep_equiv; [easy|].
        apply proper_lall_equiv. intros v.
        apply wp_produce.
      Qed.

      Lemma equiv_call_lemma {Δ} (lem : Lemma Δ) (args : CStore Δ) :
        forall (POST : Val ty.unit -> L),
        call_lemma lem args POST ⊣⊢ call_lemma' lem args POST.
      Proof.
        intros POST; destruct lem as [Σe δΔ req ens].
        cbv [call_lemma call_lemma' bind demonic].
        rewrite wp_angelic_ctx. apply proper_lex_equiv. intros ι.
        rewrite wp_assert_eq_nenv. apply proper_land_equiv; [easy|].
        rewrite wp_consume. apply proper_lsep_equiv; [easy|].
        apply wp_produce.
      Qed.

      Instance monotonic_call_contract {Δ τ} (ctr : SepContract Δ τ) (args : CStore Δ) :
        Proper Monotonic (call_contract ctr args).
      Proof.
        intros P Q PQ. rewrite !equiv_call_contract.
        destruct ctr; cbn. now setoid_rewrite PQ.
      Qed.

      Instance monotonic_call_lemma {Δ} (lem : Lemma Δ) (args : CStore Δ) :
        Proper Monotonic (call_lemma lem args).
      Proof.
        intros P Q PQ. rewrite !equiv_call_lemma.
        destruct lem; cbn. now setoid_rewrite PQ.
      Qed.

    End Calls.

  End WithProp.
  End CPureSpecM.
  Export CPureSpecM (CPureSpecM).
  #[export] Hint Unfold CPureSpecM.Monotonic : typeclass_instances.

  Module CHeapSpecM.
  Section WithProp.

    Context {L} {PI : PredicateDef L}.

    (* The main specification monad that we use for execution. It is indexed by
       two program variable contexts Γ1 Γ2 that encode the shape of the program
       variable store before and after execution. *)
    Definition CHeapSpecM (Γ1 Γ2 : PCtx) (A : Type) : Type :=
      (A -> CStore Γ2 -> L) -> CStore Γ1 -> L.
    Bind Scope mut_scope with CHeapSpecM.
    Local Open Scope mut_scope.

    Section Basic.

      Definition lift_purem {Γ A} (m : CPureSpecM A) : CHeapSpecM Γ Γ A :=
        fun POST δ => m (fun a => POST a δ).
      #[global] Arguments lift_purem {Γ A} m _ /.

      Definition pure {Γ A} (a : A) : CHeapSpecM Γ Γ A :=
        fun POST => POST a.
      #[global] Arguments pure {_ _} a _ /.
      Definition bind {Γ1 Γ2 Γ3 A B} (ma : CHeapSpecM Γ1 Γ2 A) (f : A -> CHeapSpecM Γ2 Γ3 B) : CHeapSpecM Γ1 Γ3 B :=
        fun POST => ma (fun a => f a POST).
      #[global] Arguments bind {_ _ _ _ _} ma f _ /.
      Definition bind_right {Γ1 Γ2 Γ3 A B} (ma : CHeapSpecM Γ1 Γ2 A) (mb : CHeapSpecM Γ2 Γ3 B) : CHeapSpecM Γ1 Γ3 B :=
        bind ma (fun _ => mb).
      #[global] Arguments bind_right {_ _ _ _ _} ma mb _ /.
      Definition map {Γ1 Γ2 A B} (f : A -> B) (ma : CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 B :=
        fun POST => ma (fun a => POST (f a)).

      Definition error {Γ1 Γ2 A} : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ => ⊥.
      Definition block {Γ1 Γ2 A} : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ => ⊤.
      #[global] Arguments block {_ _ _} _ /.

      Definition demonic_binary {Γ1 Γ2 A} (m1 m2 : CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ => m1 POST δ ∧ m2 POST δ.
      Definition angelic_binary {Γ1 Γ2 A} (m1 m2 : CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ => m1 POST δ ∨ m2 POST δ.

      Definition demonic {Γ} (σ : Ty) : CHeapSpecM Γ Γ (Val σ) :=
        fun POST δ => ∀ v : Val σ, POST v δ.
      Definition angelic {Γ} (σ : Ty) : CHeapSpecM Γ Γ (Val σ) :=
        fun POST δ => ∃ v : Val σ, POST v δ.
      #[global] Arguments angelic {Γ} σ _ /.
    End Basic.
    #[local] Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at level 90, mb at level 200, right associativity) : mut_scope.
    #[local] Notation "ma ;; mb" := (bind_right ma mb) : mut_scope.
    #[local] Infix "⊗" := demonic_binary (at level 40, left associativity) : mut_scope.
    #[local] Infix "⊕" := angelic_binary (at level 50, left associativity) : mut_scope.

    (* Module CHeapSpecMNotations. *)

    (*   Infix "⊗" := demonic_binary (at level 40, left associativity) : mut_scope. *)
    (*   Infix "⊕" := angelic_binary (at level 50, left associativity) : mut_scope. *)

    (*   Notation "' x <- ma ;; mb" := *)
    (*     (bind ma (fun x => mb)) *)
    (*       (at level 80, x pattern, ma at next level, mb at level 200, right associativity, *)
    (*        format "' x  <-  ma  ;;  mb") : mut_scope. *)
    (*   Notation "x <- ma ;; mb" := *)
    (*     (bind ma (fun x => mb)) *)
    (*       (at level 80, ma at level 90, mb at level 200, right associativity) : mut_scope. *)
    (*   (* Notation "ma >>= f" := (bind ma f) (at level 50, left associativity) : mut_scope. *) *)
    (*   Notation "ma ;; mb" := (bind_right ma mb) : mut_scope. *)

    (* End CHeapSpecMNotations. *)
    (* Import CHeapSpecMNotations. *)
    (* Local Open Scope mut_scope. *)

    Section PatternMatching.

      Definition match_bool {A Γ1 Γ2} (v : Val ty.bool) (kt kf : CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ => if v then kt POST δ else kf POST δ.
      #[global] Arguments match_bool {_ _ _} v kt kf _ /.

      Definition match_enum {A E} {Γ1 Γ2} (v : Val (ty.enum E))
        (cont : enumt E -> CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        cont v.
      #[global] Arguments match_enum {_ _ _ _} v cont _ /.

      Definition match_sum {A Γ1 Γ2} {σ τ} (v : Val (ty.sum σ τ))
        (kinl : Val σ -> CHeapSpecM Γ1 Γ2 A) (kinr : Val τ -> CHeapSpecM Γ1 Γ2 A) :
        CHeapSpecM Γ1 Γ2 A :=
        fun POST δ =>
          match v with
          | inl v1 => kinl v1 POST δ
          | inr v2 => kinr v2 POST δ
          end.
      #[global] Arguments match_sum {_ _ _ _ _} v kinl kinr _ /.

      Definition match_prod {A Γ1 Γ2} {σ τ} (v : Val (ty.prod σ τ)) (k : Val σ -> Val τ -> CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ =>
          match v with
          | pair v1 v2 => k v1 v2 POST δ
          end.
      #[global] Arguments match_prod {_ _ _ _ _} v k _ /.

      Definition match_list {A Γ1 Γ2} {σ} (v : Val (ty.list σ))
        (knil : CHeapSpecM Γ1 Γ2 A)
        (kcons : Val σ -> Val (ty.list σ) -> CHeapSpecM Γ1 Γ2 A) :
        CHeapSpecM Γ1 Γ2 A :=
        fun POST δ =>
          match v with
          | nil => knil POST δ
          | cons x xs => kcons x xs POST δ
          end.
      #[global] Arguments match_list {_ _ _ _} v knil kcons _ /.

      Definition match_record {N : Set} {A R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ)
        (v : Val (ty.record R)) (k : NamedEnv Val Δ -> CHeapSpecM Γ1 Γ2 A) :
        CHeapSpecM Γ1 Γ2 A := k (record_pattern_match_val p v).
      #[global] Arguments match_record {_ _ _ _ _ _} p v k _ /.

      Definition match_tuple {N : Set} {A σs Γ1 Γ2} {Δ : NCtx N Ty}
        (p : TuplePat σs Δ) (v : Val (ty.tuple σs))
        (k : NamedEnv Val Δ -> CHeapSpecM Γ1 Γ2 A) :
        CHeapSpecM Γ1 Γ2 A := k (tuple_pattern_match_val p v).
      #[global] Arguments match_tuple {_ _ _ _ _ _} p v k _ /.

      Definition match_union {N : Set} {A Γ1 Γ2 U} {Δ : unionk U -> NCtx N Ty}
        (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K)) (v : Val (ty.union U))
        (k : forall K, NamedEnv Val (Δ K) -> CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ =>
          let (UK , vf) := unionv_unfold U v in
          k UK (pattern_match_val (p UK) vf) POST δ.
      #[global] Arguments match_union {_ _ _ _ _ _} p v k _ /.

      Definition match_bvec {A n} {Γ1 Γ2} (v : Val (ty.bvec n))
        (k : bv n -> CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        k v.
      #[global] Arguments match_bvec {_ _ _ _} v k _ /.

      Definition match_bvec_split {A m n Γ1 Γ2} (v : Val (ty.bvec (m + n)))
        (k : bv m -> bv n -> CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ =>
          match bv.appView m n v with
          | bv.isapp xs ys => k xs ys POST δ
          end.
      #[global] Arguments match_bvec_split {_ _ _ _ _} v k _ /.

      Definition newpattern_match {N : Set} {A σ Γ1 Γ2} (v : Val σ) (pat : @PatternShape N σ) (k : forall (c : PatternCase pat), NamedEnv Val (PatternCaseCtx c) -> CHeapSpecM Γ1 Γ2 A) :
        CHeapSpecM Γ1 Γ2 A :=
        fun POST δ1 => let (x,p) := newpattern_match_val pat v in k x p POST δ1.
      #[global] Arguments newpattern_match {N A σ Γ1 Γ2} v pat k _ /.

    End PatternMatching.

    Section State.

      Definition pushpop {A Γ1 Γ2 x σ} (v : Val σ)
        (d : CHeapSpecM (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.tail δ1)) (δ0 ► (x∷σ ↦ v)).
      #[global] Arguments pushpop {_ _ _ _ _} v d _ /.
      Definition pushspops {A} {Γ1 Γ2 Δ} (δΔ : CStore Δ)
        (d : CHeapSpecM (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.drop Δ δ1)) (δ0 ►► δΔ).
      #[global] Arguments pushspops {_ _ _ _} δΔ d _ /.
      Definition get_local {Γ} : CHeapSpecM Γ Γ (CStore Γ) :=
        fun POST δ => POST δ δ.
      #[global] Arguments get_local {_} _ /.
      Definition put_local {Γ1 Γ2} (δ : CStore Γ2) : CHeapSpecM Γ1 Γ2 unit :=
        fun POST _ => POST tt δ.
      #[global] Arguments put_local {_ _} δ _ /.

      Definition eval_exp {Γ σ} (e : Exp Γ σ) : CHeapSpecM Γ Γ (Val σ) :=
        fun POST δ => POST (eval e δ) δ.
      #[global] Arguments eval_exp {_ _} e _ /.
      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) : CHeapSpecM Γ Γ (CStore σs) :=
        fun POST δ => POST (evals es δ) δ.
      #[global] Arguments eval_exps {_ _} es _ /.
      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : Val σ) : CHeapSpecM Γ Γ unit :=
        fun POST δ => POST tt (δ ⟪ x ↦ v ⟫).
      #[global] Arguments assign {Γ} x {σ xIn} v _ /.

    End State.

    Section Exec.

      (* The paper discusses the case that a function call is replaced by
         interpreting the contract instead. However, this is not always
         convenient. We therefore make contracts for functions optional and if a
         function does not have a contract, we continue executing the body of
         the called function. A parameter [inline_fuel] bounds the number of
         allowed levels before failing execution. Therefore, we write the
         executor in an open-recusion style and [Exec] is the closed type of
         such an executor. *)
      Definition Exec := forall Γ τ (s : Stm Γ τ), CHeapSpecM Γ Γ (Val τ).
      Definition ExecCall := forall Δ τ, 𝑭 Δ τ -> CStore Δ -> CPureSpecM (L := L) (Val τ).

      Definition ExecRefine (e1 e2 : Exec) : Prop :=
        forall Γ τ (s : Stm Γ τ) POST δ,
          e1 _ _ s POST δ ⊢ e2 _ _ s POST δ.

      Section ExecOpen.

        (* The executor for "inlining" a call. *)
        Variable exec : Exec.

        Definition exec_call_inline : ExecCall :=
          fun Δ τ f args POST =>
            exec (FunDef f) (fun v _ => POST v) args.

        Definition exec_call_with_contracts : ExecCall :=
          fun Δ τ f args =>
            match CEnv f with
            | Some c => CPureSpecM.call_contract c args
            | None   => exec_call_inline f args
            end.

        Variable exec_call : ExecCall.

        (* The openly-recursive executor. *)
        Definition exec_open : Exec :=
          fun Γ τ s =>
            match s with
            | stm_val _ l => pure l
            | stm_exp e => eval_exp e
            | stm_let x σ s k =>
              v <- exec s ;;
              pushpop v (exec k)
            | stm_block δ k =>
              pushspops δ (exec k)
            | stm_assign x e =>
              v <- exec e ;;
              _ <- assign x v ;;
              pure v
            | stm_call f es =>
              args <- eval_exps es ;;
              lift_purem (exec_call f args)
            | stm_foreign f es =>
              ts <- eval_exps es ;;
              lift_purem (CPureSpecM.call_contract (CEnvEx f) ts)
            | stm_lemmak l es k =>
              ts <- eval_exps es ;;
              _  <- lift_purem (CPureSpecM.call_lemma (LEnv l) ts) ;;
              exec k
            | stm_call_frame δ' s =>
              δ <- get_local ;;
              _ <- put_local δ' ;;
              v <- exec s ;;
              _ <- put_local δ ;;
              pure v
            | stm_seq e k => _ <- exec e ;; exec k
            | stm_assertk e1 _ k =>
              v <- eval_exp e1 ;;
              _ <- lift_purem (CPureSpecM.assume_formula (v = true)) ;;
              exec k
            | stm_fail _ s =>
              block
            | stm_newpattern_match s pat rhs =>
              v <- exec s ;;
              newpattern_match v pat
                (fun pc δpc => pushspops δpc (exec (rhs pc)))
            | stm_read_register reg =>
              v <- angelic τ ;;
              let c := scchunk_ptsreg reg v in
              _ <- lift_purem (CPureSpecM.consume_chunk c) ;;
              _ <- lift_purem (CPureSpecM.produce_chunk c) ;;
              pure v
            | stm_write_register reg e =>
              v__old <- angelic τ ;;
              _    <- lift_purem (CPureSpecM.consume_chunk (scchunk_ptsreg reg v__old)) ;;
              v__new <- eval_exp e ;;
              _    <- lift_purem (CPureSpecM.produce_chunk (scchunk_ptsreg reg v__new)) ;;
              pure v__new
            | stm_match_union U e alt__pat alt__rhs =>
              v <- eval_exp e ;;
              match_union alt__pat v (fun UK vs => pushspops vs (exec (alt__rhs UK)))
            | stm_bind s k =>
              v <- exec s ;;
              exec (k v)
            | stm_debugk k =>
              exec k
            end.

      End ExecOpen.
      #[global] Arguments exec_call_with_contracts exec [_ _] f args _ /.

      Definition exec_error : Exec :=
        fun _ _ _ => error.
      Definition exec_def (rec : Exec) : Exec :=
        exec_open rec (exec_call_inline rec).
      Definition exec_aux (exec_call : ExecCall) : Exec :=
        fix exec_aux Γ τ s := exec_open exec_aux exec_call s.

      (* The constructed closed executor. *)
      Fixpoint exec (inline_fuel : nat) : Exec :=
        match inline_fuel with
        | O   => exec_error
        | S n => exec_aux (exec_call_with_contracts (exec n))
        end.
      #[global] Arguments exec _ [_ _] s _ _.

    End Exec.

    Section WithFuel.

      Variable inline_fuel : nat.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
       Valuation (sep_contract_logic_variables c) -> CHeapSpecM Δ Δ unit :=
        match c with
        | MkSepContract _ _ _ _ req result ens =>
          fun ι =>
          _ <- lift_purem (CPureSpecM.produce ι req) ;;
          v <- exec inline_fuel s ;;
          lift_purem (CPureSpecM.consume (env.snoc ι (result∷τ) v) ens)
        end%mut.

      Definition vcgen {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        ForallNamed (fun ι : Valuation (sep_contract_logic_variables c) =>
          let δΔ : CStore Δ := inst (sep_contract_localstore c) ι in
          (* We use the FINISH alias of True for the purpose of counting
             nodes in a shallowly-generated VC. *)
          ⊤ ⊢ exec_contract c body ι (fun _ _ => ⊤) δΔ).

      Definition vcgen' {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        match c with
        | MkSepContract _ _ Σ δ req result ens =>
            forall ι : Valuation Σ,
              asn.interpret req ι ⊢
              exec inline_fuel body
                (fun v _ => asn.interpret ens (env.snoc ι (result∷τ) v)) (inst δ ι)
        end.

    End WithFuel.

    (* This section verifies the monotonicity of the calculated predicate
       transformers. Which is a necessity for the main soundness theorems. *)
    Section Monotonicity.

      Import sep.instances.

      #[local] Open Scope signature.

      Definition Monotonic {Γ1 Γ2 A} : relation (CHeapSpecM Γ1 Γ2 A) :=
        (A ::> CStore Γ2 ::> lentails) ==> CStore Γ1 ::> lentails.
      Definition Monotonic' {Γ1 Γ2 A} : relation (CHeapSpecM Γ1 Γ2 A) :=
        (A -> CStore Γ2 -> L) ::> CStore Γ1 ::> lentails.

      Definition MonotonicExec : relation Exec :=
        ∀ Γ τ, Stm Γ τ ::> Monotonic.
      Definition MonotonicExec' : relation Exec :=
        ∀ Γ τ, Stm Γ τ ::> Monotonic'.
      Definition MonotonicCall : relation ExecCall :=
        ∀ Δ σ, 𝑭 Δ σ ::> CStore Δ ::> CPureSpecM.Monotonic.

      #[export] Instance monotonic_transitive {Γ1 Γ2 A} :
        Transitive (@Monotonic Γ1 Γ2 A).
      Proof.
        intros f g h fg gh P Q PQ δ. transitivity (g Q δ).
        apply fg. assumption. apply gh. reflexivity.
      Qed.

      #[export] Instance monotonicexec_transitive :
        Transitive MonotonicExec.
      Proof.
        intros f g h fg gh Γ τ s.
        transitivity (g Γ τ s); [apply fg|apply gh].
      Qed.

      Ltac solve_monotonic :=
        repeat
          lazymatch goal with
          | |- ?x           ⊢ ?x => reflexivity
          | |- Basics.flip lentails ?x ?y => change_no_check (lentails y x)
          | |- limpl _ _    ⊢ _  => apply proper_limpl_entails; [easy|]
          | |- lsep _ _     ⊢ _  => apply proper_lsep_entails
          | |- lwand _ _    ⊢ _  => apply proper_lwand_entails
          | |- lex _        ⊢ _  => apply proper_lex_entails; intros ?
          | H : (_ ::> CStore _ ::> lentails) ?P ?Q |- ?P ?x ?δ ⊢ ?Q ?x ?δ =>
              apply H
          | H : Monotonic ?m1 ?m2 |- ?m1 _ ?δ ⊢ ?m2 _ ?δ =>
              apply H; intros ? ?
          | H: MonotonicExec ?ex1 ?ex2 |- ?ex1 _ _ ?s _ _ ⊢ ?ex2 _ _ ?s _ _ =>
              apply H; intros ? ?
          | H: MonotonicCall ?ec1 ?ec2 |- ?ec1 _ _ ?f _ _ ⊢ ?ec2 _ _ ?f _ _ =>
              apply H; intros ?
          | H: Proper MonotonicCall ?ec |- ?ec _ _ ?f _ _ ⊢ ?ec _ _ ?f _ _ =>
              apply H; intros ?
          (* | H: forall _, Monotonic (?f _) (?g _) |- ?f _ _ ?δ ⊢ ?g _ _ ?δ => *)
          (*     apply H; intros ? ? *)
          | H: forall _, Monotonic (?f _ _ _) (?g _ _ _) |- ?f _ _ _ _ _ ⊢ ?g _ _ _ _ _ =>
              apply H; intros ? ?
          | |- CPureSpecM.call_contract _ _ _ ⊢ _ =>
              apply CPureSpecM.monotonic_call_contract; intros ?
          | |- CPureSpecM.call_lemma _ _ _ ⊢ _ =>
              apply CPureSpecM.monotonic_call_lemma; intros ?
          | |- (match ?x with _ => _ end) ⊢ _ => destruct x
          | |- Proper _ _ => unfold Proper
          | |- Monotonic _ _ => intros ?P ?Q ?PQ ?δ; cbn
          | |- respectful _ _ _ _ => intros ? ? ?
          | H: (_ ::> Monotonic) ?f ?g |- ?f _ _ _ ⊢ ?g _ _ _ =>
              apply H; intros ? ?
          end.

      Instance exec_call_inline_monotonic :
        Proper (MonotonicExec ==> MonotonicCall) (exec_call_inline).
      Proof. intros ex1 ex2 ex_mon Δ σ f args P Q PQ. now apply ex_mon. Qed.

      Instance exec_call_with_contracts_monotonic :
        Proper (MonotonicExec ==> MonotonicCall) (exec_call_with_contracts).
      Proof.
        intros ex1 ex2 ex_mon Δ σ f args.
        unfold exec_call_with_contracts. destruct CEnv.
        - apply CPureSpecM.monotonic_call_contract.
        - now apply exec_call_inline_monotonic.
      Qed.

      Instance exec_open_monotonic :
        Proper (MonotonicExec ==> MonotonicCall ==> MonotonicExec) exec_open.
      Proof.
        intros ex1 ex2 ex_mon ec1 ec2 ec_mon Γ τ s P Q PQ δΓ.
        destruct s; cbn; solve_monotonic.
      Qed.

      Instance exec_def_monotonic :
        Proper (MonotonicExec ==> MonotonicExec) exec_def.
      Proof.
        intros ex1 ex2 ex_mon. unfold exec_def.
        now apply exec_open_monotonic, exec_call_inline_monotonic.
      Qed.

      Instance exec_aux_monotonic :
        Proper (MonotonicCall ==> MonotonicExec) (exec_aux).
      Proof.
        intros ec1 ec2 ec_mon Γ τ s.
        induction s; intros P Q PQ ?; cbn; solve_monotonic.
      Qed.

      Lemma fold_exec_aux (ex : Exec) (ec : ExecCall)
        (IHc : Proper MonotonicCall ec)
        (IHx : MonotonicExec (exec_open ex ec) ex) :
        MonotonicExec (exec_aux ec) ex.
      Proof.
        intros Γ τ s; induction s; cbn [exec_aux];
          match goal with
          | |- Monotonic (exec_open _ _ ?s) (ex _ _ ?s) =>
              transitivity (exec_open ex ec s);
              [cbn [exec_open]|apply IHx]
          end;
          solve_monotonic.
      Qed.

      Lemma exec_error_initial (ex : Exec) :
        MonotonicExec exec_error ex.
      Proof. intros ? ? ? ? ? ? ?. apply lfalse_left. Qed.

      Lemma exec_monotonic n : Proper MonotonicExec (exec n).
      Proof.
        induction n; cbn.
        - apply exec_error_initial.
        - now apply exec_aux_monotonic, exec_call_with_contracts_monotonic.
      Qed.

      Record Model (ex : Exec) : Prop := {
          rule_syntactic :
            MonotonicExec'
              (exec_def ex)
              ex;

          rule_contract :
            MonotonicCall
              (exec_call_with_contracts exec_error)
              (exec_call_inline ex);

          ex_monotonic :> Proper MonotonicExec ex;
        }.

    End Monotonicity.

    Import sep.instances.

    Lemma vcgen_equiv {Δ τ} n (c : SepContract Δ τ) (body : Stm Δ τ) :
      vcgen n c body <-> vcgen' n c body.
    Proof.
      destruct c as [Σ δ req result ens]; cbn.
      rewrite env.Forall_forall.
      apply base.forall_proper; intros ι.
      rewrite CPureSpecM.wp_produce.
      rewrite <- lwand_sep_adjoint.
      apply proper_entails_equiv_iff.
      rewrite lsep_true. reflexivity.
      split; apply exec_monotonic; intros v δ';
        now rewrite CPureSpecM.wp_consume, lsep_comm, lsep_true.
    Qed.

  End WithProp.
  End CHeapSpecM.
  Export CHeapSpecM (CHeapSpecM).


  Module Shallow.

    Import sep.instances.

    Section Soundness.
      Context {L} {PI : PredicateDef L}.

      Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        (* Use inline_fuel = 1 by default. *)
        CHeapSpecM.vcgen (L := L) 1 c body.

      Definition ValidContractCEnv : Prop :=
        forall (Δ : PCtx) (τ : Ty) (f : 𝑭 Δ τ) (c : SepContract Δ τ),
          CEnv f = Some c ->
          ValidContract c (FunDef f).

      Import CHeapSpecM.

      Lemma rule_syntactic' (ec : ExecCall) (ec_mon : Proper MonotonicCall ec)
        (ex : Exec) (ex_mdl : Model ex) :
        MonotonicCall ec (exec_call_inline ex) ->
        MonotonicExec (exec_aux ec) ex.
      Proof.
        intros. apply fold_exec_aux; [assumption|].
        transitivity (exec_open ex (exec_call_inline ex)).
        apply exec_open_monotonic.
        apply ex_monotonic; auto.
        assumption.
        intros Γ τ s P Q PQ δ.
        transitivity (ex _ _ s P δ).
        apply (rule_syntactic ex_mdl).
        apply ex_monotonic; auto.
      Qed.

      Definition ValidContractSem (ex : Exec) {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : L :=
        match contract with
        | MkSepContract _ _ ctxΣ θΔ req res ens =>
            ∀ (ι : Valuation ctxΣ),
              asn.interpret req ι -∗
               ex _ _ body (fun v _ => asn.interpret ens ι.[res∷σ ↦ v]) (inst θΔ ι)
        end.

      Definition ValidContractEnvSem (ex : Exec) : L :=
        ∀ Δ σ (f : 𝑭 Δ σ),
          match CEnv f with
          | Some c => ValidContractSem ex (FunDef f) c
          | None   => ⊤
          end.

      Lemma validcontractsem_monotonic :
        Proper
          (MonotonicExec ==> ∀ Γ τ, Stm Γ τ ::> SepContract Γ τ ::> lentails)
          ValidContractSem.
      Proof.
        intros ex1 ex2 ex_mon Γ τ s [Σe δΔ req res ens]; cbn.
        apply proper_lall_entails; intros ι.
        apply proper_lwand_entails; [easy|].
        now apply ex_mon.
      Qed.

      Instance validcontractenvsem_monotonic :
        Proper (MonotonicExec ==> lentails) ValidContractEnvSem.
      Proof.
        intros ex1 ex2 ex_mon.
        unfold ValidContractEnvSem.
        apply proper_lall_entails; intros Δ.
        apply proper_lall_entails; intros σ.
        apply proper_lall_entails; intros f.
        destruct CEnv; [|easy].
        now apply validcontractsem_monotonic.
      Qed.

      Definition sound_shallow (vcenv : ValidContractCEnv) :
        ⊤ ⊢ ValidContractEnvSem (exec 1).
      Proof.
        apply lall_right; intros Δ.
        apply lall_right; intros σ.
        apply lall_right; intros f.
        specialize (vcenv Δ σ f).
        destruct (CEnv f) as [ctr|]; [|easy].
        specialize (vcenv _ eq_refl).
        unfold ValidContract in vcenv.
        rewrite vcgen_equiv in vcenv.
        destruct ctr as [Σe δΔ req res ens].
        apply lall_right; intros ι.
        specialize (vcenv ι).
        apply lwand_sep_adjoint.
        now rewrite lsep_true.
      Qed.

      Lemma soundness (ex : Exec) (exmdl : Model ex) :
        ValidContractCEnv -> ⊤ ⊢ ValidContractEnvSem ex.
      Proof.
        unfold ValidContractCEnv.
        intros vcenv.
        apply lall_right; intros Δ.
        apply lall_right; intros σ.
        apply lall_right; intros f.
        specialize (vcenv Δ σ f).
        destruct (CEnv f) as [ctr|]; [|easy].
        specialize (vcenv ctr eq_refl).
        destruct ctr as [ctxΣ θΔ req res ens]; cbn in *.
        apply lall_right; intros ι.
        rewrite env.Forall_forall in vcenv.
        specialize (vcenv ι). revert vcenv.
        apply proper_entails_entails_impl; [easy|].
        rewrite CPureSpecM.wp_produce.
        apply proper_lwand_entails; [easy|].
        apply rule_syntactic'; auto.
        apply exec_call_with_contracts_monotonic.
        apply exec_error_initial.
        apply rule_contract; auto.
        intros ? ?.
        rewrite CPureSpecM.wp_consume.
        now rewrite lsep_comm, lsep_true.
      Qed.

    End Soundness.

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
        | forall (x : ?T), CPureSpecM.TRUE => pspruned
        | forall (x : ?T), CPureSpecM.FALSE => pspruned
        | forall (x : ?T), CPureSpecM.FINISH => psfinish
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

      Section WithSepLogic.
        Context {L : SepLogic}.
        (* This typeclass approach seems to be much faster than the reifyProp
           tactic above. *)
        Class ShallowStats (P : L) :=
          stats : Stats.
        Arguments stats P {_}.

        (* We make these instances global so that users can simply use the
           calc tactic qualified without importing the rest of this module. *)
        #[global] Instance stats_true {L : SepLogic} : ShallowStats CPureSpecM.TRUE :=
          {| branches := 1; pruned := 1 |}.
        #[global] Instance stats_false : ShallowStats CPureSpecM.FALSE :=
          {| branches := 1; pruned := 1 |}.
        #[global] Instance stats_finish : ShallowStats CPureSpecM.FINISH :=
          {| branches := 1; pruned := 0 |}.
        (* We do not count regular True and False towards the statistics
           because they do not (should not) represent leaves of the shallow
           execution. *)
        #[global] Instance stats_true' : ShallowStats ⊤ :=
          {| branches := 0; pruned := 0 |}.
        #[global] Instance stats_false' : ShallowStats ⊥ :=
          {| branches := 0; pruned := 0 |}.

        #[global] Instance stats_eq {A} {x y : A} : ShallowStats (!! (x = y)) :=
          {| branches := 0; pruned := 0 |}.
        #[global] Instance stats_zle {x y : Z} : ShallowStats (!! Z.le x y) :=
          {| branches := 0; pruned := 0 |}.

        #[global] Instance stats_and `{ShallowStats P, ShallowStats Q} :
          ShallowStats (P ∧ Q) := plus_stats (stats P) (stats Q).
        #[global] Instance stats_or `{ShallowStats P, ShallowStats Q} :
          ShallowStats (P ∨ Q) := plus_stats (stats P) (stats Q).
        #[global] Instance stats_impl `{ShallowStats P, ShallowStats Q} :
          ShallowStats (P → Q) := plus_stats (stats P) (stats Q).
        #[global] Instance stats_star `{ShallowStats P, ShallowStats Q} :
          ShallowStats (P ∗ Q) := plus_stats (stats P) (stats Q).
        #[global] Instance stats_wand `{ShallowStats P, ShallowStats Q} :
          ShallowStats (P -∗ Q) := plus_stats (stats P) (stats Q).

        Axiom undefined : forall A, A.

        #[global] Instance stats_forall {A} {B : A -> L} {SP : forall a, ShallowStats (B a)} :
          ShallowStats (∀ a : A, B a) := SP (undefined A).
        #[global] Instance stats_exists {A} {B : A -> L} {SP : forall a, ShallowStats (B a)} :
          ShallowStats (∃ a : A, B a) := SP (undefined A).

      End WithSepLogic.

      Ltac calc fnc :=
        let P := eval compute - [CPureSpecM.FALSE CPureSpecM.TRUE CPureSpecM.FINISH
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

End NewShallowExecOn.

Module MakeNewShallowExecutor
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SIG : Signature B)
  (Import SPEC : Specification B PROG SIG).

  Include NewShallowExecOn B PROG SIG SPEC.

End MakeNewShallowExecutor.
