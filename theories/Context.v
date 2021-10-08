(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel, Georgy Lukyanov                         *)
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
     NArith.BinNat
     Bool.Bool
     Init.Datatypes
     Init.Decimal
     Logic.EqdepFacts
     Numbers.DecimalString
     Strings.Ascii
     Strings.String.

From Equations Require Import Equations.
From stdpp Require
     base.
From Katamaran Require Import
     Notation Prelude.

Set Implicit Arguments.

(* Type of contexts. This is a list of bindings of type B. This type and
   subsequent types use the common notation of snoc lists. *)
Inductive Ctx (B : Set) : Set :=
| ctx_nil
| ctx_snoc (Γ : Ctx B) (b : B).

Section TransparentObligations.
  Local Set Transparent Obligations.
  Derive NoConfusion for Ctx.
End TransparentObligations.

Arguments ctx_nil {_}.
Arguments ctx_snoc {_} _%ctx _%ctx.
Bind Scope ctx_scope with Ctx.

Section WithBinding.
  Context {B : Set}.

  Global Instance ctx_eqdec {eqB : EqDec B} : EqDec (Ctx B) :=
    fix ctx_eqdec (Γ Δ : Ctx B) {struct Γ} : dec_eq Γ Δ :=
      match Γ , Δ with
      | ctx_nil      , ctx_nil      => left eq_refl
      | ctx_snoc Γ b , ctx_snoc Δ c => f_equal2_dec ctx_snoc noConfusion_inv
                                                    (ctx_eqdec Γ Δ) (eq_dec b c)
      | _            , _            => right noConfusion_inv
      end.

  Fixpoint ctx_lookup (Γ : Ctx B) (n : nat) : option B :=
    match Γ , n with
    | ctx_snoc _ b , O   => Some b
    | ctx_snoc Γ _ , S n => ctx_lookup Γ n
    | _            , _   => None
    end.

  (* Concatenation of two contexts. *)
  Fixpoint ctx_cat (Γ1 Γ2 : Ctx B) {struct Γ2} : Ctx B :=
    match Γ2 with
    | ctx_nil       => Γ1
    | ctx_snoc Γ2 τ => ctx_snoc (ctx_cat Γ1 Γ2) τ
    end.

  (* This is a predicate that that encodes that the de Bruijn index n points
     to the binding b in Γ. *)
  Fixpoint ctx_nth_is (Γ : Ctx B) (n : nat) (b : B) {struct Γ} : Prop :=
    match Γ , n with
    | ctx_snoc _ x , O   => x = b
    | ctx_snoc Γ _ , S n => ctx_nth_is Γ n b
    | _            , _   => False
    end.

  Lemma ctx_nth_is_right_exact {Γ : Ctx B} (n : nat) (b1 b2 : B) :
    ctx_nth_is Γ n b1 -> ctx_nth_is Γ n b2 -> b1 = b2.
  Proof.
    revert n.
    induction Γ.
    - intros ? [].
    - cbn in *.
      destruct n eqn:E.
      + congruence.
      + apply IHΓ.
  Qed.

  Section WithUIP.

    Context {UIP_B : UIP B}.

    Fixpoint ctx_nth_is_proof_irrelevance {Γ : Ctx B} (n : nat) (b : B) {struct Γ} :
      forall (p q : ctx_nth_is Γ n b), p = q.
    Proof.
      destruct Γ; intros p q.
      - destruct q.
      - destruct n; cbn in *.
        + apply uip.
        + apply (ctx_nth_is_proof_irrelevance _ n _ p q).
    Defined.

    Global Instance eqdec_ctx_nth {Γ n b} : EqDec (ctx_nth_is Γ n b).
    Proof. intros p q. left. apply ctx_nth_is_proof_irrelevance. Defined.

    Lemma ctx_nth_is_proof_irrelevance_refl {Γ : Ctx B} (n : nat) (b : B) (p : ctx_nth_is Γ n b) :
      ctx_nth_is_proof_irrelevance n b p p = eq_refl.
    Proof. apply uip. Qed.

  End WithUIP.

  Section InCtx.
    (* Set locally only for the definition of InCtx. *)
    Local Set Primitive Projections.

     (* InCtx represents context containment proofs. This is essentially a
        well-typed de Bruijn index, i.e. a de Bruijn index with a proof that it
        resolves to the binding b. This record type is defined using primitive
        projections to get eta-conversion definitionally. *)
    Class InCtx (b : B) (Γ : Ctx B) : Set :=
      MkInCtx
        { inctx_at: nat;
          inctx_valid: ctx_nth_is Γ inctx_at b
        }.

    Global Arguments MkInCtx [_ _] _ _.
    Global Arguments inctx_at [_ _] _.
    Global Arguments inctx_valid [_ _] _.

    Global Program Instance NoConfusionPackage_InCtx {uip_B : UIP B} {b Γ} : NoConfusionPackage (InCtx b Γ) :=
       {| NoConfusion xIn yIn := NoConfusion (inctx_at xIn) (inctx_at yIn);
          noConfusion xIn yIn (e : NoConfusion (inctx_at xIn) (inctx_at yIn)) :=
            match noConfusion e in _ = y
              return forall q, xIn = {| inctx_at := y; inctx_valid := q |}
            with
            | eq_refl => fun q => f_equal (MkInCtx _) (ctx_nth_is_proof_irrelevance _ _ (inctx_valid xIn) q)
            end (inctx_valid yIn);
          noConfusion_inv (xIn yIn : InCtx b Γ) (e : xIn = yIn) :=
            noConfusion_inv (f_equal (@inctx_at b Γ) e);
       |}.
    Next Obligation.
      intros ? ? ? [m p] [n q] e. cbn [inctx_at] in *.
      change (NoConfusion _ _) with (NoConfusion m n) in e.
      destruct (noConfusion e) eqn:?. cbn.
      destruct (ctx_nth_is_proof_irrelevance m b p q). cbn.
      destruct m.
      - destruct e. reflexivity.
      - apply uip.
    Qed.
    Next Obligation.
      intros ? ? ? [m p] [n q] e; intros.
      destruct e.
      destruct Γ; cbn in *. contradiction.
      destruct m, n.
      - destruct p. cbn. now rewrite EqDec.uip_refl_refl.
      - destruct p. cbn. now rewrite EqDec.uip_refl_refl.
      - cbn. rewrite ctx_nth_is_proof_irrelevance_refl. reflexivity.
      - cbn. rewrite ctx_nth_is_proof_irrelevance_refl. reflexivity.
    Qed.

  End InCtx.

  (* Two proofs of context containment are equal of the deBruijn indices are equal *)
  Definition InCtx_eqb {Γ} {b1 b2 : B}
             (b1inΓ : InCtx b1 Γ)
             (b2inΓ : InCtx b2 Γ) : bool :=
    Nat.eqb (inctx_at b1inΓ) (inctx_at b2inΓ).

  Lemma InCtx_eqb_spec `{UIP B} {Γ} {b1 b2 : B} (b1inΓ : InCtx b1 Γ) (b2inΓ : InCtx b2 Γ) :
    reflect
      (existT _ b1inΓ = existT _ b2inΓ :> sigT (fun b => InCtx b Γ))
      (InCtx_eqb b1inΓ b2inΓ).
  Proof.
    destruct b1inΓ as [m p], b2inΓ as [n q]; cbn.
    destruct (NPeano.Nat.eqb_spec m n); constructor.
    - subst. pose proof (ctx_nth_is_right_exact _ _ _ p q). subst.
      f_equal. f_equal. apply ctx_nth_is_proof_irrelevance.
    - intros e. depelim e. destruct n, m; cbn in H0; congruence.
  Qed.

  (* These are *constructors* for InCtx. *)
  Definition inctx_zero {b : B} {Γ : Ctx B} : InCtx b (ctx_snoc Γ b) :=
    @MkInCtx _ (ctx_snoc Γ b) 0 eq_refl.
  Definition inctx_succ {b : B} {Γ : Ctx B} {b' : B} (bIn : InCtx b Γ) :
    InCtx b (ctx_snoc Γ b') :=
    @MkInCtx _ (ctx_snoc Γ b') (S (inctx_at bIn)) (inctx_valid bIn).

  Inductive NilView {b : B} (i : InCtx b ctx_nil) : Set :=.

  Definition nilView {b : B} (i : InCtx b ctx_nil) : NilView i :=
    match inctx_valid i with end.

  Inductive SnocView (Γ : Ctx B) {b' : B} : forall b, InCtx b (ctx_snoc Γ b') -> Set :=
  | snocViewZero                     : SnocView inctx_zero
  | snocViewSucc {b} (i : InCtx b Γ) : SnocView (inctx_succ i).
  Global Arguments snocViewZero {_ _}.

  Definition snocView {Γ} {b b' : B} (i : InCtx b (ctx_snoc Γ b')) :
    @SnocView Γ b' b i :=
    match inctx_at i as n return forall p, SnocView (MkInCtx n p)
    with
    | O   => fun p => match p with eq_refl => snocViewZero end
    | S n => fun p => snocViewSucc (MkInCtx n p)
    end (inctx_valid i).

  Inductive InCtxView {b : B} : forall Γ, InCtx b Γ -> Set :=
  | inctxViewZero {Γ}                    : @InCtxView b (ctx_snoc Γ b) inctx_zero
  | inctxViewSucc {Γ b'} (i : InCtx b Γ) : @InCtxView b (ctx_snoc Γ b') (inctx_succ i).

  Definition inctxView {b Γ} (bIn : InCtx b Γ) : InCtxView bIn.
  Proof.
    destruct Γ.
    - destruct (nilView bIn).
    - destruct (snocView bIn); constructor.
  Defined.

  Fixpoint inctx_cat_left {b : B} {Γ : Ctx B} (Δ : Ctx B) (bIn : InCtx b Γ) : InCtx b (ctx_cat Γ Δ) :=
    match Δ with
    | ctx_nil      => bIn
    | ctx_snoc Δ _ => inctx_succ (inctx_cat_left Δ bIn)
    end.

  Fixpoint inctx_cat_right {b : B} {Γ : Ctx B} (Δ : Ctx B) : InCtx b Δ -> InCtx b (ctx_cat Γ Δ) :=
    match Δ with
    | ctx_nil      => fun bIn => match nilView bIn with end
    | ctx_snoc Δ _ =>
      fun bIn =>
        match snocView bIn with
        | snocViewZero => inctx_zero
        | snocViewSucc bIn => inctx_succ (inctx_cat_right bIn)
        end
    end.

  Inductive CatView {Γ Δ} {b : B} : InCtx b (ctx_cat Γ Δ) -> Set :=
  | isCatLeft  (bIn : InCtx b Γ) : CatView (inctx_cat_left Δ bIn)
  | isCatRight (bIn : InCtx b Δ) : CatView (inctx_cat_right bIn).

  Definition catView_succ {Γ Δ b b'} (bIn : InCtx b (ctx_cat Γ Δ)) (bInV : CatView bIn) :
    @CatView Γ (ctx_snoc Δ b') b (inctx_succ bIn) :=
    match bInV with
    | isCatLeft bIn => @isCatLeft Γ (@ctx_snoc B Δ b') b bIn
    | isCatRight bIn => @isCatRight Γ (@ctx_snoc B Δ b') b (@inctx_succ b Δ b' bIn)
    end.

  Fixpoint catView_index {Γ Δ} {b : B} {struct Δ} :
    forall (n : nat) (p : ctx_nth_is (ctx_cat Γ Δ) n b),
      @CatView Γ Δ b (@MkInCtx b (ctx_cat Γ Δ) n p) :=
    match Δ with
    | ctx_nil => fun n p => @isCatLeft Γ (@ctx_nil B) b (@MkInCtx b Γ n p)
    | ctx_snoc Δ0 b0 =>
      fun n =>
        match n with
        | 0 =>
          fun p =>
            match
              p as e in (_ = y)
              return (@CatView Γ (@ctx_snoc B Δ0 b0) y (@MkInCtx y (@ctx_snoc B (ctx_cat Γ Δ0) b0) 0 e))
            with
            | eq_refl => @isCatRight Γ (@ctx_snoc B Δ0 b0) b0 (@inctx_zero b0 Δ0)
            end
        | S n => fun p => catView_succ (catView_index n p)
        end
    end.

  Definition catView {Γ Δ} {b : B} (bIn : InCtx b (ctx_cat Γ Δ)) : CatView bIn :=
    @catView_index Γ Δ b (@inctx_at _ _ bIn) (@inctx_valid _ _ bIn).

  (* Custom pattern matching in cases where the context was already refined
     by a different match, i.e. on environments. *)
  Definition inctx_case_nil {b : B} {A : Type} (bIn : InCtx b ctx_nil) : A :=
    match nilView bIn with end.
  Definition inctx_case_snoc (D : B -> Type) (Γ : Ctx B) (b0 : B) (db0 : D b0)
    (dΓ: forall b, InCtx b Γ -> D b) (b : B) (bIn: InCtx b (ctx_snoc Γ b0)) : D b :=
    let (n, e) := bIn in
    match n return ctx_nth_is (ctx_snoc Γ b0) n b -> D b with
    | 0 => fun e => match e with eq_refl => db0 end
    | S n => fun e => dΓ b (MkInCtx n e)
    end e.

  Definition InCtx_rect (b : B)
    (P : forall (Γ : Ctx B), InCtx b Γ -> Type)
    (fzero : forall (Γ : Ctx B), P (ctx_snoc Γ b) inctx_zero)
    (fsucc : forall (Γ : Ctx B) (b0 : B) (bIn : InCtx b Γ),
        P Γ bIn -> P (ctx_snoc Γ b0) (inctx_succ bIn)) :
    forall (Γ : Ctx B) (bIn : InCtx b Γ), P Γ bIn.
  Proof.
    induction Γ; cbn.
    - intro bIn. destruct (nilView bIn).
    - intros bIn. destruct (snocView bIn).
      + apply fzero.
      + now apply fsucc.
  Defined.

  Definition InCtx_ind (b : B)
    (P : forall (Γ : Ctx B), InCtx b Γ -> Prop)
    (fzero : forall (Γ : Ctx B), P (ctx_snoc Γ b) inctx_zero)
    (fsucc : forall (Γ : Ctx B) (b0 : B) (bIn : InCtx b Γ),
        P Γ bIn -> P (ctx_snoc Γ b0) (inctx_succ bIn)) :
    forall (Γ : Ctx B) (bIn : InCtx b Γ), P Γ bIn :=
    InCtx_rect P fzero fsucc.

  (* Boolean equality of [nat]-fields in [InCtx] implies equality of
     the other field and the binding-index of [InCtx] *)
  Lemma inctx_at_exact {Γ : Ctx B} (b1 b2 : B)
        (b1In : InCtx b1 Γ) (b2In : InCtx b2 Γ) :
    @inctx_at _ _ b1In = @inctx_at _ _ b2In ->
    b1 = b2 /\
    (ctx_nth_is Γ (@inctx_at _ _ b1In) b1 = ctx_nth_is Γ (@inctx_at _ _ b2In) b2).
  Proof.
    intros.
    assert (b1 = b2) as bindings_eq.
    { generalize dependent b2.
      induction b1In using InCtx_ind; destruct b2In as [[|n] e];
      intros; cbn in *; try congruence.
      apply IHb1In with (MkInCtx n e).
      cbn; congruence. }
    split.
    - exact bindings_eq.
    - subst. f_equal. assumption.
  Qed.

  Fixpoint ctx_remove (Γ : Ctx B) {b : B} : InCtx b Γ -> Ctx B :=
    match Γ with
    | ctx_nil =>
      fun '(MkInCtx n e) =>
        match e with end
    | ctx_snoc Γ b' =>
      fun '(MkInCtx n e) =>
        match n return (ctx_nth_is (ctx_snoc Γ b') n b -> Ctx B)
        with
        | 0   => fun _ => Γ
        | S n => fun e  => ctx_snoc (@ctx_remove Γ b (MkInCtx n e)) b'
        end e
    end.
  Arguments ctx_remove _ [_] _.

  Fixpoint shift_index {b x} {Σ : Ctx B} {struct Σ} :
    forall
      (bn xn : nat) (bp : ctx_nth_is Σ bn b)
      (xp : ctx_nth_is (ctx_remove Σ {| inctx_valid := bp |}) xn x),
      InCtx x Σ :=
    match Σ with
    | ctx_nil => fun _ _ (bp : ctx_nth_is ctx_nil _ _) => match bp with end
    | ctx_snoc Σ b =>
      fun bn xn =>
        match bn , xn with
        | O    , xn   => fun bp xp => inctx_succ (MkInCtx xn xp)
        | S bn , O    => fun bp xp => MkInCtx (Γ := ctx_snoc Σ b) O xp
        | S bn , S xn => fun bp xp => inctx_succ (shift_index bn xn bp xp)
        end
    end.

  Definition shift_var {b x} {Σ : Ctx B} (bIn : InCtx b Σ) (xIn : InCtx x (ctx_remove Σ bIn)) : InCtx x Σ :=
    shift_index (inctx_at bIn) (inctx_at xIn) (inctx_valid bIn) (inctx_valid xIn).

  (* Most explicit type-signatures given below are only necessary for Coq 8.9
     and can be cleaned up for later versions. *)
  Fixpoint occurs_check_index {Σ} {x y : B} (m n : nat) {struct Σ} :
    forall (p : ctx_nth_is Σ m x) (q : ctx_nth_is Σ n y),
      (x = y) + (InCtx y (ctx_remove _ {| inctx_at := m; inctx_valid := p |})) :=
    match Σ with
    | ctx_nil => fun _ (q : ctx_nth_is ctx_nil n y) => match q with end
    | ctx_snoc Σ b =>
      match m , n with
      | 0   , 0   => fun (p : ctx_nth_is (ctx_snoc Σ b) 0 x) q =>
                       inl (eq_trans (eq_sym p) q)
      | 0   , S n => fun p (q : ctx_nth_is (ctx_snoc Σ b) (S n) y) =>
                       inr (@MkInCtx _ (ctx_remove _ (@MkInCtx _ (ctx_snoc Σ b) 0 p)) n q)
      | S m , 0   => fun _ (q : ctx_nth_is (ctx_snoc Σ b) 0 y) =>
                       inr (@MkInCtx _ (ctx_snoc (ctx_remove Σ _) b) 0 q)
      | S m , S n => fun p q => base.sum_map id inctx_succ (occurs_check_index m n p q)
      end
    end.

  Definition occurs_check_var {Σ} {x y : B} (xIn : InCtx x Σ) (yIn : InCtx y Σ) : (x = y) + (InCtx y (ctx_remove Σ xIn)) :=
    occurs_check_index (inctx_at xIn) (inctx_at yIn) (inctx_valid xIn) (inctx_valid yIn).

  Inductive OccursCheckView {Σ} {x : B} (xIn : InCtx x Σ) : forall y, InCtx y Σ -> Set :=
  | Same : OccursCheckView xIn xIn
  | Diff {y} (yIn : InCtx y (ctx_remove Σ xIn)) : OccursCheckView xIn (shift_var xIn yIn).

  Definition occurs_check_view_step {Σ} {b x y: B} (xIn : InCtx x Σ) (yIn : InCtx y Σ) :
    OccursCheckView xIn yIn ->
    OccursCheckView (Σ := ctx_snoc Σ b) (inctx_succ xIn) (inctx_succ yIn) :=
    fun v =>
    match v with
    | Same _     => Same (inctx_succ xIn)
    | Diff _ yIn => Diff (inctx_succ xIn) (inctx_succ yIn)
    end.

  Fixpoint occurs_check_view_index {Σ} {x y: B} {m n : nat} {struct Σ} :
    forall (p : ctx_nth_is Σ m x) (q : ctx_nth_is Σ n y),
      OccursCheckView
        {| inctx_at := m; inctx_valid := p |}
        {| inctx_at := n; inctx_valid := q |} :=
    match Σ with
    | ctx_nil => fun _ (q : ctx_nth_is ctx_nil n y) => match q with end
    | ctx_snoc Σ b =>
      match m , n with
      | 0   , 0   => fun (p : ctx_nth_is (ctx_snoc Σ b) 0 x) q =>
               match p , q with
               | eq_refl , eq_refl =>
                 Same (@MkInCtx b (@ctx_snoc B Σ b) 0 eq_refl)
               end
      | 0   , S n => fun p (q : ctx_nth_is (ctx_snoc Σ b) (S n) y) =>
                       Diff
                         (@MkInCtx x (@ctx_snoc B Σ b) 0 p)
                         (@MkInCtx y Σ n q)
      | S m , 0   => fun p (q : ctx_nth_is (ctx_snoc Σ b) 0 y) =>
                       Diff
                         (@MkInCtx x (@ctx_snoc B Σ b) (S m) p)
                         (@MkInCtx _ (ctx_snoc (ctx_remove Σ _) b) 0 q)
      | S m , S n => fun p q =>
                       occurs_check_view_step
                         (@occurs_check_view_index Σ x y m n p q)
      end
    end.

  Definition occurs_check_view {Σ} {x y: B} (xIn : InCtx x Σ) (yIn : InCtx y Σ) : OccursCheckView xIn yIn :=
    occurs_check_view_index (inctx_valid xIn) (inctx_valid yIn).

  Lemma occurs_check_var_spec {Σ} {x y : B} (xIn : InCtx x Σ) (yIn : InCtx y Σ) :
    match occurs_check_var xIn yIn with
    | inl e    => eq_rect x (fun z => InCtx z Σ) xIn y e = yIn
    | inr yIn' => yIn = shift_var xIn yIn' /\ inctx_at xIn <> inctx_at yIn
    end%type.
  Proof.
    unfold occurs_check_var, shift_var; destruct yIn as [n q]; revert n q.
    induction xIn using InCtx_ind; intros n q.
    - destruct n.
      + now destruct q.
      + split. reflexivity. cbn. intuition.
    - destruct n; cbn.
      + split. reflexivity. intuition.
      + specialize (IHxIn n q); revert IHxIn; cbn.
        destruct (occurs_check_index (inctx_at xIn) n (inctx_valid xIn) q).
        * destruct e; cbn. now intros ->.
        * destruct xIn as [m p]; cbn. intros [<- ?]. intuition.
  Qed.

  Lemma occurs_check_var_refl {Σ x} (xIn : InCtx x Σ) :
    occurs_check_var xIn xIn = inl eq_refl.
  Proof.
    unfold occurs_check_var.
    induction xIn using InCtx_ind.
    - reflexivity.
    - cbn; now rewrite IHxIn.
  Qed.

  Lemma occurs_check_shift_var {x y} {Σ : Ctx B} (xIn : InCtx x Σ) (yIn : InCtx y (ctx_remove Σ xIn)) :
    occurs_check_var xIn (shift_var xIn yIn) = inr yIn.
  Proof.
    unfold occurs_check_var, shift_var. destruct yIn as [m p]. cbn.
    revert m p.
    induction xIn using InCtx_ind.
    - reflexivity.
    - intros [|m]; cbn.
      + reflexivity.
      + intros p.
        now rewrite (IHxIn m p).
  Qed.

  Fixpoint ctx_forallb (Γ : Ctx B) : (forall b, InCtx b Γ -> bool) -> bool :=
    match Γ with
    | ctx_nil      => fun _ => true
    | ctx_snoc Γ b => fun p => p b inctx_zero && ctx_forallb (fun b bIn => p b (inctx_succ bIn))
    end.

  Fixpoint flip_remove_index {Γ : Ctx B} {y x} (n m : nat) {struct Γ} :
    forall
      (q : ctx_nth_is Γ n y)
      (p : ctx_nth_is (ctx_remove Γ {| inctx_at := n; inctx_valid := q |}) m x),
      InCtx y (ctx_remove Γ (shift_index n m q p)) :=
   match Γ with
   | ctx_nil => fun q => match q with end
   | ctx_snoc Γ b =>
       match n with
       | 0 =>
         fun q p =>
           @MkInCtx y (ctx_remove (ctx_snoc Γ b) (shift_index 0 m q p)) 0 q
       | S n =>
         fun q =>
           match m with
           | 0 => fun _ => @MkInCtx y Γ n q
           | S m => fun p => inctx_succ (flip_remove_index n m q p)
           end
       end
   end.

  (* Calculates x ∈ Γ - y => y ∈ Γ - x *)
  Definition flip_remove {Γ : Ctx B} {y x : B} (yIn : InCtx y Γ) (xIn : InCtx x (@ctx_remove Γ y yIn)) :
    InCtx y (@ctx_remove Γ x (@shift_var y x Γ yIn xIn)) :=
    flip_remove_index (inctx_at yIn) (inctx_at xIn) (inctx_valid yIn) (inctx_valid xIn).

  (* Σ - y - x = Σ - x - y *)
  Lemma swap_remove {Γ : Ctx B} {y x} (yIn : InCtx y Γ) (xIn : InCtx x (ctx_remove Γ yIn)) :
    ctx_remove (ctx_remove Γ yIn) xIn =
    ctx_remove (ctx_remove Γ (shift_var yIn xIn)) (flip_remove yIn xIn).
  Proof.
    destruct yIn as [n q], xIn as [m p]. cbn in *.
    unfold shift_var. cbn.
    revert n q m p.
    induction Γ; intros n q m p.
    destruct q.
    destruct n; cbn in q.
    - reflexivity.
    - destruct m; cbn in p.
      + reflexivity.
      + cbn in *. f_equal. apply IHΓ.
  Defined.

End WithBinding.
Arguments InCtx_ind [B b] _ _ _ [_].
Arguments ctx_forallb [B] Γ p.

Section WithAB.
  Context {A B : Set} (f : A -> B).

  Fixpoint ctx_map (Γ : Ctx A) : Ctx B :=
    match Γ with
    | ctx_nil      => ctx_nil
    | ctx_snoc Γ a => ctx_snoc (ctx_map Γ) (f a)
    end.

  Fixpoint inctx_map {a : A} {Γ : Ctx A} {struct Γ} : InCtx a Γ -> InCtx (f a) (ctx_map Γ) :=
   match Γ return InCtx a Γ -> InCtx (f a) (ctx_map Γ) with
   | ctx_nil => inctx_case_nil
   | ctx_snoc Γ b =>
     fun aInΓb  =>
       match inctx_at aInΓb as n return ctx_nth_is (ctx_snoc Γ b) n a -> _ with
       | 0   => fun p => @MkInCtx _ _ (ctx_snoc _ _) 0 (f_equal f p)
       | S n => fun p => inctx_succ (inctx_map {| inctx_at := n; inctx_valid := p |})
       end (inctx_valid aInΓb)
   end.

End WithAB.

(* Section Binding. *)

(*   Local Set Primitive Projections. *)
(*   Local Set Transparent Obligations. *)

(*   Context (N T : Set) {eqN : EqDec N} {eqT : EqDec T}. *)

(*   Record Binding : Set := *)
(*     MkBinding *)
(*       { name :> N; *)
(*         type :> T; *)
(*       }. *)
(*   Derive NoConfusion EqDec for Binding. *)

(* End Binding. *)
(* Arguments MkBinding {N T} name type. *)
(* Arguments name {N T} b. *)
(* Arguments type {N T} b. *)

Module CtxNotations.

  Notation NCtx Name Data := (Ctx (Name * Data)).
  (* DEPRECATED *)
  (* NB: ∶ ≠ : *)
  (*    To typeset the next notation, use \: *)
  Notation "x ∶ τ" := (x,τ) (only parsing) : ctx_scope.
  Notation "x :: τ" := (x , τ) : ctx_scope.

  Notation "'ε'" := ctx_nil : ctx_scope.
  Infix "▻" := ctx_snoc : ctx_scope.
  Notation "Γ1 ▻▻ Γ2" := (ctx_cat Γ1%ctx Γ2%ctx) : ctx_scope.
  Notation "b ∈ Γ" := (InCtx b%ctx Γ%ctx) : type_scope.

  Notation "[ x ]" := (ctx_snoc ctx_nil x)  : ctx_scope.
  Notation "[ x , .. , z ]" := (ctx_snoc .. (ctx_snoc ctx_nil x) .. z) : ctx_scope.
  Notation "Γ - x" := (@ctx_remove _ Γ x _) : ctx_scope.

End CtxNotations.

Open Scope ctx_scope.
Import CtxNotations.

Section Resolution.

  Context {Name : Set} {Name_eqdec : EqDec Name} {D : Set}.

  Fixpoint ctx_resolve (Γ : NCtx Name D) (x : Name) {struct Γ} : option D :=
    match Γ with
    | ε        => None
    | Γ ▻ y::d => if Name_eqdec x y then Some d else ctx_resolve Γ x
    end.

  Fixpoint mk_inctx (Γ : NCtx Name D) (x : Name) {struct Γ} :
    let m := ctx_resolve Γ x in forall (p : IsSome m), x::fromSome m p ∈ Γ :=
    match Γ with
    | ε => fun p => match p with end
    | Γ ▻ y::d =>
      match Name_eqdec x y as s return
        (forall p, (x::fromSome (if s then Some d else ctx_resolve Γ x) p) ∈ Γ ▻ y::d)
      with
      | left e => fun _ => match e with eq_refl => inctx_zero end
      | right _ => fun p => inctx_succ (mk_inctx Γ x p)
      end
    end.

  Fixpoint ctx_names (Γ : NCtx Name D) : list Name :=
    match Γ with
    | ε          => nil
    | Γ ▻ (y::_) => cons y (ctx_names Γ)
    end.

End Resolution.

Module NameResolution.

  (* Hook the reflective procedure for name resolution into the typeclass
     resolution mechanism. *)
  Hint Extern 10 (InCtx (?x :: _) ?Γ) =>
    let xInΓ := eval compute in (mk_inctx Γ x tt) in
      exact xInΓ : typeclass_instances.

End NameResolution.

Section FreshName.

  Local Open Scope string_scope.

  Fixpoint split_at_dot' {R} (x : string) (k : string -> string -> R) {struct x} : R :=
    match x with
    | ""           => k "" ""
    | String "." x => k "" x
    | String a x   => split_at_dot' x (fun pre => k (String a pre))
    end.

  Definition split_at_dot (x : string) : (string * string) :=
    split_at_dot' x pair.

  Definition parse_number (x : string) : N :=
    match NilEmpty.uint_of_string x with
    | Some n => N.of_uint n
    | None   => 0%N
    end.

  Definition unparse_number (x : N) : string :=
    NilEmpty.string_of_uint (N.to_uint x).

  Definition max_with_base (base : string) (xs : list string) : N :=
    List.fold_left
      (fun o x =>
         match split_at_dot x with
           (pre,suf) => if pre =? base
                        then N.max o (parse_number suf)
                        else o
         end)
      xs 0%N.

  Definition fresh {T : Set} (xs : Ctx (string * T)) (x : option string) : string :=
    let xs := ctx_names xs in
    let x := match x with Some x => x | None => "x" end in
    if List.find (String.eqb x) xs
    then let base := fst (split_at_dot x) in
         let n    := N.succ (max_with_base base xs) in
         String.append base (String "."%char (unparse_number n))
    else x.

End FreshName.
