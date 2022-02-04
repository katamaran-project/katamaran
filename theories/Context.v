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
     Bool.Bool
     NArith.BinNat
     Numbers.DecimalString
     Strings.Ascii
     Strings.String.

From Equations Require Import Equations.
From Katamaran Require Import
     Notations Prelude.

Local Set Implicit Arguments.

Declare Scope ctx_scope.
Delimit Scope ctx_scope with ctx.

Module Binding.

  (* Local Set Primitive Projections. *)
  Local Set Transparent Obligations.

  Section WithNT.
    Context (N T : Set).

    Record Binding : Set :=
      MkB { name :> N; type :> T; }.

    Context {eqN : EqDec N} {eqT : EqDec T}.
    Derive NoConfusion EqDec for Binding.

  End WithNT.

  Arguments MkB [N T] name type.
  Arguments name {N T} b.
  Arguments type {N T} b.

End Binding.
Export Binding.

Module ctx.

  (* Type of contexts. This is a list of bindings of type B. This type and
     subsequent types use the common notation of snoc lists. *)
  Inductive Ctx (B : Set) : Set :=
  | nil
  | snoc (Γ : Ctx B) (b : B).

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive NoConfusion for Ctx.
  End TransparentObligations.

  Arguments nil {_}.
  Arguments snoc {_} _%ctx _%ctx.

  Section WithBinding.
    Context {B : Set}.

    Global Instance eq_dec_ctx (eqB : EqDec B) : EqDec (Ctx B) :=
      fix eq_dec_ctx (Γ Δ : Ctx B) {struct Γ} : dec_eq Γ Δ :=
        match Γ , Δ with
        | nil      , nil      => left eq_refl
        | snoc Γ b , snoc Δ c => f_equal2_dec snoc noConfusion_inv
                                   (eq_dec_ctx Γ Δ) (eq_dec b c)
        | _        , _        => right noConfusion_inv
        end.

    Fixpoint lookup (Γ : Ctx B) (n : nat) : option B :=
      match Γ , n with
      | snoc _ b , O   => Some b
      | snoc Γ _ , S n => lookup Γ n
      | _        , _   => None
      end.

    (* Concatenation of two contexts. *)
    Fixpoint cat (Γ1 Γ2 : Ctx B) {struct Γ2} : Ctx B :=
      match Γ2 with
      | nil       => Γ1
      | snoc Γ2 τ => snoc (cat Γ1 Γ2) τ
      end.

    (* This is a predicate that that encodes that the de Bruijn index n points
       to the binding b in Γ. *)
    Fixpoint nth_is (Γ : Ctx B) (n : nat) (b : B) {struct Γ} : Prop :=
      match Γ , n with
      | snoc _ x , O   => x = b
      | snoc Γ _ , S n => nth_is Γ n b
      | _        , _   => False
      end.

    Lemma nth_is_right_exact {Γ : Ctx B} (n : nat) (b1 b2 : B) :
      nth_is Γ n b1 -> nth_is Γ n b2 -> b1 = b2.
    Proof.
      revert n.
      induction Γ.
      - intros ? [].
      - cbn in *.
        destruct n. intros e1 e2.
        refine (eq_trans _ e2).
        apply eq_sym. auto.
        apply IHΓ.
    Qed.

    Section WithUIP.

      Context {UIP_B : UIP B}.

      Fixpoint proof_irrelevance_nth_is {Γ} (n : nat) (b : B) {struct Γ} :
        forall (p q : nth_is Γ n b), p = q :=
        match Γ with
        | nil       => fun p q => match q with end
        | snoc Γ b' => match n with
                       | 0   => uip
                       | S n => proof_irrelevance_nth_is n b
                       end
        end.

      Global Instance eqdec_ctx_nth {Γ n b} : EqDec (nth_is Γ n b).
      Proof. intros p q. left. apply proof_irrelevance_nth_is. Defined.

      Lemma proof_irrelevance_nth_is_refl {Γ} (n : nat) (b : B) (p : nth_is Γ n b) :
        proof_irrelevance_nth_is n b p p = eq_refl.
      Proof. apply uip. Qed.

    End WithUIP.

    Section In.
      (* Set locally only for the definition of In. *)
      Local Set Primitive Projections.

       (* InCtx represents context containment proofs. This is essentially a
          well-typed de Bruijn index, i.e. a de Bruijn index with a proof that it
          resolves to the binding b. This record type is defined using primitive
          projections to get eta-conversion definitionally. *)
      Class In (b : B) (Γ : Ctx B) : Set :=
        MkIn
          { in_at: nat;
            in_valid: nth_is Γ in_at b
          }.

      Global Arguments MkIn [_ _] _ _.
      Global Arguments in_at [_ _] _.
      Global Arguments in_valid [_ _] _.

      Global Program Instance NoConfusionPackage_In {uip_B : UIP B} {b Γ} : NoConfusionPackage (In b Γ) :=
         {| NoConfusion xIn yIn := NoConfusion (in_at xIn) (in_at yIn);
            noConfusion xIn yIn (e : NoConfusion (in_at xIn) (in_at yIn)) :=
              match noConfusion e in _ = y
                return forall q, xIn = {| in_at := y; in_valid := q |}
              with
              | eq_refl => fun q => f_equal (MkIn _) (proof_irrelevance_nth_is _ _ (in_valid xIn) q)
              end (in_valid yIn);
            noConfusion_inv (xIn yIn : In b Γ) (e : xIn = yIn) :=
              noConfusion_inv (f_equal (@in_at b Γ) e);
         |}.
      Next Obligation.
        intros ? ? ? [m p] [n q] e. cbn [in_at] in *.
        change (NoConfusion _ _) with (NoConfusion m n) in e.
        destruct (noConfusion e) eqn:?. cbn.
        destruct (proof_irrelevance_nth_is m b p q). cbn.
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
        - cbn. rewrite proof_irrelevance_nth_is_refl. reflexivity.
        - cbn. rewrite proof_irrelevance_nth_is_refl. reflexivity.
      Qed.

    End In.

    (* Two proofs of context containment are equal of the deBruijn indices are equal *)
    Definition In_eqb {Γ} {b1 b2 : B} (b1inΓ : In b1 Γ) (b2inΓ : In b2 Γ) : bool :=
      Nat.eqb (in_at b1inΓ) (in_at b2inΓ).

    Lemma In_eqb_spec `{UIP B} {Γ} {b1 b2 : B} (b1inΓ : In b1 Γ) (b2inΓ : In b2 Γ) :
      reflect
        (existT _ b1inΓ = existT _ b2inΓ :> sigT (fun b => In b Γ))
        (In_eqb b1inΓ b2inΓ).
    Proof.
      destruct b1inΓ as [m p], b2inΓ as [n q]; cbn.
      destruct (NPeano.Nat.eqb_spec m n); constructor.
      - subst. pose proof (nth_is_right_exact _ _ _ p q). subst.
        f_equal. f_equal. apply proof_irrelevance_nth_is.
      - intros e. depelim e. destruct n, m; cbn in H0; congruence.
    Qed.

    (* These are *constructors* for In. *)
    Definition in_zero {b : B} {Γ : Ctx B} : In b (snoc Γ b) :=
      @MkIn _ (snoc Γ b) 0 eq_refl.
    Definition in_succ {b : B} {Γ : Ctx B} {b' : B} (bIn : In b Γ) :
      In b (snoc Γ b') :=
      @MkIn _ (snoc Γ b') (S (in_at bIn)) (in_valid bIn).

    Inductive NilView {b : B} (i : In b nil) : Set :=.

    Definition nilView {b : B} (i : In b nil) : NilView i :=
      match in_valid i with end.

    Inductive SnocView (Γ : Ctx B) {b' : B} : forall b, In b (snoc Γ b') -> Set :=
    | snocViewZero                  : SnocView in_zero
    | snocViewSucc {b} (i : In b Γ) : SnocView (in_succ i).
    Global Arguments snocViewZero {_ _}.

    Definition snocView {Γ} {b b' : B} (i : In b (snoc Γ b')) :
      @SnocView Γ b' b i :=
      match in_at i as n return forall p, SnocView (MkIn n p)
      with
      | O   => fun p => match p with eq_refl => snocViewZero end
      | S n => fun p => snocViewSucc (MkIn n p)
      end (in_valid i).

    (* Custom pattern matching in cases where the context was already refined
       by a different match, i.e. on environments. *)
    Definition in_case_nil {A : B -> Type} [b : B] (bIn : In b nil) : A b :=
      match nilView bIn with end.
    (* DEPRECATED *)
    Definition in_case_snoc (D : B -> Type) (Γ : Ctx B) (b0 : B) (db0 : D b0)
      (dΓ: forall b, In b Γ -> D b) (b : B) (bIn: In b (snoc Γ b0)) : D b :=
      let (n, e) := bIn in
      match n return nth_is (snoc Γ b0) n b -> D b with
      | 0 => fun e => match e with eq_refl => db0 end
      | S n => fun e => dΓ b (MkIn n e)
      end e.

    Inductive InView {b : B} : forall Γ, In b Γ -> Set :=
    | inctxViewZero {Γ}                 : @InView b (snoc Γ b) in_zero
    | inctxViewSucc {Γ b'} (i : In b Γ) : @InView b (snoc Γ b') (in_succ i).

    Definition inView {b Γ} : forall bIn : In b Γ, InView bIn :=
      match Γ with
      | nil      => fun bIn => match nilView bIn with end
      | snoc Γ b => fun bIn =>
        match snocView bIn with
        | snocViewZero   => inctxViewZero
        | snocViewSucc i => inctxViewSucc i
        end
      end.

    Fixpoint in_cat_left {b : B} {Γ : Ctx B} (Δ : Ctx B) (bIn : In b Γ) : In b (cat Γ Δ) :=
      match Δ with
      | nil      => bIn
      | snoc Δ _ => in_succ (in_cat_left Δ bIn)
      end.

    Fixpoint in_cat_right {b : B} {Γ : Ctx B} (Δ : Ctx B) : In b Δ -> In b (cat Γ Δ) :=
      match Δ with
      | nil      => fun bIn => match nilView bIn with end
      | snoc _ _ =>
        fun bIn =>
          match snocView bIn with
          | snocViewZero => in_zero
          | snocViewSucc bIn => in_succ (in_cat_right bIn)
          end
      end.

    Inductive CatView {Γ Δ} {b : B} : In b (cat Γ Δ) -> Set :=
    | isCatLeft  (bIn : In b Γ) : CatView (in_cat_left Δ bIn)
    | isCatRight (bIn : In b Δ) : CatView (in_cat_right bIn).

    Definition catView_succ {Γ Δ b b'} (bIn : In b (cat Γ Δ)) (bInV : CatView bIn) :
      @CatView Γ (snoc Δ b') b (in_succ bIn) :=
      match bInV with
      | isCatLeft bIn => @isCatLeft Γ (@snoc B Δ b') b bIn
      | isCatRight bIn => @isCatRight Γ (@snoc B Δ b') b (@in_succ b Δ b' bIn)
      end.

    Fixpoint catView_index {Γ Δ} {b : B} {struct Δ} :
      forall (n : nat) (p : nth_is (cat Γ Δ) n b),
        @CatView Γ Δ b (@MkIn b (cat Γ Δ) n p) :=
      match Δ with
      | nil => fun n p => @isCatLeft Γ (@nil B) b (@MkIn b Γ n p)
      | snoc Δ0 b0 =>
        fun n =>
          match n with
          | 0 =>
            fun p =>
              match
                p as e in (_ = y)
                return (@CatView Γ (@snoc B Δ0 b0) y (@MkIn y (@snoc B (cat Γ Δ0) b0) 0 e))
              with
              | eq_refl => @isCatRight Γ (@snoc B Δ0 b0) b0 (@in_zero b0 Δ0)
              end
          | S n => fun p => catView_succ (catView_index n p)
          end
      end.

    Definition catView {Γ Δ} {b : B} (bIn : In b (cat Γ Δ)) : CatView bIn :=
      @catView_index Γ Δ b (@in_at _ _ bIn) (@in_valid _ _ bIn).

    Definition In_rect (b : B)
      (P : forall (Γ : Ctx B), In b Γ -> Type)
      (fzero : forall (Γ : Ctx B), P (snoc Γ b) in_zero)
      (fsucc : forall (Γ : Ctx B) (b0 : B) (bIn : In b Γ),
          P Γ bIn -> P (snoc Γ b0) (in_succ bIn)) :
      forall (Γ : Ctx B) (bIn : In b Γ), P Γ bIn.
    Proof.
      induction Γ; cbn.
      - intro bIn. destruct (nilView bIn).
      - intros bIn. destruct (snocView bIn).
        + apply fzero.
        + now apply fsucc.
    Defined.
    Global Arguments In_rect [_] _.

    Definition In_ind (b : B)
      (P : forall (Γ : Ctx B), In b Γ -> Prop)
      (fzero : forall (Γ : Ctx B), P (snoc Γ b) in_zero)
      (fsucc : forall (Γ : Ctx B) (b0 : B) (bIn : In b Γ),
          P Γ bIn -> P (snoc Γ b0) (in_succ bIn)) :
      forall (Γ : Ctx B) (bIn : In b Γ), P Γ bIn :=
      In_rect P fzero fsucc.
    Global Arguments In_ind [_] _.

    (* Boolean equality of [nat]-fields in [In] implies equality of
       the other field and the binding-index of [In] *)
    Lemma in_at_exact {Γ : Ctx B} (b1 b2 : B)
          (b1In : In b1 Γ) (b2In : In b2 Γ) :
      @in_at _ _ b1In = @in_at _ _ b2In ->
      b1 = b2 /\
      (nth_is Γ (@in_at _ _ b1In) b1 = nth_is Γ (@in_at _ _ b2In) b2).
    Proof.
      intros.
      assert (b1 = b2) as bindings_eq.
      { generalize dependent b2.
        induction b1In using In_ind; destruct b2In as [[|n] e];
        intros; cbn in *; try congruence.
        apply IHb1In with (MkIn n e).
        cbn; congruence. }
      split.
      - exact bindings_eq.
      - subst. f_equal. assumption.
    Qed.

    Fixpoint remove (Γ : Ctx B) {b : B} : In b Γ -> Ctx B :=
      match Γ with
      | nil =>
        fun '(MkIn n e) =>
          match e with end
      | snoc Γ b' =>
        fun '(MkIn n e) =>
          match n return (nth_is (snoc Γ b') n b -> Ctx B)
          with
          | 0   => fun _ => Γ
          | S n => fun e  => snoc (@remove Γ b (MkIn n e)) b'
          end e
      end.
    Arguments remove _ [_] _.

    Fixpoint shift_index {b x} {Σ : Ctx B} {struct Σ} :
      forall
        (bn xn : nat) (bp : nth_is Σ bn b)
        (xp : nth_is (remove Σ {| in_valid := bp |}) xn x),
        In x Σ :=
      match Σ with
      | nil => fun _ _ (bp : nth_is nil _ _) => match bp with end
      | snoc Σ b =>
        fun bn xn =>
          match bn , xn with
          | O    , xn   => fun bp xp => in_succ (MkIn xn xp)
          | S bn , O    => fun bp xp => MkIn (Γ := snoc Σ b) O xp
          | S bn , S xn => fun bp xp => in_succ (shift_index bn xn bp xp)
          end
      end.

    Definition shift_var {b x} {Σ : Ctx B} (bIn : In b Σ) (xIn : In x (remove Σ bIn)) : In x Σ :=
      shift_index (in_at bIn) (in_at xIn) (in_valid bIn) (in_valid xIn).

    (* Most explicit type-signatures given below are only necessary for Coq 8.9
       and can be cleaned up for later versions. *)
    Fixpoint occurs_check_index {Σ} {x y : B} (m n : nat) {struct Σ} :
      forall (p : nth_is Σ m x) (q : nth_is Σ n y),
        (x = y) + (In y (remove _ {| in_at := m; in_valid := p |})) :=
      match Σ with
      | nil => fun _ (q : nth_is nil n y) => match q with end
      | snoc Σ b =>
        match m , n with
        | 0   , 0   => fun (p : nth_is (snoc Σ b) 0 x) q =>
                         inl (eq_trans (eq_sym p) q)
        | 0   , S n => fun p (q : nth_is (snoc Σ b) (S n) y) =>
                         inr (@MkIn _ (remove _ (@MkIn _ (snoc Σ b) 0 p)) n q)
        | S m , 0   => fun _ (q : nth_is (snoc Σ b) 0 y) =>
                         inr (@MkIn _ (snoc (remove Σ _) b) 0 q)
        | S m , S n => fun p q => base.sum_map id in_succ (occurs_check_index m n p q)
        end
      end.

    Definition occurs_check_var {Σ} {x y : B} (xIn : In x Σ) (yIn : In y Σ) : (x = y) + (In y (remove Σ xIn)) :=
      occurs_check_index (in_at xIn) (in_at yIn) (in_valid xIn) (in_valid yIn).

    Inductive OccursCheckView {Σ} {x : B} (xIn : In x Σ) : forall y, In y Σ -> Set :=
    | Same : OccursCheckView xIn xIn
    | Diff {y} (yIn : In y (remove Σ xIn)) : OccursCheckView xIn (shift_var xIn yIn).

    Definition occurs_check_view_step {Σ} {b x y: B} (xIn : In x Σ) (yIn : In y Σ) :
      OccursCheckView xIn yIn ->
      OccursCheckView (Σ := snoc Σ b) (in_succ xIn) (in_succ yIn) :=
      fun v =>
      match v with
      | Same _     => Same (in_succ xIn)
      | Diff _ yIn => Diff (in_succ xIn) (in_succ yIn)
      end.

    Fixpoint occurs_check_view_index {Σ} {x y: B} {m n : nat} {struct Σ} :
      forall (p : nth_is Σ m x) (q : nth_is Σ n y),
        OccursCheckView
          {| in_at := m; in_valid := p |}
          {| in_at := n; in_valid := q |} :=
      match Σ with
      | nil => fun _ (q : nth_is nil n y) => match q with end
      | snoc Σ b =>
        match m , n with
        | 0   , 0   => fun (p : nth_is (snoc Σ b) 0 x) q =>
                         match p , q with
                         | eq_refl , eq_refl =>
                             Same (@MkIn b (@snoc B Σ b) 0 eq_refl)
                         end
        | 0   , S n => fun p (q : nth_is (snoc Σ b) (S n) y) =>
                         Diff
                           (@MkIn x (@snoc B Σ b) 0 p)
                           (@MkIn y Σ n q)
        | S m , 0   => fun p (q : nth_is (snoc Σ b) 0 y) =>
                         Diff
                           (@MkIn x (@snoc B Σ b) (S m) p)
                           (@MkIn _ (snoc (remove Σ _) b) 0 q)
        | S m , S n => fun p q =>
                         occurs_check_view_step
                           (@occurs_check_view_index Σ x y m n p q)
        end
      end.

    Definition occurs_check_view {Σ} {x y: B} (xIn : In x Σ) (yIn : In y Σ) : OccursCheckView xIn yIn :=
      occurs_check_view_index (in_valid xIn) (in_valid yIn).

    Lemma occurs_check_var_spec {Σ} {x y : B} (xIn : In x Σ) (yIn : In y Σ) :
      match occurs_check_var xIn yIn with
      | inl e    => eq_rect x (fun z => In z Σ) xIn y e = yIn
      | inr yIn' => yIn = shift_var xIn yIn' /\ in_at xIn <> in_at yIn
      end%type.
    Proof.
      unfold occurs_check_var, shift_var; destruct yIn as [n q]; revert n q.
      induction xIn using In_ind; intros n q.
      - destruct n.
        + now destruct q.
        + split. reflexivity. cbn. intuition.
      - destruct n; cbn.
        + split. reflexivity. intuition.
        + specialize (IHxIn n q); revert IHxIn; cbn.
          destruct (occurs_check_index (in_at xIn) n (in_valid xIn) q).
          * destruct e; cbn. now intros ->.
          * destruct xIn as [m p]; cbn. intros [<- ?]. intuition.
    Qed.

    Lemma occurs_check_var_refl {Σ x} (xIn : In x Σ) :
      occurs_check_var xIn xIn = inl eq_refl.
    Proof.
      unfold occurs_check_var.
      induction xIn using In_ind.
      - reflexivity.
      - cbn; now rewrite IHxIn.
    Qed.

    Lemma occurs_check_shift_var {Σ x y} (xIn : In x Σ) (yIn : In y (remove Σ xIn)) :
      occurs_check_var xIn (shift_var xIn yIn) = inr yIn.
    Proof.
      unfold occurs_check_var, shift_var. destruct yIn as [m p]. cbn.
      revert m p.
      induction xIn using In_ind.
      - reflexivity.
      - intros [|m]; cbn.
        + reflexivity.
        + intros p.
          now rewrite (IHxIn m p).
    Qed.

    Local Open Scope lazy_bool_scope.

    Fixpoint forallb (Γ : Ctx B) : (forall b, In b Γ -> bool) -> bool :=
      match Γ with
      | nil      => fun _ => true
      | snoc Γ b => fun p => p b in_zero &&& forallb (fun b bIn => p b (in_succ bIn))
      end.

    Fixpoint flip_remove_index {Γ : Ctx B} {y x} (n m : nat) {struct Γ} :
      forall
        (q : nth_is Γ n y)
        (p : nth_is (remove Γ {| in_at := n; in_valid := q |}) m x),
        In y (remove Γ (shift_index n m q p)) :=
     match Γ with
     | nil => fun q => match q with end
     | snoc Γ b =>
         match n with
         | 0 =>
           fun q p =>
             @MkIn y (remove (snoc Γ b) (shift_index 0 m q p)) 0 q
         | S n =>
           fun q =>
             match m with
             | 0 => fun _ => @MkIn y Γ n q
             | S m => fun p => in_succ (flip_remove_index n m q p)
             end
         end
     end.

    (* Calculates x ∈ Γ - y => y ∈ Γ - x *)
    Definition flip_remove {Γ : Ctx B} {y x : B} (yIn : In y Γ) (xIn : In x (@remove Γ y yIn)) :
      In y (@remove Γ x (@shift_var y x Γ yIn xIn)) :=
      flip_remove_index (in_at yIn) (in_at xIn) (in_valid yIn) (in_valid xIn).

    (* Σ - y - x = Σ - x - y *)
    Lemma swap_remove {Γ : Ctx B} {y x} (yIn : In y Γ) (xIn : In x (remove Γ yIn)) :
      remove (remove Γ yIn) xIn =
      remove (remove Γ (shift_var yIn xIn)) (flip_remove yIn xIn).
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

    Lemma remove_in_cat_right {Γ Δ : Ctx B} {b : B} (bIn : In b Δ) :
      @remove (@cat Γ Δ) b (@in_cat_right b Γ Δ bIn) =
      @cat Γ (@remove Δ b bIn).
    Proof.
      induction bIn using In_rect; cbn.
      - reflexivity.
      - f_equal. auto.
    Defined.

  End WithBinding.
  Arguments In_rect [B b] _ _ _ [_].
  Arguments In_ind [B b] _ _ _ [_].
  Arguments forallb [B] Γ p.

  Section WithAB.
    Context {A B : Set} (f : A -> B).

    Fixpoint map (Γ : Ctx A) : Ctx B :=
      match Γ with
      | nil      => nil
      | snoc Γ a => snoc (map Γ) (f a)
      end.

    (* This is proof relevant because it's used in the automatic translation
       of program variables to logic variables. *)
    Definition in_map {a : A} : forall Γ, In a Γ -> In (f a) (map Γ) :=
      In_rect
        (fun Γ _ => In (f a) (map Γ))
        (fun Γ   => in_zero)
        (fun Γ _ _ => in_succ).

  End WithAB.

  Module notations.

    Open Scope ctx_scope.

    (* DEPRECATED *)
    (* NB: ∶ ≠ : *)
    (*    To typeset the next notation, use \: *)
    Notation "x ∶ τ" := (MkB x τ) (only parsing) : ctx_scope.
    Notation "x :: τ" := (MkB x τ) (only parsing) : ctx_scope.
    Notation "N ∷ T" := (Binding N T) : type_scope.
    Notation "x ∷ t" := (MkB x t) : ctx_scope.

    Notation "'ε'" := nil (only parsing) : ctx_scope.
    Infix "▻" := snoc : ctx_scope.
    Notation "Γ1 ▻▻ Γ2" := (cat Γ1%ctx Γ2%ctx) : ctx_scope.
    Notation "b ∈ Γ" := (In b%ctx Γ%ctx) : type_scope.

    (* Use the same notations as in ListNotations. *)
    Notation "[ ]" := (nil) : ctx_scope.
    Notation "[ x ]" := (snoc nil x) : ctx_scope.
    #[deprecated(since="20220204", note="Use the list compatible [ x ; .. ; z ] notation instead.")]
    Notation "[ x , y , .. , z ]" :=
      (snoc .. (snoc (snoc nil x) y) .. z)
      (only parsing) : ctx_scope.
    Notation "[ x ; y ; .. ; z ]" :=
      (snoc .. (snoc (snoc nil x) y) .. z) : ctx_scope.
    Notation "Γ - x" := (@remove _ Γ x _) : ctx_scope.

  End notations.
  Import notations.

  Local Notation NCtx N T := (Ctx (Binding N T)).

  Section Resolution.

    Context {Name : Set} {Name_eqdec : EqDec Name} {D : Set}.

    Fixpoint resolve (Γ : NCtx Name D) (x : Name) {struct Γ} : option D :=
      match Γ with
      | []      => None
      | Γ ▻ y∷d => if Name_eqdec x y then Some d else resolve Γ x
      end.

    Fixpoint resolve_mk_in (Γ : NCtx Name D) (x : Name) {struct Γ} :
      let m := resolve Γ x in forall (p : IsSome m), x∷fromSome m p ∈ Γ :=
      match Γ with
      | [] => fun p => match p with end
      | Γ ▻ y∷d =>
        match Name_eqdec x y as s return
          (forall p, (x∷fromSome (if s then Some d else resolve Γ x) p) ∈ Γ ▻ y∷d)
        with
        | left e => fun _ => match e with eq_refl => in_zero end
        | right _ => fun p => in_succ (resolve_mk_in Γ x p)
        end
      end.

    Fixpoint names (Γ : NCtx Name D) : list Name :=
      match Γ with
      | []      => List.nil
      | Γ ▻ y∷_ => cons y (names Γ)
      end.

  End Resolution.

  Module resolution.

    (* Hook the reflective procedure for name resolution into the typeclass
       resolution mechanism. *)
    #[export]
    Hint Extern 10 (?x∷_ ∈ ?Γ) =>
      let xInΓ := eval compute in (resolve_mk_in Γ x tt) in
        exact xInΓ : typeclass_instances.

  End resolution.

  Section FreshName.

    Open Scope string_scope.

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

    Definition fresh [T : Set] (xs : NCtx string T) (x : option string) : string :=
      let xs := names xs in
      let x := match x with Some x => x | None => "x" end in
      if List.find (String.eqb x) xs
      then let base := fst (split_at_dot x) in
           let n    := N.succ (max_with_base base xs) in
           String.append base (String "."%char (unparse_number n))
      else x.

  End FreshName.

End ctx.
Export ctx (Ctx).
Notation NCtx N T := (Ctx (Binding N T)).
Bind Scope ctx_scope with Ctx.
Bind Scope ctx_scope with NCtx.
