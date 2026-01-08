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
     Arith.PeanoNat
     Bool.Bool
     Classes.Morphisms
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

  Local Set Primitive Projections.
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

Module Import ctx.

  (* Type of contexts. This is a list of bindings of type B. This type and
     subsequent types use the common notation of snoc lists. *)
  #[universes(template)]
  Inductive Ctx (B : Type) : Type :=
  | nil
  | snoc (Γ : Ctx B) (b : B).

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive NoConfusion for Ctx.
  End TransparentObligations.

  Arguments nil {_}.
  Arguments snoc {_} _%_ctx _%_ctx.

  Section WithBinding.
    Context {B : Type}.

    Instance eq_dec_ctx (eqB : EqDec B) : EqDec (Ctx B) :=
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

    Definition proof_irrelevance_het_nth_is {b1 b2 : B} :
      forall {Γ n} (p1 : nth_is Γ n b1) (p2 : nth_is Γ n b2),
        existT _ p1 = existT _ p2 :=
       fix pi Γ n {struct Γ} :=
         match Γ with
         | nil => fun p q => match q with end
         | snoc Γ b =>
           match n with
           | O   => fun p q => match p , q with
                                 eq_refl , eq_refl => eq_refl
                               end
           | S n => pi Γ n
           end
         end.

    Corollary nth_is_right_exact {Γ : Ctx B} (n : nat) (b1 b2 : B)
      (p1 : nth_is Γ n b1) (p2 : nth_is Γ n b2) : b1 = b2.
    Proof. apply (f_equal projT1 (proof_irrelevance_het_nth_is p1 p2)). Qed.

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

      Instance eqdec_ctx_nth {Γ n b} : EqDec (nth_is Γ n b) :=
        fun p q => left (proof_irrelevance_nth_is n b p q).

      Definition proof_irrelevance_nth_is_refl {Γ} (n : nat) (b : B) (p : nth_is Γ n b) :
        proof_irrelevance_nth_is n b p p = eq_refl := uip _ _.

    End WithUIP.

    (* Definition of context membership proofs [In] for a well-typed de Bruijn
       representation. Ideally, we would represent [In] inductively using

         Inductive In : B -> Ctx B -> Set :=
         | in_zero {b Γ}                   : In b (snoc Γ b)
         | in_succ {b Γ b'} (bIn : In b Γ) : In b (snoc Γ b').

       However, this representation is not very efficient. Instead, we represent
       the de Bruijn index using an ordinary natural combined with a proof
       witness, i.e. a proof that the n-th element in the context from the right
       is the correct one. We package everything up in a record which is defined
       as a typeclass to automatically insert proofs (and to give us hooks to
       define name-based variable resolution later). Furthermore, the record
       (class) is defined using primitive projections to get eta-equality
       definitionally. We try to mimick the above inductive definition as much
       as possible and define case analysis and elimination schemes for the
       record that coincide with the ones that would be derived for the
       inductive type. *)
    #[projections(primitive)]
    Class In (b : B) (Γ : Ctx B) : Set :=
      MkIn { in_at: nat; in_valid: nth_is Γ in_at b }.
    #[global] Arguments MkIn [_ _] _ _.
    #[global] Arguments in_at [_ _] _.
    #[global] Arguments in_valid [_ _] _.

    (* These are smart *constructors* for In. *)
    Definition in_zero {b : B} {Γ : Ctx B} : In b (snoc Γ b) :=
      @MkIn _ (snoc Γ b) 0 eq_refl.
    Definition in_succ {b : B} {Γ : Ctx B} {b' : B} (bIn : In b Γ) :
      In b (snoc Γ b') :=
      @MkIn _ (snoc Γ b') (S (in_at bIn)) (in_valid bIn).

    (* A case analysis scheme for [In]. This corresponds to a pattern match on
       the constructors. This case analysis scheme can be used to write function
       that appear to recurse over an [In] value. Coq's termination checker will
       inspect this scheme and see the pattern match on the context. This means,
       that in principle Coq should recognize recursive functions over
       membership witnesses implemented using this analysis scheme as being
       structurally recursive (in the context argument). *)
    Definition In_case (P : forall (b : B) (Γ : Ctx B), In b Γ -> Type)
      (fz : forall b Γ, P b (snoc Γ b) in_zero)
      (fs : forall b' Γ b bIn, P b (snoc Γ b') (in_succ bIn)) :
      forall [b Γ] i, P b Γ i :=
      fun b Γ =>
       match Γ with
       | nil       => fun i => match @in_valid _ _ i with end
       | snoc Γ b' =>
           fun '(MkIn n p) =>
             match n return forall p : nth_is (snoc Γ b') n b, P _ _ (MkIn n p)
             with
             | O   => fun 'eq_refl => fz b' Γ
             | S n => fun p => fs _ _ _ (MkIn n p)
             end p
       end.

    (* Manually define a recursive elimination scheme for [In] using the case
       analysis scheme above. *)
    Definition In_rect (P : forall b Γ, In b Γ -> Type)
      (fz : forall b Γ, P b (snoc Γ b) in_zero)
      (fs : forall b Γ b' bIn, P b Γ bIn -> P b (snoc Γ b') (in_succ bIn)) :
      forall b Γ bIn, P b Γ bIn :=
      fix rect b Γ bIn {struct Γ} : P b Γ bIn :=
        In_case _ fz (fun _ _ _ bIn => fs _ _ _ bIn (rect _ _ bIn)) bIn.

    Definition In_ind (P : forall b Γ, In b Γ -> Prop)
      (fz : forall b Γ, P b (snoc Γ b) in_zero)
      (fs : forall b Γ b' bIn, P b Γ bIn -> P b (snoc Γ b') (in_succ bIn)) :
      forall b Γ bIn, P b Γ bIn :=
      In_rect P fz fs.

    (* A small tactic used locally to reduce an eta-expanded [In] record. The
       eta-expansion happens quite frequently. For instance, the smart
       constructors [in_zero] and [in_succ] are implemented by pattern
       matching on a record, which therefore will need eta-reduction after
       simplification. *)
    #[local] Ltac in_eta_reduce :=
      repeat
        match goal with
        | H: context[{| in_at := in_at ?x; in_valid := in_valid ?x |}] |- _ =>
            change_no_check {| in_at := in_at x; in_valid := in_valid x |} with x in H
        | |- context[{| in_at := in_at ?x; in_valid := in_valid ?x |}] =>
            change_no_check {| in_at := in_at ?x; in_valid := in_valid ?x |} with x
        end.

    (* We define several views on [In] which allows us to define mechanisms for
       reusable dependent pattern matching. For more information on views as a
       programming technique see:
       - Ulf Norell (2009), "Dependently Typed Programming in Agda." AFP'08.
         https://doi.org/10.1007/978-3-642-04652-0_5
       - Philip Wadler (1987). "Views: a way for pattern matching to cohabit
         with data abstraction." POPL'87.
         https://doi.org/10.1145/41625.41653
       - Conor McBride & James McKinna (2004). "The view from the left." JFP'04.
         https://doi.org/10.1017/S0956796803004829 *)

    (* A view expressing that membership in the empty context is uninhabited. *)
    Variant NilView [b : B] (i : In b nil) : Type :=.

    (* A view for membership in a non-empty context. *)
    Variant SnocView {b' : B} (Γ : Ctx B) :
      forall b, In b (snoc Γ b') -> Type :=
    | isZero                  : SnocView in_zero
    | isSucc {b} (i : In b Γ) : SnocView (in_succ i).
    #[global] Arguments SnocView {_ _} [b] _.
    #[global] Arguments isZero {_ _}.

    (* Instead of defining separate view functions, that construct a value
       of the *View datatypes, we use a single definition. This way, we
       avoid definition dummy definitions the other cases like it is usually
       done in small inversions. We simply define inversions for all cases at
       once. *)
    Definition view : forall {b Γ} (bIn : In b Γ),
        match Γ return forall b, In b Γ -> Type with
        | nil      => NilView
        | snoc _ _ => SnocView
        end b bIn :=
      In_case _ (@isZero) (@isSucc).

    (* Left and right membership proofs for context concatenation. *)
    Fixpoint in_cat_left {b Γ} Δ (bIn : In b Γ) : In b (cat Γ Δ) :=
      match Δ with
      | nil      => bIn
      | snoc Δ _ => in_succ (in_cat_left Δ bIn)
      end.

    Fixpoint in_cat_right {b Γ} Δ (bIn : In b Δ) : In b (cat Γ Δ) :=
      In_case (fun b Δ _ => In b (cat Γ Δ))
        (fun _ Δ => @in_zero _ (cat Γ Δ))
        (fun _ _ _ i => in_succ (in_cat_right i)) bIn.

    (* A view for case splitting on a proof of membership in a concatenation.
       By pattern matching on this view we get the membership in the left
       respectively right side of the concatenation and refine the original
       membership proof. *)
    Inductive CatView {Γ Δ} [b : B] : In b (cat Γ Δ) -> Type :=
    | isCatLeft  (bIn : In b Γ) : CatView (in_cat_left Δ bIn)
    | isCatRight (bIn : In b Δ) : CatView (in_cat_right bIn).

    (* The view functions that constructs a concatenation view. *)
    Fixpoint catView {Γ Δ} : forall b (bIn : In b (cat Γ Δ)), CatView bIn :=
      match Δ with
      | nil       => isCatLeft
      | snoc Δ b' =>
          fun b bIn =>
            match view bIn with
            | isZero   => isCatRight in_zero
            | isSucc bIn =>
                match catView bIn with
                | isCatLeft  bIn => isCatLeft bIn
                | isCatRight bIn => isCatRight (in_succ bIn)
                end
            end
      end.

    #[program] Instance NoConfusionPackage_In {uip_B : UIP B} {b Γ} :
      NoConfusionPackage (In b Γ) :=
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
      intros ? ? ? [m p] [n q] e. cbn [in_at in_valid] in *.
      etransitivity; [|apply noConfusion_sect].
      now destruct (noConfusion e), (proof_irrelevance_nth_is m b p q).
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

    (* Two proofs of context membership are equal of the deBruijn indices are equal *)
    Definition In_eqb {Γ} {b1 b2 : B} (b1inΓ : In b1 Γ) (b2inΓ : In b2 Γ) : bool :=
      Nat.eqb (in_at b1inΓ) (in_at b2inΓ).

    Lemma In_eqb_spec {Γ} {b1 b2 : B} (b1inΓ : In b1 Γ) (b2inΓ : In b2 Γ) :
      reflect
        (existT _ b1inΓ = existT _ b2inΓ :> sigT (fun b => In b Γ))
        (In_eqb b1inΓ b2inΓ).
    Proof.
      destruct b1inΓ as [m p], b2inΓ as [n q]; cbn.
      destruct (Nat.eqb_spec m n); constructor.
      - subst. pose proof (proof_irrelevance_het_nth_is p q) as Heq.
        now dependent elimination Heq.
      - intros e. depelim e. destruct n, m; cbn in H; congruence.
    Qed.

    Section Length.
      Fixpoint length (Γ : Ctx B) : nat :=
        match Γ with
        | nil      => 0
        | snoc Γ _ => S (length Γ)
        end.
    End Length.

    Section All.

      Inductive All (P : B -> Type) : Ctx B -> Type :=
      | all_nil : All P nil
      | all_snoc {Γ b} : @All P Γ -> P b -> All P (snoc Γ b).

      Definition all_intro {P} (HP : forall b, P b) : forall Γ, All P Γ :=
        fix all_intro Γ :=
          match Γ with
          | nil      => all_nil P
          | snoc Γ b => all_snoc (all_intro Γ) (HP b)
          end.

    End All.

    Fixpoint remove (Γ : Ctx B) {b} (bIn : In b Γ) {struct Γ} : Ctx B :=
      In_case _ (fun _ Γ => Γ) (fun b' _ _ bIn => snoc (remove bIn) b') bIn.
    Arguments remove _ [_] _.

    Fixpoint shift_var {b x Γ} (bIn : In b Γ) {struct Γ} :
      In x (remove Γ bIn) -> In x Γ :=
      In_case
        (fun _ Γ xIn => In x (remove Γ xIn) -> In x Γ)
        (fun _ _ xIn => in_succ xIn)
        (fun b' Γ b bIn (xIn : In x (snoc (remove Γ bIn) b')) =>
           match view xIn with
           | isZero     => in_zero
           | isSucc xIn => in_succ (shift_var bIn xIn)
           end) bIn.

    Inductive OccursCheckView {Σ x} (xIn : In x Σ) : forall y, In y Σ -> Type :=
    | Same : OccursCheckView xIn xIn
    | Diff {y} (yIn : In y (remove Σ xIn)) : OccursCheckView xIn (shift_var xIn yIn).

    Definition occurs_check_view_step {Σ b x y} (xIn : In x Σ) (yIn : In y Σ) :
      OccursCheckView xIn yIn ->
      OccursCheckView (Σ := snoc Σ b) (in_succ xIn) (in_succ yIn) :=
      fun v =>
      match v with
      | Same _     => Same (in_succ xIn)
      | Diff _ yIn => Diff (in_succ xIn) (in_succ yIn)
      end.

    Fixpoint occurs_check_view {Γ x} (xIn : In x Γ) :
      forall {y} (yIn : In y Γ), OccursCheckView xIn yIn :=
      In_case
        (fun x Γ xIn => forall y (yIn : In y Γ), OccursCheckView xIn yIn)
        (fun x Γ y (yIn : In y (snoc Γ x)) =>
           match view yIn with
           | isZero     => Same in_zero
           | isSucc yIn => Diff in_zero yIn
           end)
        (fun z Γ x (xIn : In x Γ) y (yIn : In y (snoc Γ z)) =>
           match view yIn with
           | isZero     => Diff (in_succ xIn) in_zero
           | isSucc yIn => occurs_check_view_step (occurs_check_view xIn yIn)
           end) xIn.

    Lemma occurs_check_view_refl {Γ x} (xIn : In x Γ) :
      occurs_check_view xIn xIn = Same _.
    Proof. induction xIn using In_ind; cbn; in_eta_reduce; now rewrite ?IHxIn. Qed.

    Lemma occurs_check_view_shift {Σ x y} (xIn : In x Σ) (yIn : In y (remove Σ xIn)) :
      occurs_check_view xIn (shift_var xIn yIn) = Diff xIn yIn.
    Proof.
      induction xIn using In_ind; [easy|].
      change_no_check (In y (snoc (remove Γ xIn) b')) in yIn.
      destruct (view yIn); [easy|]. cbn. in_eta_reduce. now rewrite IHxIn.
    Qed.

    Local Open Scope lazy_bool_scope.

    Fixpoint forallb (Γ : Ctx B) : (forall b, In b Γ -> bool) -> bool :=
      match Γ with
      | nil      => fun _ => true
      | snoc Γ b => fun p => p b in_zero &&& forallb (fun b bIn => p b (in_succ bIn))
      end.

    (* Calculates x ∈ Γ - y => y ∈ Γ - x *)
    Fixpoint flip_remove {Γ y} (yIn : In y Γ) :
      forall {x} (xIn : In x (remove Γ yIn)),
        In y (remove Γ (shift_var yIn xIn)) :=
      In_case
        (fun y Γ yIn =>
           forall x (xIn : In x (remove Γ yIn)),
             In y (remove Γ (shift_var yIn xIn)))
        (fun _ _ _ _ => in_zero)
        (fun b' Γ y yIn x (xIn : In x (snoc (remove Γ yIn) b')) =>
           match view xIn in SnocView xIn
           return In y (remove (snoc Γ b') (shift_var (in_succ yIn) xIn))
           with
           | isZero     => yIn
           | isSucc xIn => in_succ (flip_remove yIn xIn)
           end) yIn.

    (* Σ - y - x = Σ - x - y *)
    Lemma swap_remove {Γ : Ctx B} {y} (yIn : In y Γ) :
      forall x (xIn : In x (remove Γ yIn)),
        remove (remove Γ yIn) xIn =
        remove (remove Γ (shift_var yIn xIn)) (flip_remove yIn xIn).
    Proof.
      induction yIn using In_ind; [easy|].
      change_no_check (remove (snoc ?Γ ?b) (in_succ ?xIn))
        with (snoc (remove Γ xIn) b).
      intros x xIn; destruct (view xIn); cbn; in_eta_reduce; now f_equal.
    Defined.

    Definition f_equal_snoc (b : B) Γ Δ (e : Γ = Δ) : snoc Γ b = snoc Δ b :=
      f_equal (fun Γ => snoc Γ b) e.

    Definition eq_sym_map_snoc_distr (b : B) (x y : Ctx B) (e : x = y) :
      eq_sym (f_equal_snoc b e) = f_equal_snoc b (eq_sym e) :=
      eq_sym_map_distr (fun Γ => snoc Γ b) e.

    Definition map_snoc_subst_map (b : B) (Q : Ctx B -> Type)
      (x y : Ctx B) (e : x = y) (z : Q (snoc x b)) :
      eq_rect (snoc x b) Q z (snoc y b) (f_equal_snoc b e) =
      eq_rect x (fun x => Q (snoc x b)) z y e :=
      map_subst_map (fun Γ => snoc Γ b) (fun _ x => x) e z.

    Fixpoint remove_in_cat_right (Γ Δ : Ctx B) {b} (bIn : In b Δ) :
      remove (cat Γ Δ) (in_cat_right bIn) = cat Γ (remove Δ bIn) :=
      In_case
        (fun b Δ bIn => remove (cat Γ Δ) (in_cat_right bIn) = cat Γ (remove Δ bIn))
        (fun _ _        => eq_refl)
        (fun b' Δ b bIn => f_equal_snoc b' (remove_in_cat_right _ bIn))
        bIn.

    Fixpoint remove_in_cat_left (Γ Δ : Ctx B) {b} (bIn : In b Γ) {struct Δ} :
      remove (cat Γ Δ) (in_cat_left Δ bIn) = cat (remove Γ bIn) Δ :=
      match Δ with
      | nil        => eq_refl
      | snoc Δ' b' => f_equal_snoc b' (remove_in_cat_left _ bIn)
      end.

    (* In this section we define a generic Bove-Capretta style accessibility
       predicate for functions that recurse on smaller contexts by removing an
       element.

       See: BOVE, ANA, and VENANZIO CAPRETTA. “Modelling General Recursion in
       Type Theory.” Mathematical Structures in Computer Science, vol. 15,
       no. 4, 2005, pp. 671–708., doi:10.1017/S0960129505004822. *)
    Section RemoveAcc.

      (* Coq only generates non-dependent elimination schemes for inductive
         families in Prop. Hence, we disable the automatic generation and
         define the elimination schemes for the predicate ourselves. *)
      #[local] Unset Elimination Schemes.

      Inductive remove_acc (Γ : Ctx B) : Prop :=
        remove_acc_intro :
          (forall x (xIn : In x Γ), remove_acc (remove Γ xIn)) -> remove_acc Γ.

      Definition remove_acc_inv {Γ} (d : remove_acc Γ) :
        forall x (xIn : In x Γ), remove_acc (remove Γ xIn) := let (f) := d in f.

      Definition remove_acc_rect (P : forall Γ, remove_acc Γ -> Type)
        (f : forall Γ (d : forall x (xIn : In x Γ), remove_acc (remove Γ xIn)),
            (forall x (xIn : In x Γ),
                P (remove Γ xIn) (d x xIn)) -> P Γ (remove_acc_intro d)) :=
        fix F Γ (d : remove_acc Γ) {struct d} : P Γ d :=
          let (g) return _ := d in
          f Γ g (fun x xIn => F (remove Γ xIn) (g x xIn)).

      Definition remove_acc_ind (P : forall Γ, remove_acc Γ -> Prop)
        (f : forall Γ (d : forall x (xIn : In x Γ), remove_acc (remove Γ xIn)),
            (forall x (xIn : In x Γ),
                P (remove Γ xIn) (d x xIn)) -> P Γ (remove_acc_intro d)) :=
        fix F Γ (d : remove_acc Γ) {struct d} : P Γ d :=
          let (g) return _ := d in
          f Γ g (fun x xIn => F (remove Γ xIn) (g x xIn)).

      Fixpoint remove_acc_step {Γ x} (d : remove_acc Γ) {struct d} :
        remove_acc (snoc Γ x) :=
        remove_acc_intro
          (fun y (yIn : In y (snoc Γ x)) =>
             match view yIn in SnocView yIn
                   return remove_acc (remove _ yIn) with
             | isZero      => d
             | isSucc yIn' => remove_acc_step (remove_acc_inv d yIn')
             end).

      Fixpoint remove_acc_all (Γ : Ctx B) : remove_acc Γ :=
        match Γ with
        | nil      => remove_acc_intro
                        (fun x (xIn : In x nil) =>
                           match view xIn with end)
        | snoc Γ b => remove_acc_step (remove_acc_all Γ)
        end.

      (* Calculating the full predicate is costly. It has quadratic running
         time in the size of the context. It's better to keep this opaque and
         not unfold it. To prevent computation from being blocked, clients of
         this code should never pattern match on a witness of the predicate
         directly and instead use [remove_acc_inv] in the recursive call. The
         standard library uses the same style and for examples defines [Fix_F]
         for well-founded induction using [Acc_inv] for recursive calls. *)
      #[global] Opaque remove_acc_all.

    End RemoveAcc.

  End WithBinding.
  Arguments In_case [B] P fz fs [b Γ] i.
  Arguments In_rect [B] P fz fs [b Γ] : simpl never.
  Arguments In_ind [B] P fz fs [b Γ] : simpl never.
  Arguments forallb [B] Γ p.
  Arguments remove_in_cat_right [B Γ Δ b] bIn.
  Arguments remove_in_cat_left [B Γ Δ b] bIn.

  Section WithAB.
    Context {A B : Type} (f : A -> B).

    Fixpoint map (Γ : Ctx A) : Ctx B :=
      match Γ with
      | nil      => nil
      | snoc Γ a => snoc (map Γ) (f a)
      end.

    (* This is proof relevant because it's used in the automatic translation
       of program variables to logic variables. *)
    Definition in_map : forall a Γ, In a Γ -> In (f a) (map Γ) :=
      In_rect (fun a Γ _ => In (f a) (map Γ))
        (fun _ _       => in_zero)
        (fun _ _ _ _ i => in_succ i).

  End WithAB.

  Module notations.

    Open Scope ctx_scope.

    Notation "x :: τ" := (MkB x τ) (only parsing) : ctx_scope.
    Notation "N ∷ T" := (Binding N T) : type_scope.
    Notation "x ∷ t" := (MkB x t) : ctx_scope.

    Notation "'ε'" := nil (only parsing) : ctx_scope.
    Infix "▻" := snoc : ctx_scope.
    Notation "Γ1 ▻▻ Γ2" := (cat Γ1%ctx Γ2%ctx) : ctx_scope.
    Notation "b ∈ Γ" := (In b%ctx Γ%ctx) : katamaran_scope.

    (* Use the same notations as in ListNotations. *)
    Notation "[ ]" := (nil) : ctx_scope.
    Notation "[ctx]" := (nil) : ctx_scope.
    Notation "[ x ]" := (snoc nil x) : ctx_scope.
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

  Module tactics.
    Ltac fold_in :=
      repeat change_no_check
        {| ctx.in_at := ctx.in_at ?x; ctx.in_valid := ctx.in_valid ?x |} with x.
  End tactics.

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
#[export] Existing Instance ctx.eq_dec_ctx.

Notation NCtx N T := (Ctx (Binding N T)).
Bind Scope ctx_scope with Ctx.
Bind Scope ctx_scope with NCtx.

#[global] Instance: Params (@snoc) 1 := {}.
#[global] Instance: Params (@lookup) 1 := {}.
#[global] Instance: Params (@cat) 1 := {}.
#[global] Instance: Params (@map) 2 := {}.
