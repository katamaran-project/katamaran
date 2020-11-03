(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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

Require Import Coq.Logic.EqdepFacts.
Require Import Equations.Equations.
Require Import MicroSail.Notation.
Require Import MicroSail.Prelude.

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
Arguments ctx_snoc {_} _ _.
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

    Lemma ctx_nth_is_proof_irrelevance {Γ : Ctx B} (n : nat) (b : B) :
      forall (p q : ctx_nth_is Γ n b), p = q.
    Proof.
      revert Γ b; induction n; intros [|Γ b] b0; cbn.
      - intros [].
      - apply uip.
      - intros [].
      - apply IHn.
    Qed.

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

  End InCtx.

  (* Two proofs of context containment are equal of the deBruijn indices are equal *)
  Definition InCtx_eqb {Γ} {b1 b2 : B}
             (b1inΓ : InCtx b1 Γ)
             (b2inΓ : InCtx b2 Γ) : bool :=
    Nat.eqb (inctx_at b1inΓ) (inctx_at b2inΓ).

  (* These are *constructors* for InCtx. *)
  Definition inctx_zero {b : B} {Γ : Ctx B} : InCtx b (ctx_snoc Γ b) :=
    @MkInCtx _ (ctx_snoc Γ b) 0 eq_refl.
  Definition inctx_succ {b : B} {Γ : Ctx B} {b' : B} (bIn : InCtx b Γ) :
    InCtx b (ctx_snoc Γ b') :=
    @MkInCtx _ (ctx_snoc Γ b') (S (inctx_at bIn)) (inctx_valid bIn).

  Fixpoint inctx_cat {b : B} {Γ : Ctx B} (bIn : InCtx b Γ) (Δ : Ctx B) : InCtx b (ctx_cat Γ Δ) :=
    match Δ with
    | ctx_nil      => bIn
    | ctx_snoc Δ _ => inctx_succ (inctx_cat bIn Δ)
    end.

  (* Custom pattern matching in cases where the context was already refined
     by a different match, i.e. on environments. *)
  Definition inctx_case_nil {b : B} {A : Type} (bIn : InCtx b ctx_nil) : A :=
    let (n, e) := bIn in match e with end.
  Definition inctx_case_snoc (D : B -> Type) (Γ : Ctx B) (b0 : B) (db0 : D b0)
    (dΓ: forall b, InCtx b Γ -> D b) (b : B) (bIn: InCtx b (ctx_snoc Γ b0)) : D b :=
    let (n, e) := bIn in
    match n return ctx_nth_is (ctx_snoc Γ b0) n b -> D b with
    | 0 => fun e => match e with eq_refl => db0 end
    | S n => fun e => dΓ b (MkInCtx n e)
    end e.

  Definition inctx_case_snoc_dep (Γ : Ctx B) (b0 : B)
    (D : forall b, InCtx b (ctx_snoc Γ b0) -> Prop)
    (db0 : D b0 inctx_zero)
    (dΓ: forall b (bIn: InCtx b Γ), D b (inctx_succ bIn)) :
    forall (y: B) (yIn: InCtx y (ctx_snoc Γ b0)), D y yIn :=
    fun b '(MkInCtx n e) =>
      match n return forall e, D b (MkInCtx n e) with
      | 0 => eq_indd B b0 (fun z e => D z (@MkInCtx _ (ctx_snoc _ _) 0 e)) db0 b
      | S n => fun e => dΓ b (MkInCtx n e)
      end e.

  Lemma InCtx_ind (b : B)
    (P : forall (Γ : Ctx B), InCtx b Γ -> Prop)
    (fzero : forall (Γ : Ctx B), P (ctx_snoc Γ b) inctx_zero)
    (fsucc : forall (Γ : Ctx B) (b0 : B) (bIn : InCtx b Γ),
        P Γ bIn -> P (ctx_snoc Γ b0) (inctx_succ bIn)) :
    forall (Γ : Ctx B) (bIn : InCtx b Γ), P Γ bIn.
  Proof.
    induction Γ; cbn.
    - intro bIn; exact (inctx_case_nil bIn).
    - intros [[|n] e]; cbn in *.
      + subst; apply fzero.
      + pose (MkInCtx n e) as bIn.
        exact (fsucc Γ _ bIn (IHΓ bIn)).
  Qed.

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

End WithBinding.

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

Module CtxNotations.

  Notation NCtx Name Data := (Ctx (Name * Data)).
  Notation "x ∶ τ" := (x,τ) : ctx_scope.

  Notation "'ε'" := ctx_nil : ctx_scope.
  Infix "▻" := ctx_snoc : ctx_scope.
  Notation "Γ1 ▻▻ Γ2" := (ctx_cat Γ1%ctx Γ2%ctx) : ctx_scope.
  Notation "b ∈ Γ" := (InCtx b%ctx Γ%ctx) : type_scope.

  (* NB: ∶ ≠ :
     To typeset the next notation, use \: *)
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
    | ε       => None
    | Γ ▻ y∶d => if Name_eqdec x y then Some d else ctx_resolve Γ x
    end.

  Fixpoint mk_inctx (Γ : NCtx Name D) (x : Name) {struct Γ} :
    let m := ctx_resolve Γ x in forall (p : IsSome m), (x∶fromSome m p) ∈ Γ :=
    match Γ with
    | ε => fun p => match p with end
    | Γ ▻ y∶d =>
      match Name_eqdec x y as s return
        (forall p, (x∶fromSome (if s then Some d else ctx_resolve Γ x) p) ∈ (Γ ▻ y∶d))
      with
      | left e => fun _ => match e with eq_refl => inctx_zero end
      | right _ => fun p => inctx_succ (mk_inctx Γ x p)
      end
    end.

End Resolution.

Module NameResolution.

  (* Hook the reflective procedure for name resolution into the typeclass
     resolution mechanism. *)
  Hint Extern 10 (InCtx (?x , _) ?Γ) =>
    let xInΓ := eval compute in (mk_inctx Γ x tt) in
      exact xInΓ : typeclass_instances.

End NameResolution.
