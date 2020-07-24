Require Import Coq.Program.Equality.
Require Import Equations.Equations.
Require Import MicroSail.Context.
Require Import MicroSail.Notation.

Set Implicit Arguments.

Section WithBinding.
  Context {B : Set}.

  Inductive Env (D : B -> Type) : Ctx B -> Type :=
  | env_nil : Env D ctx_nil
  | env_snoc {Γ} (E : Env D Γ) (b : B) (db : D b) :
      Env D (ctx_snoc Γ b).
  Derive Signature for Env.

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive NoConfusion NoConfusionHom for Env.
  End TransparentObligations.

  Global Arguments env_nil {_}.
  Bind Scope env_scope with Env.

  Fixpoint env_cat {D : B -> Type} {Γ Δ : Ctx B}
    (EΓ : Env D Γ) (EΔ : Env D Δ) : Env D (ctx_cat Γ Δ) :=
    match EΔ with
    | env_nil => EΓ
    | env_snoc E b db => env_snoc (env_cat EΓ E) b db
    end.

  Section WithD12.

    Context {D1 D2 : B -> Type}.
    Variable f : forall b, D1 b -> D2 b.

    Fixpoint env_map {Γ : Ctx B} (E : Env D1 Γ) : Env D2 Γ :=
      match E with
      | env_nil => env_nil
      | env_snoc E b db => env_snoc (env_map E) b (f db)
      end.

  End WithD12.

  Fixpoint env_lookup {D : B -> Type} {Γ : Ctx B}
    (E : Env D Γ) : forall (b : B) (bIn : InCtx b Γ), D b :=
    match E with
    | env_nil => fun _ => inctx_case_nil
    | env_snoc E b db => inctx_case_snoc D db (env_lookup E)
    end.

  Global Arguments env_lookup {_ _} _ [_] _.

  Fixpoint env_tabulate {D : B -> Type} {Γ : Ctx B} :
    (forall (x : B) , InCtx x Γ -> D x) -> Env D Γ :=
    match Γ with
    | ctx_nil      => fun _   => env_nil
    | ctx_snoc Γ b =>
      fun EΓb =>
        env_snoc
          (env_tabulate (fun y yIn => EΓb y (inctx_succ yIn)))
          b
          (EΓb _ inctx_zero)
    end.

  Global Arguments env_tabulate {_ _} _.

  Fixpoint env_update {D : B -> Type} {Γ : Ctx B} (E : Env D Γ) {struct E} :
    forall {b0 : B} (bIn0 : InCtx b0 Γ) (new : D b0), Env D Γ :=
    match E with
    | env_nil => fun _ => inctx_case_nil
    | @env_snoc _ Γ E b bold =>
      inctx_case_snoc
        (fun z => D z -> Env D (ctx_snoc Γ b))
        (fun new => env_snoc E b new)
        (fun b0' bIn0' new => env_snoc (env_update E bIn0' new) b bold)
    end.

  Definition env_head {D : B -> Type} {Γ : Ctx B}
    {b : B} (E : Env D (ctx_snoc Γ b)) : D b:=
    match E in Env _ Γb
    return match Γb with
           | ctx_nil => unit
           | ctx_snoc Γ b => D b
           end
    with
      | env_nil => tt
      | env_snoc E _ db => db
    end.

  Definition env_tail {D : B -> Type} {Γ : Ctx B}
    {b : B} (E : Env D (ctx_snoc Γ b)) : Env D Γ :=
    match E in Env _ Γb
    return match Γb with
           | ctx_nil => unit
           | ctx_snoc Γ _ => Env D Γ
           end
    with
      | env_nil => tt
      | env_snoc E _ _ => E
    end.

  Definition env_unsnoc {D : B -> Type} {Γ : Ctx B}
    {b : B} (E : Env D (ctx_snoc Γ b)) : Env D Γ * D b:=
    match E in Env _ Γb
    return match Γb with
           | ctx_nil => unit
           | ctx_snoc Γ b => Env D Γ * D b
           end
    with
      | env_nil => tt
      | env_snoc E _ db => (E , db)
    end.

  Global Arguments env_tail {_ _ _} / _.

  Fixpoint env_drop {D : B -> Type} {Γ : Ctx B} Δ {struct Δ} :
    forall (E : Env D (ctx_cat Γ Δ)), Env D Γ :=
    match Δ with
    | ctx_nil => fun E => E
    | ctx_snoc Δ _ => fun E => env_drop Δ (env_tail E)
    end.

  Fixpoint env_split {D : B -> Type} {Γ : Ctx B} Δ {struct Δ} :
    forall (E : Env D (ctx_cat Γ Δ)), Env D Γ * Env D Δ :=
    match Δ with
    | ctx_nil => fun E => (E , env_nil)
    | ctx_snoc Δ b =>
      fun E =>
        match E in (Env _ ΓΔb)
        return match ΓΔb with
               | ctx_nil => unit
               | ctx_snoc ΓΔ b => (Env D ΓΔ -> Env D Γ * Env D Δ) ->
                                  Env D Γ * Env D (ctx_snoc Δ b)
               end
        with
        | env_nil => tt
        | env_snoc EΓΔ b db =>
          fun split => let (EΓ, EΔ) := split EΓΔ in (EΓ, env_snoc EΔ b db)
        end (env_split Δ)
    end.

  Section WithD123.

    Context {D1 D2 D3 : B -> Type}.
    Variable f : forall b, D1 b -> D2 b.
    Variable g : forall b, D2 b -> D3 b.

    Lemma env_map_map {Γ : Ctx B} (E : Env D1 Γ) :
      env_map g (env_map f E) = env_map (fun b d => g (f d)) E.
    Proof. induction E; cbn; f_equal; assumption. Qed.

  End WithD123.

  Lemma env_lookup_update {D : B -> Type} {Γ : Ctx B} (E : Env D Γ) :
    forall {b : B} (bInΓ : InCtx b Γ) (db : D b),
      env_lookup (env_update E bInΓ db) bInΓ = db.
  Proof.
    induction E; intros ? [n e]; try destruct e;
      destruct n; cbn in *; subst; auto.
  Qed.

  Lemma env_split_cat {D : B -> Type} {Γ Δ : Ctx B} :
    forall (EΓ : Env D Γ) (EΔ : Env D Δ),
      env_split Δ (env_cat EΓ EΔ) = (EΓ , EΔ).
  Proof. induction EΔ using Env_ind; cbn; now try rewrite IHEΔ. Qed.

  Lemma env_cat_split' {D : B -> Type} {Γ Δ : Ctx B} :
    forall (EΓΔ : Env D (ctx_cat Γ Δ)),
      let (EΓ,EΔ) := env_split _ EΓΔ in
      EΓΔ = env_cat EΓ EΔ.
  Proof.
    induction Δ; intros; cbn in *.
    - reflexivity.
    - dependent elimination EΓΔ as [env_snoc EΓΔ b db].
      specialize (IHΔ EΓΔ); cbn in *.
      destruct (env_split Δ EΓΔ); now subst.
  Qed.

  Lemma env_cat_split {D : B -> Type} {Γ Δ : Ctx B} (EΓΔ : Env D (ctx_cat Γ Δ)) :
    EΓΔ = env_cat (fst (env_split _ EΓΔ)) (snd (env_split _ EΓΔ)).
  Proof.
    generalize (env_cat_split' EΓΔ).
    now destruct (env_split Δ EΓΔ).
  Qed.

  Lemma env_drop_cat {D : B -> Type} {Γ Δ : Ctx B} :
    forall (δΔ : Env D Δ) (δΓ : Env D Γ),
      env_drop Δ (env_cat δΓ δΔ) = δΓ.
  Proof. induction δΔ; cbn; auto. Qed.

  Lemma env_update_update {D : B -> Type} {Γ : Ctx B} (E : Env D Γ) :
    forall {b : B} (bInΓ : InCtx b Γ) (d1 d2 : D b),
      env_update (env_update E bInΓ d1) bInΓ d2 =
      env_update E bInΓ d2.
  Proof.
    induction E; intros ? [n e]; [ contradiction e | destruct n ].
    - destruct e; reflexivity.
    - cbn. intros. f_equal. auto.
  Qed.

  Lemma env_update_lookup {D : B -> Type} {Γ : Ctx B} (E : Env D Γ) :
    forall {b : B} (bInΓ : InCtx b Γ),
      env_update E bInΓ (env_lookup E bInΓ) = E.
  Proof.
    induction E; intros ? [n e]; [ contradiction e | destruct n ].
    - destruct e; reflexivity.
    - cbn. intros. f_equal. auto.
  Qed.

  Section WithEqD.
    Context {D : B -> Type}.
    Variable eqd : forall b, D b -> D b -> bool.

    Equations env_beq {Γ : Ctx B} (δ1 δ2 : Env D Γ) : bool :=
    env_beq env_nil               env_nil              := true;
    env_beq (env_snoc δ1 _ db1) (env_snoc δ2 _ db2) := env_beq δ1 δ2 && eqd db1 db2.

  End WithEqD.

End WithBinding.

Section EnvRec.

  Local Set Universe Polymorphism.
  Context {B : Set}.

  Section WithD.
    Variable D : B -> Type.

    Fixpoint EnvRec (σs : Ctx B) {struct σs} : Type :=
      match σs with
      | ctx_nil => unit
      | ctx_snoc σs σ => EnvRec σs * D σ
      end.

  End WithD.

  Section WithEqD.
    Context {D : B -> Type}.
    Variable eqd : forall b, D b -> D b -> bool.

    Fixpoint envrec_beq {Γ : Ctx B} : forall (δ1 δ2 : EnvRec D Γ), bool :=
      match Γ with
      | ctx_nil      => fun _ _ => true
      | ctx_snoc Γ b => fun '(δ1 , d1) '(δ2 , d2) => envrec_beq δ1 δ2 && eqd d1 d2
      end%bool.

  End WithEqD.

End EnvRec.

Definition NamedEnv {X T : Set} (D : T -> Type) (Γ : Ctx (X * T)) : Type :=
  Env (fun xt => D (snd xt)) Γ.
Bind Scope env_scope with Env.
Bind Scope env_scope with NamedEnv.

Module EnvNotations.

  Notation "δ '►' b '↦' d" := (env_snoc δ b d) : env_scope.
  Notation "δ1 '►►' δ2" := (env_cat δ1 δ2) : env_scope.
  Notation "δ ⟪ x ↦ v ⟫" := (@env_update _ _ _ δ (x , _) _ v) : env_scope.
  Notation "δ ‼ x" := (@env_lookup _ _ _ δ (x , _) _) : lit_scope.

End EnvNotations.

Section WithB.

  Context {B : Set}.
  Variable (D : B -> Type).

  Fixpoint abstract (Δ : Ctx B) (r : Type) {struct Δ} : Type :=
    match Δ with
    | ctx_nil => r
    | ctx_snoc Δ σ => abstract Δ (D σ -> r)
    end.

  Fixpoint uncurry {Δ : Ctx B} {r : Type} (f : abstract Δ r) (δ : Env D Δ) {struct δ} : r :=
    match δ in Env _ Δ return forall r : Type, abstract Δ r -> r with
    | env_nil => fun _ v => v
    | env_snoc δ b db => fun r (f : abstract _ (D b -> r)) => uncurry f δ db
    end r f.

  Fixpoint curry {Δ : Ctx B} {r : Type} (f : Env D Δ -> r) {struct Δ} : abstract Δ r :=
    match Δ return forall r : Type, (Env D Δ -> r) -> abstract Δ r with
    | ctx_nil => fun r f => f env_nil
    | ctx_snoc Δ σ => fun r f => @curry Δ (D σ -> r) (fun E dσ => f (env_snoc E σ dσ))
    end r f.

  Fixpoint Forall (Δ : Ctx B) {struct Δ} : (Env D Δ -> Prop) -> Prop :=
    match Δ return (Env D Δ -> Prop) -> Prop with
    | ctx_nil      => fun P => P env_nil
    | ctx_snoc Δ b => fun P => Forall (fun δ => forall v, P (env_snoc δ _ v))
    end.

  Lemma Forall_forall (Δ : Ctx B) (P : Env D Δ -> Prop) (hyp: Forall P) :
    (forall E : Env D Δ, P E).
  Proof.
    induction Δ; intros E; depelim E.
    - apply hyp.
    - apply (IHΔ (fun E => forall v, P (env_snoc E _ v))).
      apply hyp.
  Qed.

End WithB.

Definition abstract_named {X T : Set} (D : T -> Type) (Δ : Ctx (X * T)) (r : Type) : Type :=
  abstract (fun xt => D (snd xt)) Δ r.

Definition uncurry_named {X T : Set} (D : T -> Type) {Δ : Ctx (X * T)} {r : Type} (f : abstract_named D Δ r) (δ : NamedEnv D Δ) : r :=
  uncurry f δ.

Definition curry_named {X T : Set} (D : T -> Type) {Δ : Ctx (X * T)} {r : Type} (f : NamedEnv D Δ -> r) : abstract_named D Δ r :=
  curry f.

Fixpoint ForallNamed {X T : Set} (D : T -> Type) (Δ : Ctx (X * T)) {struct Δ} : (NamedEnv D Δ -> Prop) -> Prop :=
  @Forall (X * T) (fun xt => D (snd xt)) Δ.
