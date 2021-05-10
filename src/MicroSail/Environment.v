Require Import Coq.Program.Equality.
From Equations Require Import Equations.
Require Import MicroSail.Context.
Require Import MicroSail.Notation.
Require Import MicroSail.Tactics.

Local Set Implicit Arguments.

Import CtxNotations.

Section WithBinding.
  Context {B : Set}.

  Section WithDom.
    Context {D : B -> Set}.

    Inductive Env : Ctx B -> Set :=
    | env_nil : Env ctx_nil
    | env_snoc {Γ} (E : Env Γ) (b : B) (db : D b) :
        Env (ctx_snoc Γ b).

    Inductive NilView : Env ctx_nil -> Set :=
    | isNil : NilView env_nil.

    Equations(noeqns) nilView (E : Env ctx_nil) : NilView E :=
      nilView env_nil := isNil.

    Inductive SnocView {Γ b} : Env (ctx_snoc Γ b) -> Set :=
    | isSnoc (E : Env Γ) (v : D b) : SnocView (env_snoc E v).

    Equations(noeqns) snocView {Γ b} (E : Env (ctx_snoc Γ b)) : SnocView E :=
      snocView (env_snoc E v) := isSnoc E v.

    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive Signature NoConfusion NoConfusionHom for Env.

      Context {eqdec_b : EqDec B}.
      Context {eqdec_d : forall b, EqDec (D b) }.

      Global Instance Env_eqdec {Γ} : EqDec (Env Γ).
      Proof. eqdec_proof. Defined.

    End TransparentObligations.

    Section HomEquality.

      Variable eqb : forall b, D b -> D b -> bool.

      Equations(noeqns) env_eqb_hom {Γ} (δ1 δ2 : Env Γ) : bool :=
        env_eqb_hom env_nil           env_nil           := true;
        env_eqb_hom (env_snoc δ1 db1) (env_snoc δ2 db2) :=
          if eqb db1 db2 then env_eqb_hom δ1 δ2 else false.

      Variable eqb_spec : forall b (x y : D b),
          Bool.reflect (x = y) (eqb x y).

      Lemma env_eqb_hom_spec {Γ} (δ1 δ2 : Env Γ) :
        Bool.reflect (δ1 = δ2) (env_eqb_hom δ1 δ2).
      Proof.
        induction δ1; dependent elimination δ2; cbn.
        - constructor.
          reflexivity.
        - destruct (eqb_spec db db0); cbn in *.
          + eapply (ssrbool.iffP (IHδ1 _)); intros Heq;
              dependent elimination Heq; congruence.
          + constructor; intros e; dependent elimination e; congruence.
      Qed.

    End HomEquality.

    Section HetEquality.

      Variable eqb : forall b1 b2, D b1 -> D b2 -> bool.

      Fixpoint env_eqb_het {Γ1 Γ2} (δ1 : Env Γ1) (δ2 : Env Γ2) {struct δ1} : bool :=
        match δ1 , δ2 with
        | env_nil         , env_nil         => true
        | env_snoc δ1 db1 , env_snoc δ2 db2 =>
          if eqb db1 db2 then env_eqb_het δ1 δ2 else false
        | _               , _               => false
        end.

      Variable eqb_spec : forall b1 b2 (x : D b1) (y : D b2),
          Bool.reflect ({| pr2 := x |} = {| pr2 := y |}) (eqb x y).

      Lemma env_eqb_het_spec {Γ1 Γ2} (δ1 : Env Γ1) (δ2 : Env Γ2) :
        Bool.reflect ({| pr2 := δ1 |} = {| pr2 := δ2 |}) (env_eqb_het δ1 δ2).
      Proof.
        revert Γ2 δ2; induction δ1; intros ? []; cbn.
        - constructor.
          reflexivity.
        - constructor.
          intro e; dependent elimination e.
        - constructor.
          intro e; dependent elimination e.
        - destruct (eqb_spec db db0); cbn in *.
          + apply (ssrbool.iffP (IHδ1 _ E)); intros Heq; dependent elimination Heq.
            * dependent elimination e; reflexivity.
            * reflexivity.
          + constructor; intros e; dependent elimination e; congruence.
      Qed.

    End HetEquality.

    Fixpoint env_cat {Γ Δ} (EΓ : Env Γ) (EΔ : Env Δ) : Env (ctx_cat Γ Δ) :=
      match EΔ with
      | env_nil => EΓ
      | env_snoc E db => env_snoc (env_cat EΓ E) db
      end.

    Fixpoint env_lookup {Γ} (E : Env Γ) : forall b, InCtx b Γ -> D b :=
      match E with
      | env_nil => fun _ => inctx_case_nil
      | env_snoc E db => inctx_case_snoc D db (env_lookup E)
      end.

    Fixpoint env_tabulate {Γ} : (forall b, InCtx b Γ -> D b) -> Env Γ :=
      match Γ with
      | ctx_nil      => fun _ => env_nil
      | ctx_snoc Γ b =>
        fun EΓb =>
          env_snoc
            (env_tabulate (fun y yIn => EΓb y (inctx_succ yIn)))
            (EΓb _ inctx_zero)
      end.

    Fixpoint env_update {Γ} (E : Env Γ) {struct E} :
      forall {b} (bIn : InCtx b Γ) (new : D b), Env Γ :=
      match E with
      | env_nil => fun _ => inctx_case_nil
      | env_snoc E bold =>
        inctx_case_snoc
          (fun z => D z -> Env _)
          (fun new => env_snoc E new)
          (fun b0' bIn0' new => env_snoc (env_update E bIn0' new) bold)
      end.

    Definition env_head {Γ b} (E : Env (ctx_snoc Γ b)) : D b :=
      match E in Env Γb
      return match Γb with
             | ctx_nil => unit
             | ctx_snoc Γ b => D b
             end
      with
        | env_nil => tt
        | env_snoc E db => db
      end.

    Definition env_tail {Γ b} (E : Env (ctx_snoc Γ b)) : Env Γ :=
      match E in Env Γb
      return match Γb with
             | ctx_nil => unit
             | ctx_snoc Γ _ => Env Γ
             end
      with
        | env_nil => tt
        | env_snoc E _ => E
      end.

    Fixpoint env_take {Γ} Δ (E : Env (ctx_cat Γ Δ)) : Env Δ :=
      match Δ , E with
      | ctx_nil      , E => env_nil
      | ctx_snoc Δ b , E => env_snoc (env_take Δ (env_tail E)) (env_head E)
      end.

    Definition env_unsnoc {Γ b} (E : Env (ctx_snoc Γ b)) : Env Γ * D b:=
      match E in Env Γb
      return match Γb with
             | ctx_nil => unit
             | ctx_snoc Γ b => Env Γ * D b
             end
      with
        | env_nil => tt
        | env_snoc E db => (E , db)
      end.

    Fixpoint env_drop {Γ} Δ (E : Env (ctx_cat Γ Δ)) : Env Γ :=
      match Δ , E with
      | ctx_nil      , E => E
      | ctx_snoc Δ _ , E => env_drop Δ (env_tail E)
      end.

    Fixpoint env_split {Γ} Δ (E : Env (ctx_cat Γ Δ)) : Env Γ * Env Δ :=
      match Δ , E with
      | ctx_nil      , E => (E , env_nil)
      | ctx_snoc Δ b , E =>
        match E in Env ΓΔb
        return match ΓΔb with
               | ctx_nil => unit
               | ctx_snoc ΓΔ b => (Env ΓΔ -> Env Γ * Env Δ) ->
                                  Env Γ * Env (ctx_snoc Δ b)
               end
        with
        | env_nil => tt
        | env_snoc EΓΔ db =>
          fun split => let (EΓ, EΔ) := split EΓΔ in (EΓ, env_snoc EΔ db)
        end (env_split Δ)
      end.


    Fixpoint env_remove {Γ b} (E : Env Γ) : forall (bIn : b ∈ Γ), Env (Γ - b)%ctx :=
      match E with
      | env_nil => fun '(MkInCtx n e) => match e with end
      | @env_snoc Γ0 E0 b0 db =>
        fun '(MkInCtx n e) =>
          match n return forall e, Env (ctx_remove (@MkInCtx B b (@ctx_snoc B Γ0 b0) n e))
          with
          | O   => fun _ => E0
          | S n => fun e => env_snoc (env_remove E0 (@MkInCtx B b Γ0 n e)) db
          end e
      end.
    Global Arguments env_remove {_} b E.

    Definition env_remove' {Γ b} (E : Env Γ) : forall (bIn : b ∈ Γ), Env (Γ - b)%ctx.
    Proof.
      intros bIn.
      apply env_tabulate.
      intros x xIn.
      apply (@env_lookup _ E x).
      apply (shift_var bIn xIn).
    Defined.
    Global Arguments env_remove' {_} b E.

    Lemma env_lookup_update {Γ} (E : Env Γ) :
      forall {b} (bInΓ : InCtx b Γ) (db : D b),
        env_lookup (env_update E bInΓ db) bInΓ = db.
    Proof.
      induction E; intros ? [n e]; try destruct e;
        destruct n; cbn in *; subst; auto.
    Qed.

    Lemma env_split_takedrop {Γ} Δ (E : Env (ctx_cat Γ Δ)) :
      env_split Δ E = (env_drop Δ E , env_take Δ E).
    Proof.
      induction Δ; [trivial|].
      dependent elimination E; cbn.
      now rewrite (IHΔ E).
    Qed.

    Lemma env_split_cat {Γ Δ} (EΓ : Env Γ) (EΔ : Env Δ) :
      env_split Δ (env_cat EΓ EΔ) = (EΓ , EΔ).
    Proof. induction EΔ using Env_ind; cbn; now try rewrite IHEΔ. Qed.

    Lemma env_cat_split' {Γ Δ} (EΓΔ : Env (ctx_cat Γ Δ)) :
      let (EΓ,EΔ) := env_split _ EΓΔ in
      EΓΔ = env_cat EΓ EΔ.
    Proof.
      induction Δ; intros; cbn in *.
      - reflexivity.
      - dependent elimination EΓΔ as [env_snoc EΓΔ db].
        specialize (IHΔ EΓΔ); cbn in *.
        destruct (env_split Δ EΓΔ); now subst.
    Qed.

    Lemma env_cat_split {Γ Δ} (EΓΔ : Env (ctx_cat Γ Δ)) :
      EΓΔ = env_cat (fst (env_split _ EΓΔ)) (snd (env_split _ EΓΔ)).
    Proof.
      generalize (env_cat_split' EΓΔ).
      now destruct (env_split Δ EΓΔ).
    Qed.

    Lemma env_drop_cat {Γ Δ} (δΔ : Env Δ) (δΓ : Env Γ) :
      env_drop Δ (env_cat δΓ δΔ) = δΓ.
    Proof. induction δΔ; cbn; auto. Qed.

    Lemma env_update_update {Γ} (E : Env Γ) :
      forall {b} (bInΓ : InCtx b Γ) (d1 d2 : D b),
        env_update (env_update E bInΓ d1) bInΓ d2 =
        env_update E bInΓ d2.
    Proof.
      induction E; intros ? [n e]; [ contradiction e | destruct n ].
      - destruct e; reflexivity.
      - cbn. intros. f_equal. auto.
    Qed.

    Lemma env_update_lookup {Γ} (E : Env Γ) :
      forall {b} (bInΓ : InCtx b Γ),
        env_update E bInΓ (env_lookup E bInΓ) = E.
    Proof.
      induction E; intros ? [n e]; [ contradiction e | destruct n ].
      - destruct e; reflexivity.
      - cbn. intros. f_equal. auto.
    Qed.

    Lemma env_lookup_extensional {Γ} (E1 E2 : Env Γ) :
      (forall {b} (bInΓ : InCtx b Γ),
          env_lookup E1 bInΓ = env_lookup E2 bInΓ) ->
      E1 = E2.
    Proof.
      induction E1 as [|Γ E1 HE1 b v1].
      - now destruct (nilView E2).
      - destruct (snocView E2) as [E2 v2].
        intros eq.
        f_equal.
        + eapply HE1.
          intros b' bInΓ.
          eapply (eq b' (inctx_succ bInΓ)).
        + eapply (eq _ inctx_zero).
    Qed.

    Lemma env_lookup_tabulate {Γ} (g : forall (b : B) , InCtx b Γ -> D b) :
      forall {b} (bInΓ : InCtx b Γ),
        env_lookup (env_tabulate g) bInΓ = g b bInΓ.
    Proof.
      induction Γ; intros b' bInΓ.
      - destruct (MicroSail.Context.nilView bInΓ).
      - destruct (MicroSail.Context.snocView bInΓ).
        + now cbn.
        + eapply (IHΓ (fun b bInΓ => g b (inctx_succ bInΓ))).
    Qed.

    Lemma env_remove_remove' {Γ x} (E : Env Γ) (xIn : x ∈ Γ) :
      env_remove x E xIn = env_remove' x E xIn.
    Proof.
      unfold env_remove'. induction E.
      - destruct (Context.nilView xIn).
      - destruct (Context.snocView xIn).
        + apply env_lookup_extensional.
          intros y yIn. rewrite env_lookup_tabulate.
          reflexivity.
        + cbn. f_equal. apply IHE.
    Qed.

  End WithDom.

  Arguments Env : clear implicits.

  Section Map.

    Context {D1 D2 : B -> Set}.
    Variable f : forall b, D1 b -> D2 b.

    Fixpoint env_map {Γ} (E : Env D1 Γ) : Env D2 Γ :=
      match E with
      | env_nil       => env_nil
      | env_snoc E db => env_snoc (env_map E) (f db)
      end.

    Lemma env_map_cat {Γ1 Γ2} (E1 : Env D1 Γ1) (E2 : Env D1 Γ2) :
      env_map (env_cat E1 E2) = env_cat (env_map E1) (env_map E2).
    Proof. induction E2; cbn; congruence. Qed.

    Lemma env_map_drop {Γ Δ} (EΓΔ : Env D1 (ctx_cat Γ Δ)) :
      env_map (env_drop Δ EΓΔ) = env_drop Δ (env_map EΓΔ).
    Proof.
      induction Δ; intros; cbn in *.
      - reflexivity.
      - dependent elimination EΓΔ; apply IHΔ.
    Qed.

    Lemma env_map_update {Γ} (E : Env D1 Γ) :
      forall {b} (bInΓ : InCtx b Γ) (db : D1 b),
        env_map (env_update E bInΓ db) = env_update (env_map E) bInΓ (f db).
    Proof.
      induction E; intros ? [n e]; try destruct e.
      destruct n; cbn in *; subst; cbn; congruence.
    Qed.

    Lemma env_map_tabulate {Γ} (g : forall (b : B) , InCtx b Γ -> D1 b) :
      env_map (env_tabulate g) = env_tabulate (fun b bInΓ => f (g b bInΓ)).
    Proof.
      induction Γ; intros; cbn in *.
      - reflexivity.
      - f_equal; apply IHΓ.
    Qed.

    Lemma env_lookup_map {Γ} (E : Env D1 Γ) :
      forall {b} (bInΓ : InCtx b Γ),
        env_lookup (env_map E) bInΓ = f (env_lookup E bInΓ).
    Proof.
      induction E; intros ? [n e]; try destruct e;
        destruct n; cbn in *; subst; auto.
    Qed.

  End Map.

  Section WithD123.

    Context {D1 D2 D3 : B -> Set}.
    Variable f : forall b, D1 b -> D2 b.
    Variable g : forall b, D2 b -> D3 b.

    Lemma env_map_map {Γ} (E : Env D1 Γ) :
      env_map g (env_map f E) = env_map (fun b d => g (f d)) E.
    Proof. induction E; cbn; f_equal; assumption. Qed.

  End WithD123.

  Lemma env_map_id_eq {D : B -> Set} {Γ : Ctx B} (f : forall b, D b -> D b) (E : Env D Γ) (hyp_f : forall b d, f b d = d) :
    env_map f E = E.
  Proof. induction E; cbn; congruence. Qed.

  Lemma env_map_id {D : B -> Set} {Γ : Ctx B} (E : Env D Γ) :
    env_map (fun _ d => d) E = E.
  Proof. now apply env_map_id_eq. Qed.

  Lemma env_map_ext {D1 D2 : B -> Set} (f1 f2 : forall b, D1 b -> D2 b) {Γ} (E : Env D1 Γ) :
    (forall b d, f1 b d = f2 b d) -> env_map f1 E = env_map f2 E.
  Proof.
    intros HYP.
    apply env_lookup_extensional.
    intros.
    now rewrite ?env_lookup_map.
  Qed.

End WithBinding.

Bind Scope env_scope with Env.
Arguments Env {B} D Γ.
Arguments env_nil {B D}.
Arguments env_snoc {B%type D%function Γ%ctx} E%env b%ctx db.
Arguments env_lookup {B D Γ} E [_] x.
Arguments env_update {B}%type {D}%function {Γ}%ctx E%env {b}%ctx.
(* Arguments env_tabulate {_ _} _. *)
(* Arguments env_tail {_ _ _} / _. *)

  (* End WithEqb. *)

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

Definition NamedEnv {X T : Set} (D : T -> Set) (Γ : NCtx X T) : Set :=
  Env (fun xt => D (snd xt)) Γ.
Bind Scope env_scope with NamedEnv.

Module EnvNotations.

  Notation "δ ► ( x ↦ u )" := (env_snoc δ x u) : env_scope.
  Notation "δ1 '►►' δ2" := (env_cat δ1 δ2) : env_scope.
  Notation "δ ⟪ x ↦ v ⟫" := (@env_update _ _ _ δ (x∶_)%ctx _ v) : env_scope.
  Notation "δ ‼ x" := (@env_lookup _ _ _ δ (x∶_)%ctx _) : exp_scope.
  Notation "[ x ]" := (env_snoc env_nil (_∶_)%ctx x) : env_scope.
  Notation "[ x , .. , z ]" :=
    (env_snoc .. (env_snoc env_nil (_∶_) x) .. (_∶_) z) : env_scope.

End EnvNotations.

Open Scope env_scope.
Import EnvNotations.

Section WithB.

  Context {B : Set}.
  Variable (D : B -> Set).

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

  Lemma Forall_forall (Δ : Ctx B) (P : Env D Δ -> Prop) :
    (Forall P) <-> (forall E : Env D Δ, P E).
  Proof.
    split.
    - induction Δ; intros hyp E; depelim E.
      + apply hyp.
      + apply (IHΔ (fun E => forall v, P (env_snoc E _ v))).
        apply hyp.
    - induction Δ; cbn.
      + auto.
      + intros hyp.
        apply (IHΔ (fun E => forall v, P (env_snoc E _ v))).
        auto.
  Qed.

  Lemma uncurry_curry (Δ : Ctx B) (r : Type) (f : Env D Δ -> r) :
    forall δ,
      uncurry (curry f) δ = f δ.
  Proof.
    intros δ. revert r f. induction δ; cbn; intros.
    - reflexivity.
    - now rewrite IHδ.
  Qed.

End WithB.

Definition abstract_named {X T : Set} (D : T -> Set) (Δ : NCtx X T) (r : Type) : Type :=
  abstract (fun xt => D (snd xt)) Δ r.

Definition uncurry_named {X T : Set} (D : T -> Set) {Δ : NCtx X T} {r : Type} (f : abstract_named D Δ r) (δ : NamedEnv D Δ) : r :=
  uncurry f δ.

Definition curry_named {X T : Set} (D : T -> Set) {Δ : NCtx X T} {r : Type} (f : NamedEnv D Δ -> r) : abstract_named D Δ r :=
  curry f.

Definition ForallNamed {X T : Set} (D : T -> Set) (Δ : NCtx X T) : (NamedEnv D Δ -> Prop) -> Prop :=
  @Forall (X * T) (fun xt => D (snd xt)) Δ.

Section TraverseEnv.

  Import stdpp.base.

  Context `{MRet M, MBind M} {I : Set} {A B : I -> Set} (f : forall i : I, A i -> M (B i)).

  Fixpoint traverse_env {Γ : Ctx I} (xs : Env A Γ) : M (Env B Γ) :=
    match xs with
    | env_nil => mret (env_nil)
    | env_snoc Ea i a => Eb ← traverse_env Ea ; b ← f a ; mret (env_snoc Eb i b)
    end.

End TraverseEnv.
