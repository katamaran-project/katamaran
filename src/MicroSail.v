From Coq Require Import
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith.

Set Implicit Arguments.

Section Contexts.

  Inductive Ctx (B : Set) : Set :=
  | ctx_nil
  | ctx_snoc (Γ : Ctx B) (b : B).

  Global Arguments ctx_nil {_}.
  Global Arguments ctx_snoc {_} _ _.

  Fixpoint ctx_cat {B : Set} (Γ₁ Γ₂ : Ctx B) {struct Γ₂} : Ctx B :=
    match Γ₂ with
    | ctx_nil       => Γ₁
    | ctx_snoc Γ₂ τ => ctx_snoc (ctx_cat Γ₁ Γ₂) τ
    end.

  (* Fixpoint ctx_nth {B : Set} (Γ : Ctx B) (n : nat) {struct Γ} : option B := *)
  (*   match Γ , n with *)
  (*   | ctx_snoc _ x , O   => Some x *)
  (*   | ctx_snoc Γ _ , S n => ctx_nth Γ n *)
  (*   | _            , _   => None *)
  (*   end. *)

  Fixpoint ctx_nth_is {B : Set} (Γ : Ctx B) (n : nat) (b : B) {struct Γ} : Prop :=
    match Γ , n with
    | ctx_snoc _ x , O   => x = b
    | ctx_snoc Γ _ , S n => ctx_nth_is Γ n b
    | _            , _   => False
    end.

  (* InCtx represents context containment proofs. This is essentially a
     well-typed de Bruijn index, i.e. a de Bruijn index with a proof that it
     resolves to the binding b.
     SK: I wanted to play with a sigma type here instead of using some unary
     representation. There might be some headaches in proofs ahead which require
     eta for sig which is AFAIK not given definitionally only propositionally.
     For instance proving that lookup and tabulation are inverses requires
     eta. *)
  Class InCtx {B : Set} (b : B) (Γ : Ctx B) : Set :=
    inCtx : { n : nat | ctx_nth_is Γ n b }.

  Definition inctx_zero {B : Set} {b : B} {Γ : Ctx B} : InCtx b (ctx_snoc Γ b) :=
    exist _ 0 eq_refl.
  Definition inctx_succ {B : Set} {b : B} {Γ : Ctx B} {b' : B} (bIn : InCtx b Γ) :
    InCtx b (ctx_snoc Γ b') := exist _ (S (proj1_sig bIn)) (proj2_sig bIn).

  (* Custom pattern matching in cases where the context was already refined
     by a different match, i.e. on environments. *)
  Definition inctx_case_nil {A B : Set} {x : B} (xIn : InCtx x ctx_nil) : A :=
    let (n, e) := xIn in match e with end.
  Definition inctx_case_snoc (X : Set) (D : X -> Set) (Γ : Ctx X) (x : X) (dx : D x)
    (dΓ: forall z, InCtx z Γ -> D z) (y: X) (yIn: InCtx y (ctx_snoc Γ x)) : D y :=
    let (n, e) := yIn in
    match n return (ctx_nth_is (ctx_snoc Γ x) n y -> D y) with
    | 0 =>   eq_rec x D dx y
    | S n => fun e => dΓ y (exist _ n e)
    end e.

  Definition inctx_case_snoc_dep (X : Set) (Γ : Ctx X) (x : X)
    (D : forall z, InCtx z (ctx_snoc Γ x) -> Prop)
    (dx : D x inctx_zero)
    (dΓ: forall z (zIn: InCtx z Γ), D z (inctx_succ zIn)) :
    forall (y: X) (yIn: InCtx y (ctx_snoc Γ x)), D y yIn :=
    fun y yIn =>
      match yIn with
        exist _ n e =>
        match n return (forall e, D y (exist _ n e)) with
        | 0 => fun e => eq_indd X x (fun z e => D z (exist _ 0 e)) dx y e
        | S n => fun e => dΓ y (exist (fun n => ctx_nth_is Γ n y) n e)
        end e
      end.

End Contexts.

Section Environments.

  Context {X : Set}.

  Inductive Env (D : X -> Set) : Ctx X -> Set :=
  | env_nil : Env D ctx_nil
  | env_snoc {Γ} (E : Env D Γ) (x : X) (d : D x) :
      Env D (ctx_snoc Γ x).

  Global Arguments env_nil {_}.

  Fixpoint env_cat {D : X -> Set} {Γ Δ : Ctx X}
           (EΓ : Env D Γ) (EΔ : Env D Δ) : Env D (ctx_cat Γ Δ) :=
    match EΔ with
    | env_nil => EΓ
    | env_snoc E x d => env_snoc (env_cat EΓ E) x d
    end.

  Fixpoint env_map {D₁ D₂ : X -> Set} {Γ : Ctx X}
    (f : forall x, D₁ x -> D₂ x) (E : Env D₁ Γ) : Env D₂ Γ :=
    match E with
    | env_nil => env_nil
    | env_snoc E x d => env_snoc (env_map f E) x (f x d)
    end.

  Fixpoint env_lookup {D : X -> Set} {Γ : Ctx X}
           (E : Env D Γ) : forall (x : X) (i : InCtx x Γ), D x :=
    match E with
    | env_nil => fun _ => inctx_case_nil
    | env_snoc E x d => inctx_case_snoc D d (env_lookup E)
    end.

  Arguments env_lookup {_ _} _ [_] _.

  Fixpoint env_update {D : X -> Set} {Γ : Ctx X} (E : Env D Γ) {struct E} :
    forall {x : X} (i : InCtx x Γ) (d : D x), Env D Γ :=
    match E with
    | env_nil => fun _ => inctx_case_nil
    | @env_snoc _ Γ E y old =>
      inctx_case_snoc
        (fun x => D x -> Env D (ctx_snoc Γ y))
        (fun new => env_snoc E y new)
        (fun x xIn new => env_snoc (env_update E xIn new) y old)
    end.

  Definition env_tail {D : X -> Set} {Γ : Ctx X}
    {x : X} (E : Env D (ctx_snoc Γ x)) : Env D Γ :=
    match E in Env _ Γx
    return match Γx with
           | ctx_nil => unit
           | ctx_snoc Γ _ => Env D Γ
           end
    with
      | env_nil => tt
      | env_snoc E _ _ => E
    end.

  Global Arguments env_tail {_ _ _} / _.

  Fixpoint env_drop {D : X -> Set} {Γ : Ctx X} Δ {struct Δ} :
    forall (E : Env D (ctx_cat Γ Δ)), Env D Γ :=
    match Δ with
    | ctx_nil => fun E => E
    | ctx_snoc Δ _ => fun E => env_drop Δ (env_tail E)
    end.

  Fixpoint env_split {D : X -> Set} {Γ : Ctx X} Δ {struct Δ} :
    forall (E : Env D (ctx_cat Γ Δ)), Env D Γ * Env D Δ :=
    match Δ with
    | ctx_nil => fun E => (E , env_nil)
    | ctx_snoc Δ b =>
      fun E =>
        match E in (Env _ ΓΔx)
        return match ΓΔx with
               | ctx_nil => unit
               | ctx_snoc ΓΔ x => (Env D ΓΔ -> Env D Γ * Env D Δ) ->
                                  Env D Γ * Env D (ctx_snoc Δ x)
               end
        with
        | env_nil => tt
        | env_snoc EΓΔ x d =>
          fun split => let (EΓ, EΔ) := split EΓΔ in (EΓ, env_snoc EΔ x d)
        end (env_split Δ)
    end.

  Lemma env_lookup_update {D : X -> Set} {Γ : Ctx X} (E : Env D Γ) :
    forall {x:X} (xInΓ : InCtx x Γ) (d : D x),
      env_lookup (env_update E xInΓ d) xInΓ = d.
  Proof.
    induction E; intros y [n e]; try destruct e;
      destruct n; cbn in *; subst; auto.
  Qed.

  Lemma env_split_cat {D : X -> Set} {Γ Δ : Ctx X} :
    forall (EΓ : Env D Γ) (EΔ : Env D Δ),
      env_split Δ (env_cat EΓ EΔ) = (EΓ , EΔ).
  Proof. induction EΔ using Env_ind; cbn; now try rewrite IHEΔ. Qed.

  Lemma env_cat_split' {D : X -> Set} {Γ Δ : Ctx X} :
    forall (EΓΔ : Env D (ctx_cat Γ Δ)),
      let (EΓ,EΔ) := env_split _ EΓΔ in
      EΓΔ = env_cat EΓ EΔ.
  Proof.
    induction Δ; intros; cbn in *.
    - reflexivity.
    - dependent destruction EΓΔ.
      specialize (IHΔ EΓΔ); cbn in *.
      destruct (env_split Δ EΓΔ); now subst.
  Qed.

  Lemma env_cat_split {D : X -> Set} {Γ Δ : Ctx X} (EΓΔ : Env D (ctx_cat Γ Δ)) :
    EΓΔ = env_cat (fst (env_split _ EΓΔ)) (snd (env_split _ EΓΔ)).
  Proof.
    generalize (env_cat_split' EΓΔ).
    now destruct (env_split Δ EΓΔ).
  Qed.

  Lemma env_drop_cat {D : X -> Set} {Γ Δ : Ctx X} :
    forall (δΔ : Env D Δ) (δΓ : Env D Γ),
      env_drop Δ (env_cat δΓ δΔ) = δΓ.
  Proof. induction δΔ; cbn; auto. Qed.

End Environments.

(* Section Types. *)
Module Type TypeKit.

  Definition Env' {X T : Set} (D : T -> Set) (Γ : Ctx (X * T)) : Set :=
    Env (fun xt => D (snd xt)) Γ.

  (* Names of union type constructors. *)
  Parameter 𝑻   : Set. (* input: \MIT *)
  (* Names of record type constructors. *)
  Parameter 𝑹  : Set.
  (* Names of expression variables. *)
  Parameter 𝑿 : Set. (* input: \MIX *)

  Inductive Ty : Set :=
  | ty_int
  | ty_bool
  | ty_bit
  | ty_string
  | ty_list (σ : Ty)
  | ty_prod (σ τ : Ty)
  | ty_sum  (σ τ : Ty)
  | ty_unit
  | ty_union (T : 𝑻)
  | ty_record (R : 𝑹)
  .

  Record FunTy : Set :=
    { fun_dom : Ctx (𝑿 * Ty);
      fun_cod : Ty
    }.

  Module NameNotation.

    Notation "'ε'"   := (ctx_nil).
    Notation "Γ ▻ b" := (ctx_snoc Γ b) (at level 55, left associativity).
    Notation "Γ₁ ▻▻ Γ₂" := (ctx_cat Γ₁ Γ₂) (at level 55, left associativity).
    Notation "b ∈ Γ" := (InCtx b Γ)  (at level 80).
    Notation "E '►' x '∶' τ '↦' d" := (E , ((x , τ) , d)) (at level 55, left associativity).
    Notation "E1 '►►' E2" := (env_cat E1 E2) (at level 55, left associativity).
    Notation "E [ x ↦ v ]" := (@env_update _ _ _ E (x , _) _ v) (at level 55, left associativity).

  End NameNotation.

End TypeKit.
(* End Types. *)

Module Type TermKit (typeKit : TypeKit).
  Import typeKit.

  (* Names of union data constructors. *)
  Parameter 𝑲  : 𝑻 -> Set.
  (* Union data constructor field type *)
  Parameter 𝑲_Ty : forall (T : 𝑻), 𝑲 T -> Ty.
  (* Record field names. *)
  Parameter 𝑹𝑭  : Set.
  (* Record field types. *)
  Parameter 𝑹𝑭_Ty : 𝑹 -> Ctx (𝑹𝑭 * Ty).

  (* Names of functions. *)
  Parameter 𝑭  : Set.
  Parameter pi : 𝑭 -> FunTy.

  Section Literals.

    Inductive Bit : Set := bitzero | bitone.

    Inductive TaggedLit : Ty -> Set :=
    | taglit_int           : Z -> TaggedLit (ty_int)
    | taglit_bool          : bool -> TaggedLit (ty_bool)
    | taglit_bit           : Bit -> TaggedLit (ty_bit)
    | taglit_string        : string -> TaggedLit (ty_string)
    | taglit_list   σ'     : list (TaggedLit σ') -> TaggedLit (ty_list σ')
    | taglit_prod   σ₁ σ₂  : TaggedLit σ₁ * TaggedLit σ₂ -> TaggedLit (ty_prod σ₁ σ₂)
    | taglit_sum    σ₁ σ₂  : TaggedLit σ₁ + TaggedLit σ₂ -> TaggedLit (ty_sum σ₁ σ₂)
    | taglit_unit          : TaggedLit (ty_unit)
    | taglit_union (T : 𝑻) (K : 𝑲 T) : TaggedLit (𝑲_Ty K) -> TaggedLit (ty_union T)
    | taglit_record (R : 𝑹) : Env' TaggedLit (𝑹𝑭_Ty R) -> TaggedLit (ty_record R).

    Fixpoint Lit (σ : Ty) : Set :=
      match σ with
      | ty_int => Z
      | ty_bool => bool
      | ty_bit => Bit
      | ty_string => string
      | ty_list σ' => list (Lit σ')
      | ty_prod σ₁ σ₂ => Lit σ₁ * Lit σ₂
      | ty_sum σ₁ σ₂ => Lit σ₁ + Lit σ₂
      | ty_unit => unit
      | ty_union T => { K : 𝑲 T & TaggedLit (𝑲_Ty K) }
      | ty_record R => Env' TaggedLit (𝑹𝑭_Ty R)
      end%type.

    Fixpoint untag {σ : Ty} (v : TaggedLit σ) : Lit σ :=
      match v with
      | taglit_int z        => z
      | taglit_bool b       => b
      | taglit_bit b        => b
      | taglit_string s     => s
      | taglit_list ls      => List.map untag ls
      | taglit_prod (l , r) => (untag l , untag r)
      | taglit_sum (inl v)  => inl (untag v)
      | taglit_sum (inr v)  => inr (untag v)
      | taglit_unit         => tt
      | taglit_union l      => existT _ _ l
      | taglit_record t     => t
      end.

    Definition LocalStore (Γ : Ctx (𝑿 * Ty)) : Set := Env' Lit Γ.

  End Literals.

  Section Expressions.

    Inductive Exp (Γ : Ctx (𝑿 * Ty)) : Ty -> Set :=
    | exp_var     (x : 𝑿) (σ : Ty) {xInΓ : InCtx (x , σ) Γ} : Exp Γ σ
    | exp_lit     (σ : Ty) : Lit σ -> Exp Γ σ
    | exp_plus    (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_int
    | exp_times   (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_int
    | exp_minus   (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_int
    | exp_neg     (e : Exp Γ ty_int) : Exp Γ ty_int
    | exp_eq      (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_bool
    | exp_le      (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_bool
    | exp_lt      (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_bool
    | exp_and     (e₁ e₂ : Exp Γ ty_bool) : Exp Γ ty_bool
    | exp_not     (e : Exp Γ ty_bool) : Exp Γ ty_bool
    | exp_pair    {σ₁ σ₂ : Ty} (e₁ : Exp Γ σ₁) (e₂ : Exp Γ σ₂) : Exp Γ (ty_prod σ₁ σ₂)
    | exp_inl     {σ₁ σ₂ : Ty} : Exp Γ σ₁ -> Exp Γ (ty_sum σ₁ σ₂)
    | exp_inr     {σ₁ σ₂ : Ty} : Exp Γ σ₂ -> Exp Γ (ty_sum σ₁ σ₂)
    | exp_list    {σ : Ty} (es : list (Exp Γ σ)) : Exp Γ (ty_list σ)
    | exp_cons    {σ : Ty} (h : Exp Γ σ) (t : Exp Γ (ty_list σ)) : Exp Γ (ty_list σ)
    | exp_nil     {σ : Ty} : Exp Γ (ty_list σ)
    | exp_union   {T : 𝑻} (K : 𝑲 T) (e : Exp Γ (𝑲_Ty K)) : Exp Γ (ty_union T)
    | exp_record  (R : 𝑹) (es : Env' (Exp Γ) (𝑹𝑭_Ty R)) : Exp Γ (ty_record R)
    | exp_builtin {σ τ : Ty} (f : Lit σ -> Lit τ) (e : Exp Γ σ) : Exp Γ τ.

    Global Arguments exp_union {_ _} _ _.
    Global Arguments exp_record {_} _ _.

    Fixpoint evalTagged {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (e : Exp Γ σ) (δ : LocalStore Γ) {struct e} : TaggedLit σ.
    Admitted.

    Fixpoint eval {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (e : Exp Γ σ) (δ : LocalStore Γ) {struct e} : Lit σ :=
      match e in (Exp _ t) return (Lit t) with
      | @exp_var _ x _ xInΓ => env_lookup δ xInΓ
      | exp_lit _ _ l       => l
      | exp_plus e₁ e2      => Z.add (eval e₁ δ) (eval e2 δ)
      | exp_times e₁ e2     => Z.mul (eval e₁ δ) (eval e2 δ)
      | exp_minus e₁ e2     => Z.sub (eval e₁ δ) (eval e2 δ)
      | exp_neg e           => Z.opp (eval e δ)
      | exp_eq e₁ e2        => Zeq_bool (eval e₁ δ) (eval e2 δ)
      | exp_le e₁ e2        => Z.leb (eval e₁ δ) (eval e2 δ)
      | exp_lt e₁ e2        => Z.ltb (eval e₁ δ) (eval e2 δ)
      | exp_and e₁ e2       => andb (eval e₁ δ) (eval e2 δ)
      | exp_not e           => negb (eval e δ)
      | exp_pair e₁ e2      => pair (eval e₁ δ) (eval e2 δ)
      | exp_inl e           => inl (eval e δ)
      | exp_inr e           => inr (eval e δ)
      | exp_list es         => List.map (fun e => eval e δ) es
      | exp_cons e₁ e2      => cons (eval e₁ δ) (eval e2 δ)
      | exp_nil _           => nil
      | exp_union K e       => existT _ K (evalTagged e δ)
      | exp_record R es     => env_map (fun τ e => evalTagged e δ) es
      | exp_builtin f e     => f (eval e δ)
      end.

    Definition evals {Γ Δ} (es : Env' (Exp Γ) Δ) (δ : LocalStore Γ) : LocalStore Δ :=
      env_map (fun xτ e => eval e δ) es.

  End Expressions.

  Section Statements.

    Inductive RecordPat : Ctx (𝑹𝑭 * Ty) -> Ctx (𝑿 * Ty) -> Set :=
    | pat_nil  : RecordPat ctx_nil ctx_nil
    | pat_cons
        {rfs : Ctx (𝑹𝑭 * Ty)} {Δ : Ctx (𝑿 * Ty)}
        (pat : RecordPat rfs Δ) (rf : 𝑹𝑭) {τ : Ty} (x : 𝑿) :
        RecordPat (ctx_snoc rfs (rf , τ)) (ctx_snoc Δ (x , τ)).

    Inductive Stm (Γ : Ctx (𝑿 * Ty)) : Ty -> Set :=
    | stm_lit        {τ : Ty} (l : Lit τ) : Stm Γ τ
    | stm_exp        {τ : Ty} (e : Exp Γ τ) : Stm Γ τ
    | stm_let        (x : 𝑿) (τ : Ty) (s : Stm Γ τ) {σ : Ty} (k : Stm (ctx_snoc Γ (x , τ)) σ) : Stm Γ σ
    | stm_let'       (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) {σ : Ty} (k : Stm (ctx_cat Γ Δ) σ) : Stm Γ σ
    | stm_assign     (x : 𝑿) (τ : Ty) {xInΓ : InCtx (x , τ) Γ} (e : Exp Γ τ) : Stm Γ τ
    | stm_app        (f : 𝑭) (es : Env' (Exp Γ) (fun_dom (pi f))) : Stm Γ (fun_cod (pi f))
    | stm_app'       (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) (τ : Ty) (s : Stm Δ τ) : Stm Γ τ
    | stm_if         {τ : Ty} (e : Exp Γ ty_bool) (s₁ s₂ : Stm Γ τ) : Stm Γ τ
    | stm_seq        {τ : Ty} (e : Stm Γ τ) {σ : Ty} (k : Stm Γ σ) : Stm Γ σ
    | stm_assert     (e₁ : Exp Γ ty_bool) (e₂ : Exp Γ ty_string) : Stm Γ ty_bool
    (* | stm_while      (w : 𝑾 Γ) (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ) -> Stm Γ ty_unit *)
    | stm_exit       (τ : Ty) (s : Lit ty_string) : Stm Γ τ
    | stm_match_list {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
      (xh xt : 𝑿) (alt_cons : Stm (ctx_snoc (ctx_snoc Γ (xh , σ)) (xt , ty_list σ)) τ) : Stm Γ τ
    | stm_match_sum  {σinl σinr τ : Ty} (e : Exp Γ (ty_sum σinl σinr))
      (xinl : 𝑿) (alt_inl : Stm (ctx_snoc Γ (xinl , σinl)) τ)
      (xinr : 𝑿) (alt_inr : Stm (ctx_snoc Γ (xinr , σinr)) τ) : Stm Γ τ
    | stm_match_pair {σ₁ σ₂ τ : Ty} (e : Exp Γ (ty_prod σ₁ σ₂))
      (xl xr : 𝑿) (rhs : Stm (ctx_snoc (ctx_snoc Γ (xl , σ₁)) (xr , σ₂)) τ) : Stm Γ τ
    | stm_match_union {T : 𝑻} (e : Exp Γ (ty_union T)) {τ : Ty}
      (alts : forall (K : 𝑲 T), { x : 𝑿 & Stm (ctx_snoc Γ (x , 𝑲_Ty K)) τ}) : Stm Γ τ
    | stm_match_record {R : 𝑹} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_record R))
      (p : RecordPat (𝑹𝑭_Ty R) Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) : Stm Γ τ.

    Global Arguments stm_lit {_} _ _.
    Global Arguments stm_exp {_ _} _.
    Global Arguments stm_let {_} _ _ _ {_} _.
    Global Arguments stm_let' {_ _} _ {_} _.
    Global Arguments stm_assign {_} _ {_ _} _.
    Global Arguments stm_app {_} _ _.
    Global Arguments stm_app' {_} _ _ _ _.
    Global Arguments stm_if {_ _} _ _ _.
    Global Arguments stm_seq {_ _} _ {_} _.
    Global Arguments stm_assert {_} _ _.
    Global Arguments stm_exit {_} _ _.
    Global Arguments stm_match_list {_ _ _} _ _ _ _ _.
    Global Arguments stm_match_sum {_ _ _ _} _ _ _ _ _.
    Global Arguments stm_match_pair {_ _ _ _} _ _ _ _.
    Global Arguments stm_match_union {_ _} _ {_} _.
    Global Arguments stm_match_record {_} _ {_} _ _ {_} _.

  End Statements.

  Record FunDef (fty : FunTy) : Set :=
    { fun_body : Stm (fun_dom fty)(fun_cod fty) }.

  Module NameResolution.

    Parameter 𝑿_eq_dec : forall x y : 𝑿, {x=y}+{~x=y}.

    Fixpoint ctx_resolve {D : Set} (Γ : Ctx (𝑿 * D)) (x : 𝑿) {struct Γ} : option D :=
      match Γ with
      | ctx_nil           => None
      | ctx_snoc Γ (y, d) => if 𝑿_eq_dec x y then Some d else ctx_resolve Γ x
      end.

    Definition IsSome {D : Set} (m : option D) : Set :=
      match m with
        | Some _ => unit
        | None => Empty_set
      end.

    Definition fromSome {D : Set} (m : option D) : IsSome m -> D :=
      match m return IsSome m -> D with
      | Some d => fun _ => d
      | None   => fun p => match p with end
      end.

    Fixpoint mk_inctx {D : Set} (Γ : Ctx (prod 𝑿 D)) (x : 𝑿) {struct Γ} :
      let m := ctx_resolve Γ x in forall (p : IsSome m), InCtx (x , fromSome m p) Γ :=
      match Γ with
      | ctx_nil => fun p => match p with end
      | ctx_snoc Γ (y, d) =>
        match 𝑿_eq_dec x y as s
        return (forall p, InCtx (x, fromSome (if s then Some d else ctx_resolve Γ x) p) (ctx_snoc Γ (y, d)))
        with
        | left e => fun _ => match e with | eq_refl => inctx_zero end
        | right _ => fun p => inctx_succ (mk_inctx Γ x p)
        end
      end.

    Definition exp_smart_var {Γ : Ctx (𝑿 * Ty)} (x : 𝑿) {p : IsSome (ctx_resolve Γ x)} :
      Exp Γ (fromSome (ctx_resolve Γ x) p) := @exp_var Γ x (fromSome _ p) (mk_inctx Γ x p).

    Definition stm_smart_assign {Γ : Ctx (𝑿 * Ty)} (x : 𝑿) {p : IsSome (ctx_resolve Γ x)} :
      Exp Γ (fromSome (ctx_resolve Γ x) p) -> Stm Γ (fromSome (ctx_resolve Γ x) p) :=
      @stm_assign Γ x (fromSome _ p) (mk_inctx Γ x p).

  End NameResolution.

  Definition Pred (A : Set) : Type := A -> Prop.

  Record Contract (fty : FunTy) : Type :=
    { contract_pre_condition  : Pred (Env' Lit (fun_dom fty));
      contract_post_condition : Pred (Env' Lit (fun_dom fty) * Lit (fun_cod fty))
    }.

  Definition ContractEnv : Type :=
    forall (f : 𝑭), option (Contract (pi f)).

End TermKit.

Module Type ProgramKit (typeKit : TypeKit) (termKit : TermKit typeKit).
  Import typeKit.
  Import termKit.

  Parameter Pi : forall (f : 𝑭), FunDef (pi f).

  Section SmallStep.

    Fixpoint pattern_match {rfs : Ctx (𝑹𝑭 * Ty)}  {Δ : Ctx (𝑿 * Ty)}
             (p : RecordPat rfs Δ) {struct p} : Env' TaggedLit rfs -> LocalStore Δ :=
      match p with
      | pat_nil => fun _ => env_nil
      | pat_cons p rf x =>
        fun E =>
          env_snoc
            (pattern_match p (env_tail E)) (x, _)
            (untag (env_lookup E inctx_zero))
      end.

    (* Record State (Γ : Ctx (𝑿 * Ty)) (σ : Ty) : Set := *)
    (*   { state_local_store : LocalStore Γ; *)
    (*     state_statement   : Stm Γ σ *)
    (*   }. *)

    (* Notation "'⟨' δ ',' s '⟩'" := {| state_local_store := δ; state_statement := s |}. *)
    (* Reserved Notation "st1 '--->' st2" (at level 80). *)
    Reserved Notation "'⟨' δ1 ',' s1 '⟩' '--->' '⟨' δ2 ',' s2 '⟩'" (at level 80).

    Import NameNotation.

    (* Inductive Step {Γ : Ctx (𝑿 * Ty)} : forall {σ : Ty} (st₁ st₂ : State Γ σ), Prop := *)
    Inductive Step {Γ : Ctx (𝑿 * Ty)} : forall {σ : Ty} (δ₁ δ₂ : LocalStore Γ) (s₁ s₂ : Stm Γ σ), Prop :=

    | step_stm_exp
        (δ : LocalStore Γ) (σ : Ty) (e : Exp Γ σ) :
        ⟨ δ , stm_exp e ⟩ ---> ⟨ δ , stm_lit σ (eval e δ) ⟩

    | step_stm_let_value
        (δ : LocalStore Γ) (x : 𝑿) (τ σ : Ty) (v : Lit τ) (k : Stm (Γ ▻ (x , τ)) σ) :
        ⟨ δ , stm_let x τ (stm_lit τ v) k ⟩ ---> ⟨ δ , stm_let' (env_snoc env_nil (x,τ) v) k ⟩
    | step_stm_let_exit
        (δ : LocalStore Γ) (x : 𝑿) (τ σ : Ty) (s : string) (k : Stm (Γ ▻ (x , τ)) σ) :
        ⟨ δ , stm_let x τ (stm_exit τ s) k ⟩ ---> ⟨ δ , stm_exit σ s ⟩
    | step_stm_let_step
        (δ : LocalStore Γ) (δ' : LocalStore Γ) (x : 𝑿) (τ σ : Ty)
        (s : Stm Γ τ) (s' : Stm Γ τ) (k : Stm (Γ ▻ (x , τ)) σ) :
        ⟨ δ , s ⟩ ---> ⟨ δ' , s' ⟩ ->
        ⟨ δ , stm_let x τ s k ⟩ ---> ⟨ δ' , stm_let x τ s' k ⟩
    | step_stm_let'_value
        (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (σ : Ty) (v : Lit σ) :
        ⟨ δ , stm_let' δΔ (stm_lit σ v) ⟩ ---> ⟨ δ , stm_lit σ v ⟩
    | step_stm_let'_exit
        (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (σ : Ty) (s : string) :
        ⟨ δ , stm_let' δΔ (stm_exit σ s) ⟩ ---> ⟨ δ , stm_exit σ s ⟩
    | step_stm_let'_step
        (δ δ' : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ δΔ' : LocalStore Δ) (σ : Ty) (k k' : Stm (Γ ▻▻ Δ) σ) :
        ⟨ δ ►► δΔ , k ⟩ ---> ⟨ δ' ►► δΔ' , k' ⟩ ->
        ⟨ δ , stm_let' δΔ k ⟩ ---> ⟨ δ' , stm_let' δΔ' k' ⟩

    | step_stm_seq_step
        (δ δ' : LocalStore Γ) (τ σ : Ty) (s s' : Stm Γ τ) (k : Stm Γ σ) :
        ⟨ δ , s ⟩ ---> ⟨ δ' , s' ⟩ ->
        ⟨ δ , stm_seq s k ⟩ ---> ⟨ δ' , stm_seq s' k ⟩
    | step_stm_seq_value
        (δ : LocalStore Γ) (τ σ : Ty) (v : Lit τ) (k : Stm Γ σ) :
        ⟨ δ , stm_seq (stm_lit τ v) k ⟩ ---> ⟨ δ , k ⟩
    | step_stm_seq_exit
        (δ : LocalStore Γ) (τ σ : Ty) (s : string) (k : Stm Γ σ) :
        ⟨ δ , stm_seq (stm_exit τ s) k ⟩ ---> ⟨ δ , stm_exit σ s ⟩

    | step_stm_app
        {δ : LocalStore Γ} {f : 𝑭} :
        let Δ := fun_dom (pi f) in
        let τ := fun_cod (pi f) in
        let s := fun_body (Pi f) in
        forall (es : Env' (Exp Γ) Δ),
        ⟨ δ , stm_app f es ⟩ --->
        ⟨ δ , stm_app' Δ (evals es δ) τ s ⟩
    | step_stm_app'_step
        {δ : LocalStore Γ} (Δ : Ctx (𝑿 * Ty)) {δΔ δΔ' : LocalStore Δ} (τ : Ty)
        (s s' : Stm Δ τ) :
        ⟨ δΔ , s ⟩ ---> ⟨ δΔ' , s' ⟩ ->
        ⟨ δ , stm_app' Δ δΔ τ s ⟩ ---> ⟨ δ , stm_app' Δ δΔ' τ s' ⟩
    | step_stm_app'_value
        {δ : LocalStore Γ} (Δ : Ctx (𝑿 * Ty)) {δΔ : LocalStore Δ} (τ : Ty) (v : Lit τ) :
        ⟨ δ , stm_app' Δ δΔ τ (stm_lit τ v) ⟩ ---> ⟨ δ , stm_lit τ v ⟩
    | step_stm_app'_exit
        {δ : LocalStore Γ} (Δ : Ctx (𝑿 * Ty)) {δΔ : LocalStore Δ} (τ : Ty) (s : string) :
        ⟨ δ , stm_app' Δ δΔ τ (stm_exit τ s) ⟩ ---> ⟨ δ , stm_exit τ s ⟩
    | step_stm_assign
        (δ : LocalStore Γ) (x : 𝑿) (σ : Ty) {xInΓ : InCtx (x , σ) Γ} (e : Exp Γ σ) :
        let v := eval e δ in
        ⟨ δ , stm_assign x e ⟩ ---> ⟨ env_update δ xInΓ v , stm_lit σ v ⟩
    | step_stm_if
        (δ : LocalStore Γ) (e : Exp Γ ty_bool) (σ : Ty) (s₁ s₂ : Stm Γ σ) :
        ⟨ δ , stm_if e s₁ s₂ ⟩ ---> ⟨ δ , if eval e δ then s₁ else s₂ ⟩
    | step_stm_assert
        (δ : LocalStore Γ) (e₁ : Exp Γ ty_bool) (e₂ : Exp Γ ty_string) :
        ⟨ δ , stm_assert e₁ e₂ ⟩ --->
        ⟨ δ , if eval e₁ δ then stm_lit ty_bool true else stm_exit ty_bool (eval e₂ δ) ⟩
    (* | step_stm_while : *)
    (*   (δ : LocalStore Γ) (w : 𝑾 δ) (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ) -> *)
    (*   ⟨ δ , stm_while w e s ⟩ ---> *)
    (*   ⟨ δ , stm_if e (stm_seq s (stm_while w e s)) (stm_lit tt) ⟩ *)
    | step_stm_match_list
        (δ : LocalStore Γ) {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
        (xh xt : 𝑿) (alt_cons : Stm (Γ ▻ (xh , σ) ▻ (xt , ty_list σ)) τ) :
        ⟨ δ , stm_match_list e alt_nil xh xt alt_cons ⟩ --->
        ⟨ δ , match eval e δ with
              | nil => alt_nil
              | cons vh vt => stm_let' (env_snoc (env_snoc env_nil (xh,σ) vh) (xt,ty_list σ) vt) alt_cons
              end
        ⟩
    | step_stm_match_sum
        (δ : LocalStore Γ) {σinl σinr τ : Ty} (e : Exp Γ (ty_sum σinl σinr))
        (xinl : 𝑿) (alt_inl : Stm (Γ ▻ (xinl , σinl)) τ)
        (xinr : 𝑿) (alt_inr : Stm (Γ ▻ (xinr , σinr)) τ) :
        ⟨ δ , stm_match_sum e xinl alt_inl xinr alt_inr ⟩ --->
        ⟨ δ , match eval e δ with
              | inl v => stm_let' (env_snoc env_nil (xinl,σinl) v) alt_inl
              | inr v => stm_let' (env_snoc env_nil (xinr,σinr) v) alt_inr
              end
        ⟩
    | step_stm_match_pair
        (δ : LocalStore Γ) {σ₁ σ₂ τ : Ty} (e : Exp Γ (ty_prod σ₁ σ₂)) (xl xr : 𝑿)
        (rhs : Stm (Γ ▻ (xl , σ₁) ▻ (xr , σ₂)) τ) :
        ⟨ δ , stm_match_pair e xl xr rhs ⟩ --->
        ⟨ δ , let (vl , vr) := eval e δ in
              stm_let' (env_snoc (env_snoc env_nil (xl,σ₁) vl) (xr,σ₂) vr) rhs
        ⟩
    | step_stm_match_union
        (δ : LocalStore Γ) {T : 𝑻} (e : Exp Γ (ty_union T)) {τ : Ty}
        (alts : forall (K : 𝑲 T), { x : 𝑿 & Stm (ctx_snoc Γ (x , 𝑲_Ty K)) τ}) :
        ⟨ δ , stm_match_union e alts ⟩ --->
        ⟨ δ , let (K , v) := eval e δ in
              stm_let' (env_snoc env_nil (projT1 (alts K),𝑲_Ty K) (untag v)) (projT2 (alts K))
        ⟩
    | step_stm_match_record
        (δ : LocalStore Γ) {R : 𝑹} {Δ : Ctx (𝑿 * Ty)}
        (e : Exp Γ (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ)
        {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) :
        ⟨ δ , stm_match_record R e p rhs ⟩ --->
        ⟨ δ , stm_let' (pattern_match p (eval e δ)) rhs ⟩

    (* where "st1 '--->' st2" := (@Step _ _ st1 st2). *)
    where "'⟨' δ1 ',' s1 '⟩' '--->' '⟨' δ2 ',' s2 '⟩'" := (@Step _ _ δ1 δ2 s1 s2).

    Inductive Steps {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (δ1 : LocalStore Γ) (s1 : Stm Γ σ) : LocalStore Γ -> Stm Γ σ -> Prop :=
    | step_refl : Steps δ1 s1 δ1 s1
    | step_trans {δ2 δ3 : LocalStore Γ} {s2 s3 : Stm Γ σ} :
        Step δ1 δ2 s1 s2 -> Steps δ2 s2 δ3 s3 -> Steps δ1 s1 δ3 s3.

    Definition Final {Γ σ} (s : Stm Γ σ) : Prop :=
      match s with
      | stm_lit _ _  => True
      | stm_exit _ _ => True
      | _ => False
      end.

    Lemma can_form_store_cat (Γ Δ : Ctx (𝑿 * Ty)) (δ : LocalStore (Γ ▻▻ Δ)) :
      exists (δ₁ : LocalStore Γ) (δ₂ : LocalStore Δ), δ = env_cat δ₁ δ₂.
    Proof. pose (env_cat_split δ); eauto. Qed.

    (* Lemma can_form_store_snoc (Γ : Ctx (𝑿 * Ty)) (x : 𝑿) (σ : Ty) (δ : LocalStore (Γ ▻ (x , σ))) : *)
    (*   exists (δ' : LocalStore Γ) (v : Lit σ), δ = env_snoc δ' x σ v. *)
    (* Admitted. *)

    (* Lemma can_form_store_nil (δ : LocalStore ε) : *)
    (*   δ = env_nil. *)
    (* Admitted. *)

    Local Ltac progress_can_form :=
      match goal with
      (* | [ H: LocalStore (ctx_snoc _ _) |- _ ] => pose proof (can_form_store_snoc H) *)
      (* | [ H: LocalStore ctx_nil |- _ ] => pose proof (can_form_store_nil H) *)
      | [ H: LocalStore (ctx_cat _ _) |- _ ] => pose proof (can_form_store_cat _ _ H)
      | [ H: Final ?s |- _ ] => destruct s; cbn in H
      end; destruct_conjs; subst; try contradiction.

    Local Ltac progress_simpl :=
      repeat
        (cbn in *; destruct_conjs; subst;
         try progress_can_form;
         try match goal with
             | [ |- True \/ _] => left; constructor
             | [ |- False \/ _] => right
             | [ |- forall _, _ ] => intro
             | [ H : True |- _ ] => clear H
             | [ H : _ \/ _ |- _ ] => destruct H
             end).

    Local Ltac progress_inst T :=
      match goal with
      | [ IH: (forall (δ : LocalStore (ctx_cat ?Γ ?Δ)), _),
          δ1: LocalStore ?Γ, δ2: LocalStore ?Δ |- _
        ] => specialize (IH (env_cat δ1 δ2)); T
      (* | [ IH: (forall (δ : LocalStore (ctx_snoc ctx_nil (?x , ?σ))), _), *)
      (*     v: Lit ?σ |- _ *)
      (*   ] => specialize (IH (env_snoc env_nil x σ v)); T *)
      | [ IH: (forall (δ : LocalStore ?Γ), _), δ: LocalStore ?Γ |- _
        ] => solve [ specialize (IH δ); T | clear IH; T ]
      end.

    Local Ltac progress_tac :=
      progress_simpl;
      solve
        [ repeat eexists; constructor; eauto
        | progress_inst progress_tac
        ].

    Lemma progress {Γ σ} (s : Stm Γ σ) :
      Final s \/ forall δ, exists δ' s', ⟨ δ , s ⟩ ---> ⟨ δ' , s' ⟩.
    Proof. induction s; intros; try progress_tac. Qed.

  End SmallStep.

  Section Predicates.

    Variable CEnv : ContractEnv.

    Definition Cont (R A : Type) : Type := (A -> R) -> R.

    Definition DST (Γ₁ Γ₂ : Ctx (𝑿 * Ty)) (A : Type) : Type :=
      (A -> Pred (LocalStore Γ₂)) -> Pred (LocalStore Γ₁).

    Definition evalDST {Γ₁ Γ₂ A} (m : DST Γ₁ Γ₂ A) :
      LocalStore Γ₁ -> Cont Prop A :=
      fun δ₁ k => m (fun a δ₂ => k a) δ₁.

    Definition lift {Γ A} (m : Cont Prop A) : DST Γ Γ A :=
      fun k δ => m (fun a => k a δ).

    Definition pure {Γ A} (a : A) : DST Γ Γ A :=
      fun k => k a.
    Definition ap {Γ₁ Γ₂ Γ₃ A B} (mf : DST Γ₁ Γ₂ (A -> B))
               (ma : DST Γ₂ Γ₃ A) : DST Γ₁ Γ₃ B :=
      fun k => mf (fun f => ma (fun a => k (f a))).
    Definition abort {Γ₁ Γ₂ A} : DST Γ₁ Γ₂ A :=
      fun k δ => False.
    Definition assert {Γ} (b : bool) : DST Γ Γ bool :=
      fun k δ => Bool.Is_true b /\ k b δ.
    Definition bind {Γ₁ Γ₂ Γ₃ A B} (ma : DST Γ₁ Γ₂ A) (f : A -> DST Γ₂ Γ₃ B) : DST Γ₁ Γ₃ B :=
      fun k => ma (fun a => f a k).
    Definition bindright {Γ₁ Γ₂ Γ₃ A B} (ma : DST Γ₁ Γ₂ A) (mb : DST Γ₂ Γ₃ B) : DST Γ₁ Γ₃ B :=
      bind ma (fun _ => mb).
    Definition bindleft {Γ₁ Γ₂ Γ₃ A B} (ma : DST Γ₁ Γ₂ A) (mb : DST Γ₂ Γ₃ B) : DST Γ₁ Γ₃ A :=
      bind ma (fun a => bind mb (fun _ => pure a)).
    Definition get {Γ} : DST Γ Γ (LocalStore Γ) :=
      fun k δ => k δ δ.
    Definition put {Γ Γ'} (δ' : LocalStore Γ') : DST Γ Γ' unit :=
      fun k _ => k tt δ'.
    Definition modify {Γ Γ'} (f : LocalStore Γ -> LocalStore Γ') : DST Γ Γ' unit :=
      bind get (fun δ => put (f δ)).
    Definition meval {Γ σ} (e : Exp Γ σ) : DST Γ Γ (Lit σ) :=
      bind get (fun δ => pure (eval e δ)).
    Definition push {Γ x σ} (v : Lit σ) : DST Γ (ctx_snoc Γ (x , σ)) unit :=
      modify (fun δ => env_snoc δ (x,σ) v).
    Definition pop {Γ x σ} : DST (ctx_snoc Γ (x , σ)) Γ unit :=
      modify (fun δ => env_tail δ).
    Definition pushs {Γ Δ} (δΔ : LocalStore Δ) : DST Γ (ctx_cat Γ Δ) unit :=
      modify (fun δΓ => env_cat δΓ δΔ).
    Definition pops {Γ} Δ : DST (ctx_cat Γ Δ) Γ unit :=
      modify (fun δΓΔ => env_drop Δ δΓΔ).

    Notation "ma >>= f" := (bind ma f) (at level 90, left associativity).
    Notation "ma *> mb" := (bindright ma mb) (at level 90, left associativity).
    Notation "ma <* mb" := (bindleft ma mb) (at level 90, left associativity).

    Import NameNotation.

    (* Version that computes *)
    Definition IsLit {Γ σ} (δ : LocalStore Γ) (s : Stm Γ σ) :
      forall (POST : Lit σ -> Pred (LocalStore Γ)), Prop :=
      match s with
      | stm_lit _ v => fun POST => POST v δ
      | _ => fun _ => False
      end.

    Lemma IsLit_inversion {Γ σ} (δ : LocalStore Γ) (s : Stm Γ σ)
          (POST : Lit σ -> Pred (LocalStore Γ)) :
      IsLit δ s POST -> exists v, s = stm_lit _ v /\ POST v δ.
    Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

    Fixpoint WLP {Γ τ} (s : Stm Γ τ) : DST Γ Γ (Lit τ) :=
      match s in (Stm _ τ) return (DST Γ Γ (Lit τ)) with
      | stm_lit _ l => pure l
      | stm_assign x e => meval e >>= fun v => modify (fun δ => δ [ x ↦ v ]) *> pure v
      | stm_let x σ s k => WLP s >>= push *> WLP k <* pop
      | stm_exp e => meval e
      | stm_assert e1 e2  => meval e1 >>= assert
      | stm_if e s1 s2 => meval e >>= fun b => if b then WLP s1 else WLP s2
      | stm_exit _ _  => abort
      | stm_seq s1 s2 => WLP s1 *> WLP s2
      | stm_app' Δ δ τ s => lift (evalDST (WLP s) δ)

      | stm_app f es => match CEnv f with
                        | None => abort (* NOT IMPLEMENTED *)
                        | Some c => fun POST δ =>
                                      contract_pre_condition c (evals es δ)
                                      /\ (forall v, contract_post_condition c (evals es δ, v) -> POST v δ)
                        end
      | stm_let' δ k => pushs δ *> WLP k <* pops _
      | stm_match_list e alt_nil xh xt alt_cons =>
        meval e >>= fun v =>
        match v with
        | nil => WLP alt_nil
        | cons vh vt => push vh *> @push _ _ (ty_list _) vt *> WLP alt_cons <* pop <* pop
        end
      | stm_match_sum e xinl altinl xinr altinr =>
        meval e >>= fun v =>
        match v with
        | inl v => push v *> WLP altinl <* pop
        | inr v => push v *> WLP altinr <* pop
        end
      | stm_match_pair e xl xr rhs =>
        meval e >>= fun v =>
        let (vl , vr) := v in
        push vl *> push vr *> WLP rhs <* pop <* pop
      | stm_match_union e rhs =>
        meval e >>= fun v =>
        let (K , tv) := v in
        let (x , alt) := rhs K in
        push (untag tv) *> WLP alt <* pop
      | stm_match_record R e p rhs =>
        meval e >>= fun v =>
        pushs (pattern_match p v) *> WLP rhs <* pops _
      end.

    (* Notation "'⟨' δ ',' s '⟩'" := {| state_local_store := δ; state_statement := s |}. *)
    Notation "'⟨' δ1 ',' s1 '⟩' '--->' '⟨' δ2 ',' s2 '⟩'" := (@Step _ _ δ1 δ2 s1 s2) (at level 80).

    (* Notation "t₁ --> t₂" := (@Step _ _ t₁ t₂) (at level 80). *)
    Notation "'⟨' δ1 ',' s1 '⟩' --->* '⟨' δ2 ',' s2 '⟩'" := (@Steps _ _ δ1 s1 δ2 s2) (at level 80).

    Section Soundness.

      Local Ltac steps_inversion_simpl :=
        repeat
          (try match goal with
               | [ H: exists t, _ |- _ ] => destruct H
               | [ H: _ /\ _ |- _ ] => destruct H
               | [ H: existT _ _ _ = existT _ _ _ |- _ ] => dependent destruction H
               | [ H : False |- _ ] => destruct H
               end;
           cbn in *).

      Local Ltac extend p :=
        let P := type of p in
        match goal with
        | [ _ : P |- _ ] => fail 1
        | _ => pose proof p
        end.

      Local Ltac steps_inversion_inster :=
        repeat
          (try match goal with
               | [ H : forall _, _ = _ -> _ |- _ ]
                 => specialize (H _ eq_refl)
               | [ H : forall _ _, _ = _ -> _ |- _ ]
                 => specialize (H _ _ eq_refl)
               | [ H : forall _ _ _, _ = _ -> _ |- _ ]
                 => specialize (H _ _ _ eq_refl)
               | [ H : Final ?s -> _, H' : Final ?s |- _ ]
                 => specialize (H H')
               | [ H1 : ⟨ ?δ1, ?s1 ⟩ ---> ⟨ ?δ2, ?s2 ⟩,
                   H2 : ⟨ ?δ2, ?s2 ⟩ --->* ⟨ ?δ3, ?s3 ⟩ |- _ ]
                 => extend (step_trans H1 H2)
               end;
           steps_inversion_simpl).

      Local Ltac steps_inversion_solve :=
        repeat
          (match goal with
           | [ |- exists t, _ ] => eexists
           | [ |- _ /\ _ ] => constructor
           | [ |- True ] => constructor
           | [ |- ⟨ _ , stm_lit _ _ ⟩ --->* ⟨ _, _ ⟩ ] => constructor 1
           | [ |- ⟨ _ , stm_exit _ _ ⟩ --->* ⟨ _, _ ⟩ ] => constructor 1
           end; cbn); eauto.

      Local Ltac steps_inversion_induction :=
        let step := fresh in
        induction 1 as [|? ? ? ? ? ? step]; intros; subst;
          [ steps_inversion_simpl
          | inversion step; steps_inversion_inster; steps_inversion_solve
          ].

      Lemma steps_inversion_let {Γ x τ σ} {δ1 δ3 : LocalStore Γ}
        {s1 : Stm Γ τ} {s2 : Stm (ctx_snoc Γ (x, τ)) σ} {t : Stm Γ σ} (final : Final t)
        (steps : ⟨ δ1, stm_let x τ s1 s2 ⟩ --->* ⟨ δ3, t ⟩) :
        exists (δ2 : LocalStore Γ) (s1' : Stm Γ τ),
        (⟨ δ1, s1 ⟩ --->* ⟨ δ2, s1' ⟩) /\ Final s1' /\
        (exists (s0 : Stm Γ σ),
            (⟨ δ2, stm_let x τ s1' s2 ⟩ ---> ⟨ δ2, s0 ⟩) /\ ⟨ δ2, s0 ⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_let x τ s1 s2) as s. revert steps s1 s2 Heqs.
        steps_inversion_induction.
      Qed.

      Lemma steps_inversion_let' {Γ Δ σ} (δ1 δ3 : LocalStore Γ)
        (δΔ : LocalStore Δ) (k : Stm (ctx_cat Γ Δ) σ) (t : Stm Γ σ) (final : Final t)
        (steps : ⟨ δ1, stm_let' δΔ k ⟩ --->* ⟨ δ3, t ⟩) :
        exists δ2 δΔ' k',
          ⟨ env_cat δ1 δΔ , k ⟩ --->* ⟨ env_cat δ2 δΔ' , k' ⟩ /\ Final k' /\
          exists (s0 : Stm Γ σ),
            (⟨ δ2, stm_let' δΔ' k' ⟩ ---> ⟨ δ2, s0 ⟩) /\ (⟨ δ2, s0 ⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_let' δΔ k) as s. revert steps δΔ k Heqs.
        steps_inversion_induction.
      Qed.

      Lemma steps_inversion_seq {Γ τ σ} (δ1 δ3 : LocalStore Γ)
        (s1 : Stm Γ τ) (s2 : Stm Γ σ) (t : Stm Γ σ) (final : Final t)
        (steps : ⟨ δ1, stm_seq s1 s2 ⟩ --->* ⟨ δ3, t ⟩) :
        exists δ2 s1',
          ⟨ δ1, s1 ⟩ --->* ⟨ δ2, s1' ⟩ /\ Final s1' /\
          exists (s0 : Stm Γ σ),
            (⟨ δ2, stm_seq s1' s2 ⟩ ---> ⟨ δ2 , s0 ⟩) /\ (⟨ δ2 , s0 ⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_seq s1 s2) as s. revert steps s1 s2 Heqs.
        steps_inversion_induction.
      Qed.

      Lemma steps_inversion_app' {Γ Δ σ} (δ1 δ3 : LocalStore Γ)
        (δΔ : LocalStore Δ) (k : Stm Δ σ) (t : Stm Γ σ) (final : Final t)
        (steps : ⟨ δ1, stm_app' Δ δΔ σ k ⟩ --->* ⟨ δ3, t ⟩) :
        exists δΔ' k',
          ⟨ δΔ , k ⟩ --->* ⟨ δΔ' , k' ⟩ /\ Final k' /\
          exists s0,
          (⟨ δ1, stm_app' Δ δΔ' σ k' ⟩ ---> ⟨ δ1, s0 ⟩) /\ (⟨ δ1, s0⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_app' Δ δΔ σ k) as s. revert steps δΔ k Heqs.
        steps_inversion_induction.
      Qed.

      Definition Triple {Γ τ}
        (PRE : Pred (LocalStore Γ)) (s : Stm Γ τ)
        (POST : Lit τ -> Pred (LocalStore Γ)) : Prop :=
        forall (δ δ' : LocalStore Γ) (v : Lit τ),
          ⟨ δ , s ⟩ --->* ⟨ δ' , stm_lit τ v ⟩ ->
          PRE δ ->
          POST v δ'.

      Ltac wlp_sound_steps_inversion :=
        repeat
          match goal with
          | [ H: ⟨ _, stm_assert _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>            inversion H; subst; clear H
          | [ H: ⟨ _, stm_assert _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>           inversion H; subst; clear H
          | [ H: ⟨ _, stm_assign _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>            dependent destruction H
          | [ H: ⟨ _, stm_assign _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>           dependent destruction H
          | [ H: ⟨ _, stm_exit _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>              inversion H; subst; clear H
          | [ H: ⟨ _, stm_exit _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>             inversion H; subst; clear H
          | [ H: ⟨ _, stm_exp _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>                 inversion H; subst; clear H
          | [ H: ⟨ _, stm_exp _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>                inversion H; subst; clear H
          | [ H: ⟨ _, stm_if _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>              inversion H; subst; clear H
          | [ H: ⟨ _, stm_if _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>             inversion H; subst; clear H
          | [ H: ⟨ _, stm_lit _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>               inversion H; subst; clear H
          | [ H: ⟨ _, stm_lit _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>              inversion H; subst; clear H
          | [ H: ⟨ _, stm_match_list _ _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>  inversion H; subst; clear H
          | [ H: ⟨ _, stm_match_list _ _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] => inversion H; subst; clear H
          | [ H: ⟨ _, stm_match_pair _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>    inversion H; subst; clear H
          | [ H: ⟨ _, stm_match_pair _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>   inversion H; subst; clear H
          | [ H: ⟨ _, stm_match_record _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>  inversion H; subst; clear H
          | [ H: ⟨ _, stm_match_record _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] => inversion H; subst; clear H
          | [ H: ⟨ _, stm_match_sum _ _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>   inversion H; subst; clear H
          | [ H: ⟨ _, stm_match_sum _ _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>  inversion H; subst; clear H
          | [ H: ⟨ _, stm_match_union _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>       inversion H; subst; clear H
          | [ H: ⟨ _, stm_match_union _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>      inversion H; subst; clear H

          | [ H: ⟨ _, stm_app' _ _ _ (stm_lit _ _) ⟩ ---> ⟨ _, _ ⟩ |- _ ] => inversion H; subst; clear H
          | [ H: ⟨ _, stm_let _ _ (stm_lit _ _) _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>  inversion H; subst; clear H
          | [ H: ⟨ _, stm_let' _ (stm_lit _ _) ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>     inversion H; subst; clear H
          | [ H: ⟨ _, stm_seq (stm_lit _ _) _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>      inversion H; subst; clear H

          | [ H: ⟨ _, stm_app' _ _ _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] => apply (steps_inversion_app' HF) in H
          | [ H: ⟨ _, stm_let _ _ _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>  apply (steps_inversion_let HF) in H
          | [ H: ⟨ _, stm_let' _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>     apply (steps_inversion_let' HF) in H
          | [ H: ⟨ _, stm_seq _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>      apply (steps_inversion_seq HF) in H
          end.

      Ltac wlp_sound_inst :=
        match goal with
        | [ IH: forall _ _ _, ⟨ _ , ?s ⟩ --->* ⟨ _ , _ ⟩ -> _,
            HS: ⟨ _ , ?s ⟩ --->* ⟨ _ , ?t ⟩,
            HF: Final ?t,
            WP: WLP ?s _ _
            |- _
          ] => specialize (IH _ _ _ HS _ WP HF); clear HS WP
        end.

      Ltac wlp_sound_simpl :=
        try wlp_sound_inst;
        repeat
          (steps_inversion_simpl;
           wlp_sound_steps_inversion;
           unfold Triple, assert, pure, lift, push, pop, meval, bind, bindleft, bindright, get, put, modify, pushs, abort, evalDST, pops in *;
           cbn in *;
           destruct_conjs; subst;
           try match goal with
               | [ H: existT _ _ _ = existT _ _ _ |- _ ] =>
                 dependent destruction H
               (* | [ H: ⟨ _ , _ ⟩ = ⟨ _ , _ ⟩ |- _ ] => *)
               (*   dependent destruction H *)
               | [ H: _ \/ _ |- _ ] => destruct H
               | [ H: True |- _ ] => clear H
               | [ H: False |- _ ] => destruct H
               | [ H: Env _ (ctx_snoc _ _) |- _ ] =>
                 dependent destruction H
               | [ H: Env _ ctx_nil |- _ ] =>
                 dependent destruction H
               end).

      Ltac wlp_sound_islit_inversion :=
          match goal with
          | [ H: IsLit _ _ _ |- _ ] => apply IsLit_inversion in H
          end; wlp_sound_simpl.

      Lemma WLP_sound {Γ σ} (s : Stm Γ σ) :
        forall (δ δ' : LocalStore Γ) (s' : Stm Γ σ), ⟨ δ, s ⟩ --->* ⟨ δ', s' ⟩ ->
          forall (POST : Lit σ -> Pred (LocalStore Γ)), WLP s POST δ -> Final s' -> IsLit δ' s' POST.
      Proof with wlp_sound_simpl; eauto.
        induction s; intros.
        - wlp_sound_simpl; auto.
        - wlp_sound_simpl; auto.
        - wlp_sound_simpl; auto.
          wlp_sound_inst.
          wlp_sound_islit_inversion.
          wlp_sound_inst...
          wlp_sound_islit_inversion; auto.
        - wlp_sound_simpl; auto.
          wlp_sound_inst.
          wlp_sound_islit_inversion; auto.
          now rewrite env_drop_cat in H4.
        - wlp_sound_simpl; auto.
        - wlp_sound_simpl.
          destruct (CEnv f); destruct_conjs; try contradiction.
          admit.
        - wlp_sound_simpl.
          wlp_sound_inst.
          wlp_sound_islit_inversion; auto.
        - wlp_sound_simpl.
          destruct (eval e δ2).
          + wlp_sound_inst...
          + wlp_sound_inst...
        - wlp_sound_simpl.
          wlp_sound_inst...
          wlp_sound_islit_inversion; auto.
          wlp_sound_inst...
        - wlp_sound_simpl.
          destruct (eval e₁ δ2); wlp_sound_simpl; auto.
        - wlp_sound_simpl.
        - wlp_sound_simpl.
          destruct (eval e δ2).
          + wlp_sound_inst...
          + wlp_sound_simpl.
            wlp_sound_inst.
            wlp_sound_islit_inversion...
        - wlp_sound_simpl.
          destruct (eval e δ2); wlp_sound_simpl.
          + wlp_sound_inst.
            wlp_sound_islit_inversion; auto.
          + wlp_sound_inst.
            wlp_sound_islit_inversion; auto.
        - wlp_sound_simpl.
          destruct (eval e δ2); wlp_sound_simpl.
          wlp_sound_inst.
          wlp_sound_islit_inversion; auto.
        - wlp_sound_simpl.
          destruct (eval e δ2); wlp_sound_simpl.
          admit. (* #$@&%* *)
        - wlp_sound_simpl.
          wlp_sound_inst.
          wlp_sound_islit_inversion; auto.
          now rewrite env_drop_cat in H4.
      Admitted.

    End Soundness.

  End Predicates.

End ProgramKit.
