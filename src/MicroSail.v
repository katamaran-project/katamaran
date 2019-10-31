Require Export Coq.Unicode.Utf8.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Program.Tactics.

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

  Fixpoint ctx_nth {B : Set} (Γ : Ctx B) (n : nat) {struct Γ} : option B :=
    match Γ , n with
    | ctx_snoc _ x , O   => Some x
    | ctx_snoc Γ _ , S n => ctx_nth Γ n
    | _            , _   => None
    end.

  Class InCtx {B : Set} (b : B) (Γ : Ctx B) : Set :=
    inCtx : { n : nat | ctx_nth Γ n = Some b }.

  Definition inctx_zero {B : Set} {b : B} {Γ : Ctx B} : InCtx b (ctx_snoc Γ b) :=
    exist _ 0 eq_refl.
  Definition inctx_succ {B : Set} {b : B} {Γ : Ctx B} {b' : B} (bIn : InCtx b Γ) :
    InCtx b (ctx_snoc Γ b') := let (n, e) := bIn in exist _ (S n) e.

End Contexts.

Section Environments.

  Definition Env {X T : Set} (D : T -> Set) (Γ : Ctx (X * T)) : Set :=
    forall (x : X) (τ : T), InCtx (x,τ) Γ -> D τ.

  Definition env_nil {X T : Set} {D : T -> Set} : @Env X T D ctx_nil :=
    fun x τ xIn => let (n, e) := xIn in
    eq_rec None (fun m => match m with | Some _ => D τ | None => unit end) tt (Some (x, τ)) e.

  Definition env_snoc {X T : Set} {D : T -> Set} {Γ : Ctx (X * T)}
             (E : Env D Γ) (x : X) (τ : T) (d : D τ) : Env D (ctx_snoc Γ (x , τ)).
  Admitted.

  Definition env_cat {X T : Set} {D : T -> Set} {Γ Δ : Ctx (X * T)}
             (EΓ : Env D Γ) (EΔ : Env D Δ) : Env D (ctx_cat Γ Δ).
  Admitted.

  (* Definition env_nil {X T : Set} {D : T -> Set} : @Env X T D ctx_nil := *)
  (*   fun y σ yIn => *)
  (*     match yIn in InCtx _ Γx *)
  (*               return match Γx with *)
  (*                      | ctx_nil => D σ *)
  (*                      | ctx_snoc _ _ => unit *)
  (*                      end *)
  (*               with *)
  (*               | inctx_zero _ => tt *)
  (*               | inctx_succ i => tt *)
  (*     end. *)

  (* Definition env_snoc {X T : Set} {D : T -> Set} {Γ : Ctx (X * T)} *)
  (*   (E : Env D Γ) (x : X) (τ : T) (d : D τ) : Env D (ctx_snoc Γ (x , τ)) := *)
  (*   fun y σ yIn => match yIn in InCtx _ Γx *)
  (*               return match Γx with *)
  (*                      | ctx_nil => Empty_set *)
  (*                      | ctx_snoc Γ (_, τ) => Env D Γ -> D τ -> D σ *)
  (*                      end *)
  (*               with *)
  (*               | inctx_zero _ => λ _ d, d *)
  (*               | @inctx_succ _ _ _ (_ , _) i => fun E _ => E y σ i *)
  (*               end E d. *)

  Global Arguments env_snoc {_ _ _ _} _ _ _ _.

  Definition env_drop {X T : Set} {D : T -> Set} {Γ : Ctx (X * T)}
    (x : X) (τ : T) (E : Env D (ctx_snoc Γ (x , τ))) : Env D Γ :=
    fun y σ yIn => E y σ (inctx_succ yIn).

  Definition env_map {X T : Set} {D₁ D₂ : T -> Set} {Γ : Ctx (X * T)}
    (f : forall τ, D₁ τ -> D₂ τ) (E : Env D₁ Γ) : Env D₂ Γ :=
    fun y σ yIn => f _ (E y σ yIn).
  Definition env_lookup {X T : Set} {D : T -> Set} {Γ : Ctx (X * T)}
    (E : Env D Γ) {x : X} {τ : T} (i : InCtx (x , τ) Γ) : D τ := E _ _ i.
  Definition env_update {X T : Set} {D : T -> Set} {Γ : Ctx (X * T)}
    (E : Env D Γ) {x : X} {τ : T} (i : InCtx (x , τ) Γ) (d : D τ) : Env D Γ.
  Admitted.

End Environments.

(* Section Types. *)
Module Type TypeKit.

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
    Notation "E '►' x '∶' τ '↦' d" := (env_snoc E x τ d) (at level 55, left associativity).
    Notation "E1 '►►' E2" := (env_cat E1 E2) (at level 55, left associativity).
    Notation "E [ x ↦ v ]" := (@env_update _ _ _ _ E x _ _ v) (at level 55, left associativity).

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
    | taglit_record (R : 𝑹) : Env TaggedLit (𝑹𝑭_Ty R) -> TaggedLit (ty_record R).

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
      | ty_record R => Env TaggedLit (𝑹𝑭_Ty R)
      end%type.

    Fixpoint untag {σ : Ty} (v : TaggedLit σ) : Lit σ :=
      match v with
      | taglit_int  z       => z
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

    Definition LocalStore (Γ : Ctx (𝑿 * Ty)) : Set := Env Lit Γ.

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
    | exp_record  (R : 𝑹) (es : Env (Exp Γ) (𝑹𝑭_Ty R)) : Exp Γ (ty_record R)
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
    | stm_app        (f : 𝑭) (es : Env (Exp Γ) (fun_dom (pi f))) : Stm Γ (fun_cod (pi f))
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

End TermKit.

Module Type ProgramKit (typeKit : TypeKit) (termKit : TermKit typeKit).
  Import typeKit.
  Import termKit.

  Parameter Pi : forall (f : 𝑭), FunDef (pi f).

  Section SmallStep.

    Fixpoint pattern_match {rfs : Ctx (𝑹𝑭 * Ty)}  {Δ : Ctx (𝑿 * Ty)}
             (p : RecordPat rfs Δ) {struct p} : Env TaggedLit rfs -> LocalStore Δ :=
      match p with
      | pat_nil => fun _ => env_nil
      | pat_cons p rf x =>
        fun E => env_snoc
               (pattern_match p (fun rf τ H => E rf τ (inctx_succ H))) x _
               (untag (E rf _ inctx_zero))
      end.

    (* Record State (Γ : Ctx (𝑿 * Ty)) (σ : Ty) : Set := *)
    (*   { state_local_store : LocalStore Γ; *)
    (*     state_statement   : Stm Γ σ *)
    (*   }. *)

    (* Notation "'⟨' δ ',' s '⟩'" := {| state_local_store := δ; state_statement := s |}. *)
    Reserved Notation "'⟨' δ1 ',' s1 '⟩' '--->' '⟨' δ2 ',' s2 '⟩'" (at level 80).

    Import NameNotation.

    Inductive Step {Γ : Ctx (𝑿 * Ty)} : forall {σ : Ty} (δ₁ δ₂ : LocalStore Γ) (s₁ s₂ : Stm Γ σ), Prop :=

    | step_stm_exp
        (δ : LocalStore Γ) (σ : Ty) (e : Exp Γ σ) :
        ⟨ δ , stm_exp e ⟩ ---> ⟨ δ , stm_lit σ (eval e δ) ⟩

    | step_stm_let_step
        (δ : LocalStore Γ) (δ' : LocalStore Γ) (x : 𝑿) (τ σ : Ty)
        (s : Stm Γ τ) (s' : Stm Γ τ) (k : Stm (Γ ▻ (x , τ)) σ) :
        ⟨ δ , s ⟩ ---> ⟨ δ' , s' ⟩ ->
        ⟨ δ , stm_let x τ s k ⟩ ---> ⟨ δ' , stm_let x τ s' k ⟩
    | step_stm_let_value
        (δ : LocalStore Γ) (x : 𝑿) (τ σ : Ty) (v : Lit τ) (k : Stm (Γ ▻ (x , τ)) σ) :
        ⟨ δ , stm_let x τ (stm_lit τ v) k ⟩ ---> ⟨ δ , stm_let' (env_nil ► x∶τ ↦ v) k ⟩
    | step_stm_let_exit
        (δ : LocalStore Γ) (x : 𝑿) (τ σ : Ty) (s : string) (k : Stm (Γ ▻ (x , τ)) σ) :
        ⟨ δ , stm_let x τ (stm_exit τ s) k ⟩ ---> ⟨ δ , stm_exit σ s ⟩
    | step_stm_let'_step
        (δ δ' : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ δΔ' : LocalStore Δ) (σ : Ty) (k k' : Stm (Γ ▻▻ Δ) σ) :
        ⟨ δ ►► δΔ , k ⟩ ---> ⟨ δ' ►► δΔ' , k' ⟩ ->
        ⟨ δ , stm_let' δΔ k ⟩ ---> ⟨ δ' , stm_let' δΔ' k' ⟩
    | step_stm_let'_value
        (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (σ : Ty) (v : Lit σ) :
        ⟨ δ , stm_let' δΔ (stm_lit σ v) ⟩ ---> ⟨ δ , stm_lit σ v ⟩
    | step_stm_let'_exit
        (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (σ : Ty) (s : string) :
        ⟨ δ , stm_let' δΔ (stm_exit σ s) ⟩ ---> ⟨ δ , stm_exit σ s ⟩

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
        forall (es : Env (Exp Γ) Δ),
        ⟨ δ , stm_app f es ⟩ --->
        ⟨ δ , stm_app' Δ (fun x σ xInΔ => eval (es x σ xInΔ) δ) τ s ⟩
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
        ⟨ δ , stm_assign x e ⟩ ---> ⟨ δ [ x ↦ v ] , stm_lit σ v ⟩
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
              | cons vh vt => stm_let' (env_nil ► xh∶σ ↦ vh ► xt∶ty_list σ ↦ vt) alt_cons
              end
        ⟩
    | step_stm_match_sum
        (δ : LocalStore Γ) {σinl σinr τ : Ty} (e : Exp Γ (ty_sum σinl σinr))
        (xinl : 𝑿) (alt_inl : Stm (Γ ▻ (xinl , σinl)) τ)
        (xinr : 𝑿) (alt_inr : Stm (Γ ▻ (xinr , σinr)) τ) :
        ⟨ δ , stm_match_sum e xinl alt_inl xinr alt_inr ⟩ --->
        ⟨ δ , match eval e δ with
              | inl v => stm_let' (env_nil ► xinl∶σinl ↦ v) alt_inl
              | inr v => stm_let' (env_nil ► xinr∶σinr ↦ v) alt_inr
              end
        ⟩
    | step_stm_match_pair
        (δ : LocalStore Γ) {σ₁ σ₂ τ : Ty} (e : Exp Γ (ty_prod σ₁ σ₂)) (xl xr : 𝑿)
        (rhs : Stm (Γ ▻ (xl , σ₁) ▻ (xr , σ₂)) τ) :
        ⟨ δ , stm_match_pair e xl xr rhs ⟩ --->
        ⟨ δ , let (vl , vr) := eval e δ in
              stm_let' (env_nil ► xl∶σ₁ ↦ vl ► xr∶σ₂ ↦ vr) rhs
        ⟩
    | step_stm_match_union
        (δ : LocalStore Γ) {T : 𝑻} (e : Exp Γ (ty_union T)) {τ : Ty}
        (alts : forall (K : 𝑲 T), { x : 𝑿 & Stm (ctx_snoc Γ (x , 𝑲_Ty K)) τ}) :
        ⟨ δ , stm_match_union e alts ⟩ --->
        ⟨ δ , let (K , v) := eval e δ in
              stm_let' (env_nil ► projT1 (alts K)∶𝑲_Ty K ↦ untag v) (projT2 (alts K))
        ⟩
    | step_stm_match_record
        (δ : LocalStore Γ) {R : 𝑹} {Δ : Ctx (𝑿 * Ty)}
        (e : Exp Γ (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ)
        {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) :
        ⟨ δ , stm_match_record R e p rhs ⟩ --->
        ⟨ δ , stm_let' (pattern_match p (eval e δ)) rhs ⟩

    where "'⟨' δ1 ',' s1 '⟩' '--->' '⟨' δ2 ',' s2 '⟩'" := (@Step _ _ δ1 δ2 s1 s2).

    Definition Final {Γ σ} (s : Stm Γ σ) : Prop :=
      match s with
      | stm_lit _ _  => True
      | stm_exit _ _ => True
      | _ => False
      end.

    Lemma can_form_store_cat (Γ Δ : Ctx (𝑿 * Ty)) (δ : LocalStore (Γ ▻▻ Δ)) :
      exists (δ₁ : LocalStore Γ) (δ₂ : LocalStore Δ), δ = env_cat δ₁ δ₂.
    Admitted.

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
      try solve
          [ repeat eexists; constructor; eauto
          | progress_inst progress_tac
          ].

    Lemma progress {Γ σ} (s : Stm Γ σ) :
      Final s \/ forall δ, exists δ' s', ⟨ δ , s ⟩ ---> ⟨ δ' , s' ⟩.
    Proof. induction s; intros; progress_tac. Qed.

  End SmallStep.

End ProgramKit.
