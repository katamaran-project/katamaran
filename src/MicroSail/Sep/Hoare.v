Require Import Coq.Program.Tactics.
Require Import FunctionalExtensionality.

Require Import MicroSail.Syntax.
Require Import MicroSail.Environment.
Require Import MicroSail.Sep.Logic.
Require Import MicroSail.Sep.Spec.

Module ProgramLogic

  (Import typekit : TypeKit)
  (Import termkit : TermKit typekit)
  (Import progkit : ProgramKit typekit termkit)
  (Import assertkit : AssertionKit typekit termkit progkit)
  (Import contractkit : SymbolicContractKit typekit termkit progkit assertkit)
  (Import heapkit : HeapKit typekit termkit progkit assertkit contractkit).

  Import CtxNotations.
  Import EnvNotations.

  (* Some simple instance that make writing program logic rules more natural by
   avoiding the need to mention the local variable store δ in the pre and post
   conditions that don't affect it *)
  Section WithΓ.
    Context (Γ : Ctx (𝑿 * Ty)).

    Instance δ_ILogic (L : Type) (LL : ILogic L) : ILogic (LocalStore Γ -> L) :=
      { lentails P Q := (forall δ, lentails (P δ ) (Q δ));
        ltrue := (fun _ => ltrue);
        lfalse := (fun _ => lfalse);
        land P Q := (fun δ => (land (P δ) (Q δ)));
        lor P Q := (fun δ => (lor (P δ) (Q δ)));
        limpl P Q := (fun δ => (limpl (P δ) (Q δ)));
        lprop P := fun _ => lprop P;
        lex {T} (F : T -> LocalStore Γ -> L) := fun δ => lex (fun t => F t δ);
        lall {T} (F : T -> LocalStore Γ -> L) := fun δ => lall (fun t => F t δ)
      }.

    Program Instance δ_ILogicLaws (L : Type) (LL : ILogic L) (LLL : ILogicLaws L LL) :
      ILogicLaws (LocalStore Γ -> L) (δ_ILogic L LL).
    (* (* Solve the obligations with firstorder take a lot of time. *) *)
    (* Solve Obligations with firstorder. *)
    Admit Obligations.

    Instance δ_ISepLogic (L : Type) (SL : ISepLogic L) : ISepLogic (LocalStore Γ -> L) :=
      { emp := fun _ => emp;
        sepcon P Q := fun δ => sepcon (P δ) (Q δ);
        wand P Q := fun δ => wand (P δ) (Q δ)
      }.

    Program Instance δ_ISepLogicLaws (L : Type) (LL : ISepLogic L)
                                     (LLL : ISepLogicLaws L LL) :
      ISepLogicLaws (LocalStore Γ -> L) (δ_ISepLogic L LL).
    Admit Obligations.

    Program Instance δ_IHeaplet (L : Type) (SL : IHeaplet L) :
      IHeaplet (LocalStore Γ -> L) :=
      { pred p ts := fun δ => pred p ts;
        ptsreg σ r v := fun δ => ptsreg r v
      }.

  End WithΓ.

  Open Scope logic.

  Reserved Notation "Γ ⊢ ⦃ P // δin ⦄ s ⦃ Q // δout ⦄" (at level 75, no associativity).

  Existing Instance δ_IHeaplet.

  (* Pun program variables as logical variables *)
  Definition asΣ (Γ : Ctx (𝑿 * Ty)) : Ctx (𝑺 * Ty).
    induction Γ.
    - exact ctx_nil.
    - exact (ctx_snoc IHΓ ((𝑿to𝑺 (fst b) , (snd b)))).
  Defined.

  (* Pun program variables in local store as symbolic variables to
     use them in assertion interpretation *)
  Definition asδΣ {Γ} (δΓ : LocalStore Γ) : @NamedEnv 𝑺 Ty Lit (asΣ Γ).
    unfold LocalStore in *.
    unfold NamedEnv in *.
    induction δΓ.
    - exact env_nil.
    - refine (env_snoc IHδΓ _ _).
      now exact db.
  Defined.

  Definition asSymbolicLocalStore {Γ} (δΓ : LocalStore Γ) : SymbolicLocalStore Γ (asΣ Γ) :=
    env_map (fun xt v => term_lit (snd xt) v) δΓ.

  (* Relation specification of weakest liberal preconditions for function contracts *)
  Inductive SepContractWLP
            {L : Type} {Logic : IHeaplet L}
            (Δ : Ctx (𝑿 * Ty)) {σ : Ty}
            (δΔ : LocalStore Δ)
            (POST : Lit σ -> L) :
    forall
      (wlp : L)
      (c : SepContract Δ σ)
    , Prop :=
  | rule_sep_contract_result_pure
      (Σ : Ctx (𝑺 * Ty))
      (δ : SymbolicLocalStore Δ Σ)
      (result : Term Σ σ)
      (req : Assertion Σ) (ens : Assertion Σ) :
      SepContractWLP Δ δΔ POST
        (∀ (δΣ : NamedEnv Lit Σ),
            !!(δΔ = env_map (fun _ t => eval_term t δΣ) δ) -->
            interpret δΣ req
            ∧ (∀ v, interpret δΣ ens
                    ∧ !!(v = eval_term result δΣ) --> POST v))
        (sep_contract_result_pure δ result req ens)
  | rule_sep_contract_result
      (Σ : Ctx (𝑺 * Ty))
      (δ : SymbolicLocalStore Δ Σ)
      (result : 𝑺)
      (req : Assertion Σ) (ens : Assertion (Σ ▻ (result , σ))) :
      SepContractWLP Δ δΔ POST
        (∀ (δΣ : NamedEnv Lit Σ),
            !!(δΔ = env_map (fun _ t => eval_term t δΣ) δ) -->
            interpret δΣ req
            ∧ (∀ v, interpret (env_snoc δΣ (result , σ) v) ens --> POST v))
        (@sep_contract_result _ _ _ δ result req ens)
  | rule_sep_contract_none : SepContractWLP Δ δΔ POST ⊥ (@sep_contract_none Δ σ)
  .

  Inductive Triple {L : Type} {Logic : IHeaplet L} (Γ : Ctx (𝑿 * Ty)) :
    forall {τ : Ty}
      (δin : LocalStore Γ)
      (pre : L)
      (s : Stm Γ τ)
      (δout : LocalStore Γ)
      (post :  Lit τ -> L), Prop :=
  (* | rule_bind *)
  (*    ⦃ P // δ1 ⦄ s ⦃ Q // δ2 ⦄ → (forall v, ⦃ Q v // δ2 ⦄ E[v] ⦃ R // δ3 ⦄) *)
  (*     ⦃ P // δ1 ⦄ E[s] ⦃ R // δ3 ⦄ *)
  | rule_consequence {σ : Ty}
      (δ : LocalStore Γ) (P P' : L) (Q Q' : Lit σ -> L) (s : Stm Γ σ) :
      (P ⊢ P') -> (forall v, Q' v ⊢ Q v) -> Γ ⊢ ⦃ P' // δ ⦄ s ⦃ Q' // δ ⦄ -> Γ ⊢ ⦃ P // δ ⦄ s ⦃ Q // δ ⦄
  (* | rule_frame {σ : Ty} *)
  (*     (P : LocalStore Γ -> L) (Q : Lit σ -> LocalStore Γ -> L) (s : Stm Γ σ) : *)
  (*     forall (R : LocalStore Γ -> L), Γ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ -> Γ ⊢ ⦃ R ✱ P ⦄ s ⦃ fun v => R ✱ Q v ⦄ *)
  (* | rule_stm_lit (τ : Ty) (l : Lit τ) : *)
  (*     Γ ⊢ ⦃ ⊤ ⦄ stm_lit τ l ⦃ fun x => !!(l = x) ⦄ *)
  (* | rule_stm_exp_forwards (τ : Ty) (e : Exp Γ τ) (P : LocalStore Γ -> L) : *)
  (*     Γ ⊢ ⦃ P ⦄ stm_exp e ⦃ fun v δ => P δ ∧ !!(eval e δ = v) ⦄ *)
  (* | rule_stm_exp_backwards (τ : Ty) (e : Exp Γ τ) (Q : Lit τ -> LocalStore Γ -> L) : *)
  (*     Γ ⊢ ⦃ fun δ => Q (eval e δ) δ ⦄ stm_exp e ⦃ Q ⦄ *)
  | rule_stm_let
      (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (ctx_snoc Γ (x , σ)) τ)
      (δ1 δ2 : LocalStore Γ) δ3
      (P : L) (Q : Lit σ -> L) (R : Lit τ -> L) :
      Γ ⊢ ⦃ P // δ1 ⦄ s ⦃ Q // δ2 ⦄ ->
      (forall (v : Lit σ), Γ ▻ (x,σ) ⊢ ⦃ Q v // env_snoc δ2 (x,σ) v ⦄ k ⦃ R // δ3 ⦄) ->
      Γ ⊢ ⦃ P // δ1 ⦄ let: x := s in k ⦃ R // env_tail δ3 ⦄
  (* | rule_stm_if (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ) *)
  (*               (P : LocalStore Γ -> L) *)
  (*               (Q : Lit τ -> LocalStore Γ -> L) : *)
  (*     Γ ⊢ ⦃ fun δ => P δ ∧ !!(eval e δ = true) ⦄ s1 ⦃ Q ⦄ -> *)
  (*     Γ ⊢ ⦃ fun δ => P δ ∧ !!(eval e δ = false) ⦄ s2 ⦃ Q ⦄ -> *)
  (*     Γ ⊢ ⦃ P ⦄ stm_if e s1 s2 ⦃ Q ⦄ *)
  (* | rule_stm_if_backwards (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ) *)
  (*                         (P1 : LocalStore Γ -> L) *)
  (*                         (P2 : LocalStore Γ -> L) *)
  (*                         (Q : Lit τ -> LocalStore Γ -> L) : *)
  (*     Γ ⊢ ⦃ P1 ⦄ s1 ⦃ Q ⦄ -> *)
  (*     Γ ⊢ ⦃ P2 ⦄ s2 ⦃ Q ⦄ -> *)
  (*     Γ ⊢ ⦃ fun δ => (!!(eval e δ = true) --> P1 δ) *)
  (*                 ∧ (!!(eval e δ = false) --> P2 δ) *)
  (*         ⦄ stm_if e s1 s2 ⦃ Q ⦄ *)
  | rule_stm_seq (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
      (δ1 δ2 δ3 : LocalStore Γ)
      (P Q : L) (R : Lit σ -> L) :
      Γ ⊢ ⦃ P // δ1 ⦄ s1 ⦃ (fun _ => Q) // δ2 ⦄ ->
      Γ ⊢ ⦃ Q // δ2 ⦄ s2 ⦃ R // δ3 ⦄ ->
      Γ ⊢ ⦃ P // δ1 ⦄ s1 ;; s2 ⦃ R // δ3 ⦄
  (* | rule_stm_assert (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) *)
  (*                   (P : LocalStore Γ -> L) *)
  (*                   (Q : Lit ty_bool -> LocalStore Γ -> L) : *)
  (*     Γ ⊢ ⦃ fun δ => P δ ∧ !!(eval e1 δ = true) ⦄ stm_assert e1 e2 ⦃ Q ⦄ *)
  (* | rule_stm_fail (τ : Ty) (s : Lit ty_string) : *)
  (*     forall (Q : Lit τ -> LocalStore Γ -> L), *)
  (*       Γ ⊢ ⦃ fun _ => ⊥ ⦄ stm_fail τ s ⦃ Q ⦄ *)
  (* | rule_stm_match_sum_backwards (σinl σinr τ : Ty) (e : Exp Γ (ty_sum σinl σinr)) *)
  (*                                (xinl : 𝑿) (alt_inl : Stm (ctx_snoc Γ (xinl , σinl)) τ) *)
  (*                                (xinr : 𝑿) (alt_inr : Stm (ctx_snoc Γ (xinr , σinr)) τ) *)
  (*                                (Pinl : LocalStore Γ -> L) *)
  (*                                (Pinr : LocalStore Γ -> L) *)
  (*                                (Q : Lit τ -> LocalStore Γ -> L) : *)
  (*     Γ ▻ (xinl, σinl) ⊢ ⦃ fun δ => Pinl (env_tail δ) *)
  (*                                     (* ∧ !!(eval e (env_tail δ) = inl (env_head δ)) *) *)
  (*                        ⦄ alt_inl ⦃ fun v δ => Q v (env_tail δ) ⦄ -> *)
  (*     Γ ▻ (xinr, σinr) ⊢ ⦃ fun δ => Pinr (env_tail δ) *)
  (*                                     (* ∧ !!(eval e (env_tail δ) = inr (env_head δ)) *) *)
  (*                        ⦄ alt_inr ⦃ fun v δ => Q v (env_tail δ) ⦄ -> *)
  (*     Γ ⊢ ⦃ fun δ => (∀ x, !!(eval e δ = inl x) --> Pinl δ) *)
  (*                 ∧ (∀ x, !!(eval e δ = inr x) --> Pinr δ) *)
  (*         ⦄ stm_match_sum e xinl alt_inl xinr alt_inr ⦃ Q ⦄ *)
  (* | rule_stm_read_register_backwards {σ : Ty} (r : 𝑹𝑬𝑮 σ) *)
  (*                                    (Q : Lit σ -> LocalStore Γ -> L) : *)
  (*     Γ ⊢ ⦃ ∀ v, r ↦ v ✱ (r ↦ v -✱ Q v) ⦄ stm_read_register r ⦃ Q ⦄ *)
  (* | rule_stm_write_register_backwards *)
  (*     {σ : Ty} (r : 𝑹𝑬𝑮 σ) (e : Exp Γ σ) (Q : Lit σ -> LocalStore Γ -> L) : *)
  (*     Γ ⊢ ⦃ fun δ => ∀ v, r ↦ v ✱ ((r ↦ eval e δ) -✱ Q (eval e δ) δ) ⦄ *)
  (*       stm_write_register r e *)
  (*       ⦃ Q ⦄ *)
  (* | rule_stm_assign_backwards *)
  (*     (x : 𝑿) (σ : Ty) (xIn : (x,σ) ∈ Γ) (s : Stm Γ σ) *)
  (*     (P : LocalStore Γ -> L) *)
  (*     (R : Lit σ -> LocalStore Γ -> L) : *)
  (*     Γ ⊢ ⦃ P ⦄ s ⦃ R ⦄ -> *)
  (*     Γ ⊢ ⦃ fun δ => (∀ v__old, P (δ ⟪ x ↦ v__old ⟫)%env) ⦄ stm_assign x s ⦃ R ⦄ *)
  (* | rule_stm_assign_forwards *)
  (*     (x : 𝑿) (σ : Ty) (xIn : (x,σ) ∈ Γ) (s : Stm Γ σ) *)
  (*     (P : LocalStore Γ -> L) *)
  (*     (R : Lit σ -> LocalStore Γ -> L) : *)
  (*     Γ ⊢ ⦃ P ⦄ s ⦃ R ⦄ -> *)
  (*     Γ ⊢ ⦃ P ⦄ stm_assign x s ⦃ fun v__new δ => ∃ v__old, R v__new (δ ⟪ x ↦ v__old ⟫)%env ⦄ *)
  | rule_stm_call
      {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
      (δ : LocalStore Γ)
      (P : L) (Q : Lit σ -> L) :
      SepContractWLP Δ (evals es δ) Q P (CEnv f) ->
      Γ ⊢ ⦃ P // δ ⦄ stm_call f es ⦃ Q // δ ⦄
  (* (* | rule_stm_match_pair {σ1 σ2 τ : Ty} (e : Exp Γ (ty_prod σ1 σ2)) *) *)
  (*   (xl xr : 𝑿) (rhs : Stm (ctx_snoc (ctx_snoc Γ (xl , σ1)) (xr , σ2)) τ) *)
  (*   (P : LocalStore Γ -> A) *)
  (*   (Q : LocalStore Γ -> Lit τ -> A) : *)
  (*   Γ ▻ (xl, σ1) ▻ (xr, σ2) ⊢ ⦃ P ⦄ rhs ⦃ Q ⦄ -> *)
  (*   Γ ⊢ ⦃ fun δ => P ⦄ stm_match_pair e xl xr rhs ⦃ Q ⦄ *)
  where "Γ ⊢ ⦃ P // δin ⦄ s ⦃ Q // δout ⦄" := (Triple Γ δin P s δout Q).

End ProgramLogic.
