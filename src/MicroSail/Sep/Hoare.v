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

  Reserved Notation "δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" (at level 75, no associativity).

  Existing Instance δ_IHeaplet.

  (* Hoare triples for SepContract *)

  Inductive CTriple {L : Type} {Logic : IHeaplet L} (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) :
    forall {τ : Ty} (pre : L) (post : Lit τ -> L) (c : SepContract Δ τ), Prop :=
  | rule_sep_contract_unit
      (Σ  : Ctx (𝑺 * Ty)) (θΔ : SymbolicLocalStore Δ Σ) (δΣ : NamedEnv Lit Σ)
      (req : Assertion Σ) (ens : Assertion Σ) :
      δΔ = env_map (fun _ t => eval_term t δΣ) θΔ ->
      CTriple (τ:=ty_unit) Δ δΔ
        (interpret δΣ req)
        (fun _ => interpret δΣ ens)
        (sep_contract_unit θΔ req ens)
  | rule_sep_contract_result_pure
      (σ : Ty)
      (Σ  : Ctx (𝑺 * Ty)) (θΔ : SymbolicLocalStore Δ Σ) (δΣ : NamedEnv Lit Σ)
      (req : Assertion Σ) (ens : Assertion Σ) (result : Term Σ σ) :
      δΔ = env_map (fun _ t => eval_term t δΣ) θΔ ->
      CTriple Δ δΔ
        (interpret δΣ req)
        (fun v => interpret δΣ ens ∧ !!(v = eval_term result δΣ))
        (sep_contract_result_pure θΔ result req ens)
  | rule_sep_contract_result
      (σ : Ty) (result : 𝑺)
      (Σ  : Ctx (𝑺 * Ty)) (θΔ : SymbolicLocalStore Δ Σ) (δΣ : NamedEnv Lit Σ)
      (req : Assertion Σ) (ens : Assertion (Σ ▻ (result , σ))) :
      δΔ = env_map (fun _ t => eval_term t δΣ) θΔ ->
      CTriple
        Δ δΔ
        (interpret δΣ req)
        (fun v => interpret (env_snoc δΣ (result , σ) v) ens)
        (@sep_contract_result _ _ _ θΔ result req ens).
  (* | rule_sep_contract_none {σ} : *)
  (*     Pi f *)
  (*     CTriple Γ (fun _ => ⊤) (fun _ _ => ⊤) (@sep_contract_none Γ σ). *)


  Inductive Triple {L : Type} {Logic : IHeaplet L} (Γ : Ctx (𝑿 * Ty)) (δ : LocalStore Γ) :
    forall {τ : Ty}
      (pre : L) (s : Stm Γ τ)
      (post :  Lit τ -> LocalStore Γ -> L), Prop :=
  | rule_consequence {σ : Ty}
      (P P' : L) (Q Q' : Lit σ -> LocalStore Γ -> L) (s : Stm Γ σ) :
      (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') -> δ ⊢ ⦃ P' ⦄ s ⦃ Q' ⦄ -> δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄
  | rule_frame {σ : Ty}
      (R P : L) (Q : Lit σ -> LocalStore Γ -> L) (s : Stm Γ σ) :
      δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ -> δ ⊢ ⦃ R ✱ P ⦄ s ⦃ fun v δ' => R ✱ Q v δ' ⦄
  | rule_stm_lit (τ : Ty) (l : Lit τ) :
      δ ⊢ ⦃ ⊤ ⦄ stm_lit τ l ⦃ fun v δ' => !!(l = v /\ δ = δ') ⦄
  | rule_stm_exp_forwards (τ : Ty) (e : Exp Γ τ) (P : L) :
      δ ⊢ ⦃ P ⦄ stm_exp e ⦃ fun v δ' => P ∧ !!(eval e δ = v /\ δ = δ') ⦄
  | rule_stm_exp_backwards (τ : Ty) (e : Exp Γ τ) (Q : Lit τ -> LocalStore Γ -> L) :
      δ ⊢ ⦃ Q (eval e δ) δ ⦄ stm_exp e ⦃ Q ⦄
  | rule_stm_let
      (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (ctx_snoc Γ (x , σ)) τ)
      (P : L) (Q : Lit σ -> LocalStore Γ -> L)
      (R : Lit τ -> LocalStore Γ -> L) :
      δ         ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
      (forall (v : Lit σ) (δ' : LocalStore Γ),
          env_snoc δ' (x,σ) v ⊢ ⦃ Q v δ' ⦄ k ⦃ fun v δ'' => R v (env_tail δ'') ⦄ ) ->
      δ         ⊢ ⦃ P ⦄ let: x := s in k ⦃ R ⦄
  | rule_stm_if
      (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
      (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
      δ ⊢ ⦃ P ∧ !!(eval e δ = true) ⦄ s1 ⦃ Q ⦄ ->
      δ ⊢ ⦃ P ∧ !!(eval e δ = false) ⦄ s2 ⦃ Q ⦄ ->
      δ ⊢ ⦃ P ⦄ stm_if e s1 s2 ⦃ Q ⦄
  | rule_stm_if_backwards
      (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
      (P1 P2 : L) (Q : Lit τ -> LocalStore Γ -> L) :
      δ ⊢ ⦃ P1 ⦄ s1 ⦃ Q ⦄ -> δ ⊢ ⦃ P2 ⦄ s2 ⦃ Q ⦄ ->
      δ ⊢ ⦃ (!!(eval e δ = true)  --> P1) ∧
            (!!(eval e δ = false) --> P2)
          ⦄ stm_if e s1 s2 ⦃ Q ⦄
  | rule_stm_seq
      (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
      (P : L) (Q : LocalStore Γ -> L) (R : Lit σ -> LocalStore Γ -> L) :
      δ ⊢ ⦃ P ⦄ s1 ⦃ fun _ => Q ⦄ ->
      (forall δ', δ' ⊢ ⦃ Q δ' ⦄ s2 ⦃ R ⦄) ->
      δ ⊢ ⦃ P ⦄ s1 ;; s2 ⦃ R ⦄
  | rule_stm_assert (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string)
                    (P : L)
                    (Q : Lit ty_bool -> LocalStore Γ -> L) :
      δ ⊢ ⦃ P ∧ !!(eval e1 δ = true) ⦄ stm_assert e1 e2 ⦃ Q ⦄
  | rule_stm_fail (τ : Ty) (s : Lit ty_string) :
      forall (Q : Lit τ -> LocalStore Γ -> L),
        δ ⊢ ⦃ ⊥ ⦄ stm_fail τ s ⦃ Q ⦄
  | rule_stm_match_sum (σinl σinr τ : Ty) (e : Exp Γ (ty_sum σinl σinr))
                       (xinl : 𝑿) (alt_inl : Stm (ctx_snoc Γ (xinl , σinl)) τ)
                       (xinr : 𝑿) (alt_inr : Stm (ctx_snoc Γ (xinr , σinr)) τ)
                       (Pinl : L)
                       (Pinr : L)
                       (Q : Lit τ -> LocalStore Γ -> L) :
      (forall v, env_snoc δ (xinl,σinl) v ⊢ ⦃ Pinl ⦄ alt_inl ⦃ fun v' δ' => Q v' (env_tail δ') ⦄) ->
      (forall v, env_snoc δ (xinr,σinr) v ⊢ ⦃ Pinr ⦄ alt_inr ⦃ fun v' δ' => Q v' (env_tail δ') ⦄) ->
      δ ⊢ ⦃ (∀ x, !!(eval e δ = inl x) --> Pinl)
          ∧ (∀ x, !!(eval e δ = inr x) --> Pinr)
          ⦄ stm_match_sum e xinl alt_inl xinr alt_inr ⦃ Q ⦄
  | rule_stm_read_register_backwards {σ : Ty} (r : 𝑹𝑬𝑮 σ)
                                     (Q : Lit σ -> LocalStore Γ -> L) :
      δ ⊢ ⦃ ∀ v, r ↦ v ✱ (r ↦ v -✱ Q v δ) ⦄ stm_read_register r ⦃ Q ⦄
  | rule_stm_write_register_backwards {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                                      (Q : Lit σ -> LocalStore Γ -> L) :
      δ ⊢ ⦃ ∀ v, r ↦ v ✱ (r ↦ eval w δ -✱ Q (eval w δ) δ) ⦄ stm_write_register r w ⦃ Q ⦄
  | rule_stm_assign_backwards
      (x : 𝑿) (σ : Ty) (xIn : (x,σ) ∈ Γ) (s : Stm Γ σ)
      (P : L) (R : Lit σ -> LocalStore Γ -> L) :
      δ ⊢ ⦃ P ⦄ s ⦃ fun v δ' => R v (δ' ⟪ x ↦ v ⟫)%env ⦄ ->
      δ ⊢ ⦃ P ⦄ stm_assign x s ⦃ R ⦄
  | rule_stm_assign_forwards
      (x : 𝑿) (σ : Ty) (xIn : (x,σ) ∈ Γ) (s : Stm Γ σ)
      (P : L) (R : Lit σ -> LocalStore Γ -> L) :
      δ ⊢ ⦃ P ⦄ s ⦃ R ⦄ ->
      δ ⊢ ⦃ P ⦄ stm_assign x s ⦃ fun v__new δ' => ∃ v__old, R v__new (δ' ⟪ x ↦ v__old ⟫)%env ⦄
  | rule_stm_call_forwards
      {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
      (P : L)
      (Q : Lit σ -> L) :
      CTriple Δ (evals es δ) P Q (CEnv f) ->
      δ ⊢ ⦃ P ⦄ stm_call f es ⦃ fun v δ' => Q v ∧ !!(δ = δ') ⦄
  | rule_stm_call_backwards
      {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
      (P : L) (Q : Lit σ -> LocalStore Γ -> L) :
      CTriple Δ (evals es δ) P (fun v => Q v δ) (CEnv f) ->
      δ ⊢ ⦃ P ⦄ stm_call f es ⦃ Q ⦄
  | rule_stm_match_pair {σ1 σ2 τ : Ty} (e : Exp Γ (ty_prod σ1 σ2))
    (xl xr : 𝑿) (rhs : Stm (ctx_snoc (ctx_snoc Γ (xl , σ1)) (xr , σ2)) τ)
    (P : L)
    (Q : Lit τ -> LocalStore Γ -> L) :
    (forall vl vr, env_snoc (env_snoc δ (xl, σ1) vl) (xr, σ2) vr ⊢
              ⦃ P ⦄ rhs ⦃ fun v δ' => Q v (env_tail (env_tail δ')) ⦄) ->
    δ ⊢ ⦃ P ⦄ stm_match_pair e xl xr rhs ⦃ Q ⦄
  where "δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" := (Triple _ δ P s Q).

End ProgramLogic.
