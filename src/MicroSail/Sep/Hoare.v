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
  (Import heapkit : HeapKit typekit termkit progkit assertkit).
  (* (Import contractkit : SymbolicContractKit typekit termkit progkit assertkit). *)
  (* Module CM := SymbolicContracts typekit termkit progkit assertkit contractkit. *)
  (* Export CM. *)

  (* Program Instance Assertion_NatDed (Σ : Ctx (𝑺 * Ty)) : NatDed (Term Σ ty_bool) := *)
  (* { andp := (fun P Q => term_binop binop_and P Q); *)
  (*   orp := (fun P Q => term_binop binop_or P Q); *)
  (*   exp := _; *)
  (*   allp := _; *)
  (*   imp := _; *)
  (*   prop := _; *)
  (*   derives := _; *)
  (* }. *)

  Import CtxNotations.
  Import EnvNotations.

  Open Scope logic.
  (* Definition ctxprop := Ctx (𝑿 * Ty) -> Prop. *)

  (* Definition ptstoctx {Γ : Ctx (𝑿 * Ty)} {A : Set} (x : 𝑿) (v : A) : ctxprop := *)
  (*   fun _ => True. *)

  (* Program Instance ctxpop_NatDed : NatDed ctxprop. *)
  (* Admit Obligations. *)


  Reserved Notation "Γ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" (at level 75, no associativity).

  Section HoareTriples.
    Context {A : Type} {Logic : Heaplet A}.

    Inductive Triple (Γ : Ctx (𝑿 * Ty)) :
      forall {τ : Ty}
             (pre : LocalStore Γ -> A) (s : Stm Γ τ)
             (post :  LocalStore Γ -> Lit τ -> A), Prop :=
    | rule_stm_lit (τ : Ty) (l : Lit τ) :
        Γ ⊢ ⦃ fun _ => TT ⦄ stm_lit τ l ⦃ fun _ x => !!(l = x) ⦄
    | rule_stm_exp_forwards (τ : Ty) (e : Exp Γ τ) (P : LocalStore Γ -> A) :
        Γ ⊢ ⦃ P ⦄ stm_exp e ⦃ fun δ v => P δ ∧ !!(eval e δ = v) ⦄
    | rule_stm_exp_backwards (τ : Ty) (e : Exp Γ τ) (Q : LocalStore Γ -> Lit τ -> A) :
        Γ ⊢ ⦃ fun δ => Q δ (eval e δ) ⦄ stm_exp e ⦃ Q ⦄
    | rule_stm_let
        (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (ctx_snoc Γ (x , σ)) τ)
        (P : LocalStore Γ -> A) (Q : LocalStore Γ -> Lit σ -> A)
        (R : LocalStore Γ -> Lit τ -> A) :
        Γ         ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
        Γ ▻ (x,σ) ⊢ ⦃ fun δ => Q (env_tail δ) (env_head δ) ⦄ k ⦃ fun δ => R (env_tail δ) ⦄ ->
        Γ         ⊢ ⦃ P ⦄ let: x := s in k ⦃ R ⦄
    | rule_stm_if (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
          (P : LocalStore Γ -> A)
          (Q : LocalStore Γ -> Lit τ -> A) :
          Γ ⊢ ⦃ fun δ => P δ ∧ !!(eval e δ = true) ⦄ s1 ⦃ Q ⦄ ->
          Γ ⊢ ⦃ fun δ => P δ ∧ !!(eval e δ = false) ⦄ s2 ⦃ Q ⦄ ->
          Γ ⊢ ⦃ P ⦄ stm_if e s1 s2 ⦃ Q ⦄
    | rule_stm_if_backwards (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
          (P1 : LocalStore Γ -> A)
          (P2 : LocalStore Γ -> A)
          (Q : LocalStore Γ -> Lit τ -> A) :
          Γ ⊢ ⦃ P1 ⦄ s1 ⦃ Q ⦄ ->
          Γ ⊢ ⦃ P2 ⦄ s2 ⦃ Q ⦄ ->
          Γ ⊢ ⦃ fun δ => (!!(eval e δ = true) --> P1 δ)
                    ∧ (!!(eval e δ = false) --> P2 δ)
               ⦄ stm_if e s1 s2 ⦃ Q ⦄
    | rule_stm_seq (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
          (P : LocalStore Γ -> A)
          (Q : LocalStore Γ -> A)
          (R : LocalStore Γ -> Lit σ -> A) :
          Γ ⊢ ⦃ P ⦄ s1 ⦃ fun δ _ => Q δ ⦄ ->
          Γ ⊢ ⦃ Q ⦄ s2 ⦃ R ⦄ ->
          Γ ⊢ ⦃ P ⦄ s1 ;; s2 ⦃ R ⦄
    | rule_stm_assert (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string)
    (* Just a side note: don't we need the assertion string to a literal, *)
    (*    rather than an expression? *)
          (P : LocalStore Γ -> A)
          (Q : LocalStore Γ -> Lit ty_bool -> A) :
          Γ ⊢ ⦃ fun δ => P δ ∧ !!(eval e1 δ = true) ⦄ stm_assert e1 e2 ⦃ Q ⦄
    | rule_stm_fail (τ : Ty) (s : Lit ty_string) :
        forall (Q : LocalStore Γ -> Lit τ -> A),
        Γ ⊢ ⦃ fun _ => FF ⦄ stm_fail τ s ⦃ Q ⦄
    | rule_stm_match_sum_backwards (σinl σinr τ : Ty) (e : Exp Γ (ty_sum σinl σinr))
      (xinl : 𝑿) (alt_inl : Stm (ctx_snoc Γ (xinl , σinl)) τ)
      (xinr : 𝑿) (alt_inr : Stm (ctx_snoc Γ (xinr , σinr)) τ)
      (Pinl : LocalStore Γ -> A)
      (Pinr : LocalStore Γ -> A)
      (Q : LocalStore Γ -> Lit τ -> A) :
      Γ ▻ (xinl, σinl) ⊢ ⦃ fun δ => Pinl (env_tail δ)
                               (* ∧ !!(eval e (env_tail δ) = inl (env_head δ)) *)
                          ⦄ alt_inl ⦃ fun δ => Q (env_tail δ) ⦄ ->
      Γ ▻ (xinr, σinr) ⊢ ⦃ fun δ => Pinr (env_tail δ)
                               (* ∧ !!(eval e (env_tail δ) = inr (env_head δ)) *)
                          ⦄ alt_inr ⦃ fun δ => Q (env_tail δ) ⦄ ->
      Γ ⊢ ⦃ fun δ => (∀ x, !!(eval e δ = inl x) --> Pinl δ)
                ∧ (∀ x, !!(eval e δ = inr x) --> Pinr δ)
           ⦄ stm_match_sum e xinl alt_inl xinr alt_inr ⦃ Q ⦄
    | rule_stm_read_register {σ : Ty} (r : 𝑹𝑬𝑮 σ)
      (P : LocalStore Γ -> A) (Q : LocalStore Γ -> Lit σ -> A)
      (v : Lit σ) :
      Γ ⊢ ⦃ fun δ => P δ ✱ r ↦ v ⦄ stm_read_register r ⦃ fun δ w => Q δ w ✱ !!(w = v) ⦄
    | rule_stm_write_reg {σ : Ty} (r : 𝑹𝑬𝑮 σ)
      (P : LocalStore Γ -> A) (Q : LocalStore Γ -> Lit σ -> A)
      (v : Lit σ) :
      Γ ⊢ ⦃ fun δ => P δ ⦄ stm_write_register r (exp_lit Γ σ v) ⦃ fun δ w => Q δ w ✱ r ↦ v ⦄
    (* | rule_stm_match_pair {σ1 σ2 τ : Ty} (e : Exp Γ (ty_prod σ1 σ2)) *)
    (*   (xl xr : 𝑿) (rhs : Stm (ctx_snoc (ctx_snoc Γ (xl , σ1)) (xr , σ2)) τ) *)
    (*   (P : LocalStore Γ -> A) *)
    (*   (Q : LocalStore Γ -> Lit τ -> A) : *)
    (*   Γ ▻ (xl, σ1) ▻ (xr, σ2) ⊢ ⦃ P ⦄ rhs ⦃ Q ⦄ -> *)
    (*   Γ ⊢ ⦃ fun δ => P ⦄ stm_match_pair e xl xr rhs ⦃ Q ⦄ *)
    where "Γ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" := (Triple Γ P s Q).

  End HoareTriples.

End ProgramLogic.

(* (x : 𝑿) (τ : Ty) (s : Stm Γ τ) {τ : Ty} (k : Stm (ctx_snoc Γ (x , τ)) τ) : Stm Γ τ *)
(*       | rule_stm_exp *)
(*         TT (stm_exp ) FF. *)
(*       (γ : RegStore) (μ : Memory) (δ : LocalStore Γ) (τ : Ty) (e : Exp Γ τ) : *)
(*       ⟨ γ , μ , δ , (stm_exp e) ⟩ ---> ⟨ γ , μ , δ , stm_lit τ (eval e δ) ⟩ *)
