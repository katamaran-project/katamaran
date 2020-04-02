Require Import Coq.Program.Tactics.
Require Import FunctionalExtensionality.

Require Import MicroSail.Syntax.
Require Import MicroSail.Sep.Logic.

Module ProgramLogic

  (Import typekit : TypeKit)
  (Import termkit : TermKit typekit)
  (Import progKit : ProgramKit typekit termkit).

  Import CtxNotations.
  Import EnvNotations.

  Open Scope logic.
  Definition ctxprop := Ctx (𝑿 * Ty) -> Prop.

  Definition ptstoctx {Γ : Ctx (𝑿 * Ty)} {A : Set} (x : 𝑿) (v : A) : ctxprop :=
    fun _ => True.

  Program Instance ctxpop_NatDed : NatDed ctxprop.
  Admit Obligations.



  Reserved Notation "⦃ P ⦄ s ⦃ Q ⦄" (at level 75, no associativity).
  Inductive Triple
            (* {A : Set} {ND : NatDedAxioms A} {SL : SepLogAxioms A} *)
            {Γ : Ctx (𝑿 * Ty)} :
            forall {σ : Ty}
            (pre : ctxprop) (s : Stm Γ σ) (post : ctxprop), Prop :=
    | rule_stm_lit (σ : Ty) (l : Lit σ) : forall (P : ctxprop), ⦃ P ⦄ stm_lit σ l ⦃ P ⦄
    | rule_stm_exp (σ : Ty) (e : Exp Γ σ) : forall (P : ctxprop), ⦃ P ⦄ stm_exp e ⦃ P ⦄
    | rule_stm_let (x : 𝑿) (τ : Ty) (s : Stm Γ τ) {σ : Ty}
                   (k : Stm (ctx_snoc Γ (x , τ)) σ) :
        forall (P : ctxprop), ⦃ P ⦄ let: x := s in k ⦃ P ⦄
    where "⦃ P ⦄ s ⦃ Q ⦄" := (Triple P s Q).

(x : 𝑿) (τ : Ty) (s : Stm Γ τ) {σ : Ty} (k : Stm (ctx_snoc Γ (x , τ)) σ) : Stm Γ σ
      | rule_stm_exp
        TT (stm_exp ) FF.
      (γ : RegStore) (μ : Memory) (δ : LocalStore Γ) (σ : Ty) (e : Exp Γ σ) :
      ⟨ γ , μ , δ , (stm_exp e) ⟩ ---> ⟨ γ , μ , δ , stm_lit σ (eval e δ) ⟩
