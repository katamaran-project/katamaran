Require Import Coq.Program.Tactics.
Require Import FunctionalExtensionality.

Require Import MicroSail.Syntax.
Require Import MicroSail.Environment.
Require Import MicroSail.SmallStep.Inversion.
Require Import MicroSail.Sep.Logic.
Require Import MicroSail.Sep.Spec.
Require Import MicroSail.Sep.Hoare.

Module HoareSound
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import assertkit : AssertionKit typekit termkit progkit)
       (Import heapkit : HeapKit typekit termkit progkit assertkit).
  Module SSI := Inversion typekit termkit progkit.
  Import SSI.
  Import SS.

  Module PL := ProgramLogic typekit termkit progkit assertkit heapkit.
  Import PL.

Section Soundness.
  Context {A : Type} {Logic : Heaplet A} (Valid : A -> Prop).

  Open Scope logic.

  (* The soundness proof needs to be carried out in terms of the logic interface *)


  Definition sound_forward
    (Γ : Ctx (𝑿 * Ty))
    (σ : Ty)
    (stm : Stm Γ σ)
    (pre : LocalStore Γ -> A)
    (post : LocalStore Γ -> Lit σ -> A)
    (* (triple : Γ ⊢ ⦃ pre ⦄ stm ⦃ post ⦄) : *)
    (triple : Triple Γ pre stm post) :
    Valid (∀ γ1 μ1 δ1, ∃ stm' γ2 μ2 δ2,
                !!(⟨ γ1 , μ1 , δ1 , stm ⟩ ---> ⟨ γ2 , μ2 , δ2 , stm' ⟩)).

    (* Proof. *)
    (*   destruct triple. *)
    (*   - intros. *)
    (*     exists (stm_lit τ l). *)
    (*     admit. *)
    (*   - intros. *)
    (*     exists (stm_lit τ (eval e δ1)). *)
    (*     exists γ1. exists μ1. exists δ1. *)
    (*     constructor. *)
    (* Abort. *)

  (* Theorem sound_backward *)
  (*   (Γ : Ctx (𝑿 * Ty)) *)
  (*   (σ : Ty) *)
  (*   (stm1 stm2 : Stm Γ σ) *)
  (*   (γ1 γ2 : RegStore) (μ1 μ2 : Memory) (δ1 δ2 : LocalStore Γ) *)
  (*   (step : ⟨ γ1 , μ1 , δ1 , stm1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , stm2 ⟩) : *)
  (*   exists (pre : LocalStore Γ -> A) *)
  (*     (post : LocalStore Γ -> Lit σ -> A), *)
  (*     Triple Γ pre stm1 post. *)
  (*   (* (triple : Γ ⊢ ⦃ pre ⦄ stm ⦃ post ⦄) : *) *)
  (*   (triple : Triple Γ pre stm post) : *)
  (*   forall (γ1 : RegStore) (μ1 : Memory) (δ1 : LocalStore Γ), *)
  (*        exists (stm' : Stm Γ σ) (γ2 : RegStore) (μ2 : Memory) (δ2 : LocalStore Γ) , *)

  (*   Proof. *)
  (*     destruct triple. *)
  (*     - intros. *)
  (*       exists (stm_lit τ l). *)
  (*       admit. *)
  (*     - intros. *)
  (*       exists (stm_lit τ (eval e δ1)). *)
  (*       exists γ1. exists μ1. exists δ1. *)
  (*       constructor. *)
  (*   Abort. *)
