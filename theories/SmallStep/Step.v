(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel, Georgy Lukyanov                         *)
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

From Coq Require Import
     Program.Tactics
     Strings.String
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations
     Program
     Tactics.

Set Implicit Arguments.

Module Type SmallStepOn (Import B : Base) (Import P : Program B).

  Import ctx.notations.
  Import env.notations.
  Import SigTNotations.

  Inductive Step {Γ : PCtx} {τ : Ty} (γ : RegStore) (μ : Memory) (δ : CStore Γ) :
    forall (γ2 : RegStore) (μ2 : Memory) (δ2 : CStore Γ) (s1 s2 : Stm Γ τ), Prop :=

  | step_stm_exp
      (e : Exp Γ τ) :
      ⟨ γ , μ , δ , (stm_exp e) ⟩ ---> ⟨ γ , μ , δ , stm_val τ (eval e δ) ⟩

  | step_stm_let
      (x : PVar) (σ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ) :
      ⟨ γ , μ , δ , stm_let x σ s k ⟩ --->
      ⟨ γ, μ , δ , stm_bind s (fun v => stm_block (env.snoc env.nil (x∷σ) v) k) ⟩

  | step_stm_block_value
      (Δ : PCtx) (δΔ : CStore Δ) (v : Val τ) :
      ⟨ γ , μ , δ , stm_block δΔ (stm_val τ v) ⟩ ---> ⟨ γ , μ , δ , stm_val τ v ⟩
  | step_stm_block_fail
      (Δ : PCtx) (δΔ : CStore Δ) (s : string) :
      ⟨ γ , μ , δ , stm_block δΔ (stm_fail τ s) ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩
  | step_stm_block_step
      (Δ : PCtx) (δΔ δΔ' : CStore Δ) (k k' : Stm (Γ ▻▻ Δ) τ)
      (γ' : RegStore) (μ' : Memory) (δ' : CStore Γ) :
      ⟨ γ , μ , δ ►► δΔ , k ⟩ ---> ⟨ γ', μ' , δ' ►► δΔ' , k' ⟩ ->
      ⟨ γ , μ , δ , stm_block δΔ k ⟩ ---> ⟨ γ' , μ' , δ' , stm_block δΔ' k' ⟩

  | step_stm_seq
      (σ : Ty) (s : Stm Γ σ) (k : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_seq s k ⟩ ---> ⟨ γ , μ , δ , stm_bind s (fun _ => k) ⟩

  | step_stm_call
      {Δ} {f : 𝑭 Δ τ} (es : NamedEnv (Exp Γ) Δ) :
      ⟨ γ , μ , δ , stm_call f es ⟩ --->
      ⟨ γ , μ , δ , stm_call_frame (evals es δ) (FunDef f) ⟩
  | step_stm_call_frame_step
      (Δ : PCtx) {δΔ δΔ' : CStore Δ} (s s' : Stm Δ τ)
      (γ' : RegStore) (μ' : Memory) :
      ⟨ γ , μ , δΔ , s ⟩ ---> ⟨ γ' , μ' , δΔ' , s' ⟩ ->
      ⟨ γ , μ , δ , stm_call_frame δΔ s ⟩ ---> ⟨ γ' , μ' , δ , stm_call_frame δΔ' s' ⟩
  | step_stm_call_frame_value
      (Δ : PCtx) {δΔ : CStore Δ} (v : Val τ) :
      ⟨ γ , μ , δ , stm_call_frame δΔ (stm_val τ v) ⟩ ---> ⟨ γ , μ , δ , stm_val τ v ⟩
  | step_stm_call_frame_fail
      (Δ : PCtx) {δΔ : CStore Δ} (s : string) :
      ⟨ γ , μ , δ , stm_call_frame δΔ (stm_fail τ s) ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩
  | step_stm_foreign
      {Δ} {f : 𝑭𝑿 Δ τ} (es : NamedEnv (Exp Γ) Δ) (res : string + Val τ)
      (γ' : RegStore) (μ' : Memory) :
      ForeignCall f (evals es δ) res γ γ' μ μ' ->
      ⟨ γ  , μ  , δ , stm_foreign f es ⟩ --->
      ⟨ γ' , μ' , δ , match res with
                      | inl msg => stm_fail τ msg
                      | inr v__σ  => stm_val τ v__σ
                      end ⟩
  | step_stm_lemmak
      {Δ} {l : 𝑳 Δ} (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_lemmak l es k ⟩ --->
      ⟨ γ , μ , δ , k ⟩

  | step_stm_assign_value
      (x : PVar) {xInΓ : x∷τ ∈ Γ} (v : Val τ) :
      ⟨ γ , μ , δ , stm_assign x (stm_val τ v) ⟩ ---> ⟨ γ , μ , δ ⟪ x ↦ v ⟫ , stm_val τ v ⟩
  | step_stm_assign_fail
      (x : PVar) {xInΓ : x∷τ ∈ Γ} (s : string) :
      ⟨ γ , μ , δ , stm_assign x (stm_fail τ s) ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩
  | step_stm_assign_step
      (x : PVar) {xInΓ : x∷τ ∈ Γ} (s s' : Stm Γ τ)
      (γ' : RegStore) (μ' : Memory) (δ' : CStore Γ) :
      ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ' , μ' , δ' , s' ⟩ ->
      ⟨ γ , μ , δ , stm_assign x s ⟩ ---> ⟨ γ' , μ' , δ' , stm_assign x s' ⟩

  | step_stm_assertk
      (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_assertk e1 e2 k ⟩ --->
      ⟨ γ , μ , δ , if eval e1 δ then k else stm_fail τ (eval e2 δ) ⟩

  | step_stm_read_register
      (r : 𝑹𝑬𝑮 τ) :
      ⟨ γ, μ , δ, stm_read_register r ⟩ ---> ⟨ γ, μ , δ, stm_val τ (read_register γ r) ⟩
  | step_stm_write_register
      (r : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) :
      let v := eval e δ in
      ⟨ γ , μ , δ, stm_write_register r e ⟩ ---> ⟨ write_register γ r v , μ , δ , stm_val τ v ⟩

  | step_stm_bind_step
      (σ : Ty) (s s' : Stm Γ σ) (k : Val σ -> Stm Γ τ)
      (γ' : RegStore) (μ' : Memory) (δ' : CStore Γ) :
      ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ', μ' , δ' , s' ⟩ ->
      ⟨ γ , μ , δ , stm_bind s k ⟩ ---> ⟨ γ', μ' , δ' , stm_bind s' k ⟩
  | step_stm_bind_value
      (σ : Ty) (v : Val σ) (k : Val σ -> Stm Γ τ) :
      ⟨ γ , μ , δ , stm_bind (stm_val σ v) k ⟩ ---> ⟨ γ , μ , δ , k v ⟩
  | step_stm_bind_fail
      (σ : Ty) (s : string) (k : Val σ -> Stm Γ τ) :
      ⟨ γ , μ , δ , stm_bind (stm_fail σ s) k ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩

  | step_debugk
      (k : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_debugk k ⟩ ---> ⟨ γ , μ , δ , k ⟩

  | step_newpattern_match
      {σ} (s : Stm Γ σ) (pat : Pattern σ)
      (rhs : forall (pc : PatternCase pat), Stm (Γ ▻▻ PatternCaseCtx pc) τ) :
      ⟨ γ , μ , δ , stm_pattern_match s pat rhs ⟩ --->
      ⟨ γ , μ , δ , stm_bind s (fun v => let (pc,δpc) := pattern_match_val pat v
                                         in stm_block δpc (rhs pc))
      ⟩

  where "⟨ γ1 , μ1 , δ1 , s1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , s2 ⟩" := (@Step _ _ γ1%env μ1%env δ1%env γ2%env μ2%env δ2%env s1%exp s2%exp).

  Inductive Steps {Γ : PCtx} {σ : Ty} (γ1 : RegStore) (μ1 : Memory) (δ1 : CStore Γ) (s1 : Stm Γ σ) : RegStore -> Memory -> CStore Γ -> Stm Γ σ -> Prop :=
  | step_refl : Steps γ1 μ1 δ1 s1 γ1 μ1 δ1 s1
  | step_trans {γ2 γ3 : RegStore} {μ2 μ3 : Memory} {δ2 δ3 : CStore Γ} {s2 s3 : Stm Γ σ} :
      Step γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 -> Steps γ2 μ2 δ2 s2 γ3 μ3 δ3 s3 -> Steps γ1 μ1 δ1 s1 γ3 μ3 δ3 s3.

  Module Import SmallStepNotations.
    Notation "⟨ γ1 , μ1 , δ1 , s1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , s2 ⟩" := (@Step _ _ γ1%env μ1%env δ1%env γ2%env μ2%env δ2%env s1%exp s2%exp).
    Notation "⟨ γ1 , μ1 , δ1 , s1 ⟩ --->* ⟨ γ2 , μ2 , δ2 , s2 ⟩" := (@Steps _ _ γ1 μ1 δ1 s1 γ2 μ2 δ2 s2).
  End SmallStepNotations.

  (* Tests if a statement is a final one, i.e. a finished computation. *)
  Ltac microsail_stm_is_final s :=
    lazymatch s with
    | stm_val _ _  => idtac
    | stm_fail _ _ => idtac
    end.

  (* Tests if a statement has a primitive step, i.e. it can be reduced
     by an axiom rule of the step relation instead of a congruence rule. *)
  Ltac microsail_stm_primitive_step s :=
    first
      [ lazymatch s with
        | stm_call_frame _ ?s' => microsail_stm_is_final s'
        | stm_block _ ?s'      => microsail_stm_is_final s'
        | stm_assign _ ?s'     => microsail_stm_is_final s'
        | stm_bind ?s' _       => microsail_stm_is_final s'
        end
      | lazymatch head s with
        | @stm_val              => idtac
        | @stm_exp              => idtac
        | @stm_seq              => idtac
        | @stm_let              => idtac
        | @stm_call             => idtac
        | @stm_foreign          => idtac
        | @stm_lemmak           => idtac
        | @stm_assertk          => idtac
        | @stm_fail             => idtac
        | @stm_pattern_match    => idtac
        | @stm_read_register    => idtac
        | @stm_write_register   => idtac
        | @stm_debugk           => idtac
        end
      ].

  (* This 'Lemma' simply exists for testing that the above predicate on
     statements is complete with respect to the step relation. *)
  Lemma microsail_stm_primitive_step__complete {Γ σ γ1 γ2 μ1 μ2 δ1 δ2} {s1 s2 : Stm Γ σ} :
    ⟨ γ1 , μ1 , δ1 , s1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , s2 ⟩ -> True.
    intro step. remember s1 as s1'.
    dependent elimination step;
      match goal with
      | [ H: ⟨ _,_,_,_ ⟩ ---> ⟨ _,_,_,_ ⟩ |- _ ] =>
        (* If there is a step hypothesis then this case represents a congruence
           rule, not an axiom rule. *)
        constructor
      | [ H: ?s1' = s1 |- _ ] =>
        (* Otherwise, it's an axiom rule and the microsail_stm_primitive_step
           tactic should recognize it. *)
        microsail_stm_primitive_step s1'; constructor
      end; fail.
    Abort.

  Definition Final {Γ σ} (s : Stm Γ σ) : Prop :=
    match s with
    | stm_val _ _   => True
    | stm_fail _ _ => True
    | _ => False
    end.

  Definition ResultOrFail {Γ σ} (s : Stm Γ σ) :
    forall (POST : Val σ -> Prop), Prop :=
    match s with
    | stm_val _ v => fun POST => POST v
    | stm_fail _ _ => fun _ => True
    | _ => fun _ => False
    end.

  Lemma result_or_fail_inversion {Γ σ} (s : Stm Γ σ) (POST : Val σ -> Prop) :
    ResultOrFail s POST -> (exists msg, s = stm_fail _ msg)
                        \/ (exists v, s = stm_val _ v /\ POST v).
  Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

  (* This predicate encodes that the statement s is a finished computation and
     that the result is not a failure. This is a computational version that is
     better suited for the goal and the inversion below is better suited for
     a hypothesis. *)
  Definition ResultNoFail {Γ σ} (s : Stm Γ σ) :
    forall (POST : Val σ -> Prop), Prop :=
    match s with
    | stm_val _ v => fun POST => POST v
    | _ => fun _ => False
    end.

  Lemma result_no_fail_inversion {Γ σ} (s : Stm Γ σ) (POST : Val σ -> Prop) :
    ResultNoFail s POST -> exists v, s = stm_val _ v /\ POST v.
  Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

End SmallStepOn.
