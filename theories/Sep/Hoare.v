(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov, Steven Keuchel     *)
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

Require Import Coq.Classes.Morphisms.

From Katamaran Require Import
     Environment
     Sep.Logic
     Sep.Spec
     Syntax.

Module ProgramLogic
  (Import termkit : TermKit)
  (Import progkit : ProgramKit termkit)
  (Import assertkit : AssertionKit termkit progkit)
  (Import contractkit : SymbolicContractKit termkit progkit assertkit).

  Import ctx.notations.
  Import env.notations.

  Open Scope logic.
  Import LogicNotations.

  Section Triples.

    Context {L : Type}.
    Context {LL : IHeaplet L}.

    (* Hoare triples for SepContract *)

    Inductive CTriple {Δ σ} (δΔ : CStore Δ) (pre : L) (post : Lit σ -> L) :
      SepContract Δ σ -> Prop :=
    | rule_sep_contract
        (result : 𝑺)
        (Σ  : LCtx) (θΔ : SStore Δ Σ) (ι : SymInstance Σ)
        (req : Assertion Σ) (ens : Assertion (Σ ▻ result∷σ))
        (frame : L) :
        δΔ = inst θΔ ι ->
        pre ⊢ frame ✱ interpret_assertion req ι ->
        (forall v, frame ✱ interpret_assertion ens (env.snoc ι (result∷σ) v) ⊢ post v) ->
        CTriple δΔ pre post (MkSepContract _ _ _ θΔ req result ens).

    Inductive LTriple {Δ} (δΔ : CStore Δ) (pre post : L) :
      Lemma Δ -> Prop :=
    | rule_ltriple
        (Σ  : LCtx) (θΔ : SStore Δ Σ) (ι : SymInstance Σ)
        (req ens : Assertion Σ)
        (frame : L) :
        δΔ = inst θΔ ι ->
        pre ⊢ frame ✱ interpret_assertion req ι ->
        (frame ✱ interpret_assertion ens ι ⊢ post) ->
        LTriple δΔ pre post (MkLemma _ _ θΔ req ens).

    Inductive Triple {Γ : PCtx} (δ : CStore Γ) {τ : Ty} :
      forall (pre : L) (s : Stm Γ τ) (post :  Lit τ -> CStore Γ -> L), Prop :=
    | rule_consequence
        {s : Stm Γ τ} {P P' : L} {Q Q' : Lit τ -> CStore Γ -> L}
        (Hleft : P ⊢ P') (Hright : forall v δ', Q' v δ' ⊢ Q v δ') :
        ⦃ P' ⦄ s ; δ ⦃ Q' ⦄ ->
        ⦃ P ⦄ s ; δ ⦃ Q ⦄
    | rule_frame
        (s : Stm Γ τ) (R P : L) (Q : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ s ; δ ⦃ Q ⦄ ->
        ⦃ R ✱ P ⦄ s ; δ ⦃ fun v δ' => R ✱ Q v δ' ⦄
    | rule_pull
        (s : Stm Γ τ) (P : L) (Q : Prop) (R : Lit τ -> CStore Γ -> L) :
        (Q -> ⦃ P ⦄ s ; δ ⦃ R ⦄) ->
        ⦃ P ∧ !!Q ⦄ s ; δ ⦃ R ⦄
    | rule_exist
        (s : Stm Γ τ) {A : Type} {P : A -> L} {Q : Lit τ -> CStore Γ -> L} :
        (forall x, ⦃ P x ⦄ s ; δ ⦃ Q ⦄) ->
        ⦃ ∃ x, P x ⦄ s ; δ ⦃ Q ⦄
    | rule_stm_lit
        {l : Lit τ} {P : L} {Q : Lit τ -> CStore Γ -> L} :
        P ⊢ Q l δ ->
        ⦃ P ⦄ stm_lit τ l ; δ ⦃ Q ⦄
    | rule_stm_exp
        {e : Exp Γ τ} {P : L} {Q : Lit τ -> CStore Γ -> L} :
        P ⊢ Q (eval e δ) δ ->
        ⦃ P ⦄ stm_exp e ; δ ⦃ Q ⦄
    | rule_stm_let
        (x : 𝑿) (σ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ)
        (P : L) (Q : Lit σ -> CStore Γ -> L)
        (R : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ s ; δ ⦃ Q ⦄ ->
        (forall (v : Lit σ) (δ' : CStore Γ),
            ⦃ Q v δ' ⦄ k ; env.snoc δ' (x∷σ) v ⦃ fun v δ'' => R v (env.tail δ'') ⦄ ) ->
        ⦃ P ⦄ let: x := s in k ; δ ⦃ R ⦄
    | rule_stm_block
        (Δ : PCtx) (δΔ : CStore Δ)
        (k : Stm (Γ ▻▻ Δ) τ)
        (P : L) (R : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ k ; δ ►► δΔ ⦃ fun v δ'' => R v (env.drop Δ δ'') ⦄ ->
        ⦃ P ⦄ stm_block δΔ k ; δ ⦃ R ⦄
    | rule_stm_if
        {e : Exp Γ ty_bool} {s1 s2 : Stm Γ τ}
        {P : L} {Q : Lit τ -> CStore Γ -> L} :
        ⦃ P ∧ !!(eval e δ = true) ⦄ s1 ; δ ⦃ Q ⦄ ->
        ⦃ P ∧ !!(eval e δ = false) ⦄ s2 ; δ ⦃ Q ⦄ ->
        ⦃ P ⦄ stm_if e s1 s2 ; δ ⦃ Q ⦄
    | rule_stm_seq
        (σ : Ty) (s1 : Stm Γ σ) (s2 : Stm Γ τ)
        (P : L) (Q : CStore Γ -> L) (R : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ s1 ; δ ⦃ fun _ => Q ⦄ ->
        (forall δ', ⦃ Q δ' ⦄ s2 ; δ' ⦃ R ⦄) ->
        ⦃ P ⦄ s1 ;; s2 ; δ ⦃ R ⦄
    | rule_stm_assert
        (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) (k : Stm Γ τ)
        (P : L) (Q : Lit τ -> CStore Γ -> L) :
        ⦃ P ∧ !! (eval e1 δ = true) ⦄ k ; δ ⦃ Q ⦄ ->
        ⦃ P ⦄ stm_assertk e1 e2 k ; δ ⦃ Q ⦄
    | rule_stm_fail
        (s : Lit ty_string) (Q : Lit τ -> CStore Γ -> L) :
        ⦃ ⊤ ⦄ stm_fail τ s ; δ ⦃ Q ⦄
    | rule_stm_match_list
        {σ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
        (xh xt : 𝑿) (alt_cons : Stm (Γ ▻ xh∷σ ▻ xt∷ty_list σ) τ)
        (P : L) (Q : Lit τ -> CStore Γ -> L) :
        ⦃ P ∧ !! (eval e δ = nil) ⦄ alt_nil ; δ ⦃ Q ⦄ ->
        (forall (v : Lit σ) (vs : Lit (ty_list σ)),
           ⦃ P ∧ !! (eval e δ = cons v vs) ⦄
             alt_cons ; env.snoc (env.snoc δ (xh∷σ) v) (xt∷ty_list σ) vs
           ⦃ fun v' δ' => Q v' (env.tail (env.tail δ')) ⦄) ->
        ⦃ P ⦄ stm_match_list e alt_nil xh xt alt_cons ; δ ⦃ Q ⦄
    | rule_stm_match_sum
        {xl xr : 𝑿} {σl σr : Ty} {e : Exp Γ (ty_sum σl σr)}
        {alt_inl : Stm (Γ ▻ xl∷σl) τ}
        {alt_inr : Stm (Γ ▻ xr∷σr) τ}
        {P : L} {Q : Lit τ -> CStore Γ -> L} :
        (forall (v : Lit σl), ⦃ P ∧ !! (eval e δ = inl v) ⦄ alt_inl ; env.snoc δ (xl∷σl) v ⦃ fun v' δ' => Q v' (env.tail δ') ⦄) ->
        (forall (v : Lit σr), ⦃ P ∧ !! (eval e δ = inr v) ⦄ alt_inr ; env.snoc δ (xr∷σr) v ⦃ fun v' δ' => Q v' (env.tail δ') ⦄) ->
        ⦃ P ⦄ stm_match_sum e xl alt_inl xr alt_inr ; δ ⦃ Q ⦄
    | rule_stm_match_prod
        {xl xr : 𝑿} {σl σr : Ty} {e : Exp Γ (ty_prod σl σr)}
        {rhs : Stm (Γ ▻ xl∷σl ▻ xr∷σr) τ}
        {P : L} {Q : Lit τ -> CStore Γ -> L} :
        (forall (vl : Lit σl) (vr : Lit σr),
           ⦃ P ∧ !! (eval e δ = (vl,vr)) ⦄
             rhs ; env.snoc (env.snoc δ (xl∷σl) vl) (xr∷σr) vr
           ⦃ fun v δ' => Q v (env.tail (env.tail δ')) ⦄) ->
        ⦃ P ⦄ stm_match_prod e xl xr rhs ; δ ⦃ Q ⦄
    | rule_stm_match_enum
        {E : 𝑬} (e : Exp Γ (ty_enum E))
        (alts : forall (K : 𝑬𝑲 E), Stm Γ τ)
        (P : L) (Q : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ alts (eval e δ) ; δ ⦃ Q ⦄ ->
        ⦃ P ⦄ stm_match_enum E e alts ; δ ⦃ Q ⦄
    | rule_stm_match_tuple
        {σs : Ctx Ty} {Δ : PCtx} (e : Exp Γ (ty_tuple σs))
        (p : TuplePat σs Δ) (rhs : Stm (Γ ▻▻ Δ) τ)
        (P : L) (Q : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ rhs ; env.cat δ (tuple_pattern_match_lit p (eval e δ)) ⦃ fun v δ' => Q v (env.drop Δ δ') ⦄ ->
        ⦃ P ⦄ stm_match_tuple e p rhs ; δ ⦃ Q ⦄
    | rule_stm_match_union
        {U : 𝑼} (e : Exp Γ (ty_union U))
        (alt__Δ : forall (K : 𝑼𝑲 U), PCtx)
        (alt__p : forall (K : 𝑼𝑲 U), Pattern (alt__Δ K) (𝑼𝑲_Ty K))
        (alt__r : forall (K : 𝑼𝑲 U), Stm (Γ ▻▻ alt__Δ K) τ)
        (P : L) (Q : Lit τ -> CStore Γ -> L) :
        (forall (K : 𝑼𝑲 U) (v : Lit (𝑼𝑲_Ty K)),
           ⦃ P ∧ !! (eval e δ = 𝑼_fold (existT K v)) ⦄
             alt__r K ; env.cat δ (pattern_match_lit (alt__p K) v)
           ⦃ fun v δ' => Q v (env.drop (alt__Δ K) δ') ⦄) ->
        ⦃ P ⦄ stm_match_union U e alt__p alt__r ; δ ⦃ Q ⦄
    | rule_stm_match_record
        {R : 𝑹} {Δ : PCtx} (e : Exp Γ (ty_record R))
        (p : RecordPat (𝑹𝑭_Ty R) Δ) (rhs : Stm (Γ ▻▻ Δ) τ)
        (P : L) (Q : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ rhs ; env.cat δ (record_pattern_match_lit p (eval e δ)) ⦃ fun v δ' => Q v (env.drop Δ δ') ⦄ ->
        ⦃ P ⦄ stm_match_record R e p rhs ; δ ⦃ Q ⦄
    | rule_stm_read_register
        (r : 𝑹𝑬𝑮 τ) (v : Lit τ) :
        ⦃ lptsreg r v ⦄
          stm_read_register r ; δ
        ⦃ fun v' δ' => !!(δ' = δ) ∧ !!(v' = v) ∧ lptsreg r v ⦄
    | rule_stm_write_register
        (r : 𝑹𝑬𝑮 τ) (w : Exp Γ τ) (v : Lit τ)
        (Q : Lit τ -> CStore Γ -> L) :
        ⦃ lptsreg r v ⦄
          stm_write_register r w ; δ
        ⦃ fun v' δ' => !!(δ' = δ) ∧ !!(v' = eval w δ) ∧ lptsreg r v' ⦄
    | rule_stm_assign_backwards
        (x : 𝑿) (xIn : x∷τ ∈ Γ) (s : Stm Γ τ)
        (P : L) (R : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ s ; δ ⦃ fun v δ' => R v (δ' ⟪ x ↦ v ⟫)%env ⦄ ->
        ⦃ P ⦄ stm_assign x s ; δ ⦃ R ⦄
    | rule_stm_assign_forwards
        (x : 𝑿) (xIn : x∷τ ∈ Γ) (s : Stm Γ τ)
        (P : L) (R : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ s ; δ ⦃ R ⦄ ->
        ⦃ P ⦄
          stm_assign x s ; δ
        ⦃ fun v__new δ' => ∃ v__old, R v__new (δ' ⟪ x ↦ v__old ⟫)%env ∧ !!(env.lookup δ' xIn = v__new) ⦄
    | rule_stm_call_forwards
        {Δ} {f : 𝑭 Δ τ} {es : NamedEnv (Exp Γ) Δ} {c : SepContract Δ τ}
        {P : L} {Q : Lit τ -> L} :
        CEnv f = Some c ->
        CTriple (evals es δ) P Q c ->
        ⦃ P ⦄ stm_call f es ; δ ⦃ fun v δ' => Q v ∧ !!(δ = δ') ⦄
    | rule_stm_call_inline
        {Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ)
        (P : L) (Q : Lit τ -> L) :
        ⦃ P ⦄ Pi f ; evals es δ ⦃ fun v _ => Q v ⦄ ->
        ⦃ P ⦄ stm_call f es ; δ ⦃ fun v δ' => Q v ∧ !!(δ = δ') ⦄
    | rule_stm_call_frame
        (Δ : PCtx) (δΔ : CStore Δ) (s : Stm Δ τ)
        (P : L) (Q : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ s ; δΔ ⦃ fun v _ => Q v δ ⦄ ->
        ⦃ P ⦄ stm_call_frame δΔ s ; δ ⦃ Q ⦄
    | rule_stm_foreign_backwards
        {Δ} {f : 𝑭𝑿 Δ τ} (es : NamedEnv (Exp Γ) Δ)
        (P : L) (Q : Lit τ -> CStore Γ -> L) :
        CTriple (evals es δ) P (fun v => Q v δ) (CEnvEx f) ->
        ⦃ P ⦄ stm_foreign f es ; δ ⦃ Q ⦄
    | rule_stm_lemmak
        {Δ} {l : 𝑳 Δ} (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ)
        (P Q : L) (R : Lit τ -> CStore Γ -> L) :
        LTriple (evals es δ) P Q (LEnv l) ->
        ⦃ Q ⦄ k ; δ ⦃ R ⦄ ->
        ⦃ P ⦄ stm_lemmak l es k ; δ ⦃ R ⦄
    | rule_stm_bind
        {σ : Ty} (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ)
        (P : L) (Q : Lit σ -> CStore Γ -> L)
        (R : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ s ; δ ⦃ Q ⦄ ->
        (forall (v__σ : Lit σ) (δ' : CStore Γ),
           ⦃ Q v__σ δ' ⦄ k v__σ ; δ' ⦃ R ⦄) ->
        ⦃ P ⦄ stm_bind s k ; δ ⦃ R ⦄
    | rule_stm_debugk
        (k : Stm Γ τ)
        (P : L) (Q : Lit τ -> CStore Γ -> L) :
        ⦃ P ⦄ k ; δ ⦃ Q ⦄ ->
        ⦃ P ⦄ stm_debugk k ; δ ⦃ Q ⦄
    where "⦃ P ⦄ s ; δ ⦃ Q ⦄" := (@Triple _ δ _ P s Q).

    Notation "⦃ P ⦄ s ; δ ⦃ Q ⦄" := (@Triple _ δ _ P s Q).

    Context {SLL : ISepLogicLaws L}.
    Lemma rule_consequence_left {Γ σ} {δ : CStore Γ} {s : Stm Γ σ}
      (P1 : L) {P2 : L} {Q : Lit σ -> CStore Γ -> L} :
      ⦃ P1 ⦄ s ; δ ⦃ Q ⦄ -> P2 ⊢ P1 -> ⦃ P2 ⦄ s ; δ ⦃ Q ⦄.
    Proof.
      intros H hyp. refine (rule_consequence δ hyp _ H).
      intros; apply entails_refl.
    Qed.

    Lemma rule_consequence_right {Γ σ} {δ : CStore Γ} {s : Stm Γ σ}
      {P : L} Q {Q'} :
      ⦃ P ⦄ s ; δ ⦃ Q ⦄ -> (forall v δ, Q v δ ⊢ Q' v δ) -> ⦃ P ⦄ s ; δ ⦃ Q' ⦄.
    Proof.
      intros H hyp. exact (rule_consequence δ (entails_refl P) hyp H).
    Qed.

    Lemma rule_exist' {Γ : PCtx} {δ : CStore Γ} {A : Type} {σ : Ty} (s : Stm Γ σ)
      {P : A -> L} (Q :  A -> Lit σ -> CStore Γ -> L) :
      (forall x, ⦃ P x ⦄ s ; δ ⦃ Q x ⦄) ->
      ⦃ ∃ x, P x ⦄ s ; δ ⦃ fun v δ' => ∃ x, Q x v δ' ⦄.
    Proof.
      intros hyp.
      apply rule_exist.
      intros x.
      apply (rule_consequence_right (Q x) (hyp x)).
      intros.
      apply lex_right with x.
      apply entails_refl.
    Qed.

    Lemma rule_disj {Γ σ} {δ : CStore Γ} {s : Stm Γ σ}
      {P Q : L} {R : Lit σ -> CStore Γ -> L} :
      ⦃ P ⦄ s ; δ ⦃ R ⦄ -> ⦃ Q ⦄ s ; δ ⦃ R ⦄ ->
      ⦃ P ∨ Q ⦄ s ; δ ⦃ R ⦄.
    Proof.
      intros H1 H2.
      apply (rule_consequence_left (∃ b : bool, if b then P else Q)).
      - apply rule_exist; intros []; assumption.
      - apply lor_left.
        + apply lex_right with true, entails_refl.
        + apply lex_right with false, entails_refl.
    Qed.

    Lemma rule_disj' {Γ σ} {δ : CStore Γ} {s : Stm Γ σ}
      {P1 P2 : L} {Q1 Q2 : Lit σ -> CStore Γ -> L} :
      ⦃ P1 ⦄ s ; δ ⦃ Q1 ⦄ -> ⦃ P2 ⦄ s ; δ ⦃ Q2 ⦄ ->
      ⦃ P1 ∨ P2 ⦄ s ; δ ⦃ fun v δ' => Q1 v δ' ∨ Q2 v δ' ⦄.
    Proof.
      intros H1 H2.
      apply rule_disj.
      - apply (rule_consequence_right _ H1).
        intros. apply lor_right1, entails_refl.
      - apply (rule_consequence_right _ H2).
        intros. apply lor_right2, entails_refl.
    Qed.

    Lemma rule_false {Γ σ} {δ : CStore Γ} {s : Stm Γ σ}
      {Q : Lit σ -> CStore Γ -> L} :
      ⦃ lfalse ⦄ s ; δ ⦃ Q ⦄.
    Proof.
      apply (rule_consequence_left (∃ (x : Empty_set), ltrue)).
      - apply rule_exist; intros [].
      - apply lfalse_left.
    Qed.

    (* Lemma rule_forall' {Γ σ} {δ : CStore Γ} {s : Stm Γ σ} *)
    (*   {A : Type} {P : A -> L} {Q : A -> Lit σ -> CStore Γ -> L} *)
    (*   (hyp : forall x, δ ⊢ ⦃ P x ⦄ s ⦃ Q x ⦄) (x : A) : *)
    (*   δ ⊢ ⦃ ∀ x, P x ⦄ s ⦃ fun v δ' => ∀ x, Q x v δ' ⦄. *)
    (* Proof. *)
    (*   apply rule_forall; [ intros | assumption ]. *)
    (*   apply (rule_consequence_left (P x0 ∧ P x)). *)
    (*   - apply (rule_consequence_left (P x0)). *)
    (*     + apply hyp. *)
    (*     + apply land_left1. *)
    (*       apply entails_refl. *)
    (*   - apply land_right. *)
    (*     + apply lall_left with x0. *)
    (*       apply entails_refl. *)
    (*     + apply lall_left with x. *)
    (*       apply entails_refl. *)
    (* Qed. *)

    (* Lemma rule_conj {Γ σ} {δ : CStore Γ} {s : Stm Γ σ} *)
    (*   {P : L} {Q1 Q2 : Lit σ -> CStore Γ -> L} : *)
    (*   δ ⊢ ⦃ P ⦄ s ⦃ Q1 ⦄ -> δ ⊢ ⦃ P ⦄ s ⦃ Q2 ⦄ -> *)
    (*   δ ⊢ ⦃ P ⦄ s ⦃ fun v δ' => Q1 v δ' ∧ Q2 v δ' ⦄. *)
    (* Proof. *)
    (*   intros H1 H2. *)
    (*   apply (rule_consequence_right (fun v δ' => ∀ b : bool, if b then Q1 v δ' else Q2 v δ')). *)
    (*   - apply rule_forall. *)
    (*     intros []; auto. *)
    (*     apply true. *)
    (*   - intros. *)
    (*     apply land_right. *)
    (*     + apply lall_left with true, entails_refl. *)
    (*     + apply lall_left with false, entails_refl. *)
    (* Qed. *)

    (* Lemma rule_conj' {Γ σ} {δ : CStore Γ} {s : Stm Γ σ} *)
    (*   {P1 P2 : L} {Q1 Q2 : Lit σ -> CStore Γ -> L} : *)
    (*   δ ⊢ ⦃ P1 ⦄ s ⦃ Q1 ⦄ -> δ ⊢ ⦃ P2 ⦄ s ⦃ Q2 ⦄ -> *)
    (*   δ ⊢ ⦃ P1 ∧ P2 ⦄ s ⦃ fun v δ' => Q1 v δ' ∧ Q2 v δ' ⦄. *)
    (* Proof. *)
    (*   intros H1 H2. *)
    (*   apply rule_conj. *)
    (*   - apply (rule_consequence_left _ H1), land_left1, entails_refl. *)
    (*   - apply (rule_consequence_left _ H2), land_left2, entails_refl. *)
    (* Qed. *)

    Definition WP {Γ τ} (s : Stm Γ τ) (POST :  Lit τ -> CStore Γ -> L) : CStore Γ -> L :=
      fun δ => ∃ (P : L), P ∧ !! (⦃ P ⦄ s ; δ ⦃ POST ⦄).

    Lemma rule_wp {Γ σ} (s : Stm Γ σ) (POST :  Lit σ -> CStore Γ -> L) (δ : CStore Γ) :
      ⦃ WP s POST δ ⦄ s ; δ ⦃ POST ⦄.
    Proof. apply rule_exist; intros P; now apply rule_pull. Qed.

    Global Instance proper_triple {Γ δ τ} :
      Proper (bientails ==> eq ==> pointwise_relation _ (pointwise_relation _ bientails) ==> iff) (@Triple Γ δ τ).
    Proof.
      intros P Q pq s s' eq__s R S rs; subst s'.
      split; intro H; (eapply rule_consequence; [apply pq | apply rs | exact H ]).
    Qed.

    Lemma rule_stm_read_register_backwards {Γ δ σ r v} (Q : Lit σ -> CStore Γ -> L) :
      ⦃ lptsreg r v ✱ (lptsreg r v -✱ Q v δ) ⦄
        stm_read_register r ; δ
      ⦃ Q ⦄.
    Proof.
      rewrite sepcon_comm.
      eapply rule_consequence_right.
      apply rule_frame, rule_stm_read_register.
      cbn; intros.
      rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      apply limpl_and_adjoint.
      rewrite lprop_land_distr.
      apply lprop_left; intros []; subst.
      apply limpl_and_adjoint.
      apply land_left2.
      apply wand_sepcon_adjoint.
      rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      apply entails_refl.
    Qed.

    Lemma rule_stm_write_register_backwards {Γ δ σ r v} {e : Exp Γ σ}
      (Q : Lit σ -> CStore Γ -> L) :
      ⦃ lptsreg r v ✱ (lptsreg r (eval e δ) -✱ Q (eval e δ) δ) ⦄
        stm_write_register r e ; δ
      ⦃ Q ⦄.
    Proof.
      rewrite sepcon_comm.
      eapply rule_consequence_right.
      apply rule_frame, rule_stm_write_register.
      apply Q.
      cbn; intros.
      rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      apply limpl_and_adjoint.
      rewrite lprop_land_distr.
      apply lprop_left; intros []; subst.
      apply limpl_and_adjoint.
      apply land_left2.
      apply wand_sepcon_adjoint.
      rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      apply entails_refl.
    Qed.

    Lemma rule_stm_call_backwards {Γ δ Δ σ} {f : 𝑭 Δ σ} {es : NamedEnv (Exp Γ) Δ}
      (P : L) (Q : Lit σ -> CStore Γ -> L) (c : SepContract Δ σ) :
      CEnv f = Some c ->
      CTriple (evals es δ) P (fun v => Q v δ) c ->
      ⦃ P ⦄ stm_call f es ; δ ⦃ Q ⦄.
    Proof.
      intros Heq HYP.
      eapply rule_consequence_right.
      apply rule_stm_call_forwards with c.
      assumption.
      apply HYP.
      cbn; intros v δ1.
      rewrite land_comm.
      apply limpl_and_adjoint.
      apply lprop_left. intro. subst δ1.
      apply limpl_and_adjoint.
      apply land_left2, entails_refl.
    Qed.

    Definition ValidContract {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) : Prop :=
      forall (ι : SymInstance (sep_contract_logic_variables c)),
        ⦃ interpret_contract_precondition c ι ⦄
          body ; inst_contract_localstore c ι
        ⦃ fun v _ => interpret_contract_postcondition c ι v ⦄.

    Definition ValidContractEnv (cenv : SepContractEnv) : Prop :=
      forall (Δ : PCtx) (τ : Ty) (f : 𝑭 Δ τ) (c : SepContract Δ τ),
        cenv Δ τ f = Some c ->
        ValidContract c (Pi f).

  End Triples.

  Notation "⦃ P ⦄ s ; δ ⦃ Q ⦄" := (@Triple _ _ _ δ _ P s Q).

End ProgramLogic.
