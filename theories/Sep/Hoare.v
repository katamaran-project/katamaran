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

From Coq Require Import
  Classes.Morphisms.

From iris Require Import
  proofmode.tactics.

From Katamaran Require Import
  Context
  Environment
  Notations
  Specification.

Import ctx.notations.
Import env.notations.

Module Type ProgramLogicOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG).
Module ProgramLogic.

  Section Triples.

    Context {L : bi} {PI : PredicateDef L}.

    (* Hoare triples for SepContract *)

    Definition CTriple {Δ σ} (pre : L) (c : SepContract Δ σ) (δΔ : CStore Δ) (post : Val σ -> L) : Prop :=
      match c with
      | MkSepContract _ _ Σe θΔ req result ens =>
          pre ⊢ ∃ ι : Valuation Σe, ⌜δΔ = inst θΔ ι⌝ ∧ asn.interpret req ι ∗
                ∀ v : Val σ, asn.interpret ens (env.snoc ι (result∷σ) v) -∗ post v
      end.

    Inductive LTriple {Δ} (δΔ : CStore Δ) (pre post : L) :
      Lemma Δ -> Prop :=
    | rule_ltriple
        (Σ  : LCtx) (θΔ : SStore Δ Σ) (req ens : Assertion Σ) :
        (pre ⊢ ∃ ι : Valuation Σ, ⌜δΔ = inst θΔ ι⌝ ∧ asn.interpret req ι ∗
                 (asn.interpret ens ι -∗ post)) ->
        LTriple δΔ pre post (MkLemma _ _ θΔ req ens).

    Reserved Notation "# f ⦃ P ⦄ s ; δ ⦃ Q ⦄".

    Inductive Triple {Γ : PCtx} (δ : CStore Γ) {τ : Ty} :
      forall (fuel : nat) (pre : L) (s : Stm Γ τ) (post :  Val τ -> CStore Γ -> L), Prop :=
    | rule_consequence
        {fuel : nat} {s : Stm Γ τ} {P P' : L} {Q Q' : Val τ -> CStore Γ -> L}
        (Hleft : P ⊢ P') (Hright : forall v δ', Q' v δ' ⊢ Q v δ') :
        # fuel ⦃ P' ⦄ s ; δ ⦃ Q' ⦄ ->
        # fuel ⦃ P ⦄ s ; δ ⦃ Q ⦄
    | rule_frame
        {fuel : nat } (s : Stm Γ τ) (R P : L) (Q : Val τ -> CStore Γ -> L) :
        # fuel ⦃ P ⦄ s ; δ ⦃ Q ⦄ ->
        # fuel ⦃ R ∗ P ⦄ s ; δ ⦃ fun v δ' => R ∗ Q v δ' ⦄
    | rule_pull
        {fuel : nat} (s : Stm Γ τ) (P : L) (Q : Prop) (R : Val τ -> CStore Γ -> L) :
        (Q -> # fuel ⦃ P ⦄ s ; δ ⦃ R ⦄) ->
        # fuel ⦃ P ∧ ⌜Q⌝ ⦄ s ; δ ⦃ R ⦄
    | rule_exist
        {fuel : nat} (s : Stm Γ τ) {A : Type} {P : A -> L} {Q : Val τ -> CStore Γ -> L} :
        (forall x, # fuel ⦃ P x ⦄ s ; δ ⦃ Q ⦄) ->
        # fuel ⦃ ∃ x, P x ⦄ s ; δ ⦃ Q ⦄
    | rule_stm_val
        {fuel : nat} {l : Val τ} {P : L} {Q : Val τ -> CStore Γ -> L} :
        (P ⊢ Q l δ) ->
        # fuel ⦃ P ⦄ stm_val τ l ; δ ⦃ Q ⦄
    | rule_stm_exp
        {fuel : nat} {e : Exp Γ τ} {P : L} {Q : Val τ -> CStore Γ -> L} :
        (P ⊢ Q (eval e δ) δ) ->
        # fuel ⦃ P ⦄ stm_exp e ; δ ⦃ Q ⦄
    | rule_stm_let
        {fuel : nat} (x : PVar) (σ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ)
        (P : L) (Q : Val σ -> CStore Γ -> L)
        (R : Val τ -> CStore Γ -> L) :
        # fuel ⦃ P ⦄ s ; δ ⦃ Q ⦄ ->
        (forall (v : Val σ) (δ' : CStore Γ),
            # fuel ⦃ Q v δ' ⦄ k ; env.snoc δ' (x∷σ) v ⦃ fun v δ'' => R v (env.tail δ'') ⦄ ) ->
        # fuel ⦃ P ⦄ let: x := s in k ; δ ⦃ R ⦄
    | rule_stm_block
        {fuel : nat} (Δ : PCtx) (δΔ : CStore Δ)
        (k : Stm (Γ ▻▻ Δ) τ)
        (P : L) (R : Val τ -> CStore Γ -> L) :
        # fuel ⦃ P ⦄ k ; δ ►► δΔ ⦃ fun v δ'' => R v (env.drop Δ δ'') ⦄ ->
        # fuel ⦃ P ⦄ stm_block δΔ k ; δ ⦃ R ⦄
    | rule_stm_seq
        {fuel : nat}
        (σ : Ty) (s1 : Stm Γ σ) (s2 : Stm Γ τ)
        (P : L) (Q : Val σ -> CStore Γ -> L) (R : Val τ -> CStore Γ -> L) :
        # fuel ⦃ P ⦄ s1 ; δ ⦃ Q ⦄ ->
        (forall v δ', # fuel ⦃ Q v δ' ⦄ s2 ; δ' ⦃ R ⦄) ->
        # fuel ⦃ P ⦄ s1 ;; s2 ; δ ⦃ R ⦄
    | rule_stm_assert
        {fuel : nat} (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ)
        (P : L) (Q : Val τ -> CStore Γ -> L) :
        (eval e1 δ = true -> # fuel ⦃ P ⦄ k ; δ ⦃ Q ⦄) ->
        # fuel ⦃ P ⦄ stm_assertk e1 e2 k ; δ ⦃ Q ⦄
    | rule_stm_fail
        {fuel : nat} (s : Val ty.string) (Q : Val τ -> CStore Γ -> L) :
        # fuel ⦃ True ⦄ stm_fail τ s ; δ ⦃ Q ⦄
    | rule_stm_read_register
        {fuel : nat} (r : 𝑹𝑬𝑮 τ) (v : Val τ) :
        # fuel ⦃ lptsreg r v ⦄
          stm_read_register r ; δ
        ⦃ fun v' δ' => ⌜δ' = δ⌝ ∧ ⌜v' = v⌝ ∧ lptsreg r v ⦄
    | rule_stm_write_register
        {fuel : nat} (r : 𝑹𝑬𝑮 τ) (w : Exp Γ τ) (v : Val τ)
        (Q : Val τ -> CStore Γ -> L) :
        # fuel ⦃ lptsreg r v ⦄
          stm_write_register r w ; δ
        ⦃ fun v' δ' => ⌜δ' = δ⌝ ∧ ⌜v' = eval w δ⌝ ∧ lptsreg r v' ⦄
    | rule_stm_assign
        {fuel : nat} (x : PVar) (xIn : (x∷τ ∈ Γ)%katamaran) (s : Stm Γ τ)
        (P : L) (R : Val τ -> CStore Γ -> L) :
        # fuel ⦃ P ⦄ s ; δ ⦃ fun v δ' => R v (δ' ⟪ x ↦ v ⟫)%env ⦄ ->
        # fuel ⦃ P ⦄ stm_assign x s ; δ ⦃ R ⦄
    | rule_stm_call
        {fuel : nat} {Δ} {f : 𝑭 Δ τ} {es : NamedEnv (Exp Γ) Δ} {c : SepContract Δ τ}
        (P : L) (Q : Val τ -> CStore Γ -> L) :
        CEnv f = Some c ->
        CTriple P c (evals es δ) (fun v => Q v δ) ->
        # fuel ⦃ P ⦄ stm_call f es ; δ ⦃ Q ⦄
    | rule_stm_call_inline
        {fuel : nat} {Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ)
        (P : L) (Q : Val τ -> CStore Γ -> L) :
        # fuel ⦃ P ⦄ FunDef f ; evals es δ ⦃ fun v _ => Q v δ ⦄ ->
        # S fuel ⦃ P ⦄ stm_call f es ; δ ⦃ Q ⦄
    | rule_stm_call_frame (* TODO: remove stm_call_frame (similar for bind and block then) *)
        {fuel : nat} (Δ : PCtx) (δΔ : CStore Δ) (s : Stm Δ τ)
        (P : L) (Q : Val τ -> CStore Γ -> L) :
        # fuel ⦃ P ⦄ s ; δΔ ⦃ fun v _ => Q v δ ⦄ ->
        # fuel ⦃ P ⦄ stm_call_frame δΔ s ; δ ⦃ Q ⦄ (* TODO: to S or not to S for the fuel *)
    | rule_stm_foreign
        {fuel : nat} {Δ} {f : 𝑭𝑿 Δ τ} (es : NamedEnv (Exp Γ) Δ)
        (P : L) (Q : Val τ -> CStore Γ -> L) :
        CTriple P (CEnvEx f) (evals es δ) (fun v => Q v δ) ->
        # fuel ⦃ P ⦄ stm_foreign f es ; δ ⦃ Q ⦄
    | rule_stm_lemmak
        {fuel : nat} {Δ} {l : 𝑳 Δ} (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ)
        (P Q : L) (R : Val τ -> CStore Γ -> L) :
        LTriple (evals es δ) P Q (LEnv l) ->
        # fuel ⦃ Q ⦄ k ; δ ⦃ R ⦄ ->
        # fuel ⦃ P ⦄ stm_lemmak l es k ; δ ⦃ R ⦄
    | rule_stm_bind
        {fuel : nat} {σ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
        (P : L) (Q : Val σ -> CStore Γ -> L)
        (R : Val τ -> CStore Γ -> L) :
        # fuel ⦃ P ⦄ s ; δ ⦃ Q ⦄ ->
        (forall (v__σ : Val σ) (δ' : CStore Γ),
           # fuel ⦃ Q v__σ δ' ⦄ k v__σ ; δ' ⦃ R ⦄) ->
        # fuel ⦃ P ⦄ stm_bind s k ; δ ⦃ R ⦄
    | rule_stm_debugk
        {fuel : nat} (k : Stm Γ τ)
        (P : L) (Q : Val τ -> CStore Γ -> L) :
        # fuel ⦃ P ⦄ k ; δ ⦃ Q ⦄ ->
        # fuel ⦃ P ⦄ stm_debugk k ; δ ⦃ Q ⦄

    | rule_stm_pattern_match
        {fuel : nat} {σ} (s : Stm Γ σ) (pat : Pattern σ)
        (rhs : forall (pc : PatternCase pat), Stm (Γ ▻▻ PatternCaseCtx pc) τ)
        (P : L) (Q : Val σ -> CStore Γ -> L) (R : Val τ -> CStore Γ -> L) :
        # fuel ⦃ P ⦄ s ; δ ⦃ Q ⦄ ->
        (forall pc δpc δ',
           # fuel ⦃ Q (pattern_match_val_reverse pat pc δpc) δ' ⦄ rhs pc ; δ' ►► δpc
           ⦃ fun v2 δ' => R v2 (env.drop (PatternCaseCtx pc) δ') ⦄) ->
        # fuel ⦃ P ⦄ stm_pattern_match s pat rhs ; δ ⦃ R ⦄

    where "# f ⦃ P ⦄ s ; δ ⦃ Q ⦄" := (@Triple _ δ _ f P%I s Q%I).

    Notation "# f ⦃ P ⦄ s ; δ ⦃ Q ⦄" := (@Triple _ δ _ f P%I s Q%I).

    Lemma rule_consequence_left {Γ σ} {fuel : nat} {δ : CStore Γ} {s : Stm Γ σ}
      (P1 : L) {P2 : L} {Q : Val σ -> CStore Γ -> L} :
      # fuel ⦃ P1 ⦄ s ; δ ⦃ Q ⦄ -> (P2 ⊢ P1) -> # fuel ⦃ P2 ⦄ s ; δ ⦃ Q ⦄.
    Proof.
      intros H hyp. exact (rule_consequence δ hyp (fun _ _ => reflexivity _) H).
    Qed.

    Lemma rule_consequence_right {Γ σ} {fuel : nat} {δ : CStore Γ} {s : Stm Γ σ}
      {P : L} Q {Q'} :
      # fuel ⦃ P ⦄ s ; δ ⦃ Q ⦄ -> (forall v δ, Q v δ ⊢ Q' v δ) -> # fuel ⦃ P ⦄ s ; δ ⦃ Q' ⦄.
    Proof.
      intros H hyp. exact (rule_consequence δ (reflexivity P) hyp H).
    Qed.

    Lemma rule_exist' {Γ : PCtx} {δ : CStore Γ} {fuel : nat} {A : Type} {σ : Ty} (s : Stm Γ σ)
      {P : A -> L} (Q :  A -> Val σ -> CStore Γ -> L) :
      (forall x, # fuel ⦃ P x ⦄ s ; δ ⦃ Q x ⦄) ->
      # fuel ⦃ ∃ x, P x ⦄ s ; δ ⦃ fun v δ' => ∃ x, Q x v δ' ⦄.
    Proof.
      intros hyp. apply rule_exist. intros x.
      apply (rule_consequence_right (Q x) (hyp x)).
      intros v δ'. now apply bi.exist_intro' with x.
    Qed.

    Lemma rule_disj {Γ σ} {fuel : nat} {δ : CStore Γ} {s : Stm Γ σ}
      {P Q : L} {R : Val σ -> CStore Γ -> L} :
      # fuel ⦃ P ⦄ s ; δ ⦃ R ⦄ -> # fuel ⦃ Q ⦄ s ; δ ⦃ R ⦄ ->
      # fuel ⦃ P ∨ Q ⦄ s ; δ ⦃ R ⦄.
    Proof.
      intros H1 H2.
      apply (rule_consequence_left (∃ b : bool, if b then P else Q)).
      - apply rule_exist; intros []; assumption.
      - apply bi.or_elim.
        + now apply bi.exist_intro' with true.
        + now apply bi.exist_intro' with false.
    Qed.

    Lemma rule_disj' {Γ σ} {fuel : nat} {δ : CStore Γ} {s : Stm Γ σ}
      {P1 P2 : L} {Q1 Q2 : Val σ -> CStore Γ -> L} :
      # fuel ⦃ P1 ⦄ s ; δ ⦃ Q1 ⦄ -> # fuel ⦃ P2 ⦄ s ; δ ⦃ Q2 ⦄ ->
      # fuel ⦃ P1 ∨ P2 ⦄ s ; δ ⦃ fun v δ' => Q1 v δ' ∨ Q2 v δ' ⦄.
    Proof.
      intros H1 H2.
      apply rule_disj.
      - apply (rule_consequence_right _ H1).
        intros ? ?. apply bi.or_intro_l.
      - apply (rule_consequence_right _ H2).
        intros ? ?. apply bi.or_intro_r.
    Qed.

    Lemma rule_false {Γ σ} {fuel : nat} {δ : CStore Γ} {s : Stm Γ σ}
      {Q : Val σ -> CStore Γ -> L} :
      # fuel ⦃ False ⦄ s ; δ ⦃ Q ⦄.
    Proof.
      apply (rule_consequence_left (∃ (x : Empty_set), True)).
      - apply rule_exist; intros [].
      - auto.
    Qed.


    Lemma rule_S_fuel {Γ σ} {fuel : nat} {δ : CStore Γ} {s : Stm Γ σ} {P Q} :
      # fuel ⦃ P ⦄ s ; δ ⦃ Q ⦄ →
      # S fuel ⦃ P ⦄ s ; δ ⦃ Q ⦄.
    Proof.
      intros H. induction H.
      - by eapply rule_consequence.
      - by eapply rule_frame.
      - by eapply rule_pull.
      - by eapply rule_exist.
      - by apply rule_stm_val.
      - by apply rule_stm_exp.
      - by eapply rule_stm_let.
      - by apply rule_stm_block.
      - by eapply rule_stm_seq.
      - by apply rule_stm_assert.
      - by apply rule_stm_fail.
      - by apply rule_stm_read_register.
      - by apply rule_stm_write_register.
      - by apply rule_stm_assign.
      - by eapply rule_stm_call.
      - by apply rule_stm_call_inline.
      - by apply rule_stm_call_frame.
      - by apply rule_stm_foreign.
      - by eapply rule_stm_lemmak.
      - by eapply rule_stm_bind.
      - by apply rule_stm_debugk.
      - by eapply rule_stm_pattern_match.
    Qed.

    Definition WP {Γ τ} (fuel : nat) (s : Stm Γ τ) (POST :  Val τ -> CStore Γ -> L) : CStore Γ -> L :=
      fun δ => (∃ (P : L), P ∧ ⌜# fuel ⦃ P ⦄ s; δ ⦃ POST ⦄⌝)%I.

    Lemma rule_wp {Γ σ} (fuel : nat) (s : Stm Γ σ) (POST :  Val σ -> CStore Γ -> L) (δ : CStore Γ) :
      # fuel ⦃ WP fuel s POST δ ⦄ s ; δ ⦃ POST ⦄.
    Proof. apply rule_exist; intros P; now apply rule_pull. Qed.

    #[export] Instance proper_triple_entails {Γ δ τ f} :
      Proper (Basics.flip (⊢) ==> eq ==> pointwise_relation _ (pointwise_relation _ (⊢)) ==> Basics.impl) (@Triple Γ δ τ f).
    Proof.
      intros P Q qp s s' eq__s R S rs H; subst s'.
      eapply rule_consequence. apply qp. apply rs. apply H.
    Qed.

    #[export] Instance proper_triple_equiv {Γ δ τ f} :
      Proper ((⊣⊢) ==> eq ==> pointwise_relation _ (pointwise_relation _ (⊣⊢)) ==> iff) (@Triple Γ δ τ f).
    Proof.
      intros P Q pq s s' eq__s R S rs; subst s'.
      split; intro H.
      - eapply rule_consequence; intros.
        + rewrite -pq. reflexivity.
        + rewrite -rs. reflexivity.
        + exact H.
      - eapply rule_consequence; intros.
        + rewrite pq. reflexivity.
        + rewrite rs. reflexivity.
        + exact H.
    Qed.

    Lemma rule_stm_read_register_backwards {Γ δ σ r v f} (Q : Val σ -> CStore Γ -> L) :
      # f ⦃ lptsreg r v ∗ (lptsreg r v -∗ Q v δ) ⦄
        stm_read_register r ; δ
      ⦃ Q ⦄.
    Proof.
      rewrite bi.sep_comm.
      eapply rule_consequence_right.
      apply rule_frame, rule_stm_read_register.
      cbn. iIntros (? ?) "(H1 & %H2 & %H3 & H4)".
      subst. now iApply "H1".
    Qed.

    Lemma rule_stm_write_register_backwards {Γ δ σ r v f} {e : Exp Γ σ}
      (Q : Val σ -> CStore Γ -> L) :
      # f ⦃ lptsreg r v ∗ (lptsreg r (eval e δ) -∗ Q (eval e δ) δ) ⦄
        stm_write_register r e ; δ
      ⦃ Q ⦄.
    Proof.
      rewrite bi.sep_comm.
      eapply rule_consequence_right.
      apply rule_frame, rule_stm_write_register.
      apply Q. cbn.
      iIntros (? ?) "(H1 & %H2 & %H3 & H4)".
      subst. now iApply "H1".
    Qed.

    Definition ValidContract {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) : Prop :=
      forall (ι : Valuation (sep_contract_logic_variables c)),
        ∃ (fuel : nat),
          # fuel ⦃ interpret_contract_precondition c ι ⦄
            body ; inst_contract_localstore c ι
          ⦃ fun v _ => interpret_contract_postcondition c ι v ⦄.

    Definition ValidContractCEnv : Prop :=
      forall (Δ : PCtx) (τ : Ty) (f : 𝑭 Δ τ) (c : SepContract Δ τ),
        CEnv f = Some c ->
        ValidContract c (FunDef f).

    Definition TValidContract {Γ τ} (fuel : nat) (c : SepContract Γ τ) (body : Stm Γ τ) : Prop :=
      forall (ι : Valuation (sep_contract_logic_variables c)),
          # fuel ⦃ interpret_contract_precondition c ι ⦄
            body ; inst_contract_localstore c ι
          ⦃ fun v _ => interpret_contract_postcondition c ι v ⦄.

    Definition TValidContractCEnv (fuel : nat) : Prop :=
      forall (Δ : PCtx) (τ : Ty) (f : 𝑭 Δ τ) (c : SepContract Δ τ),
        CEnv f = Some c ->
        TValidContract fuel c (FunDef f).

  End Triples.

  Notation "# f ⦃ P ⦄ s ; δ ⦃ Q ⦄" := (@Triple _ _ _ δ _ f P%I s Q%I) (at level 50).

End ProgramLogic.
End ProgramLogicOn.
