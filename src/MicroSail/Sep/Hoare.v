Require Import Coq.Program.Tactics.
Require Import Coq.Classes.Morphisms.
Require Import FunctionalExtensionality.

Require Import MicroSail.Syntax.
Require Import MicroSail.Environment.
Require Import MicroSail.Sep.Logic.
Require Import MicroSail.Sep.Spec.

Module ProgramLogic
  (Import termkit : TermKit)
  (Import progkit : ProgramKit termkit)
  (Import assertkit : AssertionKit termkit progkit)
  (Import contractkit : SymbolicContractKit termkit progkit assertkit).

  Import CtxNotations.
  Import EnvNotations.

  (* (* Some simple instance that make writing program logic rules more natural by *)
  (*  avoiding the need to mention the local variable store δ in the pre and post *)
  (*  conditions that don't affect it *) *)
  (* Section WithΓ. *)
  (*   Context (Γ : PCtx). *)

  (*   Instance δ_ILogic (L : Type) (LL : ILogic L) : ILogic (LocalStore Γ -> L) := *)
  (*     { lentails P Q := (forall δ, lentails (P δ ) (Q δ)); *)
  (*       ltrue := (fun _ => ltrue); *)
  (*       lfalse := (fun _ => lfalse); *)
  (*       land P Q := (fun δ => (land (P δ) (Q δ))); *)
  (*       lor P Q := (fun δ => (lor (P δ) (Q δ))); *)
  (*       limpl P Q := (fun δ => (limpl (P δ) (Q δ))); *)
  (*       lprop P := fun _ => lprop P; *)
  (*       lex {T} (F : T -> LocalStore Γ -> L) := fun δ => lex (fun t => F t δ); *)
  (*       lall {T} (F : T -> LocalStore Γ -> L) := fun δ => lall (fun t => F t δ) *)
  (*     }. *)

  (*   Program Instance δ_ILogicLaws (L : Type) (LL : ILogic L) (LLL : ILogicLaws L LL) : *)
  (*     ILogicLaws (LocalStore Γ -> L) (δ_ILogic L LL). *)
  (*   (* (* Solve the obligations with firstorder take a lot of time. *) *) *)
  (*   (* Solve Obligations with firstorder. *) *)
  (*   Admit Obligations. *)

  (*   Instance δ_ISepLogic (L : Type) (SL : ISepLogic L) : ISepLogic (LocalStore Γ -> L) := *)
  (*     { emp := fun _ => emp; *)
  (*       sepcon P Q := fun δ => sepcon (P δ) (Q δ); *)
  (*       wand P Q := fun δ => wand (P δ) (Q δ) *)
  (*     }. *)

  (*   Program Instance δ_ISepLogicLaws (L : Type) (LL : ISepLogic L) (LLL : ISepLogicLaws L) : *)
  (*     ISepLogicLaws (LocalStore Γ -> L). *)
  (*   Admit Obligations. *)

  (*   Program Instance δ_IHeaplet (L : Type) (SL : IHeaplet L) : *)
  (*     IHeaplet (LocalStore Γ -> L) := *)
  (*     { pred p ts := fun δ => pred p ts; *)
  (*       ptsreg σ r v := fun δ => ptsreg r v *)
  (*     }. *)

  (* End WithΓ. *)

  (* Existing Instance δ_IHeaplet. *)


  Open Scope logic.

  Section Triples.

    Context {L : Type}.
    Context {LL : IHeaplet L}.

    (* Hoare triples for SepContract *)

    Inductive CTriple {Δ σ} (δΔ : LocalStore Δ) (pre : L) (post : Lit σ -> L) :
      SepContract Δ σ -> Prop :=
    | rule_sep_contract
        (result : 𝑺)
        (Σ  : LCtx) (θΔ : SymbolicLocalStore Δ Σ) (ι : SymInstance Σ)
        (req : Assertion Σ) (ens : Assertion (Σ ▻ (result :: σ)))
        (frame : L) :
        δΔ = inst ι θΔ ->
        pre ⊢ frame ✱ interpret_assertion ι req ->
        (forall v, frame ✱ interpret_assertion (env_snoc ι (result :: σ) v) ens ⊢ post v) ->
        CTriple δΔ pre post (MkSepContract _ _ _ θΔ req result ens).

    Inductive Triple {Γ : PCtx} (δ : LocalStore Γ) {τ : Ty} :
      forall (pre : L) (s : Stm Γ τ) (post :  Lit τ -> LocalStore Γ -> L), Prop :=
    | rule_consequence
        {s : Stm Γ τ} {P P' : L} {Q Q' : Lit τ -> LocalStore Γ -> L}
        (Hleft : P ⊢ P') (Hright : forall v δ', Q' v δ' ⊢ Q v δ') :
        δ ⊢ ⦃ P' ⦄ s ⦃ Q' ⦄ ->
        δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄
    | rule_frame
        (s : Stm Γ τ) (R P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
        δ ⊢ ⦃ R ✱ P ⦄ s ⦃ fun v δ' => R ✱ Q v δ' ⦄
    | rule_pull
        (s : Stm Γ τ) (P : L) (Q : Prop) (R : Lit τ -> LocalStore Γ -> L) :
        (Q -> δ ⊢ ⦃ P ⦄ s ⦃ R ⦄) ->
        δ ⊢ ⦃ P ∧ !!Q ⦄ s ⦃ R ⦄
    | rule_exist
        (s : Stm Γ τ) {A : Type} {P : A -> L} {Q : Lit τ -> LocalStore Γ -> L} :
        (forall x, δ ⊢ ⦃ P x ⦄ s ⦃ Q ⦄) ->
        δ ⊢ ⦃ ∃ x, P x ⦄ s ⦃ Q ⦄
    (* | rule_forall *)
    (*     {s : Stm Γ τ} {A : Type} {P : L} *)
    (*     {Q : A -> Lit τ -> LocalStore Γ -> L} *)
    (*     (hyp : forall x, δ ⊢ ⦃ P ⦄ s ⦃ Q x ⦄) (x : A) : *)
    (*     δ ⊢ ⦃ P ⦄ s ⦃ fun v δ' => ∀ x, Q x v δ' ⦄ *)
    | rule_stm_lit
        {l : Lit τ} {P : L} {Q : Lit τ -> LocalStore Γ -> L} :
        P ⊢ Q l δ ->
        δ ⊢ ⦃ P ⦄ stm_lit τ l ⦃ Q ⦄
    | rule_stm_exp
        {e : Exp Γ τ} {P : L} {Q : Lit τ -> LocalStore Γ -> L} :
        P ⊢ Q (eval e δ) δ ->
        δ ⊢ ⦃ P ⦄ stm_exp e ⦃ Q ⦄
    | rule_stm_let
        (x : 𝑿) (σ : Ty) (s : Stm Γ σ) (k : Stm (ctx_snoc Γ (x :: σ)) τ)
        (P : L) (Q : Lit σ -> LocalStore Γ -> L)
        (R : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
        (forall (v : Lit σ) (δ' : LocalStore Γ),
            env_snoc δ' (x::σ) v ⊢ ⦃ Q v δ' ⦄ k ⦃ fun v δ'' => R v (env_tail δ'') ⦄ ) ->
        δ ⊢ ⦃ P ⦄ let: x := s in k ⦃ R ⦄
    | rule_stm_block
        (Δ : PCtx) (δΔ : LocalStore Δ)
        (k : Stm (ctx_cat Γ Δ) τ)
        (P : L) (R : Lit τ -> LocalStore Γ -> L) :
        (δ ►► δΔ ⊢ ⦃ P ⦄ k ⦃ fun v δ'' => R v (env_drop Δ δ'') ⦄) ->
        δ        ⊢ ⦃ P ⦄ stm_block δΔ k ⦃ R ⦄
    | rule_stm_if
        {e : Exp Γ ty_bool} {s1 s2 : Stm Γ τ}
        {P : L} {Q : Lit τ -> LocalStore Γ -> L} :
        δ ⊢ ⦃ P ∧ !!(eval e δ = true) ⦄ s1 ⦃ Q ⦄ ->
        δ ⊢ ⦃ P ∧ !!(eval e δ = false) ⦄ s2 ⦃ Q ⦄ ->
        δ ⊢ ⦃ P ⦄ stm_if e s1 s2 ⦃ Q ⦄
    | rule_stm_seq
        (σ : Ty) (s1 : Stm Γ σ) (s2 : Stm Γ τ)
        (P : L) (Q : LocalStore Γ -> L) (R : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ P ⦄ s1 ⦃ fun _ => Q ⦄ ->
        (forall δ', δ' ⊢ ⦃ Q δ' ⦄ s2 ⦃ R ⦄) ->
        δ ⊢ ⦃ P ⦄ s1 ;; s2 ⦃ R ⦄
    | rule_stm_assert
        (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) (k : Stm Γ τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ P ∧ !! (eval e1 δ = true) ⦄ k ⦃ Q ⦄ ->
        δ ⊢ ⦃ P ⦄ stm_assertk e1 e2 k ⦃ Q ⦄
    | rule_stm_fail
        (s : Lit ty_string) (Q : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ ⊤ ⦄ stm_fail τ s ⦃ Q ⦄
    | rule_stm_match_list
        {σ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
        (xh xt : 𝑿) (alt_cons : Stm (ctx_snoc (ctx_snoc Γ (xh :: σ)) (xt :: ty_list σ)) τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ P ∧ !! (eval e δ = nil) ⦄ alt_nil ⦃ Q ⦄ ->
        (forall (v : Lit σ) (vs : Lit (ty_list σ)),
            env_snoc (env_snoc δ (xh::σ) v) (xt::ty_list σ) vs ⊢
                     ⦃ P ∧ !! (eval e δ = cons v vs) ⦄ alt_cons ⦃ fun v' δ' => Q v' (env_tail (env_tail δ')) ⦄) ->
        δ ⊢ ⦃ P ⦄ stm_match_list e alt_nil xh xt alt_cons ⦃ Q ⦄
    | rule_stm_match_sum
        {xl xr : 𝑿} {σl σr : Ty} {e : Exp Γ (ty_sum σl σr)}
        {alt_inl : Stm (ctx_snoc Γ (xl :: σl)) τ}
        {alt_inr : Stm (ctx_snoc Γ (xr :: σr)) τ}
        {P : L} {Q : Lit τ -> LocalStore Γ -> L} :
        (forall (v : Lit σl), env_snoc δ (xl::σl) v ⊢ ⦃ P ∧ !! (eval e δ = inl v) ⦄ alt_inl ⦃ fun v' δ' => Q v' (env_tail δ') ⦄) ->
        (forall (v : Lit σr), env_snoc δ (xr::σr) v ⊢ ⦃ P ∧ !! (eval e δ = inr v) ⦄ alt_inr ⦃ fun v' δ' => Q v' (env_tail δ') ⦄) ->
        δ ⊢ ⦃ P ⦄ stm_match_sum e xl alt_inl xr alt_inr ⦃ Q ⦄
    | rule_stm_match_pair
        {xl xr : 𝑿} {σl σr : Ty} {e : Exp Γ (ty_prod σl σr)}
        {rhs : Stm (Γ ▻ (xl::σl) ▻ (xr::σr)) τ}
        {P : L} {Q : Lit τ -> LocalStore Γ -> L} :
        (forall (vl : Lit σl) (vr : Lit σr),
            env_snoc (env_snoc δ (xl::σl) vl) (xr::σr) vr ⊢
              ⦃ P ∧ !! (eval e δ = (vl,vr)) ⦄ rhs ⦃ fun v δ' => Q v (env_tail (env_tail δ')) ⦄) ->
        δ ⊢ ⦃ P ⦄ stm_match_pair e xl xr rhs ⦃ Q ⦄
    | rule_stm_match_enum
        {E : 𝑬} (e : Exp Γ (ty_enum E))
        (alts : forall (K : 𝑬𝑲 E), Stm Γ τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ P ⦄ alts (eval e δ) ⦃ Q ⦄ ->
        δ ⊢ ⦃ P ⦄ stm_match_enum E e alts ⦃ Q ⦄
    | rule_stm_match_tuple
        {σs : Ctx Ty} {Δ : PCtx} (e : Exp Γ (ty_tuple σs))
        (p : TuplePat σs Δ) (rhs : Stm (ctx_cat Γ Δ) τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        env_cat δ (tuple_pattern_match p (eval e δ)) ⊢ ⦃ P ⦄ rhs ⦃ fun v δ' => Q v (env_drop Δ δ') ⦄ ->
        δ ⊢ ⦃ P ⦄ stm_match_tuple e p rhs ⦃ Q ⦄
    | rule_stm_match_union
        {U : 𝑼} (e : Exp Γ (ty_union U))
        (alt__Δ : forall (K : 𝑼𝑲 U), PCtx)
        (alt__p : forall (K : 𝑼𝑲 U), Pattern (alt__Δ K) (𝑼𝑲_Ty K))
        (alt__r : forall (K : 𝑼𝑲 U), Stm (Γ ▻▻ alt__Δ K) τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        (forall (K : 𝑼𝑲 U) (v : Lit (𝑼𝑲_Ty K)),
            env_cat δ (pattern_match (alt__p K) v) ⊢ ⦃ P ∧ !! (eval e δ = 𝑼_fold (existT K v)) ⦄ alt__r K ⦃ fun v δ' => Q v (env_drop (alt__Δ K) δ') ⦄) ->
        δ ⊢ ⦃ P ⦄ stm_match_union U e alt__p alt__r ⦃ Q ⦄
    | rule_stm_match_record
        {R : 𝑹} {Δ : PCtx} (e : Exp Γ (ty_record R))
        (p : RecordPat (𝑹𝑭_Ty R) Δ) (rhs : Stm (ctx_cat Γ Δ) τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        env_cat δ (record_pattern_match p (𝑹_unfold (eval e δ))) ⊢ ⦃ P ⦄ rhs ⦃ fun v δ' => Q v (env_drop Δ δ') ⦄ ->
        δ ⊢ ⦃ P ⦄ stm_match_record R e p rhs ⦃ Q ⦄
    | rule_stm_read_register
        (r : 𝑹𝑬𝑮 τ) (v : Lit τ) :
        δ ⊢ ⦃ lptsreg r v ⦄ stm_read_register r ⦃ fun v' δ' => !!(δ' = δ) ∧ !!(v' = v) ∧ lptsreg r v ⦄
    | rule_stm_write_register
        (r : 𝑹𝑬𝑮 τ) (w : Exp Γ τ) (v : Lit τ)
        (Q : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ lptsreg r v ⦄ stm_write_register r w ⦃ fun v' δ' => !!(δ' = δ) ∧ !!(v' = eval w δ)
                                                         ∧ lptsreg r v' ⦄
    | rule_stm_assign_backwards
        (x : 𝑿) (xIn : (x::τ) ∈ Γ) (s : Stm Γ τ)
        (P : L) (R : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ P ⦄ s ⦃ fun v δ' => R v (δ' ⟪ x ↦ v ⟫)%env ⦄ ->
        δ ⊢ ⦃ P ⦄ stm_assign x s ⦃ R ⦄
    | rule_stm_assign_forwards
        (x : 𝑿) (xIn : (x::τ) ∈ Γ) (s : Stm Γ τ)
        (P : L) (R : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ P ⦄ s ⦃ R ⦄ ->
        δ ⊢ ⦃ P ⦄ stm_assign x s ⦃ fun v__new δ' => ∃ v__old, R v__new (δ' ⟪ x ↦ v__old ⟫)%env ∧ !!(env_lookup δ' xIn = v__new) ⦄
    | rule_stm_call_forwards
        {Δ} {f : 𝑭 Δ τ} {es : NamedEnv (Exp Γ) Δ} {c : SepContract Δ τ}
        {P : L} {Q : Lit τ -> L} :
        CEnv f = Some c ->
        CTriple (evals es δ) P Q c ->
        δ ⊢ ⦃ P ⦄ stm_call f es ⦃ fun v δ' => Q v ∧ !!(δ = δ') ⦄
    | rule_stm_call_inline
        {Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) (c : SepContract Δ τ)
        (P : L) (Q : Lit τ -> L) :
        evals es δ ⊢ ⦃ P ⦄ Pi f ⦃ fun v _ => Q v ⦄ ->
        δ ⊢ ⦃ P ⦄ stm_call f es ⦃ fun v δ' => Q v ∧ !!(δ = δ') ⦄
    | rule_stm_call_frame
        (Δ : PCtx) (δΔ : LocalStore Δ) (s : Stm Δ τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        δΔ ⊢ ⦃ P ⦄ s ⦃ fun v _ => Q v δ ⦄ ->
        δ ⊢ ⦃ P ⦄ stm_call_frame δΔ s ⦃ Q ⦄
    | rule_stm_call_external_backwards
        {Δ} {f : 𝑭𝑿 Δ τ} (es : NamedEnv (Exp Γ) Δ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        CTriple (evals es δ) P (fun v => Q v δ) (CEnvEx f) ->
        δ ⊢ ⦃ P ⦄ stm_call_external f es ⦃ Q ⦄
    | rule_stm_bind
        {σ : Ty} (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ)
        (P : L) (Q : Lit σ -> LocalStore Γ -> L)
        (R : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
        (forall (v__σ : Lit σ) (δ' : LocalStore Γ),
            δ' ⊢ ⦃ Q v__σ δ' ⦄ k v__σ ⦃ R ⦄) ->
        δ ⊢ ⦃ P ⦄ stm_bind s k ⦃ R ⦄
    | rule_stm_debugk
        (k : Stm Γ τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ P ⦄ k ⦃ Q ⦄ ->
        δ ⊢ ⦃ P ⦄ stm_debugk k ⦃ Q ⦄
    where "δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" := (@Triple _ δ _ P s Q).

    Context {SLL : ISepLogicLaws L}.
    Lemma rule_consequence_left {Γ σ} {δ : LocalStore Γ} {s : Stm Γ σ}
      (P1 : L) {P2 : L} {Q : Lit σ -> LocalStore Γ -> L} :
      δ ⊢ ⦃ P1 ⦄ s ⦃ Q ⦄ -> P2 ⊢ P1 -> δ ⊢ ⦃ P2 ⦄ s ⦃ Q ⦄.
    Proof.
      intros H hyp. refine (rule_consequence δ hyp _ H).
      intros; apply entails_refl.
    Qed.

    Lemma rule_consequence_right {Γ σ} {δ : LocalStore Γ} {s : Stm Γ σ}
      {P : L} Q {Q'} :
      δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ -> (forall v δ, Q v δ ⊢ Q' v δ) -> δ ⊢ ⦃ P ⦄ s ⦃ Q' ⦄.
    Proof.
      intros H hyp. exact (rule_consequence δ (entails_refl P) hyp H).
    Qed.

    Lemma rule_exist' {Γ : PCtx} {δ : LocalStore Γ} {A : Type} {σ : Ty} (s : Stm Γ σ)
          {P : A -> L} (Q :  A -> Lit σ -> LocalStore Γ -> L) :
      (forall x, δ ⊢ ⦃ P x ⦄ s ⦃ Q x ⦄) ->
      δ ⊢ ⦃ ∃ x, P x ⦄ s ⦃ fun v δ' => ∃ x, Q x v δ' ⦄.
    Proof.
      intros hyp.
      apply rule_exist.
      intros x.
      apply (rule_consequence_right (Q x) (hyp x)).
      intros.
      apply lex_right with x.
      apply entails_refl.
    Qed.

    Lemma rule_disj {Γ σ} {δ : LocalStore Γ} {s : Stm Γ σ}
        {P Q : L} {R : Lit σ -> LocalStore Γ -> L} :
        δ ⊢ ⦃ P ⦄ s ⦃ R ⦄ -> δ ⊢ ⦃ Q ⦄ s ⦃ R ⦄ ->
        δ ⊢ ⦃ P ∨ Q ⦄ s ⦃ R ⦄.
    Proof.
      intros H1 H2.
      apply (rule_consequence_left (∃ b : bool, if b then P else Q)).
      - apply rule_exist; intros []; assumption.
      - apply lor_left.
        + apply lex_right with true, entails_refl.
        + apply lex_right with false, entails_refl.
    Qed.

    Lemma rule_disj' {Γ σ} {δ : LocalStore Γ} {s : Stm Γ σ}
          {P1 P2 : L} {Q1 Q2 : Lit σ -> LocalStore Γ -> L} :
        δ ⊢ ⦃ P1 ⦄ s ⦃ Q1 ⦄ -> δ ⊢ ⦃ P2 ⦄ s ⦃ Q2 ⦄ ->
        δ ⊢ ⦃ P1 ∨ P2 ⦄ s ⦃ fun v δ' => Q1 v δ' ∨ Q2 v δ' ⦄.
    Proof.
      intros H1 H2.
      apply rule_disj.
      - apply (rule_consequence_right _ H1).
        intros. apply lor_right1, entails_refl.
      - apply (rule_consequence_right _ H2).
        intros. apply lor_right2, entails_refl.
    Qed.

    Lemma rule_false {Γ σ} {δ : LocalStore Γ} {s : Stm Γ σ}
      {Q : Lit σ -> LocalStore Γ -> L} :
      δ ⊢ ⦃ lfalse ⦄ s ⦃ Q ⦄.
    Proof.
      apply (rule_consequence_left (∃ (x : Empty_set), ltrue)).
      - apply rule_exist; intros [].
      - apply lfalse_left.
    Qed.

    (* Lemma rule_forall' {Γ σ} {δ : LocalStore Γ} {s : Stm Γ σ} *)
    (*   {A : Type} {P : A -> L} {Q : A -> Lit σ -> LocalStore Γ -> L} *)
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

    (* Lemma rule_conj {Γ σ} {δ : LocalStore Γ} {s : Stm Γ σ} *)
    (*   {P : L} {Q1 Q2 : Lit σ -> LocalStore Γ -> L} : *)
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

    (* Lemma rule_conj' {Γ σ} {δ : LocalStore Γ} {s : Stm Γ σ} *)
    (*   {P1 P2 : L} {Q1 Q2 : Lit σ -> LocalStore Γ -> L} : *)
    (*   δ ⊢ ⦃ P1 ⦄ s ⦃ Q1 ⦄ -> δ ⊢ ⦃ P2 ⦄ s ⦃ Q2 ⦄ -> *)
    (*   δ ⊢ ⦃ P1 ∧ P2 ⦄ s ⦃ fun v δ' => Q1 v δ' ∧ Q2 v δ' ⦄. *)
    (* Proof. *)
    (*   intros H1 H2. *)
    (*   apply rule_conj. *)
    (*   - apply (rule_consequence_left _ H1), land_left1, entails_refl. *)
    (*   - apply (rule_consequence_left _ H2), land_left2, entails_refl. *)
    (* Qed. *)

    Definition WP {Γ τ} (s : Stm Γ τ) (POST :  Lit τ -> LocalStore Γ -> L) : LocalStore Γ -> L :=
      fun δ => ∃ (P : L), P ∧ !! (δ ⊢ ⦃ P ⦄ s ⦃ POST ⦄).

    Lemma rule_wp {Γ σ} (s : Stm Γ σ) (POST :  Lit σ -> LocalStore Γ -> L) (δ1 : LocalStore Γ) :
      δ1 ⊢ ⦃ WP s POST δ1 ⦄ s ⦃ POST ⦄.
    Proof. apply rule_exist; intros P; now apply rule_pull. Qed.

    Global Instance proper_triple {Γ δ τ} :
      Proper (bientails ==> eq ==> pointwise_relation _ (pointwise_relation _ bientails) ==> iff) (@Triple Γ δ τ).
    Proof.
      intros P Q pq s s' eq__s R S rs; subst s'.
      split; intro H; (eapply rule_consequence; [apply pq | apply rs | exact H ]).
    Qed.

    Lemma rule_stm_read_register_backwards {Γ δ σ r v}
          (Q : Lit σ -> LocalStore Γ -> L) :
      δ ⊢ ⦃ lptsreg r v ✱ (lptsreg r v -✱ Q v δ) ⦄ stm_read_register r ⦃ Q ⦄.
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
          (Q : Lit σ -> LocalStore Γ -> L) :
      δ ⊢ ⦃ lptsreg r v ✱ (lptsreg r (eval e δ) -✱ Q (eval e δ) δ) ⦄ stm_write_register r e ⦃ Q ⦄.
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
      (P : L) (Q : Lit σ -> LocalStore Γ -> L) (c : SepContract Δ σ) :
      CEnv f = Some c ->
      CTriple (evals es δ) P (fun v => Q v δ) c ->
      δ ⊢ ⦃ P ⦄ stm_call f es ⦃ Q ⦄.
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
        inst_contract_localstore c ι ⊢
          ⦃ interpret_contract_precondition c ι ⦄
            body
          ⦃ fun v _ => interpret_contract_postcondition c ι v ⦄.

    Definition ValidContractEnv (cenv : SepContractEnv) : Prop :=
      forall (Δ : PCtx) (τ : Ty) (f : 𝑭 Δ τ) (c : SepContract Δ τ),
        cenv Δ τ f = Some c ->
        ValidContract c (Pi f).

  End Triples.

  Notation "δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" := (@Triple _ _ _ δ _ P s Q).

End ProgramLogic.
