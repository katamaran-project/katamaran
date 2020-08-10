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

  (* (* Some simple instance that make writing program logic rules more natural by *)
  (*  avoiding the need to mention the local variable store δ in the pre and post *)
  (*  conditions that don't affect it *) *)
  (* Section WithΓ. *)
  (*   Context (Γ : Ctx (𝑿 * Ty)). *)

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

    Inductive CTriple (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) {σ : Ty} :
      forall (pre : L) (post : Lit σ -> L) (c : SepContract Δ σ), Prop :=
    (* | rule_sep_contract_unit *)
    (*     (Σ  : Ctx (𝑺 * Ty)) (θΔ : SymbolicLocalStore Δ Σ) (ι : SymInstance Σ) *)
    (*     (req : Assertion Σ) (ens : Assertion Σ) : *)
    (*     δΔ = inst_localstore ι θΔ -> *)
    (*     CTriple (τ:=ty_unit) Δ δΔ *)
    (*       (inst_assertion ι req) *)
    (*       (fun _ => inst_assertion ι ens) *)
    (*       (sep_contract_unit θΔ req ens) *)
    | rule_sep_contract_result_pure
        (Σ  : Ctx (𝑺 * Ty)) (θΔ : SymbolicLocalStore Δ Σ) (ι : SymInstance Σ)
        (req : Assertion Σ) (ens : Assertion Σ) (result : Term Σ σ) :
        δΔ = inst_localstore ι θΔ ->
        CTriple Δ δΔ
          (inst_assertion ι req)
          (fun v => inst_assertion ι ens ∧ !!(v = inst_term ι result))
          (sep_contract_result_pure θΔ result req ens)
    | rule_sep_contract_result
        (result : 𝑺)
        (Σ  : Ctx (𝑺 * Ty)) (θΔ : SymbolicLocalStore Δ Σ) (ι : SymInstance Σ)
        (req : Assertion Σ) (ens : Assertion (Σ ▻ (result , σ))) :
        δΔ = inst_localstore ι θΔ ->
        CTriple
          Δ δΔ
          (inst_assertion ι req)
          (fun v => inst_assertion (env_snoc ι (result , σ) v) ens)
          (@sep_contract_result _ _ _ θΔ result req ens).
    (* | rule_sep_contract_none {σ} : *)
    (*     Pi f *)
    (*     CTriple Γ (fun _ => ⊤) (fun _ _ => ⊤) (@sep_contract_none Γ σ). *)


    Inductive Triple {Γ : Ctx (𝑿 * Ty)} (δ : LocalStore Γ) :
      forall {τ : Ty}
        (pre : L) (s : Stm Γ τ)
        (post :  Lit τ -> LocalStore Γ -> L), Prop :=
    | rule_consequence {σ : Ty}
        {P P' : L} {Q Q' : Lit σ -> LocalStore Γ -> L} {s : Stm Γ σ} :
        (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') -> δ ⊢ ⦃ P' ⦄ s ⦃ Q' ⦄ -> δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄
    | rule_frame {σ : Ty}
        (R P : L) (Q : Lit σ -> LocalStore Γ -> L) (s : Stm Γ σ) :
        δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ -> δ ⊢ ⦃ R ✱ P ⦄ s ⦃ fun v δ' => R ✱ Q v δ' ⦄
    | rule_pull
        {σ : Ty} (s : Stm Γ σ)
        (P : L) (Q : Prop) (R : Lit σ -> LocalStore Γ -> L) :
        (Q -> δ ⊢ ⦃ P ⦄ s ⦃ R ⦄) ->
        δ ⊢ ⦃ P ∧ !!Q ⦄ s ⦃ R ⦄
    | rule_exist
        {A : Type} {σ : Ty} (s : Stm Γ σ)
        {P : A -> L} (Q :  Lit σ -> LocalStore Γ -> L) :
        (forall x, δ ⊢ ⦃ P x ⦄ s ⦃ Q ⦄) ->
        δ ⊢ ⦃ ∃ x, P x ⦄ s ⦃ Q ⦄
    | rule_disj
        {σ : Ty} {s : Stm Γ σ} {P Q : L} {R : Lit σ -> LocalStore Γ -> L} :
        δ ⊢ ⦃ P ⦄ s ⦃ R ⦄ -> δ ⊢ ⦃ Q ⦄ s ⦃ R ⦄ ->
        δ ⊢ ⦃ P ∨ Q ⦄ s ⦃ R ⦄
    | rule_conj
        {σ : Ty} {s : Stm Γ σ}
        {P : L} {Q1 Q2 : Lit σ -> LocalStore Γ -> L} :
        δ ⊢ ⦃ P ⦄ s ⦃ Q1 ⦄ -> δ ⊢ ⦃ P ⦄ s ⦃ Q2 ⦄ ->
        δ ⊢ ⦃ P ⦄ s ⦃ fun v δ' => Q1 v δ' ∧ Q2 v δ' ⦄
    | rule_false
        {σ : Ty} {s : Stm Γ σ}
        {Q : Lit σ -> LocalStore Γ -> L} :
        δ ⊢ ⦃ lfalse ⦄ s ⦃ Q ⦄
    | rule_stm_lit
        {τ : Ty} {l : Lit τ}
        {P : L} {Q : Lit τ -> LocalStore Γ -> L} :
        P ⊢ Q l δ ->
        δ ⊢ ⦃ P ⦄ stm_lit τ l ⦃ Q ⦄
    | rule_stm_exp
        {τ : Ty} {e : Exp Γ τ}
        {P : L} {Q : Lit τ -> LocalStore Γ -> L} :
        P ⊢ Q (eval e δ) δ ->
        δ ⊢ ⦃ P ⦄ stm_exp e ⦃ Q ⦄
    | rule_stm_let
        (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (ctx_snoc Γ (x , σ)) τ)
        (P : L) (Q : Lit σ -> LocalStore Γ -> L)
        (R : Lit τ -> LocalStore Γ -> L) :
        δ         ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
        (forall (v : Lit σ) (δ' : LocalStore Γ),
            env_snoc δ' (x,σ) v ⊢ ⦃ Q v δ' ⦄ k ⦃ fun v δ'' => R v (env_tail δ'') ⦄ ) ->
        δ         ⊢ ⦃ P ⦄ let: x := s in k ⦃ R ⦄
    | rule_stm_let_forwards
        (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (ctx_snoc Γ (x , σ)) τ)
        (P : L) (Q : Lit σ -> LocalStore Γ -> L)
        (R : Lit τ -> LocalStore (Γ ▻ (x,σ)) -> L) :
        δ         ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
        (forall (v : Lit σ) (δ' : LocalStore Γ),
            env_snoc δ' (x,σ) v ⊢ ⦃ Q v δ' ⦄ k ⦃ R ⦄ ) ->
        δ         ⊢ ⦃ P ⦄ let: x := s in k ⦃ fun v δ' => ∃ v__let, R v (env_snoc δ' (x,σ) v__let)⦄
    | rule_stm_block
        (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ)
        (τ : Ty) (k : Stm (ctx_cat Γ Δ) τ)
        (P : L) (R : Lit τ -> LocalStore Γ -> L) :
        (δ ►► δΔ ⊢ ⦃ P ⦄ k ⦃ fun v δ'' => R v (env_drop Δ δ'') ⦄) ->
        δ         ⊢ ⦃ P ⦄ stm_block δΔ k ⦃ R ⦄
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
                      (P : L) :
        δ ⊢ ⦃ P ⦄ stm_assert e1 e2 ⦃ fun v δ' => !!(δ = δ' /\ eval e1 δ' = v /\ v = true) ∧ P ⦄
    | rule_stm_fail (τ : Ty) (s : Lit ty_string) :
        forall (Q : Lit τ -> LocalStore Γ -> L),
          δ ⊢ ⦃ ⊤ ⦄ stm_fail τ s ⦃ Q ⦄
    | rule_stm_match_list
        {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
        (xh xt : 𝑿) (alt_cons : Stm (ctx_snoc (ctx_snoc Γ (xh , σ)) (xt , ty_list σ)) τ)
        (Pnil : L) (Pcons : L) (Q : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ Pnil ⦄ alt_nil ⦃ fun v' δ' => Q v' δ' ⦄ ->
        (forall v vs, env_snoc (env_snoc δ (xh,σ) v) (xt,ty_list σ) vs ⊢
                        ⦃ Pcons ⦄ alt_cons ⦃ fun v' δ' => Q v' (env_tail (env_tail δ')) ⦄) ->
        δ ⊢ ⦃ (!!(eval e δ = nil) --> Pnil)
            ∧ (∀ v vs, !!(eval e δ = cons v vs) --> Pcons)
            ⦄ stm_match_list e alt_nil xh xt alt_cons ⦃ Q ⦄
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
    | rule_stm_match_pair
        {σ1 σ2 τ : Ty} (e : Exp Γ (ty_prod σ1 σ2))
        (xl xr : 𝑿) (rhs : Stm (ctx_snoc (ctx_snoc Γ (xl , σ1)) (xr , σ2)) τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        (forall vl vr,
            env_snoc (env_snoc δ (xl, σ1) vl) (xr, σ2) vr ⊢
              ⦃ P ⦄ rhs ⦃ fun v δ' => Q v (env_tail (env_tail δ')) ⦄) ->
        δ ⊢ ⦃ P ⦄ stm_match_pair e xl xr rhs ⦃ Q ⦄
    | rule_stm_match_enum
        {E : 𝑬} (e : Exp Γ (ty_enum E)) {τ : Ty}
        (alts : forall (K : 𝑬𝑲 E), Stm Γ τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        (forall K, δ ⊢ ⦃ P ⦄ alts K ⦃ Q ⦄) ->
        δ ⊢ ⦃ P ⦄ stm_match_enum E e alts ⦃ Q ⦄
    | rule_stm_match_tuple
        {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_tuple σs))
        (p : TuplePat σs Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        (forall (δΔ : LocalStore Δ),
            env_cat δ δΔ ⊢ ⦃ P ⦄ rhs ⦃ fun v δ' => Q v (env_drop Δ δ') ⦄) ->
        δ ⊢ ⦃ P ⦄ stm_match_tuple e p rhs ⦃ Q ⦄
    | rule_stm_match_union
        {U : 𝑼} (e : Exp Γ (ty_union U)) {σ τ : Ty}
        (alt__Δ : forall (K : 𝑼𝑲 U), Ctx (𝑿 * Ty))
        (alt__p : forall (K : 𝑼𝑲 U), Pattern (alt__Δ K) (𝑼𝑲_Ty K))
        (alt__r : forall (K : 𝑼𝑲 U), Stm (ctx_cat Γ (alt__Δ K)) τ)
        (P : forall (K : 𝑼𝑲 U), L) (Q : Lit τ -> LocalStore Γ -> L) :
        (forall (K : 𝑼𝑲 U) (δΔ : LocalStore (alt__Δ K)),
            env_cat δ δΔ ⊢ ⦃ P K ⦄ alt__r K ⦃ fun v δ' => Q v (env_drop (alt__Δ K) δ') ⦄) ->
        δ ⊢
          ⦃ ∀ (K : 𝑼𝑲 U) (v : Lit (𝑼𝑲_Ty K)), !!(eval e δ = 𝑼_fold (existT K v)) --> P K ⦄
          stm_match_union U e (fun K => @alt Γ (𝑼𝑲_Ty K) τ (alt__Δ K) (alt__p K) (alt__r K))
          ⦃ Q ⦄
    | rule_stm_match_record
        {R : 𝑹} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_record R))
        (p : RecordPat (𝑹𝑭_Ty R) Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        (forall (δΔ : LocalStore Δ),
            env_cat δ δΔ ⊢ ⦃ P ⦄ rhs ⦃ fun v δ' => Q v (env_drop Δ δ') ⦄) ->
        δ ⊢ ⦃ P ⦄ stm_match_record R e p rhs ⦃ Q ⦄
    | rule_stm_read_register {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Lit σ) :
        δ ⊢ ⦃ r ↦ v ⦄ stm_read_register r ⦃ fun v' δ' => !!(δ' = δ) ∧ !!(v' = v) ∧ r ↦ v ⦄
    (* | rule_stm_read_register_backwards {σ : Ty} (r : 𝑹𝑬𝑮 σ) *)
    (*                                    (Q : Lit σ -> LocalStore Γ -> L) *)
    (*                                    (v : Lit σ) : *)
    (*     δ ⊢ ⦃ r ↦ v ✱ (r ↦ v -✱ Q v δ) ⦄ stm_read_register r ⦃ Q ⦄ *)
    | rule_stm_write_register {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                              (Q : Lit σ -> LocalStore Γ -> L)
                              (v : Lit σ) :
        δ ⊢ ⦃ r ↦ v ⦄ stm_write_register r w ⦃ fun v' δ' => !!(δ' = δ) ∧ !!(v' = eval w δ)
                                                         ∧ r ↦ v' ⦄
    (* | rule_stm_write_register_backwards {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ) *)
    (*                                     (Q : Lit σ -> LocalStore Γ -> L) *)
    (*                                     (v : Lit σ) : *)
    (*     δ ⊢ ⦃ r ↦ v ✱ (r ↦ eval w δ -✱ Q (eval w δ) δ) ⦄ stm_write_register r w ⦃ Q ⦄ *)
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
    (* | rule_stm_call_backwards *)
    (*     {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ) *)
    (*     (P : L) (Q : Lit σ -> LocalStore Γ -> L) : *)
    (*     CTriple Δ (evals es δ) P (fun v => Q v δ) (CEnv f) -> *)
    (*     δ ⊢ ⦃ P ⦄ stm_call f es ⦃ Q ⦄ *)
    | rule_stm_call_frame
        (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (τ : Ty) (s : Stm Δ τ)
        (P : L) (Q : Lit τ -> LocalStore Γ -> L) :
        δΔ ⊢ ⦃ P ⦄ s ⦃ fun v _ => Q v δ ⦄ ->
        δ ⊢ ⦃ P ⦄ stm_call_frame Δ δΔ τ s ⦃ Q ⦄
    | rule_stm_bind
        {σ τ : Ty} (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ)
        (P : L) (Q : Lit σ -> LocalStore Γ -> L)
        (R : Lit τ -> LocalStore Γ -> L) :
        δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
        (forall (v__σ : Lit σ) (δ' : LocalStore Γ),
            δ' ⊢ ⦃ Q v__σ δ' ⦄ k v__σ ⦃ R ⦄) ->
        δ ⊢ ⦃ P ⦄ stm_bind s k ⦃ R ⦄
    where "δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" := (@Triple _ δ _ P s Q).

    Context {LLL : ILogicLaws L _}.
    Lemma rule_consequence_right {Γ : Ctx (𝑿 * Ty)} {δ : LocalStore Γ} {σ : Ty}
      {P : L} {Q Q' : Lit σ -> LocalStore Γ -> L} {s : Stm Γ σ} :
      δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄ -> (forall v δ, Q v δ ⊢ Q' v δ) -> δ ⊢ ⦃ P ⦄ s ⦃ Q' ⦄.
    Proof.
      intros H hyp. exact (rule_consequence δ (entails_refl P) hyp H).
    Qed.

    Lemma rule_exist' {Γ : Ctx (𝑿 * Ty)} {δ : LocalStore Γ} {A : Type} {σ : Ty} (s : Stm Γ σ)
          {P : A -> L} (Q :  A -> Lit σ -> LocalStore Γ -> L) :
      (forall x, δ ⊢ ⦃ P x ⦄ s ⦃ Q x ⦄) ->
      δ ⊢ ⦃ ∃ x, P x ⦄ s ⦃ fun v δ' => ∃ x, Q x v δ' ⦄.
    Proof.
      intros hyp.
      apply rule_exist.
      intros x.
      eapply rule_consequence_right.
      apply hyp.
      intros.
      apply lex_right with x.
      apply entails_refl.
    Qed.

    Lemma rule_disj' {Γ : Ctx (𝑿 * Ty)} {δ : LocalStore Γ} {σ : Ty} {s : Stm Γ σ}
          {P1 P2 : L} {Q1 Q2 : Lit σ -> LocalStore Γ -> L} :
        δ ⊢ ⦃ P1 ⦄ s ⦃ Q1 ⦄ -> δ ⊢ ⦃ P2 ⦄ s ⦃ Q2 ⦄ ->
        δ ⊢ ⦃ P1 ∨ P2 ⦄ s ⦃ fun v δ' => Q1 v δ' ∨ Q2 v δ' ⦄.
    Proof.
      intros H1 H2.
      apply rule_disj.
      - eapply rule_consequence_right. apply H1.
        intros. apply lor_right1, entails_refl.
      - eapply rule_consequence_right. apply H2.
        intros. apply lor_right2, entails_refl.
    Qed.

    Lemma rule_conj' {Γ : Ctx (𝑿 * Ty)} {δ : LocalStore Γ} {σ : Ty} {s : Stm Γ σ}
          {P1 P2 : L} {Q1 Q2 : Lit σ -> LocalStore Γ -> L} :
        δ ⊢ ⦃ P1 ⦄ s ⦃ Q1 ⦄ -> δ ⊢ ⦃ P2 ⦄ s ⦃ Q2 ⦄ ->
        δ ⊢ ⦃ P1 ∧ P2 ⦄ s ⦃ fun v δ' => Q1 v δ' ∧ Q2 v δ' ⦄.
    Proof.
      intros H1 H2.
      apply rule_conj.
      - eapply rule_consequence.
        apply land_left1. apply entails_refl.
        intros. apply entails_refl. apply H1.
      - eapply rule_consequence.
        apply land_left2. apply entails_refl.
        intros. apply entails_refl. apply H2.
    Qed.

  End Triples.

  Notation "δ ⊢ ⦃ P ⦄ s ⦃ Q ⦄" := (@Triple _ _ _ δ _ P s Q).

End ProgramLogic.
