From iris.algebra Require Import auth excl.
From iris.base_logic Require Import lib.own.
From iris.proofmode Require Import tactics.

Class iostateG (IOStateG : Type) Σ := IOStateG {
   iostate_inG :: inG Σ (authR (optionUR (exclR (leibnizO IOStateG))));
   iostate_name : gname
}.


Definition iostatePreΣ (IOStateG : Type) : gFunctors := #[GFunctor (authR (optionUR (exclR (leibnizO IOStateG))))].

Class iostate_preG (IOState: Type) Σ := {
    iostate_preG_inG :: inG Σ (authR (optionUR (exclR (leibnizO IOState))));
  }.

#[export] Instance iostateG_preG `{iostateG T Σ} : iostate_preG T Σ.
Proof. constructor. typeclasses eauto. Defined.

#[export] Instance subG_iostatePreG{Σ T}:
  subG (iostatePreΣ T) Σ →
  iostate_preG T Σ.
Proof. solve_inG. Qed.

Section S.
  Context `{!iostate_preG T Σ}.
  Context (γ : gname). (* To allow using different gnames *)

  Definition st_auth (s: T) : iProp Σ := own γ (● (Some (Excl (s: leibnizO T)))).
  Definition st_frag (s: T) : iProp Σ := own γ (◯ (Some (Excl (s: leibnizO T)))).

  Lemma iost_full_frag_eq s s':
    st_auth s -∗ st_frag s' -∗
    ⌜ s = s' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid_discrete.
    rewrite Excl_included in Hi.  apply leibniz_equiv in Hi. subst; auto.
  Qed.

  Lemma st_frag_excl s s' :
    st_frag s -∗ st_frag s' -∗ ⌜ False ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    now apply excl_auth.excl_auth_frag_op_valid in Hv.
  Qed.

  Lemma state_update s s' :
    st_auth s ∗ st_frag s ==∗
    st_auth s' ∗ st_frag s'.
  Proof.
    rewrite /st_auth /st_frag. rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  #[export] Instance st_auth_Timeless s : Timeless (st_auth s).
  Proof.
    intros. apply _.
  Qed.

  #[export] Instance st_frag_Timeless s : Timeless (st_frag s).
  Proof.
    intros. apply _.
  Qed.
End S.

Notation st_auth1 := (st_auth iostate_name).
Notation st_frag1 := (st_frag iostate_name).


Lemma state_alloc_names `{!iostate_preG T Σ} s :
  ⊢ |==> ∃ γ, st_auth γ s ∗ st_frag γ s.
Proof.
  iMod (own_alloc (● (Some (Excl (s: leibnizO T))) ⋅ ◯ (Some (Excl (s: leibnizO T))))) as (γ) "[? ?]".
  { apply auth_both_valid_2; done. }
  iModIntro. iExists _. iFrame.
Qed.

Lemma state_alloc `{!iostate_preG T Σ} s :
  ⊢ |==> ∃ sG : iostateG T Σ,

      @st_auth _ _ (@iostateG_preG _ _ sG) iostate_name s ∗ @st_frag _ _ (@iostateG_preG _ _ sG) iostate_name s.
Proof.
  iMod (state_alloc_names s) as (γ) "Hinit".
  by iExists (IOStateG _ _ _ γ).
Qed.
