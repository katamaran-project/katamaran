From iris.algebra Require Import auth excl.
From iris.base_logic Require Import lib.own.
From iris.proofmode Require Import tactics.

Module Type TraceResources.
  Parameter Trace : Type.
  Definition traceO : ofe := leibnizO Trace.

  Class traceG Σ := TraceG {
      trace_inG :> inG Σ (authR (optionUR (exclR traceO)));
      trace_name : gname
  }.
  Definition tracePreΣ : gFunctors := #[GFunctor (authR (optionUR (exclR traceO)))].

  Class trace_preG Σ := {
    trace_preG_inG :> inG Σ (authR (optionUR (exclR traceO)));
  }.

  #[export] Instance traceG_preG `{traceG Σ} : trace_preG Σ.
  Proof. constructor. typeclasses eauto. Defined.

  #[export] Instance subG_tracePreΣ {Σ}:
    subG tracePreΣ Σ →
    trace_preG Σ.
  Proof. solve_inG. Qed.

  Section S.
    Context `{!trace_preG Σ}.
    Context (γ : gname). (* To allow using different gnames *)

    Definition tr_auth (t: Trace) : iProp Σ := own γ (● (Some (Excl (t: traceO)))).
    Definition tr_frag (t: Trace) : iProp Σ := own γ (◯ (Some (Excl (t: traceO)))).

    Lemma trace_full_frag_eq t t':
      tr_auth t -∗ tr_frag t' -∗
      ⌜ t = t' ⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid_discrete.
      rewrite Excl_included in Hi.  apply leibniz_equiv in Hi. subst; auto.
    Qed.

    Lemma tr_frag_excl t t' :
      tr_frag t -∗ tr_frag t' -∗ ⌜ False ⌝.
    Proof.
      iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
      now apply excl_auth.excl_auth_frag_valid_op_1_l in Hv.
    Qed.

    Lemma trace_update t t' :
      tr_auth t ∗ tr_frag t ==∗
      tr_auth t' ∗ tr_frag t'.
    Proof.
      rewrite /tr_auth /tr_frag. rewrite -!own_op.
      apply own_update, auth_update.
      apply option_local_update.
      apply exclusive_local_update. constructor.
    Qed.

    (* For the moment, there is no need for a lemma stating that traces can only be appened to, but we could customize the RA to enforce this. *)

    #[export] Instance tr_auth_Timeless t : Timeless (tr_auth t).
    Proof.
      intros. apply _.
    Qed.

    #[export] Instance tr_frag_Timeless t : Timeless (tr_frag t).
    Proof.
      intros. apply _.
    Qed.
  End S.

  Notation tr_auth1 := (tr_auth trace_name).
  Notation tr_frag1 := (tr_frag trace_name).

  Lemma trace_alloc `{!trace_preG Σ} t :
    ⊢ |==> ∃ γ, tr_auth γ t ∗ tr_frag γ t.
  Proof.
    iMod (own_alloc (● (Some (Excl (t: traceO))) ⋅ ◯ (Some (Excl (t: traceO))))) as (γ) "[? ?]".
    { apply auth_both_valid_2; done. }
    iModIntro. iExists _. iFrame.
  Qed.

  (* Conditional trace fragments *)
  Definition tr_frag1_if `{traceG Σ} (trb : bool) t :=
    if trb then tr_frag1 t else True%I.

  #[export] Instance tr_frag1_if_Timeless `{traceG Σ} trb t : Timeless (tr_frag1_if trb t).
  Proof.
    intros. rewrite /tr_frag1_if. destruct trb; apply _.
  Qed.
End TraceResources.
