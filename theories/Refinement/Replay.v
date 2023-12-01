(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Base
     Signature
     Shallow.Replay
     Symbolic.Replay.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type ReplayRefinementOn
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import SHALREPL : ShallowReplayOn B SIG)
  (Import SYMBREPL : SymbolicReplayOn B SIG).

  Import logicalrelation.
  Import logicalrelation.notations.

  Section Replay.

    Context {SM CM} {RM : forall {SA CA} (RA : Rel SA CA), Rel (SM SA) (CM CA)}.
    Context {spureM : SPureSpecM SM} {cpureM : CPureSpecM CM} {rpureM : RPureSpecM RM}.

    Lemma rel_replay {Σ} (s : 𝕊 Σ) :
      ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RM RUnit⟧ (sreplay s) (creplay s).
    Proof.
      unfold RValid. cbn.
      induction s; cbn; intros w ι Hpc sδ cδ rδ.
      - apply rel_angelic_binary; auto.
      - apply rel_demonic_binary; auto.
      - apply rel_error; auto.
      - apply rel_block; auto.
      - eapply rel_bind; auto.
        + apply rel_assert_formula; auto.
          now apply refine_formula_subst.
        + intros w1 θ1 ι1 Hι1 Hpc1 _ _ _.
          apply IHs; auto. subst.
          now rewrite <- inst_persist.
      - eapply rel_bind; auto.
        + apply rel_assume_formula; auto.
          now apply refine_formula_subst.
        + intros w1 θ1 ι1 Hι1 Hpc1 _ _ _.
          apply IHs; auto. subst.
          now rewrite <- inst_persist.
      - eapply rel_bind; auto.
        + apply rel_angelic; auto.
        + intros w1 θ1 ι1 Hι1 Hpc1 t v ->.
          apply IHs; auto. subst.
          now rewrite <- inst_persist.
      - eapply rel_bind; auto.
        + apply rel_demonic; auto.
        + intros w1 θ1 ι1 Hι1 Hpc1 t v ->.
          apply IHs; auto. subst.
          now rewrite <- inst_persist.
      - eapply rel_bind; auto.
        + apply rel_assert_formula; auto.
          cbn. subst.
          rewrite !inst_subst.
          rewrite inst_sub_shift.
          now rewrite <- inst_lookup.
        + intros w1 θ1 ι1 Hι1 Hpc1 _ _ _.
          apply IHs; auto. subst.
          rewrite <- inst_subst.
          rewrite <- persist_subst.
          rewrite <- inst_sub_shift.
          rewrite <- inst_subst.
          rewrite sub_comp_shift.
          reflexivity.
      - eapply rel_bind; auto.
        + apply rel_assume_formula; auto.
          cbn. subst.
          rewrite !inst_subst.
          rewrite inst_sub_shift.
          now rewrite <- inst_lookup.
        + intros w1 θ1 ι1 Hι1 Hpc1 _ _ _.
          apply IHs; auto. subst.
          rewrite <- inst_subst.
          rewrite <- persist_subst.
          rewrite <- inst_sub_shift.
          rewrite <- inst_subst.
          rewrite sub_comp_shift.
          reflexivity.
      - apply rel_error; auto.
      - apply rel_error; auto.
      - apply rel_debug; auto.
    Qed.

    (* Lemma shallow_replay_complete {Σ} (s : 𝕊 Σ) {w : World} : *)
    (*   forall *)
    (*     (ω : MkWorld Σ [ctx] ⊒ w) *)
    (*     (ι : Valuation w) *)
    (*     (i : Valuation Σ) *)
    (*     (Hpc0 : instprop (wco w) ι), *)
    (*     i = inst (sub_acc ω) ι -> *)
    (*     SHAL.Replay.replay i s -> *)
    (*     safe s i. *)
    (* Proof. *)
    (*   revert w; induction s; intros w ω ι i Hpc0 Hi Hreplay. *)
    (*   - destruct Hreplay as [H|H]. *)
    (*     + left. *)
    (*       apply (IHs1 w ω ι i Hpc0 Hi H). *)
    (*     + right. *)
    (*       apply (IHs2 w ω ι i Hpc0 Hi H). *)
    (*   - destruct Hreplay as [Hs1 Hs2]. *)
    (*     split. *)
    (*     + apply (IHs1 w ω ι i Hpc0 Hi Hs1). *)
    (*     + apply (IHs2 w ω ι i Hpc0 Hi Hs2). *)
    (*   - auto. *)
    (*   - auto. *)
    (*   - cbn in Hreplay. *)
    (*     unfold CPureSpecM.bind, CPureSpecM.assert_formula in Hreplay. *)
    (*     destruct Hreplay as [Hfml Hs]. *)
    (*     split; auto. *)
    (*     apply (IHs w ω ι i Hpc0 Hi Hs). *)
    (*   - cbn in Hreplay. *)
    (*     unfold CPureSpecM.bind, CPureSpecM.assume_formula in Hreplay. *)
    (*     intros Hfml. *)
    (*     apply (IHs w ω ι i Hpc0 Hi (Hreplay Hfml)). *)
    (*   - cbn in Hreplay. *)
    (*     unfold CPureSpecM.bind, CPureSpecM.angelic in Hreplay. *)
    (*     destruct Hreplay as [v Hreplay]. *)
    (*     exists v. *)
    (*     unshelve eapply (IHs (wsnoc w b) _ ι.[b ↦ v] _ _ _ Hreplay). *)
    (*     + apply acc_sub with (ζ := sub_up1 (sub_acc ω)). *)
    (*       apply Entailment.entails_nil. *)
    (*     + cbn. *)
    (*       now rewrite instprop_subst, inst_sub_wk1. *)
    (*     + subst. *)
    (*       now rewrite <- inst_sub_up1. *)
    (*   - cbn in Hreplay. *)
    (*     unfold CPureSpecM.bind, CPureSpecM.demonic in Hreplay. *)
    (*     intros v. *)
    (*     unshelve eapply (IHs (wsnoc w b) _ ι.[b ↦ v] _ _ _ (Hreplay v)). *)
    (*     + apply acc_sub with (ζ := sub_up1 (sub_acc ω)). *)
    (*       apply Entailment.entails_nil. *)
    (*     + cbn. *)
    (*       now rewrite instprop_subst, inst_sub_wk1. *)
    (*     + subst. *)
    (*       now rewrite <- inst_sub_up1. *)
    (*   - cbn in Hreplay. *)
    (*     unfold CPureSpecM.bind, CPureSpecM.assert_formula in Hreplay. *)
    (*     destruct Hreplay as [Heq Hreplay]. *)
    (*     split; auto. *)
    (*     unshelve eapply (IHs _ _ (inst (sub_acc ω) ι) _ _ _ Hreplay). *)
    (*     + apply acc_sub with (ζ := sub_shift xIn). *)
    (*       apply Entailment.entails_nil. *)
    (*     + now cbn. *)
    (*     + rewrite <- inst_sub_shift. *)
    (*       cbn [sub_acc]. *)
    (*       now subst. *)
    (*   - cbn in Hreplay. *)
    (*     unfold CPureSpecM.bind, CPureSpecM.assume_formula in Hreplay. *)
    (*     intros Heq. *)
    (*     unshelve eapply (IHs _ _ (inst (sub_acc ω) ι) _ _ _ (Hreplay Heq)). *)
    (*     + apply acc_sub with (ζ := sub_shift xIn). *)
    (*       apply Entailment.entails_nil. *)
    (*     + now cbn. *)
    (*     + rewrite <- inst_sub_shift. *)
    (*       cbn [sub_acc]. *)
    (*       now subst. *)
    (*   - now cbn in Hreplay. *)
    (*   - now cbn in Hreplay. *)
    (*   - cbn in Hreplay. *)
    (*     apply (IHs _ _ ι _ Hpc0 Hi Hreplay). *)
    (* Qed. *)

    (* Lemma replay_sound_nil (s : 𝕊 [ctx]) : *)
    (*   forall ι, *)
    (*     safe (Replay.replay s) ι -> safe s ι. *)
    (* Proof. *)
    (*   intros ι H. *)
    (*   destruct (env.view ι). *)
    (*   rewrite <- ?safe_debug_safe in H. *)
    (*   rewrite <- (@wsafe_safe wnil _ [env]) in H. *)
    (*   apply (@refine_replay [ctx] s wnil acc_refl [env]) in H. *)
    (*   assert (Hwco: instprop (wco wnil) [env]) by now cbn. *)
    (*   apply (@shallow_replay_complete [ctx] s wnil acc_refl [env] [env] Hwco eq_refl H). *)
    (* Qed. *)

  End Replay.

End ReplayRefinementOn.
