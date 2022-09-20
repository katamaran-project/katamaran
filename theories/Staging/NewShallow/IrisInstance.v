(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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

From Equations Require Import
     Equations Signature.
Require Import Equations.Prop.EqDec.

From stdpp Require finite gmap list.

From iris Require Import
     algebra.auth
     algebra.excl
     algebra.gmap
     base_logic.lib.fancy_updates
     base_logic.lib.gen_heap
     base_logic.lib.own
     bi.big_op
     bi.interface
     program_logic.adequacy
     program_logic.weakestpre
     proofmode.tactics.

From Katamaran Require Import
     Iris.Model
     Prelude
     Semantics
     Sep.Logic
     Signature
     SmallStep.Inversion
     SmallStep.Step
     Specification
     Staging.NewShallow.Executor.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

(* The following three modules define the Iris instance of the program logic
   depending solely on the operational semantics (through IrisBase) and the
   user-defined predicates (in IrisPredicates), but without depending on a
   Specification module. The program logic rules of this subset are implemented
   in IrisSignatureRules, which is combined with IrisPredicates to form
   IrisInstance.

   This split allows us to use multiple different specifications with the same
   Iris model, so that the resulting triples can be combined. This is important
   particularly when combining specifications of universal contracts for unknown
   code with known code verifications, e.g. as in the RiscvPmp.BlockVerification
   proofs. *)
Module Type IrisPredicates
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import SIG  : Signature B)
  (Import IB   : IrisBase B PROG SEM).
  Parameter luser_inst : forall `{sRG : sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) (p : 𝑯) (ts : Env Val (𝑯_Ty p)), iProp Σ.
  Parameter lduplicate_inst : forall `{sRG : sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) (p : 𝑯) (ts : Env Val (𝑯_Ty p)),
      is_duplicable p = true -> bi_entails (luser_inst (sRG := sRG) mG ts) (luser_inst (sRG := sRG) mG ts ∗ luser_inst (sRG := sRG) mG ts).

End IrisPredicates.

Module Type IrisSignatureRules
  (Import B     : Base)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import SIG   : Signature B)
  (Import IB    : IrisBase B PROG SEM)
  (Import IPred : IrisPredicates B PROG SEM SIG IB).
Section Soundness.

  Import SmallStepNotations.

  Context `{sG : sailGS Σ}.

  #[export] Instance PredicateDefIProp : PredicateDef (IProp Σ) :=
    {| lptsreg σ r v        := reg_pointsTo r v;
       luser p ts           := luser_inst sailGS_memGS ts;
       lduplicate p ts Hdup := lduplicate_inst (sRG := sailGS_sailRegGS) sailGS_memGS ts Hdup
    |}.

  Definition ValidLemma {Δ} (lem : Lemma Δ) : Prop :=
    match lem with
      {| lemma_logic_variables := Σ;
         lemma_patterns        := θΔ;
         lemma_precondition    := req;
         lemma_postcondition   := ens;
      |} =>
      forall (ι : Valuation Σ),
        ⊢ asn.interpret req ι -∗
          asn.interpret ens ι
    end.

  Fixpoint Forall {Δ : LCtx} {struct Δ} : (Valuation Δ -> iProp Σ) -> iProp Σ :=
    match Δ return (Valuation Δ -> iProp Σ) -> iProp Σ with
    | ctx.nil      => fun P => P env.nil
    | ctx.snoc Δ b => fun P => Forall (fun δ => ∀ (v : Val (type b)), P (env.snoc δ b v))
    end%I.

End Soundness.

Section Adequacy.

  Import SmallStepNotations.

  Definition sailΣ : gFunctors := #[ memΣ ; invΣ ; GFunctor regUR].

  Instance subG_sailGpreS {Σ} : subG sailΣ Σ -> sailGpreS Σ.
  Proof.
    intros.
    lazymatch goal with
    | H:subG ?xΣ _ |- _ => try unfold xΣ in H
    end.
    repeat match goal with
           | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
           end.
    split; eauto using memΣ_GpreS, subG_invΣ.
    solve_inG.
 Qed.

  Definition RegStore_to_map (γ : RegStore) : gmap SomeReg (exclR (leibnizO SomeVal)) :=
    list_to_map (K := SomeReg)
                (fmap (fun x => match x with
                              existT _ r =>
                                pair (existT _ r) (Excl (existT _ (read_register γ r)))
                            end)
                     (finite.enum (sigT 𝑹𝑬𝑮))).

  Lemma RegStore_to_map_Forall (γ : RegStore) :
    map_Forall (K := SomeReg)
      (fun reg v => match reg with | existT _ reg => Excl (existT _ (read_register γ reg)) = v end)
      (RegStore_to_map γ).
  Proof.
    eapply map_Forall_lookup_2.
    intros [σ r] x eq.
    unfold RegStore_to_map in eq.
    remember (list_to_map _ !! _) as o in eq.
    destruct o; inversion eq; subst.
    assert (eq' := eq_sym Heqo).
    rewrite <-elem_of_list_to_map in eq'.
    - eapply elem_of_list_fmap_2 in eq'.
      destruct eq' as ([σ' r'] & eq2 & eq3).
      now inversion eq2.
    - rewrite <-list_fmap_compose.
      rewrite (list_fmap_ext (compose fst (λ x : {H : Ty & 𝑹𝑬𝑮 H},
          let (x0, r0) := x in (existT x0 r0 , Excl (existT x0 (read_register γ r0))))) id _ _ _ eq_refl).
      + rewrite list_fmap_id.
        eapply finite.NoDup_enum.
      + now intros [σ' r'].
  Qed.

  Lemma RegStore_to_map_valid (γ : RegStore) :
    valid (RegStore_to_map γ).
  Proof.
    intros i.
    cut (exists v, RegStore_to_map γ !! i = Some (Excl v)).
    - intros [v eq].
      now rewrite eq.
    - destruct i as [σ r].
      exists (existT _ (read_register γ r)).
      eapply elem_of_list_to_map_1'.
      + intros y eq.
        eapply elem_of_list_fmap_2 in eq.
        destruct eq as ([σ2 r2] & eq1 & eq2).
        now inversion eq1.
      + refine (elem_of_list_fmap_1 _ _ (existT _ r) _).
        eapply finite.elem_of_enum.
  Qed.

  Lemma steps_to_erased {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}:
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    rtc erased_step (cons (MkConf s δ) nil, (γ,μ)) (cons (MkConf s' δ') nil, (γ',μ')).
  Proof.
    induction 1; first done.
    refine (rtc_l _ _ _ _ _ IHSteps).
    exists nil.
    refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _).
    by eapply mk_prim_step.
  Qed.

  Lemma own_RegStore_to_map_reg_pointsTos `{sailRegGS Σ'} {γ : RegStore} {l : list (sigT 𝑹𝑬𝑮)} :
    NoDup l ->
    ⊢ own reg_gv_name (◯ list_to_map (K := SomeReg)
                         (fmap (fun x => match x with existT _ r =>
                                                     pair (existT _ r) (Excl (existT _ (read_register γ r)))
                                      end) l)) -∗
      [∗ list] x ∈ l,
        let (x0, r) := (x : sigT 𝑹𝑬𝑮) in reg_pointsTo r (read_register γ r).
  Proof.
    iIntros (nodups) "Hregs".
    iInduction l as [|[x r]] "IH".
    - now iFrame.
    - rewrite big_sepL_cons. cbn.
      rewrite (insert_singleton_op (A := exclR (leibnizO SomeVal)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ r)))).
      rewrite auth_frag_op.
      iPoseProof (own_op with "Hregs") as "[Hreg Hregs]".
      iFrame.
      iApply "IH".
      + iPureIntro.
        refine (NoDup_cons_1_2 (existT x r) l nodups).
      + iFrame.
      + destruct (proj1 (NoDup_cons (existT x r) _) nodups) as [notin _].
        refine (not_elem_of_list_to_map_1 _ (existT x r) _).
        rewrite <-list_fmap_compose.
        rewrite (list_fmap_ext (compose fst (λ x : {H : Ty & 𝑹𝑬𝑮 H},
          let (x0, r0) := x in (existT x0 r0, Excl (existT x0 (read_register γ r0))))) id _ _ _ eq_refl).
        now rewrite list_fmap_id.
        now intros [σ2 r2].
  Qed.

  Lemma adequacy {Γ σ} (s : Stm Γ σ) {γ γ'} {μ μ'}
        {δ δ' : CStore Γ} {s' : Stm Γ σ} {Q : Val σ -> Prop} :
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
    (forall `{sailGS Σ'},
        ⊢ semTriple (Σ := Σ') δ
          (mem_res sailGS_memGS μ ∗
           [∗ list] _ ↦ x ∈ finite.enum (sigT 𝑹𝑬𝑮),
              match x with | existT _ r => reg_pointsTo r (read_register γ r) end
          )%I s (fun v δ' => bi_pure (Q v)))%I ->
    ResultOrFail s' Q.
  Proof.
    intros steps fins trips.
    cut (adequate MaybeStuck (MkConf s δ) (γ,μ)
             (λ (v : val (microsail_lang Γ σ)) (_ : state (microsail_lang Γ σ)),
                (λ v0 : val (microsail_lang Γ σ), match v0 with
                                                  | MkValConf _ v' _ => Q v'
                                                  end) v)).
    - destruct s'; cbn in fins; destruct fins; last done.
      intros adeq.
      apply (adequate_result MaybeStuck (MkConf s δ) (γ , μ) (fun v _ => match v with | MkValConf _ v' δ' => Q v' end) adeq nil (γ' , μ') (MkValConf _ v δ')).
      by apply steps_to_erased.
    - constructor; last done.
      intros t2 σ2 [v2 δ2] eval.
      assert (eq := RegStore_to_map_Forall γ).
      assert (regsmapv := RegStore_to_map_valid γ).
      pose proof (wp_adequacy sailΣ (microsail_lang Γ σ) MaybeStuck (MkConf s δ) (γ , μ) (fun v => match v with | MkValConf _ v' δ' => Q v' end)) as adeq.
      refine (adequate_result _ _ _ _ (adeq _) _ _ _ eval); clear adeq.
      iIntros (Hinv κs) "".
      iMod (own_alloc ((● RegStore_to_map γ ⋅ ◯ RegStore_to_map γ ) : regUR)) as (spec_name) "[Hs1 Hs2]";
        first by apply auth_both_valid.
      pose proof (memΣ_GpreS (Σ := sailΣ) _) as mPG.
      iMod (mem_inv_init μ mPG) as (memG) "[Hmem Rmem]".
      iModIntro.
      iExists (fun σ _ => regs_inv (srGS := (SailRegGS _ spec_name)) (σ.1) ∗ mem_inv memG (σ.2))%I.
      iExists _.
      iSplitR "Hs2 Rmem".
      * iSplitL "Hs1".
        + iExists (RegStore_to_map γ).
          by iFrame.
        + iFrame.
      * iPoseProof (trips sailΣ (SailGS Hinv (SailRegGS reg_pre_inG spec_name) memG) with "[Rmem Hs2]") as "trips'".
        + iFrame.
          unfold RegStore_to_map.
          iApply (own_RegStore_to_map_reg_pointsTos (H := SailRegGS reg_pre_inG spec_name)(γ := γ) (l := finite.enum (sigT 𝑹𝑬𝑮)) with "Hs2").
          eapply finite.NoDup_enum.
        + iApply (wp_mono with "trips'").
          by iIntros ([δ3 v]).
  Qed.
End Adequacy.
End IrisSignatureRules.

Module Type IrisInstance (B : Base) (PROG : Program B) (SEM : Semantics B PROG) (SIG : Signature B) (IB : IrisBase B PROG SEM) :=
  IrisPredicates B PROG SEM SIG IB <+ IrisSignatureRules B PROG SEM SIG IB.

(*
 * The following module defines the parts of the Iris model that must depend on the Specification, not just on the Signature.
 * This is kept to a minimum (see comment for the IrisPredicates module).
 *)
Module IrisInstanceWithContracts
  (Import B     : Base)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import SIG   : Signature B)
  (Import SPEC  : Specification B PROG SIG)
  (Import IB    : IrisBase B PROG SEM)
  (Import II    : IrisInstance B PROG SEM SIG IB)
  (Import NS    : NewShallowExecOn B PROG SIG SPEC).

  Section WithSailGS.
  Context {Σ} {sG : sailGS Σ}.

  Definition ForeignSem : Prop :=
    ∀ (Γ : PCtx) (Δ : PCtx) (τ : Ty) (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
      (POST : Val τ → CStore Γ → iProp Σ) (δΓ : CStore Γ),
      CPureSpecM.call_contract (CEnvEx f) (evals es δΓ) (fun v => POST v δΓ) -∗
      semWP (stm_foreign f es) POST δΓ.

  Definition LemmaSem : Prop :=
    forall (Δ : PCtx) (l : 𝑳 Δ),
      ValidLemma (LEnv l).

  Definition semCall [Δ τ] (f : 𝑭 Δ τ) (args : CStore Δ) (Q : Val τ -> iProp Σ) :
    iProp Σ := ▷ CHeapSpecM.exec_call_inline semWP f args Q.

  Definition semWP' [Γ τ] (s : Stm Γ τ) :
    (Val τ -> CStore Γ -> iProp Σ) -> CStore Γ -> iProp Σ :=
    CHeapSpecM.exec_open semWP semCall s.
  Arguments semWP' : simpl never.

  Definition ref {Γ1 Γ2 A}
    (F G : (A → CStore Γ2 → iProp Σ) → CStore Γ1 → iProp Σ) : iProp Σ :=
    ∀ (POST : A → CStore Γ2 → iProp Σ) (δ : CStore Γ1),
      F POST δ -∗ G POST δ.
  Notation "F ≼ G" := (ref F G).

  Lemma semWP_val {Γ τ} (v : Val τ) (POST : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) :
    semWP (stm_val τ v) POST δ ⊣⊢ |={⊤}=> POST v δ.
  Proof. unfold semWP. rewrite wp_unfold. reflexivity. Qed.

  Lemma rule_val {Γ τ} (v : Val τ) :
    ⊢ semWP' (Γ := Γ) (stm_val τ v) ≼ semWP (stm_val τ v).
  Proof. iIntros (POST δ). rewrite semWP_val; auto. Qed.

  Lemma rule_exp {Γ τ} (e : Exp Γ τ) :
    ⊢ semWP' (stm_exp e) ≼ semWP (stm_exp e).
  Proof.
    iIntros (POST δ) "P". unfold semWP.
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold.
    iIntros ([regs μ] ns k ks nt) "[Hregs Hmem]".
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    remember (MkConf (stm_exp e) δ) as t.
    destruct H.
    dependent elimination Heqt.
    dependent elimination H. cbn.
    iModIntro. iModIntro. iModIntro.
    iFrame.
    iSplitL; trivial.
    by iApply wp_value.
  Qed.

  Lemma semWP_fail {Γ τ s} (POST : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) :
    semWP (stm_fail _ s) POST δ ⊣⊢ True.
  Proof.
    apply bi.entails_anti_sym.
    - auto.
    - iIntros "_".
      unfold semWP. rewrite wp_unfold. cbn.
      iIntros (σ _ ks1 ks nt) "Hregs".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 σ2 efs) "%".
      remember (MkConf (fail s) δ) as s1.
      destruct H.
      inversion Heqs1. subst.
      inversion H.
  Qed.

  Lemma rule_fail {Γ τ s} :
    ⊢ semWP' (Γ := Γ) (stm_fail τ s) ≼ semWP (stm_fail τ s).
  Proof. iIntros (POST δ) "_". rewrite semWP_fail; auto. Qed.

  Lemma rule_bind {Γ τ σ} (s : Stm Γ σ) (k : Val σ → Stm Γ τ) :
    ⊢ semWP' (stm_bind s k) ≼ semWP (stm_bind s k).
  Proof.
    iIntros (POST). iRevert (s). iLöb as "IH". iIntros (s δ) "WPs".
    unfold semWP at 2. rewrite wp_unfold. cbn.
    iIntros ([regs μ] ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s0.
    + unfold semWP'; cbn.
      unfold semWP at 4. rewrite wp_unfold.
      unfold wp_pre.
      rewrite (val_stuck (MkConf s13 δ1) (γ1 , μ1) [] _ _ [] (mk_prim_step s14)).
      iSpecialize ("WPs" $! (γ1 , μ1) ns nil nil nt with "Hregs"). cbn.
      iMod "Hclose".
      iMod "WPs" as "[_ WPs]".
      iSpecialize ("WPs" $! _ _ nil (mk_prim_step s14)).
      iMod "WPs" as "WPs".
      iModIntro. iModIntro.
      iMod "WPs".
      iModIntro.
      iMod "WPs" as "[Hregs [wps _]]".
      fold_semWP.
      iModIntro.
      iFrame.
      by iApply "IH".
    + iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      unfold semWP', CHeapSpecM.exec_open; cbn.
      rewrite semWP_val.
      iMod "WPs" as "WPs".
      iModIntro.
      by iFrame.
    + iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iFrame; iSplitL; auto.
      by iApply semWP_fail.
  Qed.

  Lemma rule_block {Γ τ Δ} (δΔ : CStore Δ) (s : Stm (Γ ▻▻ Δ) τ) :
    ⊢ semWP' (stm_block δΔ s) ≼ semWP (stm_block δΔ s).
  Proof.
    iIntros (POST). iRevert (δΔ s).
    iLöb as "IH". iIntros (δΔ k δΓ) "WPk".
    unfold semWP at 2. rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s.
    - iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      unfold semWP', CHeapSpecM.exec_open, CHeapSpecM.pushspops.
      rewrite semWP_val.
      rewrite env.drop_cat.
      iMod "WPk" as "WPk".
      iModIntro.
      iFrame.
      iSplitL; [|trivial].
      by iApply semWP_val.
    - iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iFrame; iSplitL; auto.
      by iApply semWP_fail.
    - unfold semWP', CHeapSpecM.exec_open, CHeapSpecM.pushspops.
      unfold semWP at 3. rewrite wp_unfold. cbn.
      unfold wp_pre.
      rewrite (val_stuck (MkConf k1 _) (γ1 , μ1) [] _ _ [] (mk_prim_step s1)).
      iSpecialize ("WPk" $! (γ1 , μ1) ns nil nil nt with "state_inv"). cbn.
      iMod "Hclose".
      iMod "WPk" as "[_ WPk]".
      iSpecialize ("WPk" $! _ _ nil (mk_prim_step s1)).
      iMod "WPk" as "WPk".
      iModIntro. iModIntro.
      iMod "WPk".
      iModIntro.
      iMod "WPk" as "[Hregs [wps _]]".
      fold_semWP.
      iModIntro.
      iFrame.
      by iApply "IH".
  Qed.

  Lemma rule_let {Γ τ x σ} (s1 : Stm Γ σ) (s2 : Stm (Γ ▻ x∷σ) τ) :
    ⊢ semWP' (stm_let x σ s1 s2) ≼ semWP (stm_let x σ s1 s2).
  Proof.
    iIntros (POST δ) "WPs". unfold semWP.
    rewrite wp_unfold. cbn.
    iIntros ([regs μ] ns ks1 ks nt) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame; iSplitL; auto.
    iApply rule_bind.
    unfold semWP', CHeapSpecM.exec_open, CHeapSpecM.bind, CHeapSpecM.pushpop.
    iApply (semWP_mono with "WPs"); cbn.
    iIntros (v δ) "wpk".
    by iApply (rule_block [env].[_∷_ ↦ v]).
  Qed.

  Lemma rule_assign {Γ τ x} (xInΓ : x∷τ ∈ Γ) (s : Stm Γ τ) :
    ⊢ semWP' (stm_assign x s) ≼ semWP (stm_assign x s).
  Proof.
    iIntros (POST). iRevert (s). iLöb as "IH". iIntros (s δ) "WPs".
    unfold semWP at 2. rewrite wp_unfold. cbn.
    iIntros ([regs μ] ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    dependent elimination H.
    dependent elimination s0; fold_semWP.
    + iModIntro. iModIntro. iModIntro.
      unfold semWP' at 2, CHeapSpecM.exec_open, CHeapSpecM.bind, CHeapSpecM.assign, CHeapSpecM.pure.
      rewrite semWP_val.
      iMod "Hclose" as "_".
      iMod "WPs" as "WPs".
      iModIntro.
      iFrame.
      iSplitL; [|trivial].
      by iApply semWP_val.
    + iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iFrame; iSplitL; auto.
      by iApply semWP_fail.
    + unfold semWP' at 2, CHeapSpecM.exec_open, CHeapSpecM.bind, CHeapSpecM.assign, CHeapSpecM.pure.
      unfold semWP at 2. rewrite wp_unfold. unfold wp_pre.
      rewrite (val_stuck (MkConf s9 δ1) _ [] _ _ [] (mk_prim_step s10)).
      iSpecialize ("WPs" $! _ ns nil nil nt with "Hregs"). cbn.
      iMod "Hclose".
      iMod "WPs" as "[_ WPs]".
      iSpecialize ("WPs" $! _ _ nil (mk_prim_step s10)).
      fold_semWP.
      iMod "WPs" as "WPs".
      iModIntro. iModIntro.
      iMod "WPs".
      iModIntro.
      iMod "WPs" as "[Hregs [WPs _]]".
      iModIntro.
      iFrame.
      by iApply "IH".
  Qed.

  Lemma rule_call_frame {Γ τ Δ} (δΔ : CStore Δ) (s : Stm Δ τ) :
    ⊢ semWP' (Γ := Γ) (stm_call_frame δΔ s) ≼ semWP (stm_call_frame δΔ s).
  Proof.
    iIntros (POST δΓ). iRevert (δΔ s).
    iLöb as "IH". iIntros (δΔ s) "WPs".
    unfold semWP at 2. rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first trivial.
    iIntros (e2 σ2 efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s0.
    - iMod "Hclose" as "_".
      unfold semWP' at 2; cbn.
      unfold semWP at 2.
      rewrite wp_unfold.
      rewrite {1}/wp_pre.
      rewrite (val_stuck (MkConf s5 _) (γ1 , μ1) [] _ _ [] (mk_prim_step s6)).
      iMod ("WPs" $! (γ1 , μ1) ns nil ks nt with "Hregs") as "[% WPs]". cbn.
      iMod ("WPs" $! _ _ _ (mk_prim_step s6)) as "WPs".
      fold_semWP.
      iModIntro. iModIntro.
      iMod "WPs".
      iModIntro.
      iMod "WPs" as "[Hregs [WPs' _]]".
      iModIntro.
      iFrame.
      iSplitL; last trivial.
      by iApply "IH".
    - iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro.
      iFrame.
      iSplitL; last trivial.
      unfold semWP' at 2, CHeapSpecM.exec_open, CHeapSpecM.bind,
        CHeapSpecM.get_local, CHeapSpecM.put_local.
      by rewrite ?semWP_val.
    - iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iFrame.
      iModIntro.
      iSplitL; [|trivial].
      by iApply semWP_fail.
  Qed.

  Lemma semWP_call {Γ τ Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δΓ : CStore Γ),
        ▷ semWP (FunDef f) (fun vτ _ => Q vτ δΓ) (evals es δΓ) -∗
        semWP (stm_call f es) Q δΓ.
  Proof.
    iIntros (Q δΓ) "wpbody".
    unfold semWP at 2.
    rewrite wp_unfold. cbn.
    iIntros (σ' ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ'' efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    by iApply rule_call_frame.
  Qed.

  Lemma rule_call {Γ τ Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
    ⊢ semWP' (stm_call f es) ≼ semWP (stm_call f es).
  Proof.
    iIntros (POST δ) "WPbody".
    unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ' ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ'' efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s.
    unfold semWP', semCall. cbn.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    by iApply rule_call_frame.
  Qed.

  Lemma rule_foreign {Γ τ Δ} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
    ForeignSem ->
    ⊢ semWP' (stm_foreign f es) ≼ semWP (stm_foreign f es).
  Proof. iIntros (extSem POST δΓ) "WPs". by iApply extSem. Qed.

  Lemma equiv_call_lemma {Δ} (lem : Lemma Δ) (args : CStore Δ) POST :
    CPureSpecM.call_lemma lem args POST ⊣⊢ CPureSpecM.call_lemma' lem args POST.
  Proof. apply bi.entails_anti_sym; apply CPureSpecM.equiv_call_lemma. Qed.

  Lemma rule_lemma {Γ τ Δ} (L : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (s : Stm Γ τ) :
    LemmaSem ->
    ⊢ semWP' (stm_lemmak L es s) ≼ semWP (stm_lemmak L es s).
  Proof.
    iIntros (lemSem POST δ) "WPs". specialize (lemSem _ L).
    unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s0.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    unfold semWP'; cbn.
    rewrite equiv_call_lemma.
    destruct LEnv as [Σe δΔ req ens]. cbn in lemSem |- *.
    iDestruct "WPs" as "[% [% [req ens]]]".
    iApply "ens". by iApply lemSem.
  Qed.

  Lemma rule_if {Γ τ} (e : Exp Γ ty.bool) (s1 s2 : Stm Γ τ) :
    ⊢ semWP' (stm_if e s1 s2) ≼ semWP (stm_if e s1 s2).
  Proof.
    iIntros (POST δ) "wp". unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ _ ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    unfold semWP'; cbn.
    now destruct (eval e1 δ1).
  Qed.

  Lemma rule_seq {Γ τ σ} (s1 : Stm Γ σ) (s2 : Stm Γ τ) :
    ⊢ semWP' (stm_seq s1 s2) ≼ semWP (stm_seq s1 s2).
  Proof.
    iIntros (POST δ) "WPs1". unfold semWP. rewrite wp_unfold. cbn.
    iIntros ([regs μ] ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_". iFrame.
    iModIntro.
    iSplitL; [|trivial].
    unfold semWP'; cbn.
    by iApply rule_bind.
  Qed.

  Lemma rule_assertk {Γ τ} (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (s : Stm Γ τ) :
    ⊢ semWP' (stm_assertk e1 e2 s) ≼ semWP (stm_assertk e1 e2 s).
  Proof.
    iIntros (POST δ) "WPs". unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s0.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    unfold semWP'; cbn.
    destruct (eval e3 δ1).
    - by iApply "WPs".
    - by iApply semWP_fail.
  Qed.

  Lemma rule_match_list {Γ τ σ xh xt} (e : Exp Γ (ty.list σ))
    (s1 : Stm Γ τ) (s2 : Stm (Γ ▻ xh∷σ ▻ xt∷ty.list σ) τ) :
    ⊢ semWP' (stm_match_list e s1 xh xt s2) ≼ semWP (stm_match_list e s1 xh xt s2).
  Proof.
    iIntros (POST δ) "WPs". unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ1 ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    unfold semWP'; cbn.
    destruct eval as [|l ls]; [easy|].
    by iApply (rule_block [env].[xh0∷_ ↦ l].[xt0∷ty.list _ ↦ ls]).
  Qed.

  Lemma rule_match_sum {Γ τ σinl σinr xinl xinr} (e : Exp Γ (ty.sum σinl σinr))
    (s1 : Stm (Γ ▻ xinl∷σinl) τ) (s2 : Stm (Γ ▻ xinr∷σinr) τ) :
    ⊢ semWP' (stm_match_sum e xinl s1 xinr s2) ≼ semWP (stm_match_sum e xinl s1 xinr s2).
  Proof.
    iIntros (POST δ) "WPs". unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ1 _ ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    unfold semWP'; cbn.
    destruct eval.
    - by iApply (rule_block [env].[xinl0∷σinl0 ↦ v]).
    - by iApply (rule_block [env].[xinr0∷σinr0 ↦ v]).
  Qed.

  Lemma rule_match_enum {Γ τ E} (e : Exp Γ (ty.enum E)) (alts : enumt E → Stm Γ τ) :
    ⊢ semWP' (stm_match_enum E e alts) ≼ semWP (stm_match_enum E e alts).
  Proof.
    iIntros (POST δ) "WPa". unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ _ ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. by iFrame.
  Qed.

  Lemma rule_match_union {Γ τ U} (e : Exp Γ (ty.union U))
    (alt__ctx : unionk U → PCtx)
    (alt__pat : ∀ K : unionk U, Pattern (alt__ctx K) (unionk_ty U K))
    (alt__rhs : ∀ K : unionk U, Stm (Γ ▻▻ alt__ctx K) τ) :
    ⊢ semWP' (stm_match_union U e alt__pat alt__rhs) ≼
      semWP (stm_match_union U e alt__pat alt__rhs).
  Proof.
    iIntros (POST δ) "WPs". unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame; iSplitL; auto.
    unfold semWP'; cbn.
    destruct unionv_unfold.
    by iApply rule_block.
  Qed.

  Lemma rule_match_bvec {Γ τ n} (e : Exp Γ (ty.bvec n)) (rhs : bv n → Stm Γ τ) :
    ⊢ semWP' (stm_match_bvec n e rhs) ≼ semWP (stm_match_bvec n e rhs).
  Proof.
    iIntros (POST δ) "WPs". unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. by iFrame.
  Qed.

  Lemma rule_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) :
    ⊢ semWP' (Γ := Γ) (stm_read_register reg) ≼ semWP (stm_read_register reg).
  Proof.
    iIntros (POST δ) "[% [Hreg HP]]"; cbn.
    unfold semWP. iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold; cbn.
    iIntros (σ _ ls _ n) "[Hregs Hmem]".
    iDestruct (@reg_valid with "Hregs Hreg") as %<-.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    dependent elimination H.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iFrame. iSplitR ""; auto.
    iModIntro.
    iApply wp_value.
    by iApply "HP".
  Qed.

  Lemma rule_write_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) :
    ⊢ semWP' (stm_write_register reg e) ≼ semWP (stm_write_register reg e).
  Proof.
    iIntros (POST δ) "[% [Hreg HP]]"; cbn.
    unfold semWP. iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold; cbn.
    iIntros (σ _ ls _ n) "[Hregs Hmem]".
    iMod (reg_update σ.1 reg v (eval e δ) with "Hregs Hreg") as "[Hregs Hreg]".
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    dependent elimination H.
    destruct (steps_inversion_write_register s) as [-> [<- [<- ->]]].
    iModIntro. iModIntro. iModIntro.
    iFrame. iSplitL; auto.
    iApply wp_value.
    by iApply "HP".
  Qed.

  Lemma rule_debug {Γ τ} (s : Stm Γ τ) :
    ⊢ semWP' (stm_debugk s) ≼ semWP (stm_debugk s).
  Proof.
    iIntros (POST δ) "WPs". unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s0.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; by iFrame.
  Qed.

  Lemma rule_match_pattern {Γ τ Δ σ} (s : Stm Γ σ) (pat : Pattern Δ σ) (rhs : Stm (Γ ▻▻ Δ) τ) :
    ⊢ semWP' (stm_match_pattern s pat rhs) ≼ semWP (stm_match_pattern s pat rhs).
  Proof.
    iIntros (POST δ) "WPs". unfold semWP. rewrite wp_unfold. cbn.
    iIntros (? ns ks1 ks nt) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s0.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame; iSplitL; auto.
    unfold semWP'; cbn.
    iApply rule_bind; unfold semWP'; cbn.
    iApply (semWP_mono with "WPs"); cbn.
    clear - sG.
    iIntros (v δ) "WPrhs".
    iApply rule_block; unfold semWP'; cbn.
    iApply (semWP_mono with "WPrhs").
    iIntros (v0 δ0); auto.
  Qed.

  Lemma rule_newpattern_match {Γ τ σ} (s : Stm Γ σ) (pat : PatternShape σ)
    (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ) :
    ⊢ semWP' (stm_newpattern_match s pat rhs) ≼ semWP (stm_newpattern_match s pat rhs).
  Proof.
    iIntros (POST δ) "WPs". unfold semWP. rewrite wp_unfold. cbn.
    iIntros (? ns ks1 ks nt) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    dependent elimination H.
    fold_semWP.
    dependent elimination s0.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame; iSplitL; auto.
    unfold semWP'; cbn.
    iApply rule_bind; unfold semWP'; cbn.
    iApply (semWP_mono with "WPs"); cbn.
    clear - sG.
    iIntros (v δ) "WPrhs".
    destruct newpattern_match_val.
    iApply rule_block; unfold semWP'; cbn.
    iApply (semWP_mono with "WPrhs").
    iIntros (v0 δ0); auto.
  Qed.

  Lemma sound_stm_open (extSem : ForeignSem) (lemSem : LemmaSem) :
    forall {Γ τ} (s : Stm Γ τ),
      ⊢ semWP' s ≼ semWP s.
  Proof.
    unfold ref.
    intros Γ τ [].
    - iIntros (Q δΓ). rewrite semWP_val. auto.
    - apply rule_exp.
    - apply rule_let.
    - apply rule_block.
    - apply rule_assign.
    - apply rule_call; auto.
    - apply rule_call_frame.
    - apply rule_foreign; auto.
    - apply rule_lemma; auto.
    - apply rule_if.
    - apply rule_seq.
    - apply rule_assertk.
    - apply rule_fail.
    - apply rule_newpattern_match.
    - apply rule_match_pattern.
    - apply rule_match_list.
    - apply rule_match_sum.
    - apply rule_match_enum.
    - apply rule_match_union.
    - apply rule_match_bvec.
    - apply rule_read_register.
    - apply rule_write_register.
    - apply rule_bind.
    - apply rule_debug.
  Qed.

  Lemma sound_stm (extSem : ForeignSem) (lemSem : LemmaSem) :
    forall {Γ τ} (s : Stm Γ τ) (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
      CHeapSpecM.exec_aux semCall s Q δ ⊢ semWP s Q δ.
  Proof.
    intros.
    apply (CHeapSpecM.fold_exec_aux (ex := semWP) (ec := semCall)).
    - admit.
    - clear - extSem lemSem.
      intros Γ τ s.
      intros P Q PQ δ. cbn.
      iIntros "WP". iApply sound_stm_open; auto.
      unfold semWP'.
      iStopProof.
      iApply CHeapSpecM.exec_open_monotonic; auto.
      admit.
      admit.
    - unfold pointwise_relation. easy.
  Admitted.

  Import sep.instances.

  Lemma sound :
    ForeignSem -> LemmaSem -> Shallow.ValidContractCEnv ->
    ⊢ Shallow.ValidContractEnvSem semWP.
  Proof.
    intros extSem lemSem vcenv.
    iLöb as "IH".
    iIntros (σs σ f).
    specialize (vcenv σs σ f).
    destruct (CEnv f) as [[Σe δΔ req res ens]|];[|trivial].
    iIntros (ι) "PRE".
    specialize (vcenv _ eq_refl).
    cbn in vcenv.
    rewrite env.Forall_forall in vcenv.
    specialize (vcenv ι).
    rewrite CPureSpecM.wp_produce in vcenv.
    cbn in vcenv.
    iPoseProof (vcenv with "[$] PRE") as "vcenv". clear vcenv.
    iApply (sound_stm extSem lemSem).
    iRevert "vcenv".
    iApply CHeapSpecM.exec_aux_monotonic.
  Abort.

  End WithSailGS.

End IrisInstanceWithContracts.
