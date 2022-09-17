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
     Sep.Hoare
     Sep.Logic
     Signature
     SmallStep.Inversion
     SmallStep.Step
     Specification.

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

  Definition semTriple {Γ τ} (δ : CStore Γ)
             (PRE : iProp Σ) (s : Stm Γ τ) (POST : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
    PRE -∗ semWP s POST δ.
  (* always modality needed? perhaps not because sail not higher-order? *)

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

  Lemma iris_rule_consequence {Γ σ} {δ : CStore Γ}
        {P P'} {Q Q' : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
        (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') ->
        semTriple δ P' s Q' -∗ semTriple δ P s Q.
  Proof.
    iIntros (PP QQ) "trips P".
    iApply (wp_mono _ _ _ (fun v => match v with MkValConf _ v δ' => Q' v δ' end)).
    + intros [v δ']; cbn.
      apply QQ.
    + iApply "trips".
      iApply PP; iFrame.
  Qed.

  Lemma iris_rule_frame {Γ σ} {δ : CStore Γ}
        (R P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) (s : Stm Γ σ) :
        (⊢ semTriple δ P s Q -∗ semTriple δ (R ∗ P) s (fun v δ' => R ∗ Q v δ'))%I.
  Proof.
    iIntros "trips [HR HP]".
    iApply (wp_frame_l _ _ (MkConf s δ) (fun v => match v with MkValConf _ v δ' => Q v δ' end) R).
    iFrame.
    by iApply "trips".
  Qed.

  Lemma iris_rule_pull {σ Γ} (δ : CStore Γ) (s : Stm Γ σ)
        (P : iProp Σ) (Q : Prop) (R : Val σ -> CStore Γ -> iProp Σ) :
        (⊢ (⌜ Q ⌝ → semTriple δ P s R) -∗ semTriple δ (P ∧ bi_pure Q) s R)%I.
  Proof.
    iIntros "QP [P %]".
    by iApply "QP".
  Qed.

  Lemma iris_rule_exist {σ Γ} (δ : CStore Γ)
        (s : Stm Γ σ) {A : Type} {P : A -> iProp Σ}
        {Q :  Val σ -> CStore Γ -> iProp Σ} :
        ⊢ ((∀ x, semTriple δ (P x) s Q) -∗ semTriple δ (∃ x, P x) s Q)%I.
  Proof.
    iIntros "trips Px".
    iDestruct "Px" as (x) "Px".
    by iApply "trips".
  Qed.

  Lemma iris_rule_stm_val {Γ} (δ : CStore Γ)
        {τ : Ty} {v : Val τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q v δ)%I -∗ semTriple δ P (stm_val τ v) Q)%I.
  Proof.
    iIntros "PQ P".
    iApply semWP_val.
    by iApply "PQ".
  Qed.

  Lemma iris_rule_stm_exp {Γ} (δ : CStore Γ)
        {τ : Ty} {e : Exp Γ τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q (eval e δ) δ) -∗ semTriple δ P (stm_exp e) Q)%I.
  Proof.
    iIntros "PQ P".
    iApply semWP_exp.
    now iApply "PQ".
  Qed.

  Lemma iris_rule_stm_let {Γ} (δ : CStore Γ)
        (x : PVar) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
                     (∀ (v : Val σ) (δ' : CStore Γ),
                         semTriple (env.snoc δ' (x∷σ) v) (Q v δ') k (fun v δ'' => R v (env.tail δ'')) ) -∗
                     semTriple δ P (let: x := s in k) R).
  Proof.
    iIntros "trips tripk P".
    iApply semWP_let.
    iSpecialize ("trips" with "P").
    by iApply (semWP_mono with "trips").
  Qed.

  Lemma iris_rule_stm_block {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStore Δ)
        (τ : Ty) (k : Stm (Γ ▻▻ Δ) τ)
        (P : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple (δ ►► δΔ) P k (fun v δ'' => R v (env.drop Δ δ'')) -∗
                   semTriple δ P (stm_block δΔ k) R)%I.
  Proof.
    iIntros "tripk P". iPoseProof ("tripk" with "P") as "wpk".
    by iApply semWP_block.
  Qed.

  Lemma iris_rule_stm_if {Γ} (δ : CStore Γ)
    (τ : Ty) (e : Exp Γ ty.bool) (s1 s2 : Stm Γ τ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (⌜ eval e δ = true ⌝ → semTriple δ P s1 Q) -∗
      (⌜ eval e δ = false ⌝ → semTriple δ P s2 Q) -∗
      semTriple δ P (stm_if e s1 s2) Q.
  Proof.
    iIntros "trips1 trips2 P".
    iApply semWP_if.
    destruct eval.
    - by iApply "trips1".
    - by iApply "trips2".
  Qed.

  Lemma iris_rule_stm_seq {Γ} (δ : CStore Γ)
        (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
        (P : iProp Σ) (Q : CStore Γ -> iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P s1 (fun _ => Q) -∗
                 (∀ δ', semTriple δ' (Q δ') s2 R) -∗
                 semTriple δ P (s1 ;; s2) R)%I.
  Proof.
    iIntros "trips1 trips2 P".
    iSpecialize ("trips1" with "P").
    iApply semWP_seq.
    iApply (semWP_mono with "trips1").
    by iFrame.
  Qed.

  Lemma iris_rule_stm_assertk {Γ τ} (δ : CStore Γ)
        (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ)
                      (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (⌜ eval e1 δ = true ⌝ → semTriple δ P k Q) -∗
      semTriple δ P (stm_assertk e1 e2 k) Q.
  Proof.
    iIntros "tripk P".
    iApply semWP_assertk.
    iIntros (->).
    by iApply "tripk".
  Qed.

  Lemma iris_rule_stm_fail {Γ} (δ : CStore Γ)
        (τ : Ty) (s : Val ty.string) :
        forall (Q : Val τ -> CStore Γ -> iProp Σ),
          ⊢ semTriple δ True%I (stm_fail τ s) Q.
  Proof.
    iIntros (Q) "_".
    by iApply semWP_fail.
  Qed.

  Lemma iris_rule_stm_match_list {Γ} (δ : CStore Γ)
        {σ τ : Ty} (e : Exp Γ (ty.list σ)) (alt_nil : Stm Γ τ)
        (xh xt : PVar) (alt_cons : Stm (Γ ▻ xh∷σ ▻ xt∷ty.list σ) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (⌜ eval e δ = nil ⌝ → semTriple δ P alt_nil (fun v' δ' => Q v' δ')) -∗
          (∀ (v : Val σ) (vs : Val (ty.list σ)),
              ⌜ eval e δ = cons v vs ⌝ →
              semTriple δ.[xh∷σ ↦ v].[xt∷ty.list σ ↦ vs] P alt_cons
                (fun v' δ' => Q v' (env.tail (env.tail δ')))) -∗
          semTriple δ P (stm_match_list e alt_nil xh xt alt_cons) Q.
  Proof.
    iIntros "tripnil tripcons P".
    iApply semWP_match_list.
    destruct eval as [|l ls].
    - by iApply "tripnil".
    - by iApply "tripcons".
  Qed.

  Lemma iris_rule_stm_match_sum {Γ} (δ : CStore Γ)
        (σinl σinr τ : Ty) (e : Exp Γ (ty.sum σinl σinr))
        (xinl : PVar) (alt_inl : Stm (Γ ▻ xinl∷σinl) τ)
        (xinr : PVar) (alt_inr : Stm (Γ ▻ xinr∷σinr) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ ((∀ (v : Val σinl), ⌜ eval e δ = inl v ⌝ → semTriple (env.snoc δ (xinl∷σinl) v) P alt_inl (fun v' δ' => Q v' (env.tail δ'))) -∗
           (∀ (v : Val σinr), ⌜ eval e δ = inr v ⌝ → semTriple (env.snoc δ (xinr∷σinr) v) P alt_inr (fun v' δ' => Q v' (env.tail δ'))) -∗
        semTriple δ P (stm_match_sum e xinl alt_inl xinr alt_inr) Q)%I.
  Proof.
    iIntros "tripinl tripinr P".
    iApply semWP_match_sum.
    destruct eval.
    - by iApply "tripinl".
    - by iApply "tripinr".
  Qed.

  Lemma iris_rule_stm_match_prod {Γ} (δ : CStore Γ)
        {σ1 σ2 τ : Ty} (e : Exp Γ (ty.prod σ1 σ2))
        (xl xr : PVar) (rhs : Stm (Γ ▻ xl∷σ1 ▻ xr∷σ2) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ ((∀ (vl : Val σ1) (vr : Val σ2), ⌜ eval e δ = (vl,vr) ⌝ →
            semTriple (env.snoc (env.snoc δ (xl∷σ1) vl) (xr∷σ2) vr)
              P rhs (fun v δ' => Q v (env.tail (env.tail δ')))) -∗
          semTriple δ P (stm_match_prod e xl xr rhs) Q)%I.
  Proof.
    iIntros "trippair P".
    iApply semWP_match_prod.
    destruct eval.
    by iApply "trippair".
  Qed.

  Lemma iris_rule_stm_match_enum {Γ} (δ : CStore Γ)
        {E : enumi} (e : Exp Γ (ty.enum E)) {τ : Ty}
        (alts : forall (K : enumt E), Stm Γ τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P (alts (eval e δ)) Q -∗
          semTriple δ P (stm_match_enum E e alts) Q)%I.
  Proof.
    iIntros "tripalt P".
    iApply semWP_match_enum.
    by iApply "tripalt".
  Qed.

  Lemma iris_rule_stm_match_tuple {Γ} (δ : CStore Γ)
        {σs : Ctx Ty} {Δ : PCtx} (e : Exp Γ (ty.tuple σs))
        (p : TuplePat σs Δ) {τ : Ty} (rhs : Stm (Γ ▻▻ Δ) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ ((semTriple (env.cat δ (tuple_pattern_match_val p (eval e δ))) P rhs (fun v δ' => Q v (env.drop Δ δ'))) -∗
       semTriple δ P (stm_match_tuple e p rhs) Q)%I.
  Proof.
    iIntros "triptup P".
    iApply semWP_match_tuple.
    by iApply "triptup".
  Qed.

  Lemma iris_rule_stm_match_union {Γ} (δ : CStore Γ)
        {U : unioni} (e : Exp Γ (ty.union U)) {τ : Ty}
        (alt__Δ : forall (K : unionk U), PCtx)
        (alt__p : forall (K : unionk U), Pattern (alt__Δ K) (unionk_ty U K))
        (alt__r : forall (K : unionk U), Stm (Γ ▻▻ alt__Δ K) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ ((∀ (K : unionk U) (v : Val (unionk_ty U K)),
               ⌜eval e δ = unionv_fold U (existT K v)⌝ →
               semTriple (env.cat δ (pattern_match_val (alt__p K) v)) P (alt__r K) (fun v δ' => Q v (env.drop (alt__Δ K) δ'))) -∗
               semTriple δ P (stm_match_union U e alt__p alt__r) Q
          )%I.
  Proof.
    iIntros "tripunion P".
    iApply semWP_match_union.
    destruct unionv_unfold eqn:?.
    iApply "tripunion"; [|easy].
    now rewrite <- Heqs, unionv_fold_unfold.
  Qed.

  Lemma iris_rule_stm_match_record {Γ} (δ : CStore Γ)
        {R : recordi} {Δ : PCtx} (e : Exp Γ (ty.record R))
        (p : RecordPat (recordf_ty R) Δ) {τ : Ty} (rhs : Stm (Γ ▻▻ Δ) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ ((semTriple (env.cat δ (record_pattern_match_val p (eval e δ))) P rhs (fun v δ' => Q v (env.drop Δ δ'))) -∗
        semTriple δ P (stm_match_record R e p rhs) Q)%I.
  Proof.
    iIntros "triprec P".
    iApply semWP_match_record.
    by iApply "triprec".
  Qed.

  Lemma iris_rule_stm_match_bvec {Γ} (δ : CStore Γ)
        {n : nat} (e : Exp Γ (ty.bvec n)) {τ : Ty}
        (rhs : forall (v : bv n), Stm Γ τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P (rhs (eval e δ)) Q -∗
          semTriple δ P (stm_match_bvec n e rhs) Q)%I.
  Proof.
    iIntros "triprhs P".
    iApply semWP_match_bvec.
    by iApply "triprhs".
  Qed.

  Lemma iris_rule_stm_match_bvec_split {Γ} (δ : CStore Γ)
        {m n : nat} (e : Exp Γ (ty.bvec (m + n))) {τ : Ty}
        (xl xr : PVar) (rhs : Stm (Γ ▻ xl∷ty.bvec m ▻ xr∷ty.bvec n) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ ((∀ vl vr,
           ⌜ eval e δ = bv.app vl vr ⌝ →
           semTriple (env.snoc (env.snoc δ (xl∷ty.bvec m) vl) (xr∷ty.bvec n) vr)
             P rhs (fun v δ' => Q v (env.tail (env.tail δ')))) -∗
          semTriple δ P (stm_match_bvec_split m n e xl xr rhs) Q)%I.
  Proof.
    iIntros "triprhs P".
    iApply semWP_match_bvec_split.
    destruct bv.appView.
    by iApply "triprhs".
  Qed.

  Lemma iris_rule_stm_read_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
        ⊢ (semTriple δ (lptsreg r v) (stm_read_register r) (fun v' δ' => ⌜ δ' = δ ⌝ ∧ ⌜ v' = v ⌝ ∧ lptsreg r v))%I.
  Proof.
    iIntros "Hreg".
    iApply semWP_read_register.
    iExists v.
    iFrame.
    iIntros "Hreg".
    repeat iSplit; auto.
  Qed.

  Lemma iris_rule_stm_write_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                              (Q : Val σ -> CStore Γ -> iProp Σ)
                              (v : Val σ) :
        ⊢ semTriple δ (lptsreg r v) (stm_write_register r w)
                  (fun v' δ' => ⌜δ' = δ⌝ ∧ ⌜v' = eval w δ⌝ ∧ lptsreg r v')%I.
  Proof.
    iIntros "Hreg".
    iApply semWP_write_register.
    iExists v.
    iFrame.
    iIntros "Hreg".
    repeat iSplit; auto.
  Qed.

  Lemma iris_rule_stm_assign {Γ} (δ : CStore Γ)
        (x : PVar) (σ : Ty) (xIn : x∷σ ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s (fun v δ' => R v (@env.update _ _ _ δ' (x∷_) _ v)) -∗
           semTriple δ P (stm_assign x s) R)%I.
  Proof.
    iIntros "trips P".
    iPoseProof ("trips" with "P") as "wpv".
    by iApply semWP_assign.
  Qed.

  Lemma iris_rule_stm_bind {Γ} (δ : CStore Γ)
        {σ τ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
           (∀ (v__σ : Val σ) (δ' : CStore Γ),
               semTriple δ' (Q v__σ δ') (k v__σ) R) -∗
           semTriple δ P (stm_bind s k) R)%I.
  Proof.
    iIntros "trips tripk P".
    iSpecialize ("trips" with "P").
    iApply semWP_bind.
    by iApply (semWP_mono with "trips").
  Qed.

  Lemma iris_rule_stm_call_inline_later
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ ▷ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
    iIntros "tripbody P".
    iApply semWP_call_inline_later.
    iModIntro.
    by iApply "tripbody".
  Qed.

  Lemma iris_rule_stm_call_inline
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
    iIntros "Hdef".
    iApply (iris_rule_stm_call_inline_later with "Hdef").
  Qed.

  Lemma iris_rule_stm_debugk
    {Γ τ} (δ : CStore Γ) (k : Stm Γ τ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P k Q -∗
       semTriple δ P (stm_debugk k) Q)%I.
  Proof.
    iIntros "tripk P".
    unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    dependent elimination H.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    iApply "tripk".
    by iFrame.
  Qed.

  Lemma iris_rule_noop {Γ σ} {δ : CStore Γ}
        {P} {Q : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
    language.to_val (MkConf s δ) = None ->
    (forall {s' γ γ' μ μ' δ'}, ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩ ->
                            (γ' = γ) /\ (μ' = μ) /\ (δ' = δ) /\
                            ((exists v, s' = stm_val _ v) \/ (exists msg, s' = stm_fail _ msg))) ->
    (∀ v, P ={⊤}=∗ Q v δ) -∗
                 semTriple δ P s Q.
  Proof.
    iIntros (Hnv Hnoop) "HPQ HP".
    unfold semWP. rewrite wp_unfold.
    unfold wp_pre.
    rewrite Hnv. cbn.
    iIntros (σ' ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first done.
    iIntros (e2 σ'' efs) "%".
    dependent elimination H.
    destruct (Hnoop _ _ _ _ _ _ s0) as (-> & -> & -> & [[v ->]|[msg ->]]).
    - do 3 iModIntro.
      iMod "Hclose" as "_".
      iMod ("HPQ" with "HP") as "HQ".
      iModIntro.
      iFrame.
      iSplitL; trivial.
      now iApply wp_value.
    - do 3 iModIntro.
      iMod "Hclose" as "_".
      iModIntro.
      iFrame.
      iSplitL; trivial.
      now iApply semWP_fail.
  Qed.

  Definition ValidContractSemCurried {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    match contract with
    | MkSepContract _ _ ctxΣ θΔ pre result post =>
      sep.Forall (fun (ι : Valuation ctxΣ) =>
        semTriple (inst θΔ ι) (asn.interpret pre ι) body
                  (fun v δ' => asn.interpret post (env.snoc ι (result∷σ) v)))
    end%I.

  Definition ValidContractSem {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    match contract with
    | MkSepContract _ _ ctxΣ θΔ pre result post =>
      ∀ (ι : Valuation ctxΣ),
        semTriple (inst θΔ ι) (asn.interpret pre ι) body
                  (fun v δ' => asn.interpret post (env.snoc ι (result∷σ) v))
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
  (Import PLOG  : ProgramLogicOn B PROG SIG SPEC).

  Section WithSailGS.
  Import ProgramLogic.
  Context {Σ} {sG : sailGS Σ}.

  Definition ValidContractEnvSem (cenv : SepContractEnv) : iProp Σ :=
    (∀ σs σ (f : 𝑭 σs σ),
      match cenv σs σ f with
      | Some c => ValidContractSem (FunDef f) c
      | None => True
      end)%I.

  Definition ForeignSem :=
    ∀ (Γ : PCtx) (τ : Ty)
      (Δ : PCtx) f (es : NamedEnv (Exp Γ) Δ) (δ : CStore Γ),
      match CEnvEx f with
      | MkSepContract _ _ Σ' θΔ req result ens =>
        forall (ι : Valuation Σ'),
        evals es δ = inst θΔ ι ->
        ⊢ semTriple δ (asn.interpret req ι) (stm_foreign f es)
          (fun v δ' => asn.interpret ens (env.snoc ι (result∷τ) v) ∗ bi_pure (δ' = δ))
      end.

  Definition LemmaSem : Prop :=
    forall (Δ : PCtx) (l : 𝑳 Δ),
      ValidLemma (LEnv l).

  Lemma iris_rule_stm_call {Γ} (δ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (c : SepContract Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ)
    (Q : Val σ -> CStore Γ -> iProp Σ) :
    CEnv f = Some c ->
    CTriple P c (evals es δ) (fun v => Q v δ) ->
    ⊢ ▷ ValidContractEnvSem CEnv -∗
       semTriple δ P (stm_call f es) Q.
  Proof.
    iIntros (ceq ctrip) "cenv P".
    iApply semWP_call_inline_later.
    iModIntro.
    iSpecialize ("cenv" $! _ _ f).
    rewrite ceq. clear ceq.
    destruct c as [Σe δΔ req res ens]; cbn in *.
    iPoseProof (ctrip with "P") as (ι Heq) "[req consr]". clear ctrip.
    iPoseProof ("cenv" $! ι with "req") as "wpf0". rewrite Heq.
    iApply (semWP_mono with "wpf0").
    by iIntros (v _).
  Qed.

  Lemma iris_rule_stm_call_frame {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStore Δ) (τ : Ty) (s : Stm Δ τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δΔ P s (fun v _ => Q v δ) -∗
           semTriple δ P (stm_call_frame δΔ s) Q)%I.
  Proof.
    iIntros "trips P".
    iSpecialize ("trips" with "P").
    by iApply semWP_call_frame.
  Qed.

  Lemma iris_rule_stm_foreign
    {Γ} (δ : CStore Γ) {τ} {Δ} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ForeignSem ->
    CTriple P (CEnvEx f) (evals es δ) (λ v : Val τ, Q v δ) ->
    ⊢ semTriple δ P (stm_foreign f es) Q.
  Proof.
    iIntros (forSem ctrip) "P".
    specialize (forSem Γ τ Δ f es δ).
    destruct CEnvEx as [Σe δΔ req res ens]; cbn in *.
    iPoseProof (ctrip with "P") as "[%ι [%Heq [req consr]]]". clear ctrip.
    iPoseProof (forSem ι Heq with "req") as "WPf". clear forSem.
    iApply (semWP_mono with "WPf").
    iIntros (v δΓ') "[ens ->]".
    by iApply "consr".
  Qed.

  Lemma iris_rule_stm_lemmak
    {Γ} (δ : CStore Γ) {τ} {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ)
    (P Q : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
    LemmaSem ->
    LTriple (evals es δ) P Q (LEnv l) ->
    ⊢ semTriple δ Q k R -∗
      semTriple δ P (stm_lemmak l es k) R.
  Proof.
    iIntros (lemSem ltrip).
    specialize (lemSem _ l).
    revert ltrip lemSem.
    generalize (LEnv l) as contractL.
    intros contractL ltrip lemSem.
    iIntros "tripk P".
    unfold semWP. rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "Hregs".
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
    iApply "tripk".
    dependent elimination ltrip; cbn in lemSem.
    iPoseProof (l with "P") as (ι Heq) "[req consr]". clear l.
    iApply "consr".
    by iApply lemSem.
  Qed.

  Lemma iris_rule_stm_match_pattern {Γ τ Δ σ} (δΓ : CStore Γ) (s : Stm Γ σ)
    (pat : Pattern Δ σ) (rhs : Stm (Γ ▻▻ Δ) τ) (P : iProp Σ)
    (Q : Val σ → CStore Γ → iProp Σ) (R : Val τ → CStore Γ → iProp Σ) :
    ⊢ semTriple δΓ P s Q -∗
      (∀ (x : Val σ) (x0 : Env (λ xt : PVar∷Ty, Val (type xt)) Γ),
         semTriple (x0 ►► pattern_match_val pat x) (Q x x0) rhs
           (λ (v2 : Val τ) (δ' : CStore (Γ ▻▻ Δ)), R v2 (env.drop Δ δ'))) -∗
      semTriple δΓ P (stm_match_pattern s pat rhs) R.
  Proof.
    iIntros "WPs WPrhs P".
    iSpecialize ("WPs" with "P").
    iApply semWP_match_pattern.
    by iApply (semWP_mono with "WPs").
  Qed.

  Lemma sound_stm
    {Γ} {τ} (s : Stm Γ τ) {δ : CStore Γ}:
    forall (PRE : iProp Σ) (POST : Val τ -> CStore Γ -> iProp Σ),
      ForeignSem ->
      LemmaSem ->
      ⦃ PRE ⦄ s ; δ ⦃ POST ⦄ ->
      ⊢ (□ ▷ ValidContractEnvSem CEnv -∗
          semTriple δ PRE s POST)%I.
  Proof.
    iIntros (PRE POST extSem lemSem triple) "#vcenv".
    iInduction triple as [x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x] "trips".
    - by iApply iris_rule_consequence.
    - by iApply iris_rule_frame.
    - by iApply iris_rule_pull.
    - by iApply iris_rule_exist.
    - iApply iris_rule_stm_val.
      by iApply H.
    - iApply iris_rule_stm_exp.
      by iApply H.
    - by iApply iris_rule_stm_let.
    - by iApply iris_rule_stm_block.
    - by iApply iris_rule_stm_if.
    - by iApply iris_rule_stm_seq.
    - by iApply iris_rule_stm_assertk.
    - by iApply iris_rule_stm_fail.
    - by iApply iris_rule_stm_match_list.
    - by iApply iris_rule_stm_match_sum.
    - by iApply iris_rule_stm_match_prod.
    - by iApply iris_rule_stm_match_enum.
    - by iApply iris_rule_stm_match_tuple.
    - by iApply iris_rule_stm_match_union.
    - by iApply iris_rule_stm_match_record.
    - by iApply iris_rule_stm_match_bvec.
    - by iApply iris_rule_stm_match_bvec_split.
    - by iApply iris_rule_stm_read_register.
    - by iApply iris_rule_stm_write_register.
    - by iApply iris_rule_stm_assign.
    - by iApply iris_rule_stm_call.
    - by iApply iris_rule_stm_call_inline.
    - by iApply iris_rule_stm_call_frame.
    - by iApply iris_rule_stm_foreign.
    - by iApply iris_rule_stm_lemmak.
    - by iApply iris_rule_stm_bind.
    - by iApply iris_rule_stm_debugk.
    - by iApply iris_rule_stm_match_pattern.
  Qed.

  Lemma sound :
    ForeignSem -> LemmaSem -> ValidContractCEnv ->
    ⊢ ValidContractEnvSem CEnv.
  Proof.
    intros extSem lemSem vcenv.
    iLöb as "IH".
    iIntros (σs σ f).
    specialize (vcenv σs σ f).
    destruct (CEnv f) as [[]|];[|trivial].
    specialize (vcenv _ eq_refl).
    iIntros (ι).
    iApply (sound_stm extSem lemSem); [|trivial].
    apply (vcenv ι).
  Qed.

  End WithSailGS.
End IrisInstanceWithContracts.
