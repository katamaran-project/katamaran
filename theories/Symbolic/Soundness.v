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

From Coq Require Import
     Bool.Bool
     Program.Tactics
     ZArith.ZArith
     Strings.String
     Classes.Morphisms
     Classes.RelationClasses
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.
Require Import Basics.

From Coq Require Lists.List.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Signature
     Shallow.Executor
     Specification
     Symbolic.Executor
     Program
     Tactics.

Set Implicit Arguments.

Import ctx.notations.
Import env.notations.

Module Soundness
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG)
  (Import SHAL : ShallowExecOn B SIG PROG SPEC)
  (Import SYMB : SymbolicExecOn B SIG PROG SPEC).

  Import ModalNotations.
  Import SymProp.
  Import logicalrelation logicalrelation.notations.
  Import LogicalSoundness.
  Import proofmode.
  Import iris.proofmode.environments.
  Import iris.proofmode.tactics.

  Ltac rsolve_step :=
    first [
        (lazymatch goal with
         | |- envs_entails _ (ℛ⟦□ᵣ _⟧ _ _) => iIntros (? ?) "!>"
         | |- envs_entails _ (ℛ⟦_ -> _⟧ _ _) => iIntros (? ?) "#?"
         end)
      | lazymatch goal with
        | |- envs_entails _ (ℛ⟦ ?R ⟧ ?v ?vs) =>
            (iApply (refine_compat_lemma (R := R) (vs := vs));
             lazymatch goal with | |- RefineCompat _ _ _ _ _ => fail | _ => idtac end
            )
        | |- envs_entails _ (_ ∗ _) => iSplit
        | |- envs_entails _ (unconditionally _) => iIntros (? ?) "!>"
        end
      ].

  Ltac rsolve :=
    iStartProof;
    repeat rsolve_step; try done;
    (* After walking through the symbolic computation using the above lemmas,
     * we try to apply induction hypotheses.
     * To do this, we determine the right world to apply the IH in by looking at the current goal.
     *)
    repeat match goal with
      | H : (forall (w : World), _) |- @envs_entails (@bi_pred ?w) _ _ => specialize (H w)
      | H : (forall (w : World), _) |- @envs_entails _ _ (@logicalrelation.RSat _ _ _ _ ?w _) => specialize (H w)
      | H : ⊢ ?P |- envs_entails _ ?P => (try iApply H); clear H
      end.

  Ltac rsolve2_step :=
    first [
        (lazymatch goal with
         | |- envs_entails _ (ℛ⟦□ᵣ _⟧ _ _) => iIntros (? ?) "!>"
         | |- envs_entails _ (ℛ⟦_ -> _⟧ _ _) => iIntros (? ?) "#?"
         end)
      | lazymatch goal with
        | |- envs_entails _ ?P => iApply (refine_compat_gen_lemma P true)
        | |- envs_entails _ (unconditionally _) => iIntros (? ?) "!>"
        end
      ].

  Ltac rsolve2 :=
    iStartProof;
    progress rsolve2_step; try done;
    (* After walking through the symbolic computation using the above lemmas,
     * we try to apply induction hypotheses.
     * To do this, we determine the right world to apply the IH in by looking at the current goal.
     *)
    repeat match goal with
      | H : (forall (w : World), _) |- @envs_entails (@bi_pred ?w) _ _ => specialize (H w)
      | H : (forall (w : World), _) |- @envs_entails _ _ (@logicalrelation.RSat _ _ _ _ ?w _) => specialize (H w)
      | H : ⊢ ?P |- envs_entails _ ?P => (try iApply H); clear H
      end.

  Definition RStore (Γ : PCtx) : Rel (SStore Γ) (CStore Γ) :=
    RInst (SStore Γ) (CStore Γ).

  Definition RStoreSpec Γ1 Γ2 `(R : Rel AT A) :
    Rel (SStoreSpec Γ1 Γ2 AT) (CStoreSpec Γ1 Γ2 A) :=
    □ᵣ (R -> RStore Γ2 -> RHeap -> ℙ) -> RStore Γ1 -> RHeap -> ℙ.

  Definition RefineExecCall (cexec_call : SHAL.ExecCall) (sexec_call : SYMB.ExecCall) : Prop :=
    ∀ Δ τ (f : 𝑭 Δ τ) w,
      ⊢ ℛ⟦RStore Δ -> RHeapSpec (RVal τ)⟧ (cexec_call Δ τ f) (sexec_call Δ τ f w).
  Definition RefineExecCallForeign (cexec_call_foreign : SHAL.ExecCallForeign)
    (sexec_call_foreign : SYMB.ExecCallForeign) : Prop :=
    ∀ Δ τ (f : 𝑭𝑿 Δ τ) w,
      ⊢ ℛ⟦RStore Δ -> RHeapSpec (RVal τ)⟧ (cexec_call_foreign Δ τ f) (sexec_call_foreign Δ τ f w).
  Definition RefineExecLemma (cexec_lemma : SHAL.ExecLemma) (sexec_lemma : SYMB.ExecLemma) : Prop :=
    ∀ Δ (l : 𝑳 Δ) w,
      ⊢ ℛ⟦RStore Δ -> RHeapSpec RUnit⟧ (cexec_lemma Δ l) (sexec_lemma Δ l w).
  Definition RefineExec (cexec : SHAL.Exec) (sexec : SYMB.Exec) : Prop :=
    ∀ Γ τ (s : Stm Γ τ) w,
      ⊢ ℛ⟦RStoreSpec Γ Γ (RVal τ)⟧ (cexec Γ τ s) (sexec Γ τ s w).

  Module StoreSpec.
    Import PureSpec.
    Import HeapSpec.

    Lemma refine_evalStoreSpec {Γ1 Γ2} `{RA : Rel SA CA} {w : World} :
      ⊢ (ℛ⟦RStoreSpec Γ1 Γ2 RA -> RStore Γ1 -> RHeapSpec RA⟧
           CStoreSpec.evalStoreSpec (fun w => SStoreSpec.evalStoreSpec w) : Pred w).
    Proof.
      unfold SStoreSpec.evalStoreSpec, CStoreSpec.evalStoreSpec.
      iIntros (ss tss) "Hss".
      iIntros (s ts) "Hs".
      iIntros (k ks) "Hk".
      iIntros (h hs) "Hh".
      iIntros "Hsym".
      iApply ("Hss" with "[Hk] Hs Hh Hsym").
      iIntros (w' ω).
      iSpecialize ("Hk" $! _ ω).
      iModIntro.
      iIntros (a ta) "Ha".
      iIntros (s2 ts2) "Hs2".
      iIntros (h2 th2) "Hh2".
      now iApply ("Hk" with "Ha Hh2").
    Qed.

    Lemma refine_lift_purespec {Γ} `(R : Rel AT A) {w : World}:
      ⊢ ℛ⟦RPureSpec R -> RStoreSpec Γ Γ R⟧
        CStoreSpec.lift_purespec (SStoreSpec.lift_purespec (w := w)).
    Proof.
      unfold RPureSpec, RStoreSpec, SStoreSpec.lift_purespec, CStoreSpec.lift_purespec.
      iIntros (p ps) "Hp".
      iIntros (k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh".
      iApply "Hp".
      iIntros (w' ω).
      iSpecialize ("Hk" $! _ ω).
      iModIntro.
      iIntros (k2 k2s) "Hk2".
      iApply ("Hk" with "Hk2 [Hs]").
      - now iApply (refine_inst_persist with "Hs").
      - rewrite !RList_RInst.
        now iApply (refine_inst_persist with "Hh").
    Qed.

    Lemma refine_lift_heapspec {Γ} `(R : Rel AT A) {w : World}:
      ⊢ ℛ⟦RHeapSpec R -> RStoreSpec Γ Γ R⟧
          CStoreSpec.lift_heapspec (SStoreSpec.lift_heapspec (w := w)).
    Proof.
      unfold RHeapSpec, RStoreSpec, SStoreSpec.lift_heapspec, CStoreSpec.lift_heapspec.
      iIntros (p ps) "Hp".
      iIntros (k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh".
      iApply ("Hp" with "[Hk Hs] Hh").
      iIntros (w1 θ1).
      iSpecialize ("Hk" $! _ θ1).
      iModIntro.
      iIntros (k2 k2s) "Hk2".
      iApply ("Hk" with "Hk2 [Hs]").
      now iApply (refine_inst_persist with "Hs").
    Qed.

    Lemma refine_block {Γ1 Γ2} `{R : Rel AT A} {w : World} :
      ⊢ ℛ⟦RStoreSpec Γ1 Γ2 R⟧ CStoreSpec.block (SStoreSpec.block (w := w)).
    Proof.
      iIntros (k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh _".
      now iPureIntro.
    Qed.

    Lemma refine_error `{Subst M, OccursCheck M, R : Rel AT A} {Γ1 Γ2} {w : World} :
      forall (cm : CStoreSpec Γ1 Γ2 A),
        ⊢ ℛ⟦RMsg _ (RStoreSpec Γ1 Γ2 R)⟧ cm (SStoreSpec.error (w := w)).
    Proof.
      iIntros (cm msg k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh []".
    Qed.

    (* Disable refine_compat_msg because it gets spuriously searched very often during instance search and is only used in refine_compat_error.
     * Better to integrate into refine_compat_error.
     *)
    (* #[export] Program Instance refine_compat_msg `{R : Rel AT A} {M v w vs msg Ob} *)
    (*   (compatf : RefineCompat (RMsg M R) v w vs Ob) : RefineCompat R v w (vs msg) Ob | 4 := *)
    (*   MkRefineCompat _. *)
    (* Next Obligation. *)
    (*   iIntros (AT A R M v w vs msg Ob compatf) "Hcf". *)
    (*   iApply (refine_compat_lemma compatf with "Hcf"). *)
    (* Qed. *)

    (* #[export] Instance refine_compat_error `{Subst M, OccursCheck M, R : Rel AT A} {Γ1 Γ2} {w : World} {cm : CStoreSpec Γ1 Γ2 A} : *)
    (*   RefineCompat (RMsg _ (RStoreSpec Γ1 Γ2 R)) cm w (SStoreSpec.error (w := w)) _ := *)
    (*   MkRefineCompat (refine_error cm). *)

    #[export] Program Instance refine_compat_error `{Subst M, OccursCheck M, R : Rel AT A} {Γ1 Γ2} {w : World} {cm : CStoreSpec Γ1 Γ2 A} {msg} :
      RefineCompat (RStoreSpec Γ1 Γ2 R) cm w (SStoreSpec.error (w := w) msg) emp :=
      MkRefineCompat _.
    Next Obligation.
       iIntros (M HsubstM HocM AT A R Γ1 Γ2 w cm msg) "_".
       now iApply refine_error.
    Qed.


    Lemma refine_pure `{R : Rel AT A} {Γ} {w : World} :
      ⊢ ℛ⟦R -> RStoreSpec Γ Γ R⟧ CStoreSpec.pure (SStoreSpec.pure (w := w)).
    Proof.
      unfold SStoreSpec.pure, CStoreSpec.pure.
      iIntros (r rs) "Hr".
      iIntros (k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh HPS".
      iMod "Hk".
      now iApply ("Hk" with "Hr Hs Hh HPS").
    Qed.

    Lemma refine_bind `{RA : Rel AT A, RB : Rel BT B} {Γ1 Γ2 Γ3} {w : World} :
      ⊢ ℛ⟦RStoreSpec Γ1 Γ2 RA -> □ᵣ(RA -> RStoreSpec Γ2 Γ3 RB) -> RStoreSpec Γ1 Γ3 RB⟧
        CStoreSpec.bind (SStoreSpec.bind (w := w)).
    Proof.
      unfold SStoreSpec.bind, CStoreSpec.bind.
      iIntros (m ms) "Hm".
      iIntros (c cs) "Hc".
      iIntros (k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh HPS".
      iApply ("Hm" with "[Hk Hc] Hs Hh HPS").
      iIntros (w' ω).
      iModIntro.
      iIntros (a aas) "Ha".
      iIntros (s2 s2s) "Hs".
      iIntros (h2 h2s) "Hh".
      iApply ("Hc" with "Ha [Hk] Hs Hh").
      now iApply (refine_four with "Hk").
    Qed.

    Lemma refine_angelic (x : option LVar) {Γ} {w : World} :
      ⊢ ℛ⟦∀ᵣ σ, RStoreSpec Γ Γ (RVal σ)⟧ CStoreSpec.angelic (SStoreSpec.angelic (w := w) x).
    Proof.
      unfold SStoreSpec.angelic, CStoreSpec.angelic.
      iIntros (σ).
      iApply (refine_lift_purespec (RVal σ)).
      now iApply PureSpec.refine_angelic.
    Qed.

    Lemma refine_demonic (x : option LVar) {Γ} {w : World} :
      ⊢ ℛ⟦∀ᵣ σ, RStoreSpec Γ Γ (RVal σ)⟧ CStoreSpec.demonic (SStoreSpec.demonic (w := w) x).
    Proof.
      unfold SStoreSpec.demonic, CStoreSpec.demonic.
      iIntros (σ).
      iApply (refine_lift_purespec (RVal σ)).
      now iApply PureSpec.refine_demonic.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} {Γ} {w} :
      ⊢ ℛ⟦∀ᵣ Δ, RStoreSpec Γ Γ (RNEnv N Δ)⟧
        CStoreSpec.angelic_ctx (SStoreSpec.angelic_ctx (w := w) n).
    Proof.
      unfold SStoreSpec.angelic_ctx, CStoreSpec.angelic_ctx.
      iIntros (Δ).
      iApply (refine_lift_purespec (RNEnv N Δ)).
      iApply PureSpec.refine_angelic_ctx.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} {Γ} {w} :
      ⊢ ℛ⟦∀ᵣ Δ, RStoreSpec Γ Γ (RNEnv N Δ)⟧
        CStoreSpec.demonic_ctx (SStoreSpec.demonic_ctx (w := w) n).
    Proof.
      unfold SStoreSpec.demonic_ctx, CStoreSpec.demonic_ctx.
      iIntros (Δ).
      iApply (refine_lift_purespec (RNEnv N Δ)).
      iApply PureSpec.refine_demonic_ctx.
    Qed.

    Lemma refine_debug `{R : Rel AT A}
      {Γ1 Γ2} {w0 : World} {f ms mc} :
      ℛ⟦RStoreSpec Γ1 Γ2 R⟧ mc ms ⊢
                   ℛ⟦RStoreSpec Γ1 Γ2 R⟧ mc (@SStoreSpec.debug AT Γ1 Γ2 w0 f ms).
    Proof.
      iIntros "Hm %K %Ks HK %s %ss Hs %h %hs Hh HSP".
      iApply ("Hm" with "HK Hs Hh [HSP]").
      now iApply elim_debugPred.
    Qed.

    Lemma refine_angelic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} {w} :
      ⊢ ℛ⟦RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R⟧
        CStoreSpec.angelic_binary (SStoreSpec.angelic_binary (w := w)).
    Proof.
      iIntros (c1 cs1) "Hc1 %c2 %cs2 Hc2 %K %Ks #HK %s %ss #Hs %h %hs #Hh".
      unfold SStoreSpec.angelic_binary, CStoreSpec.angelic_binary.
      iApply (refine_symprop_angelic_binary with "[Hc1] [Hc2]").
      - now iApply "Hc1".
      - now iApply "Hc2".
    Qed.

    Lemma refine_demonic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} {w} :
      ⊢ ℛ⟦RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R⟧
        CStoreSpec.demonic_binary (SStoreSpec.demonic_binary (w := w)).
    Proof.
      iIntros (c1 cs1) "Hc1 %c2 %cs2 Hc2 %K %Ks #HK %s %ss #Hs %h %hs #Hh".
      unfold SStoreSpec.angelic_binary, CStoreSpec.angelic_binary.
      iApply (refine_symprop_demonic_binary with "[Hc1] [Hc2]").
      - now iApply "Hc1".
      - now iApply "Hc2".
    Qed.

    Section BasicsCompatLemmas.
      Import logicalrelation.

      #[export] Instance refine_compat_evalStoreSpec {Γ1 Γ2} `{RA : Rel SA CA} {w : World} :
        RefineCompat (RStoreSpec Γ1 Γ2 RA -> RStore Γ1 -> RHeapSpec RA)
          CStoreSpec.evalStoreSpec w (SStoreSpec.evalStoreSpec (w := w)) emp :=
        MkRefineCompat (refine_evalStoreSpec).

      #[export] Instance refine_compat_lift_heapspec {Γ} `(R : Rel AT A) {w : World}:
        RefineCompat (RHeapSpec R -> RStoreSpec Γ Γ R)
            CStoreSpec.lift_heapspec w (SStoreSpec.lift_heapspec (w := w)) emp :=
        MkRefineCompat (refine_lift_heapspec R).

      #[export] Instance refine_compat_block {Γ1 Γ2} `{R : Rel AT A} {w : World} :
        RefineCompat (RStoreSpec Γ1 Γ2 R) CStoreSpec.block w (SStoreSpec.block (w := w)) _ :=
        MkRefineCompat refine_block.

      #[export] Instance refine_compat_pure {Γ : PCtx} `{R : Rel AT A} {w} : RefineCompat (R -> RStoreSpec Γ Γ R) CStoreSpec.pure w (SStoreSpec.pure (w := w)) _ :=
        MkRefineCompat (refine_pure (R := R)).

      #[export] Instance refine_compat_bind {Γ1 Γ2 Γ3 : PCtx} `{RA : Rel AT A} `{RB : Rel BT B} {w} : RefineCompat (RStoreSpec Γ1 Γ2 RA -> (□ᵣ (RA -> RStoreSpec Γ2 Γ3 RB)) -> RStoreSpec Γ1 Γ3 RB) CStoreSpec.bind w (SStoreSpec.bind (w := w)) _ | (RefineCompat _ _ _ SStoreSpec.bind _) :=
        MkRefineCompat refine_bind.

      #[export] Program Instance refine_compat_angelic (x : option LVar) {Γ} {w : World} {σ}:
        RefineCompat (RStoreSpec Γ Γ (RVal σ)) (CStoreSpec.angelic σ) w (SStoreSpec.angelic (w := w) x σ) emp :=
        MkRefineCompat _.
      Next Obligation.
        iIntros (? ? ? ?) "_".
        iApply refine_angelic.
      Qed.

      #[export] Program Instance refine_compat_demonic (x : option LVar) {Γ} {w : World} {σ} :
        RefineCompat (RStoreSpec Γ Γ (RVal σ)) (CStoreSpec.demonic σ) w (SStoreSpec.demonic (w := w) x σ) emp :=
        MkRefineCompat _.
      Next Obligation.
        iIntros (? ? ? ?) "_".
        iApply refine_demonic.
      Qed.

      #[export] Program Instance refine_compat_angelic_ctx {N : Set} {n : N -> LVar} {Γ} {w} {Δ}:
        RefineCompat (RStoreSpec Γ Γ (RNEnv N Δ)) (CStoreSpec.angelic_ctx Δ) w (SStoreSpec.angelic_ctx (w := w) n Δ) emp :=
        MkRefineCompat _.
      Next Obligation.
        iIntros (N n Γ w Δ) "_".
        now iApply refine_angelic_ctx.
      Qed.

      #[export] Program Instance refine_compat_demonic_ctx {N : Set} {n : N -> LVar} {Γ} {w} {Δ} :
        RefineCompat (RStoreSpec Γ Γ (RNEnv N Δ)) (CStoreSpec.demonic_ctx Δ) w (SStoreSpec.demonic_ctx (w := w) n Δ) emp :=
        MkRefineCompat _.
      Next Obligation.
        iIntros (N n Γ w Δ) "_".
        now iApply refine_demonic_ctx.
      Qed.

      #[export] Instance refine_compat_debug `{R : Rel AT A} {Γ1 Γ2} {w0 : World} {f} {mc ms} :
        RefineCompat (RStoreSpec Γ1 Γ2 R) mc w0 (@SStoreSpec.debug AT Γ1 Γ2 w0 f ms) _ :=
        MkRefineCompat refine_debug.

      #[export] Instance refine_compat_angelic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} {w} :
        RefineCompat (RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R) CStoreSpec.angelic_binary w (SStoreSpec.angelic_binary (w := w)) _ :=
        MkRefineCompat refine_angelic_binary.

      #[export] Instance refine_compat_demonic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} {w} :
        RefineCompat (RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R) CStoreSpec.demonic_binary w (SStoreSpec.demonic_binary (w := w)) _ :=
        MkRefineCompat refine_demonic_binary.

      Definition refine_compat_inst_subst {Σ} {T : LCtx -> Type} `{InstSubst T A} (vs : T Σ) {w : World} :
        RefineCompat (RInst (Sub Σ) (Valuation Σ) -> RInst T A) (inst vs) w (subst vs) _ :=
        MkRefineCompat (refine_inst_subst vs).
      Opaque refine_compat_inst_subst.

    End BasicsCompatLemmas.
    #[export] Hint Extern 0 (RefineCompat _ (inst ?vs) _ (subst ?vs) _) => refine (refine_compat_inst_subst vs) : typeclass_instances.

  Section PatternMatching.
    Import logicalrelation.

    Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : @Pattern N σ) {w} :
      ⊢ ℛ⟦RVal σ -> RStoreSpec Γ Γ (RMatchResult pat)⟧
        (CStoreSpec.demonic_pattern_match pat)
        (SStoreSpec.demonic_pattern_match (w := w) n pat).
    Proof.
      iIntros (v sv) "rv %Φ %sΦ rΦ %δ %sδ rδ %h %sh rh".
      unfold SStoreSpec.demonic_pattern_match, CStoreSpec.demonic_pattern_match,
               CStoreSpec.lift_purespec.
      iApply (PureSpec.refine_demonic_pattern_match with "rv").
      iIntros (w1 θ1) "!> %mr %smr rmr".
      iApply ("rΦ" with "rmr [rδ] [rh]").
      - iApply (refine_inst_persist with "rδ").
      - rewrite !RList_RInst.
        iApply (refine_inst_persist with "rh").
    Qed.
  End PatternMatching.

  Section PatternMatchingCompatLemmas.
    Import logicalrelation.

    #[export] Instance refine_compat_demonic_pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : @Pattern N σ) {w} :
      RefineCompat (RVal σ -> RStoreSpec Γ Γ (RMatchResult pat)) (CStoreSpec.demonic_pattern_match pat) w (SStoreSpec.demonic_pattern_match (w := w) n pat) _ :=
      MkRefineCompat (refine_demonic_pattern_match n pat).
  End PatternMatchingCompatLemmas.

  Section State.
    Import logicalrelation.
    Lemma refine_pushpop `{R : Rel AT A} {Γ1 Γ2 x σ} {w} :
      ⊢ ℛ⟦RVal σ -> RStoreSpec (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) R -> RStoreSpec Γ1 Γ2 R⟧
        CStoreSpec.pushpop (SStoreSpec.pushpop (w := w)).
    Proof.
      iIntros (v sv) "Hv %m %sm Hm %K %sK HK %δ %sδ Hδ %h %sh Hh".
      unfold SStoreSpec.pushpop, CStoreSpec.pushpop.
      iApply ("Hm" with "[HK] [Hδ Hv] Hh").
      - clear.
        iIntros (w2 ω2) "!> %v %sv Hv %δ %sδ Hδ".
        iApply ("HK" with "Hv").
        iApply (repₚ_cong (T1 := SStore (Γ2 ▻ x∷σ)) (T2 := SStore Γ2) env.tail env.tail with "Hδ").
        intros. now env.destroy vs1.
      - iApply (repₚ_cong₂ (T1 := SStore Γ1) (T2 := STerm σ) (T3 := SStore (Γ1 ▻ x∷σ)) (fun δ v => δ.[x∷σ ↦ v]) (w := w) (fun δ v => δ.[x∷σ ↦ v]) with "[$Hδ $Hv]").
        now intros.
    Qed.

    Lemma refine_pushspops `{R : Rel AT A} {Γ1 Γ2 Δ} {w} :
      ⊢ ℛ⟦RStore Δ -> RStoreSpec (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) R -> RStoreSpec Γ1 Γ2 R⟧
        CStoreSpec.pushspops (SStoreSpec.pushspops (w := w)).
    Proof.
      iIntros (c sc) "Hc %m %sm Hm %K %sK HK %δ %sδ Hδ %h %sh Hh".
      unfold SStoreSpec.pushspops, CStoreSpec.pushspops.
      iApply ("Hm" with "[HK] [Hδ Hc] Hh").
      - iIntros (w1 ω1) "!> %v %sv Hv %δ1 %sδ1 Hδ1 %h1 %sh1 Hh1".
        iApply ("HK" with "Hv [Hδ1] Hh1").
        iApply (repₚ_cong (T1 := SStore (Γ2 ▻▻ Δ)) (T2 := SStore Γ2) (env.drop Δ) (env.drop Δ) with "Hδ1").
        intros. env.destroy vs1.
        now rewrite inst_env_cat !env.drop_cat.
      - iApply (repₚ_cong₂ (T1 := SStore Γ1) (T2 := SStore Δ) (T3 := SStore (Γ1 ▻▻ Δ)) env.cat env.cat with "[$Hδ $Hc]").
        intros; now rewrite inst_env_cat.
    Qed.

    Lemma refine_get_local {Γ} {w} :
      ⊢ ℛ⟦RStoreSpec Γ Γ (RStore Γ)⟧ CStoreSpec.get_local (SStoreSpec.get_local (w := w)).
    Proof.
      iIntros (K sK) "HK %δ %sδ #Hδ %h %sh Hh".
      unfold SStoreSpec.get_local, CStoreSpec.get_local.
      now iApply (refine_T with "HK Hδ Hδ Hh").
    Qed.

    #[export] Instance refine_compat_get_local {Γ} {w} :
      RefineCompat (RStoreSpec Γ Γ (RStore Γ)) CStoreSpec.get_local w (SStoreSpec.get_local (w := w)) _ :=
      MkRefineCompat refine_get_local.

    Lemma refine_put_local {Γ1 Γ2} {w} :
      ⊢ ℛ⟦RStore Γ2 -> RStoreSpec Γ1 Γ2 RUnit⟧
        CStoreSpec.put_local (SStoreSpec.put_local (w := w)).
    Proof.
      iIntros (δ2 sδ2) "Hδ2 %K %sK HK %δ %sδ Hδ %h %sh Hh".
      unfold SStoreSpec.put_local, CStoreSpec.put_local.
      iApply (refine_T with "HK [//] Hδ2 Hh").
    Qed.

    #[export] Instance refine_compat_put_local {Γ1 Γ2} {w} :
      RefineCompat (RStore Γ2 -> RStoreSpec Γ1 Γ2 RUnit) CStoreSpec.put_local w (SStoreSpec.put_local (w := w)) _ :=
      MkRefineCompat refine_put_local.

    Lemma refine_peval {w : World} {σ} (t : STerm σ w) v :
      ℛ⟦RVal σ⟧ v t ⊢ ℛ⟦RVal σ⟧ v (peval t).
    Proof. unfold RVal, RInst. crushPredEntails3. now rewrite peval_sound. Qed.

    Lemma refine_seval_exp {Γ σ} (e : Exp Γ σ) {w : World} {δ} {sδ : SStore Γ w} :
      ℛ⟦ RStore Γ ⟧ δ sδ ⊢ ℛ⟦RVal σ⟧ (B.eval e δ) (seval_exp sδ e).
    Proof.
      unfold RStore, RVal, RInst. crushPredEntails3.
      rewrite <-eval_exp_inst.
      now subst.
    Qed.

    Lemma refine_seval_exps {Γ Δ : PCtx} {es : NamedEnv (Exp Γ) Δ} {w : World} {δ : CStore Γ} {sδ : SStore Γ w} :
      ℛ⟦RStore Γ⟧ δ sδ ⊢ ℛ⟦RStore Δ⟧ (evals es δ) (seval_exps sδ es).
    Proof.
      unfold RStore, RInst; cbn.
      crushPredEntails3.
      unfold seval_exps, inst, inst_store, inst_env, evals.
      rewrite env.map_map.
      apply env.map_ext.
      intros.
      rewrite peval_sound.
      now apply refine_seval_exp.
    Qed.

    Lemma refine_eval_exp {Γ σ} (e : Exp Γ σ) {w} :
        ⊢ ℛ⟦RStoreSpec Γ Γ (RVal σ)⟧ (CStoreSpec.eval_exp e) (SStoreSpec.eval_exp (w := w) e).
    Proof.
      iIntros (K sK) "HK %δ0 %sδ0 #Hδ0 %h0 %sh0 Hh0".
      unfold SStoreSpec.eval_exp, CStoreSpec.eval_exp.
      iApply (refine_T with "HK [Hδ0] Hδ0 Hh0").
      iApply refine_peval.
      now iApply refine_seval_exp.
    Qed.

    Lemma refine_eval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) {w} :
      ⊢ ℛ⟦RStoreSpec Γ Γ (RStore Δ)⟧
        (CStoreSpec.eval_exps es) (SStoreSpec.eval_exps (w := w) es).
    Proof.
      iIntros (K sK) "HK %δ0 %sδ0 #Hδ0 %h0 %sh0 Hh0".
      unfold SStoreSpec.eval_exps, CStoreSpec.eval_exps.
      iApply (refine_T with "HK [Hδ0] Hδ0 Hh0").
      now iApply refine_seval_exps.
    Qed.

    Lemma refine_env_update {Γ x σ} (xIn : (x∷σ ∈ Γ)%katamaran) (w : World)
      (t : Term w σ) (v : Val σ) (δs : SStore Γ w) (δc : CStore Γ) :
      ℛ⟦RVal σ⟧ v t ∗ ℛ⟦RStore Γ⟧ δc δs ⊢ ℛ⟦RStore Γ⟧ (δc ⟪ x ↦ v ⟫) (δs ⟪ x ↦ t ⟫).
    Proof.
      unfold RVal, RStore, RInst.
      crushPredEntails3; subst.
      unfold inst, inst_store, inst_env.
      now rewrite env.map_update.
    Qed.

    Lemma refine_assign {Γ x σ} {xIn : (x∷σ ∈ Γ)%katamaran} {w} :
      ⊢ ℛ⟦RVal σ -> RStoreSpec Γ Γ RUnit⟧
        (CStoreSpec.assign x) (SStoreSpec.assign (w := w) x).
    Proof.
      iIntros (v sv) "Hv %K %sK HK %δ %sδ Hδ %h %sh Hh".
      unfold SStoreSpec.assign, CStoreSpec.assign.
      iApply (refine_T with "HK [//] [Hv Hδ] Hh").
      now iApply (refine_env_update with "[$Hv $Hδ]").
    Qed.

  End State.

  Section StateCompatLemmas.
    Import logicalrelation.

    #[export] Instance refine_compat_pushpop `{R : Rel AT A} {Γ1 Γ2 x σ} {w} : RefineCompat (RVal σ -> RStoreSpec (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) R -> RStoreSpec Γ1 Γ2 R) CStoreSpec.pushpop w (SStoreSpec.pushpop (w := w)) _ :=
    MkRefineCompat refine_pushpop.

    #[export] Instance refine_compat_pushspops `{R : Rel AT A} {Γ1 Γ2 Δ} {w} :
    RefineCompat (RStore Δ -> RStoreSpec (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) R -> RStoreSpec Γ1 Γ2 R) CStoreSpec.pushspops w (SStoreSpec.pushspops (w := w)) _ :=
    MkRefineCompat refine_pushspops.

    #[export] Instance refine_compat_peval {w : World} {σ} (t : STerm σ w) v : RefineCompat (RVal σ) v w (peval t) _ :=
    MkRefineCompat (refine_peval t v).

    #[export] Instance refine_compat_seval_exp {Γ σ} (e : Exp Γ σ) {w : World} {δ} {sδ : SStore Γ w} :
    RefineCompat (RVal σ) (B.eval e δ) w (seval_exp sδ e) _ :=
    MkRefineCompat (refine_seval_exp e).

    #[export] Instance refine_compat_seval_exps {Γ Δ : PCtx} {es : NamedEnv (Exp Γ) Δ} {w : World} {δ : CStore Γ} {sδ : SStore Γ w} : RefineCompat (RStore Δ) (evals es δ) w (seval_exps sδ es) _ :=
      MkRefineCompat refine_seval_exps.

    #[export] Instance refine_compat_eval_exp {Γ σ} (e : Exp Γ σ) {w} : RefineCompat _ _ _ (SStoreSpec.eval_exp (w := w) e) _ :=
      MkRefineCompat (refine_eval_exp e).

    #[export] Instance refine_compat_eval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) {w} : RefineCompat (RStoreSpec Γ Γ (RStore Δ)) (CStoreSpec.eval_exps es) w (SStoreSpec.eval_exps (w := w) es) _ :=
    MkRefineCompat (refine_eval_exps es).

    #[export] Instance refine_compat_env_update {Γ x σ} (xIn : (x∷σ ∈ Γ)%katamaran) (w : World)
      (t : Term w σ) (v : Val σ) (δs : SStore Γ w) (δc : CStore Γ) :
      RefineCompat (RStore Γ) (δc ⟪ x ↦ v ⟫) w (δs ⟪ x ↦ t ⟫) _ :=
      MkRefineCompat (refine_env_update xIn w t v δs δc).

    #[export] Instance refine_compat_assign {Γ x σ} {xIn : (x∷σ ∈ Γ)%katamaran} {w} :
      RefineCompat (RVal σ -> RStoreSpec Γ Γ RUnit) (CStoreSpec.assign x) w (SStoreSpec.assign (w := w) x) _ :=
      MkRefineCompat refine_assign.

  End StateCompatLemmas.

  (* Local Hint Unfold RSat : core. *)
  (* Local Hint Unfold RInst : core. *)

  Section ExecAux.
    Import logicalrelation.

    Context `(rexec_call_foreign : RefineExecCallForeign c_exec_call_foreign s_exec_call_foreign).
    Context `(rexec_lemma : RefineExecLemma c_exec_lemma s_exec_lemma).
    Context `(rexec_call : RefineExecCall c_exec_call s_exec_call).

    Lemma refine_exec_aux :
      RefineExec (@CStoreSpec.exec_aux c_exec_call_foreign c_exec_lemma c_exec_call) (@SStoreSpec.exec_aux s_exec_call_foreign s_exec_lemma s_exec_call) .
    Proof.
      intros ? ? s. induction s; cbn; intros w; rsolve.
      - now iApply rexec_call.
      - now iApply rexec_call_foreign.
      - now iApply rexec_lemma.
      - iApply IHs1.
      - destruct a0, ta0.
        iRename select (ℛ⟦RMatchResult pat⟧ (existT x n) (existT x0 n0)) into "Hmr".
        iDestruct "Hmr" as "[%e Hvs]".
        subst x0.
        rsolve.
        now iApply H.
    Qed.

  End ExecAux.

  Section WithExec.

    Context `(rexec : RefineExec c_exec s_exec).

    Lemma refine_exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) w :
      ⊢ ℛ⟦RHeapSpec RUnit⟧
          (CStoreSpec.exec_contract c_exec c s)
          (SStoreSpec.exec_contract s_exec c s (w := w)).
    Proof.
      destruct c as [lvars pats req result ens]; cbn. rsolve.
      iApply rexec.
      rewrite forgetting_trans. iModIntro. rsolve.
    Qed.

    Lemma refine_vcgen {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) w :
      ⊢ ℛ⟦RProp⟧ (CStoreSpec.vcgen c_exec c body) (SStoreSpec.vcgen s_exec c body w).
    Proof.
      iApply HeapSpec.refine_run.
      iApply refine_exec_contract.
    Qed.

  End WithExec.

  End StoreSpec.

  Section WithSpec.

    Import PureSpec HeapSpec StoreSpec.

    Lemma refine_exec_call_error :
      RefineExecCall SHAL.exec_call_error SYMB.exec_call_error.
    Proof.
      iIntros (? ? ? ? cδ sδ) "#rδ".
      unfold SHAL.exec_call_error, SYMB.exec_call_error.
      iApply HeapSpec.refine_lift_purespec.
      iApply PureSpec.refine_error.
    Qed.

    Lemma refine_exec_call_foreign :
      RefineExecCallForeign cexec_call_foreign sexec_call_foreign.
    Proof.
      iIntros (? ? ? ? cδ sδ) "#rδ".
      unfold cexec_call_foreign, sexec_call_foreign.
      now iApply refine_call_contract.
    Qed.

    Lemma refine_exec_lemma :
      RefineExecLemma cexec_lemma sexec_lemma.
    Proof.
      iIntros (? ? ? cδ sδ) "#rδ".
      unfold cexec_lemma, sexec_lemma.
      now iApply refine_call_lemma.
    Qed.

    Variable cfg : Config.

    Lemma refine_debug_call [Δ τ] (f : 𝑭 Δ τ) w :
      ⊢ ℛ⟦RStore Δ -> RHeapSpec RUnit⟧
          (SHAL.debug_call f)
          (SYMB.debug_call cfg f (w := w)).
    Proof.
      iIntros (cδ sδ) "#rδ". unfold SHAL.debug_call, SYMB.debug_call.
      destruct config_debug_function.
      - iApply ((HeapSpec.refine_debug (RA := RUnit) (w := w)) with "[]").
        fold (CHeapSpec.pure tt).
        iApply HeapSpec.refine_pure.
        iApply refine_unit.
      - iApply HeapSpec.refine_pure.
        iApply refine_unit.
    Qed.

    Lemma refine_exec_call (fuel : nat) :
      RefineExecCall (cexec_call fuel) (sexec_call cfg fuel).
    Proof.
      induction fuel; cbn; iIntros (? ? ? ? cδ sδ) "#rδ".
      - iApply HeapSpec.refine_bind.
        iApply refine_debug_call; auto.
        iIntros (w1 θ1) "!> %cu %su _". clear cu su.
        destruct (CEnv f).
        + iApply HeapSpec.refine_call_contract. rsolve.
        + iApply refine_exec_call_error. rsolve.
      - iApply HeapSpec.refine_bind.
        iApply refine_debug_call; auto.
        iIntros (w1 θ1) "!> %cu %su _". clear cu su.
        destruct (CEnv f).
        + iApply HeapSpec.refine_call_contract. rsolve.
        + rsolve.
          iApply StoreSpec.refine_exec_aux;
          auto using refine_exec_call_foreign, refine_exec_lemma.
    Qed.

    Lemma refine_exec (fuel : nat) :
      RefineExec (cexec fuel) (sexec cfg fuel).
    Proof.
      unfold cexec, sexec. apply refine_exec_aux.
      all: auto using refine_exec_call_foreign, refine_exec_lemma, refine_exec_call.
    Qed.

    #[export] Instance refine_compat_exec {fuel : nat} (Γ : PCtx) (τ : Ty) (s : Stm Γ τ) {w} :
      RefineCompat (RStoreSpec Γ Γ (RVal τ))
        (cexec fuel s) w (sexec cfg fuel s w) _ :=
      MkRefineCompat (refine_exec fuel s w).

  End WithSpec.

  Lemma replay_sound (s : 𝕊 wnil) :
    safe (SPureSpec.replay s) [env] -> safe s [env].
  Proof.
    intros H.
    apply CPureSpec.replay_sound.
    pose proof (PureSpec.refine_replay s).
    unfold RProp in H0; cbn in H0.
    rewrite psafe_safe in H0.
    now apply (fromEntails H0 [env]).
  Qed.

  Lemma symbolic_vcgen_fuel_soundness {Γ τ} (fuel : nat) (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContractWithFuel fuel c body ->
    Shallow.ValidContractWithFuel fuel c body.
  Proof.
    unfold Symbolic.ValidContractWithFuel, Shallow.ValidContractWithFuel.
    intros [Hwp%postprocess_sound].
    apply replay_sound in Hwp.
    apply postprocess_sound in Hwp.
    apply (psafe_safe (w := wnil)) in Hwp; [|easy].
    revert Hwp.
    apply StoreSpec.refine_vcgen; try done.
    apply refine_exec.
  Qed.

  Lemma symbolic_vcgen_soundness {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContract c body ->
    Shallow.ValidContract c body.
  Proof.
    unfold Symbolic.ValidContract, Shallow.ValidContract.
    apply symbolic_vcgen_fuel_soundness.
  Qed.

  (* Print Assumptions symbolic_vcgen_soundness. *)

End Soundness.

Module MakeSymbolicSoundness
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG)
  (Import SHAL : ShallowExecOn B SIG PROG SPEC)
  (Import SYMB : SymbolicExecOn B SIG PROG SPEC).

  Include Soundness B SIG PROG SPEC SHAL SYMB.
End MakeSymbolicSoundness.
