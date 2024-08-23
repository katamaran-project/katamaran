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
  Import iris.proofmode.tactics.

  Module StoreSpec.
    Import PureSpec.
    Import HeapSpec.

    Definition RStore (Γ : PCtx) : Rel (SStore Γ) (CStore Γ) :=
      RInst (SStore Γ) (CStore Γ).

    Definition RStoreSpec Γ1 Γ2 `(R : Rel AT A) :
      Rel (SStoreSpec Γ1 Γ2 AT) (CStoreSpec Γ1 Γ2 A) :=
      □ᵣ (R -> RStore Γ2 -> RHeap -> ℙ) -> RStore Γ1 -> RHeap -> ℙ.

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

    Lemma refine_lift_purem {Γ} `(R : Rel AT A) {w : World}:
      ⊢ ℛ⟦RPureSpec R -> RStoreSpec Γ Γ R⟧
        CStoreSpec.lift_purem (SStoreSpec.lift_purem (w := w)).
    Proof.
      unfold RPureSpec, RStoreSpec, SStoreSpec.lift_purem, CStoreSpec.lift_purem.
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

    Class RefineCompat `(R : Rel AT A) (v : A)  w (vs : AT w) (Ob : Pred w) :=
      MkRefineCompat {
          refine_compat_lemma : Ob ⊢ ℛ⟦ R ⟧ v vs
        }.
    Hint Mode RefineCompat - - - + + + - : typeclass_instances.
    Arguments refine_compat_lemma {AT A R v w vs Ob} rci : rename.
    Arguments RefineCompat {AT A} R v w vs Ob%I.
    Arguments MkRefineCompat {AT A R v w vs Ob%I} rci : rename.

    Program Definition refine_compat_impl `{RA : Rel AT A} `{RB : Rel BT B} {f v w fs vs} {Pf}
      (compatf : RefineCompat (RA -> RB) f w fs Pf) : RefineCompat RB (f v) w (fs vs) (Pf ∗ RSat RA v vs) :=
      MkRefineCompat _.
    Next Obligation.
      iIntros (AT A RA BT B RB f v w fs vs Pf compatf) "[Hcf Hv]".
      now iApply (refine_compat_lemma compatf with "Hcf").
    Qed.
    (* The Hint Resolve used "simple apply", which wasn't instantiating evars sufficiently strongly. Hint Extern with eapply works better. *)
    Hint Extern 1 (RefineCompat ?RB (?f ?v) ?w (?fs ?vs) _) => eapply (refine_compat_impl (RB := RB) (fs := fs) (vs := vs) (f := f) (v := v) (w := w)) : typeclass_instances.

    #[export] Program Instance refine_compat_forall {𝑲} {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type} (RA : forall K, Rel (AT K) (A K)) {f w fs k P}
      (compatf : RefineCompat (RForall RA) f w fs P) : RefineCompat (RA k) (f k) w (fs k) P :=
      MkRefineCompat _.
    Next Obligation.
      iIntros (𝑲 AT A RA f w fs k P compatf) "Hcf".
      now iApply (refine_compat_lemma compatf with "Hcf").
    Qed.

    Definition refine_compat_inst_persist {AT A} `{InstSubst AT A, @SubstLaws AT _} {v} {w1 w2} {ω : Acc w1 w2} {t} :
      RefineCompat (RInst AT A) v w2 (persist t ω) _ :=
      MkRefineCompat (refine_inst_persist _).
    Opaque refine_compat_inst_persist.
    Hint Extern 0 (RefineCompat _ ?v _ (persist ?t ?ω) _) => refine (refine_compat_inst_persist (v := v) (t := t) (ω := ω)) : typeclass_instances.

    #[export] Instance refine_compat_inst_persist_term {σ} {v} {w1 w2} {ω : Acc w1 w2} {t} :
      RefineCompat (RVal σ) v w2 (persist__term t ω) _ :=
      MkRefineCompat (refine_inst_persist _).

    #[export] Instance refine_lift `{InstLift AT A} {w : World} (a : A) :
      RefineCompat (RInst AT A) a w (lift a) _ :=
      MkRefineCompat (refine_lift a).

    #[export] Instance refine_compat_term_val {σ} {v w} : RefineCompat (RVal σ) v w (term_val σ v) _ :=
      MkRefineCompat refine_term_val.

    Definition refine_compat_term_binop {w τ1 τ2 τ3} {op : BinOp τ1 τ2 τ3} {a1 sa1 a2 sa2} :
        RefineCompat (RVal τ3) (bop.eval op a1 a2)  w (term_binop op sa1 sa2) _ :=
      MkRefineCompat refine_term_binop.
    Opaque refine_compat_term_binop.
    Hint Extern 0 (RefineCompat (RVal _) _ _ (term_binop ?binop _ _) _) => ( refine (refine_compat_term_binop (op := binop)) ) : typeclass_instances.

    #[export] Instance refine_compat_formula_bool {w : World} {v} {sv : Term w ty.bool} :
      RefineCompat RFormula (v = true) w (formula_bool sv) _ :=
      MkRefineCompat refine_formula_bool.

    Definition refine_compat_formula_relop {w : World} {σ v1 v2} {sv1 sv2 : Term w σ}  {relop : RelOp σ} :
      RefineCompat RFormula (bop.eval_relop_prop relop v1 v2) w (formula_relop relop sv1 sv2) _ :=
      MkRefineCompat refine_formula_relop.
    Opaque refine_compat_formula_relop.
    Hint Extern 0 (RefineCompat RFormula _ _ (formula_relop ?relop _ _) _) => ( refine (refine_compat_formula_relop (relop := relop)) ) : typeclass_instances.

    #[export] Instance refine_compat_chunk_ptsreg {w σ} {pc a ta} : 
      RefineCompat RChunk (scchunk_ptsreg pc a) w(chunk_ptsreg (σ := σ) pc ta) _ :=
      MkRefineCompat refine_chunk_ptsreg.

    #[export] Instance refine_compat_chunk_user {w c vs svs} :
      RefineCompat RChunk (scchunk_user c vs) w (chunk_user c svs) _ :=
      MkRefineCompat refine_chunk_user.
    
    #[export] Instance refine_compat_env_snoc {Δ : Ctx Ty} {τ} {w : World} {vs : Env Val Δ} {svs : Env (Term w) Δ} {v : Val τ} {sv : Term w τ} :
      RefineCompat (REnv (Δ ▻ τ)) (vs ► ( τ ↦ v ))%env w (svs ► (τ ↦ sv ))%env _ :=
      MkRefineCompat refine_env_snoc.

    #[export] Instance refine_compat_sub_snoc {τ : Ty} {Γ : LCtx} {x : LVar}
        {w : World} {vs : NamedEnv Val Γ} {svs : NamedEnv (Term w) Γ}
        {v : Val τ} {sv : Term w τ} :
      RefineCompat (RNEnv LVar (Γ ▻ x∷τ)) (vs.[x∷τ ↦ v])%env w (sub_snoc svs (x∷τ) sv) _ :=
      MkRefineCompat refine_sub_snoc.

    #[export] Instance refine_compat_env_nil {w : World} {vs : Env Val [ctx]} {svs : Env (Term w) [ctx]} :
      RefineCompat (REnv [ctx]) vs  w svs _ :=
      MkRefineCompat refine_env_nil.

    Class RefineCompatGen (w : World) (P : Pred w) (Ob : Pred w) (withbase : bool):=
      MkRefineCompatGen {
        refine_compat_gen_lemma : Ob ⊢ P
        }.
    Arguments RefineCompatGen w P%I Ob%I withbase.
    Arguments MkRefineCompatGen {w} {P} _%I _ {_}.
    Arguments refine_compat_gen_lemma {w} P%I {Ob} withbase rcg : rename.

    #[export] Program Instance refine_compat_gen_step `(R : Rel AT A) (v : A) (w : World) (vs : AT w) Ob1 Ob2 b
      (rc : RefineCompat R v w vs Ob1)
      (iter : RefineCompatGen Ob1 Ob2 b) :
      RefineCompatGen (ℛ⟦ R ⟧ v vs) Ob2 b := MkRefineCompatGen Ob2 _.
    Next Obligation.
      iIntros (AT A R v w vs Ob1 Ob2 b rc iter) "H".
      iApply (refine_compat_lemma with "[H]").
      now iApply (refine_compat_gen_lemma with "[H]").
    Qed.

    #[export] Program Instance refine_compat_gen_base_true {w} {b} :
      RefineCompatGen (w := w) True emp b := MkRefineCompatGen emp _.
    Next Obligation.
      now iIntros.
    Qed.

    #[export] Program Instance refine_compat_gen_base_emp {w} {b} :
      RefineCompatGen (w := w) emp emp b := MkRefineCompatGen emp _.
    Next Obligation.
      now iIntros.
    Qed.

    #[export] Program Instance refine_compat_gen_base {w} (P : Pred w):
      RefineCompatGen (w := w) P P true | 10 := MkRefineCompatGen P _.
    Next Obligation.
      now iIntros.
    Qed.

    Class ObSep {w} (P1 P2 P3 : Pred w) : Prop :=
      obsep_equiv : P1 ∗ P2 ⊣⊢ P3.
    #[export] Instance obsep_empL {w} {P : Pred w} : ObSep emp%I P P.
    Proof. apply bi.emp_sep. Qed.
    #[export] Instance obsep_empR {w} {P : Pred w} : ObSep P emp%I P.
    Proof. apply bi.sep_emp. Qed.
    #[export] Instance obsep_sep {w} {P1 P2 : Pred w} : ObSep P1 P2 (P1 ∗ P2)%I | 1.
    Proof. done. Qed.

    #[export] Program Instance refine_compat_gen_split {w} {P1 P2 : Pred w} {Ob1 Ob2 Ob} {b}
      (rcg1 : RefineCompatGen P1 Ob1 b) (rcg2 : RefineCompatGen P2 Ob2 b) {_ : ObSep Ob1 Ob2 Ob} :
      RefineCompatGen (w := w) (P1 ∗ P2) Ob b | 1 := MkRefineCompatGen Ob _.
    Next Obligation.
      iIntros (w P1 P2 Ob1 Ob2 Ob b rcg1 rcg2 obsep) "H".
      rewrite -(obsep_equiv (ObSep := obsep)).
      iDestruct "H" as "(H1 & H2)".
      iSplitL "H1".
      - iApply (refine_compat_gen_lemma with "H1").
      - iApply (refine_compat_gen_lemma with "H2").
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
      iApply (refine_lift_purem (RVal σ)).
      now iApply PureSpec.refine_angelic.
    Qed.

    Lemma refine_demonic (x : option LVar) {Γ} {w : World} :
      ⊢ ℛ⟦∀ᵣ σ, RStoreSpec Γ Γ (RVal σ)⟧ CStoreSpec.demonic (SStoreSpec.demonic (w := w) x).
    Proof.
      unfold SStoreSpec.demonic, CStoreSpec.demonic.
      iIntros (σ).
      iApply (refine_lift_purem (RVal σ)).
      now iApply PureSpec.refine_demonic.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} {Γ} {w} :
      ⊢ ℛ⟦∀ᵣ Δ, RStoreSpec Γ Γ (RNEnv N Δ)⟧
        CStoreSpec.angelic_ctx (SStoreSpec.angelic_ctx (w := w) n).
    Proof.
      unfold SStoreSpec.angelic_ctx, CStoreSpec.angelic_ctx.
      iIntros (Δ).
      iApply (refine_lift_purem (RNEnv N Δ)).
      iApply refine_angelic_ctx.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} {Γ} {w} :
      ⊢ ℛ⟦∀ᵣ Δ, RStoreSpec Γ Γ (RNEnv N Δ)⟧
        CStoreSpec.demonic_ctx (SStoreSpec.demonic_ctx (w := w) n).
    Proof.
      unfold SStoreSpec.demonic_ctx, CStoreSpec.demonic_ctx.
      iIntros (Δ).
      iApply (refine_lift_purem (RNEnv N Δ)).
      iApply refine_demonic_ctx.
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

    Import iris.proofmode.environments.

    #[export] Ltac rsolve_step :=
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

    #[export] Ltac rsolve :=
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

    #[export] Ltac rsolve2_step :=
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

    #[export] Ltac rsolve2 :=
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

  Section AssumeAssert.
    Import logicalrelation.
    Import logicalrelation.notations.
    
    Lemma refine_assume_formula {Γ} {w} :
      ⊢ ℛ⟦RFormula -> RStoreSpec Γ Γ RUnit⟧
        CStoreSpec.assume_formula (SStoreSpec.assume_formula (w := w)).
    Proof.
      unfold SStoreSpec.assume_formula, CStoreSpec.assume_formula.
      iIntros (fml fmls) "Hfml %K %Ks HK %s %ss Hs %h %hs Hh".
      iApply (refine_lift_purem with "[Hfml] HK Hs Hh").
      iApply (PureSpec.refine_assume_formula with "Hfml").
    Qed.

    Lemma refine_assert_formula {Γ} {w} :
      ⊢ ℛ⟦RFormula -> RStoreSpec Γ Γ RUnit⟧
        CStoreSpec.assert_formula (SStoreSpec.assert_formula (w := w)).
    Proof.
      unfold SStoreSpec.assert_formula, CStoreSpec.assert_formula.
      iIntros (fml fmls) "Hfml %K %Ks HK %s %ss Hs %h %hs Hh".
      iApply (refine_lift_purem with "[Hfml] HK Hs Hh").
      iApply (PureSpec.refine_assert_formula with "Hfml").
    Qed.

    Lemma refine_assert_pathcondition {Γ} {w} :
      ⊢ ℛ⟦RPathCondition -> RStoreSpec Γ Γ RUnit⟧
        CStoreSpec.assert_formula (SStoreSpec.assert_pathcondition (w := w)).
    Proof.
      iIntros (pc pcs) "Hpc %K %Ks HK %δ %δs Hδ %h %hs Hh".
      iApply (refine_lift_purem with "[Hpc] HK Hδ Hh").
      now iApply PureSpec.refine_assert_pathcondition.
    Qed.

    Lemma refine_assert_eq_nenv {N Γ} (Δ : NCtx N Ty) {w} :
      ⊢ ℛ⟦RNEnv N Δ -> RNEnv N Δ -> RStoreSpec Γ Γ RUnit⟧
        CStoreSpec.assert_eq_nenv (SStoreSpec.assert_eq_nenv (w := w)).
    Proof.
      iIntros (E1 sE1) "HE1 %E2 %sE2 HE2 %K %sK HK %δ %sδ Hδ %h %sh Hh".
      iApply (refine_lift_purem RUnit $! _ _ with "[HE1 HE2] HK Hδ Hh").
      now iApply (PureSpec.refine_assert_eq_nenv with "HE1 HE2").
    Qed.

  End AssumeAssert.

  Section AssumeAssertCompatLemmas.
    Import logicalrelation.

    #[export] Instance refine_compat_assume_formula {Γ} {w} :
    RefineCompat (RFormula -> RStoreSpec Γ Γ RUnit) CStoreSpec.assume_formula w (SStoreSpec.assume_formula (w := w)) _ :=
    MkRefineCompat refine_assume_formula.

    #[export] Instance refine_compat_assert_formula {Γ} {w} :
    RefineCompat (RFormula -> RStoreSpec Γ Γ RUnit) CStoreSpec.assert_formula w (SStoreSpec.assert_formula (w := w)) _ :=
    MkRefineCompat refine_assert_formula.

    #[export] Instance refine_compat_assert_pathcondition {Γ} {w} :
    RefineCompat (RPathCondition -> RStoreSpec Γ Γ RUnit) CStoreSpec.assert_formula w (SStoreSpec.assert_pathcondition (w := w)) _ :=
    MkRefineCompat refine_assert_pathcondition.

    #[export] Instance refine_compat_assert_eq_nenv {N Γ} (Δ : NCtx N Ty) {w} :
      RefineCompat (RNEnv N Δ -> RNEnv N Δ -> RStoreSpec Γ Γ RUnit) CStoreSpec.assert_eq_nenv w (SStoreSpec.assert_eq_nenv (w := w)) _ :=
      MkRefineCompat (refine_assert_eq_nenv Δ).

  End AssumeAssertCompatLemmas.

  Section PatternMatching.
    Import logicalrelation.

    Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : @Pattern N σ) {w} :
      ⊢ ℛ⟦RVal σ -> RStoreSpec Γ Γ (RMatchResult pat)⟧
        (CStoreSpec.demonic_pattern_match pat)
        (SStoreSpec.demonic_pattern_match (w := w) n pat).
    Proof.
      iIntros (v sv) "rv %Φ %sΦ rΦ %δ %sδ rδ %h %sh rh".
      unfold SStoreSpec.demonic_pattern_match, CStoreSpec.demonic_pattern_match, CStoreSpec.lift_purem.
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

    Lemma refine_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      ⊢ ℛ⟦RStoreSpec Γ Γ (RVal τ)⟧
        (CStoreSpec.read_register reg) (SStoreSpec.read_register (w := w) reg).
    Proof.
      iIntros (Φ sΦ) "rΦ %δ %sδ rδ".
      iApply HeapSpec.refine_read_register.
      iIntros (w1 θ1) "!> %v %sv rv".
      iApply ("rΦ" with "rv").
      iApply (refine_inst_persist with "rδ").
    Qed.

    Lemma refine_write_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      ⊢ ℛ⟦RVal τ -> RStoreSpec Γ Γ (RVal τ)⟧
        (CStoreSpec.write_register reg) (SStoreSpec.write_register (w := w) reg).
    Proof.
      iIntros (vnew svnew) "rvnew %Φ %sΦ rΦ %δ %sδ rδ".
      iApply (HeapSpec.refine_write_register with "rvnew").
      iIntros (w1 θ1) "!> %v %sv rv".
      iApply ("rΦ" with "rv").
      iApply (refine_inst_persist with "rδ").
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

  Section ProduceConsume.
    Import logicalrelation.
    Import logicalrelation.notations.

    Lemma refine_produce_chunk {Γ} {w} :
      ⊢ ℛ⟦RChunk -> RStoreSpec Γ Γ RUnit⟧
        CStoreSpec.produce_chunk (SStoreSpec.produce_chunk (w := w)).
    Proof.
      iIntros (c sc) "Hc %Φ %sΦ HΦ %δ %sδ Hδ %h %sh Hh".
      iApply (PureSpec.refine_produce_chunk with "Hc Hh [HΦ Hδ]").
      iIntros (w2 ω2) "!> %h2 %sh2 Hh2".
      iApply ("HΦ" with "[//] [Hδ] Hh2").
      now iApply (refine_inst_persist with "Hδ").
    Qed.

    Lemma refine_consume_chunk {Γ} {w} :
      ⊢ ℛ⟦RChunk -> RStoreSpec Γ Γ RUnit⟧
        CStoreSpec.consume_chunk (SStoreSpec.consume_chunk (w := w)).
    Proof.
      iIntros (c sc) "Hc %Φ %sΦ HΦ %δ %sδ Hδ %h %sh Hh".
      iApply (PureSpec.refine_consume_chunk with "Hc Hh").
      iIntros (w2 ω2) "!> %h2 %sh2 Hh2".
      iApply ("HΦ" with "[//] [Hδ] Hh2").
      now iApply (refine_inst_persist with "Hδ").
    Qed.

    Lemma refine_consume_chunk_angelic {Γ} {w} :
      ⊢ ℛ⟦RChunk -> RStoreSpec Γ Γ RUnit⟧
        CStoreSpec.consume_chunk (SStoreSpec.consume_chunk_angelic (w := w)).
    Proof.
      iIntros (c sc) "Hc %Φ %sΦ HΦ %δ %sδ Hδ %h %sh Hh".
      iApply (PureSpec.refine_consume_chunk_angelic with "Hc Hh").
      iIntros (w2 ω2) "!> %h2 %sh2 Hh2".
      iApply ("HΦ" with "[//] [Hδ] Hh2").
      now iApply (refine_inst_persist with "Hδ").
    Qed.

    Lemma refine_produce {Γ} {w1 w2 : World} (ω : Acc w1 w2) (asn : Assertion w1) (ι : Valuation w1):
      ℛ⟦RNEnv LVar w1 ⟧ ι (sub_acc ω) ⊢ ℛ⟦RStoreSpec Γ Γ RUnit⟧ (CStoreSpec.produce ι asn) (SStoreSpec.produce (w := w1) asn ω).
    Proof.
      unfold SStoreSpec.produce, CStoreSpec.produce.
      iIntros "Hι %Φ %sΦ rΦ %δ %sδ rδ".
      iPoseProof (HeapSpec.refine_produce asn) as "Hcons".
      iApply (refine_T with "Hcons Hι").
      iIntros (w3 ω3) "!> %u %su _".
      iApply ("rΦ" with "[//] [rδ]").
      now iApply (refine_inst_persist with "rδ").
    Qed.

    Lemma refine_consume {Γ} {w1 w2 : World} (ω : Acc w1 w2) (asn : Assertion w1) (ι : Valuation w1):
      ℛ⟦RNEnv LVar w1 ⟧ ι (sub_acc ω) ⊢ ℛ⟦RStoreSpec Γ Γ RUnit⟧ (CStoreSpec.consume ι asn) (SStoreSpec.consume (w := w1) asn ω).
    Proof.
      unfold SStoreSpec.consume, CStoreSpec.consume.
      iIntros "Hι %Φ %sΦ rΦ %δ %sδ rδ".
      iPoseProof (HeapSpec.refine_consume asn) as "Hcons".
      iApply (refine_T with "Hcons Hι").
      iIntros (w3 ω3) "!> %u %su _".
      iApply ("rΦ" with "[//] [rδ]").
      now iApply (refine_inst_persist with "rδ").
    Qed.

  End ProduceConsume.

  Section ProduceConsumeCompatLemmas.
    Import logicalrelation.

    #[export] Instance refine_compat_produce_chunk {Γ} {w} :
      RefineCompat (RChunk -> RStoreSpec Γ Γ RUnit) CStoreSpec.produce_chunk w (SStoreSpec.produce_chunk (w := w)) _ :=
      MkRefineCompat refine_produce_chunk.

    #[export] Instance refine_compat_consume_chunk {Γ} {w} :
      RefineCompat (RChunk -> RStoreSpec Γ Γ RUnit) CStoreSpec.consume_chunk w (SStoreSpec.consume_chunk (w := w)) _ :=
      MkRefineCompat refine_consume_chunk.

    #[export] Instance refine_compat_consume_chunk_angelic {Γ} {w} :
      RefineCompat (RChunk -> RStoreSpec Γ Γ RUnit) CStoreSpec.consume_chunk w (SStoreSpec.consume_chunk_angelic (w := w)) _ :=
      MkRefineCompat refine_consume_chunk_angelic.

      #[export] Instance refine_compat_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      RefineCompat (RStoreSpec Γ Γ (RVal τ)) (CStoreSpec.read_register reg) w (SStoreSpec.read_register (w := w) reg) _ :=
      MkRefineCompat (refine_read_register reg).

      #[export] Instance refine_compat_write_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      RefineCompat (RVal τ -> RStoreSpec Γ Γ (RVal τ)) (CStoreSpec.write_register reg) w (SStoreSpec.write_register (w := w) reg) _ :=
        MkRefineCompat (refine_write_register reg).

      #[export] Instance refine_compat_produce {Γ} {Σ1 wco1} {w2 : World} (ω : Acc (MkWorld Σ1 wco1) w2) (asn : Assertion Σ1) (ι : Valuation (MkWorld Σ1 wco1)):
        RefineCompat (RStoreSpec Γ Γ RUnit) (CStoreSpec.produce ι asn) w2 (SStoreSpec.produce (w := MkWorld Σ1 wco1) asn ω) _ :=
        MkRefineCompat (refine_produce ω asn ι).

      #[export] Instance refine_compat_consume {Γ} {Σ1 wco1} {w2 : World} (ω : Acc (MkWorld Σ1 wco1) w2) (asn : Assertion Σ1) (ι : Valuation Σ1):
        RefineCompat (RStoreSpec Γ Γ RUnit) (CStoreSpec.consume ι asn) w2 (SStoreSpec.consume (w := MkWorld Σ1 wco1) asn ω) _ :=
        MkRefineCompat (refine_consume ω asn ι).

  End ProduceConsumeCompatLemmas.


  Section CallContracts.
    Import logicalrelation.

    Lemma refine_call_contract {Γ Δ τ} (c : SepContract Δ τ) {w} :
      ⊢ ℛ⟦RStore Δ -> RStoreSpec Γ Γ (RVal τ)⟧
        (CStoreSpec.call_contract c) (SStoreSpec.call_contract (w := w) c).
    Proof.
      iIntros (args sargs) "#Hargs".
      destruct c; cbv [SStoreSpec.call_contract CStoreSpec.call_contract]. 
      rsolve.
      - rewrite sub_acc_trans -(persist_subst (a := ta)).
        now rsolve.
      - rewrite !sub_acc_trans.
        now rsolve.
      (* rsolve2_step. *)
      (* iIntros (? ?) "!>". *)
      (* rsolve2_step. *)
      (* rsolve2_step. *)
      (* iRename select (ℛ⟦_⟧ _ _) into "Ha". *)
      (* iFrame "Hargs Ha". *)
      (* iIntros (? ?) "!>". *)
      (* rsolve2_step. *)
      (* rsolve2_step. *)
      (* rewrite sub_acc_trans -(persist_subst (a := ta)). *)
      (* rsolve2_step. *)
      (* iFrame "Ha". *)
      (* rsolve2_step. *)
      (* iIntros (? ?) "_". *)
      (* rsolve2_step. *)
      (* iIntros (? ?) "!>". *)
      (* rsolve2_step. *)
      (* rsolve2_step. *)
      (* rewrite !sub_acc_trans. *)
      (* iRename select (ℛ⟦_⟧ a2 _) into "Ha2". *)
      (* iFrame "Ha Ha2". *)
      (* iIntros (? ?) "!>". *)
      (* rsolve2_step. *)
      (* now rsolve2_step. *)
    Qed.

    Lemma refine_call_lemma {Γ Δ : PCtx} (lem : Lemma Δ) {w} :
      ⊢ ℛ⟦RStore Δ -> RStoreSpec Γ Γ RUnit⟧
        (CStoreSpec.call_lemma lem) (SStoreSpec.call_lemma (w := w) lem).
    Proof.
      destruct lem; cbv [SStoreSpec.call_lemma CStoreSpec.call_lemma].
      iIntros (args sargs) "Hargs".
      rsolve.
      - rewrite sub_acc_trans -(persist_subst (a := ta)); rsolve.
      - cbn; rsolve; rewrite sub_acc_trans; now rsolve.
      (*   rsolve2. *)
      (* iIntros (? ?) "!>". *)
      (* rsolve2_step. *)
      (* rsolve2_step. *)
      (* iRename select (ℛ⟦_⟧ _ _) into "Ha". *)
      (* iFrame "Ha Hargs". *)
      (* rsolve2_step. *)
      (* rsolve2_step. *)
      (* rsolve2_step. *)
      (* rewrite sub_acc_trans. *)
      (* rewrite -(persist_subst). *)
      (* rsolve2_step. *)
      (* iFrame "Ha". *)
      (* rsolve2_step. *)
      (* rsolve2_step. *)
      (* rsolve2_step. *)
      (* cbn. *)
      (* rsolve2_step. *)
      (* now rewrite sub_acc_trans. *)
    Qed.

  End CallContracts.

  Section CallContractsCompatLemmas.
    Import logicalrelation.

    #[export] Instance refine_compat_call_contract {Γ Δ τ} (c : SepContract Δ τ) {w} :
      RefineCompat (RStore Δ -> RStoreSpec Γ Γ (RVal τ)) (CStoreSpec.call_contract c) w (SStoreSpec.call_contract (w := w) c) _ :=
      MkRefineCompat (refine_call_contract c).

    #[export] Instance refine_compat_call_lemma {Γ Δ : PCtx} (lem : Lemma Δ) {w} : RefineCompat (RStore Δ -> RStoreSpec Γ Γ RUnit) (CStoreSpec.call_lemma lem) w (SStoreSpec.call_lemma (w := w) lem) _ :=
      MkRefineCompat (refine_call_lemma lem).

  End CallContractsCompatLemmas.

  Section ExecRefine.
    Import logicalrelation.

    Definition ExecRefine (sexec : SStoreSpec.Exec) (cexec : CStoreSpec.Exec) :=
      forall Γ τ (s : Stm Γ τ) w,
        ⊢ ℛ⟦RStoreSpec Γ Γ (RVal τ)⟧ (cexec Γ τ s) (@sexec Γ τ s w).

    Lemma refine_exec_aux {cfg} srec crec (HYP : ExecRefine srec crec) :
      ExecRefine (@SStoreSpec.exec_aux cfg srec) (@CStoreSpec.exec_aux crec).
    Proof.
      unfold ExecRefine.
      induction s; cbn; intros w; rsolve.
      - destruct (CEnv f).
        + unfold SStoreSpec.call_contract_debug.
          destruct (config_debug_function cfg f); rsolve.
        + iIntros (POST sPOST) "#HPOST %δ1 %sδ1 #Hδ1".
          iApply HYP; try done; rsolve.
          iApply ("HPOST"); try done.
          now iApply (refine_inst_persist with "Hδ1").
      - now rewrite sub_acc_trans.
      - iApply IHs1.
      - destruct a0, ta0.
        iRename select (ℛ⟦RMatchResult pat⟧ (existT x n) (existT x0 n0)) into "Hmr".
        iDestruct "Hmr" as "[%e Hvs]".
        subst x0.
        rsolve.
        now iApply H.
    Qed.

    Lemma refine_exec {cfg n} :
      ExecRefine (@SStoreSpec.exec cfg n) (@CStoreSpec.exec n).
    Proof.
      induction n; cbn.
      - unfold ExecRefine. iIntros (Γ τ s w).
        iApply (refine_error (R := RVal _)).
      - now apply refine_exec_aux.
    Qed.

    #[export] Instance refine_compat_exec_gen {w cfg n Γ τ s} :
    RefineCompat (RStoreSpec Γ Γ (RVal τ)) (@CStoreSpec.exec n Γ τ s) w (@SStoreSpec.exec cfg n Γ τ s w) _ :=
    MkRefineCompat (refine_exec s w).

    Lemma refine_exec_contract {cfg : Config} n {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) ι :
      ⊢ forgetting (w2 := wnil) (lift ι)
        (ℛ⟦RStoreSpec Γ Γ RUnit⟧
           (CStoreSpec.exec_contract n c s ι) (SStoreSpec.exec_contract cfg n c s)).
    Proof.
      unfold SStoreSpec.exec_contract, CStoreSpec.exec_contract;
        destruct c as [Σ δ pre result post]; cbn - [RSat] in *.
      iPoseProof (forgetting_valuation_curval (Σ := Σ) (ι := ι)) as "#Hι".
      change (lift ι) with (sub_acc (acc_wlctx_valuation ι)).
      iModIntro.
      rsolve.
      - now iApply refine_rinst_sub_initial.
      - iApply (refine_rnenv_sub_acc (w := wlctx _)).
        now rewrite sub_acc_trans.
    Qed.
  End ExecRefine.

  Section ExecRefineCompat.

    (* #[export] Instance refine_compat_exec_unit {w cfg n Γ s} : *)
    (* RefineCompat (RStoreSpec Γ Γ (RVal ty.unit)) (@CStoreSpec.exec n Γ ty.unit s) w (@SStoreSpec.exec cfg n Γ ty.unit s w) := *)
    (* MkRefineCompat _ _ _ (refine_exec s w). *)
  End ExecRefineCompat.
  
  End StoreSpec.

  Lemma refine_psafe_demonic_close {Σ} (P : SymProp Σ):
    psafe (demonic_close P : SymProp wnil) ⊢ ∀ ι, forgetting (lift ι) (psafe (P : SymProp (wlctx Σ))).
  Proof.
    unfold forgetting.
    crushPredEntails3.
    rewrite inst_lift.
    destruct (env.view ι).
    apply psafe_safe; first done.
    apply psafe_safe in H0; last done.
    now apply safe_demonic_close.
  Qed.

  Lemma refine_demonic_close {Σ} (P : 𝕊 (wlctx Σ)) (p : Valuation Σ -> Prop) :
    (∀ ι, forgetting (lift ι) (ℛ⟦RProp⟧ (p ι) P)) ⊢
      ℛ⟦RProp⟧ (ForallNamed p) (demonic_close P : SymProp wnil).
  Proof.
    iIntros "HYP Hwp".
    unfold ForallNamed.
    rewrite env.Forall_forall. iIntros (ι).
    iSpecialize ("HYP" $! ι).
    rewrite <-(forgetting_pure (w2 := wlctx Σ) (lift ι)).
    iPoseProof (refine_psafe_demonic_close P with "Hwp") as "HP".
    iSpecialize ("HP" $! ι).
    iModIntro.
    now iApply "HYP".
  Qed.

  Lemma refine_vcgen {Γ τ} n (c : SepContract Γ τ) (body : Stm Γ τ) :
    ⊢ ℛ⟦RProp⟧ (CStoreSpec.vcgen n c body) (SStoreSpec.vcgen default_config n c body : SymProp wnil).
  Proof.
    unfold SStoreSpec.vcgen, CStoreSpec.vcgen.
    iApply refine_demonic_close.
    iIntros (ι).
    iPoseProof (StoreSpec.refine_exec_contract n c body ι) as "H".
    iPoseProof (forgetting_valuation_curval (ι := ι)) as "#Hι".
    iModIntro.
    iApply ("H").
    - iIntros (w ω) "!> %u %su _ %δ %sδ Hδ %h %sh Hh HSP".
      now iPureIntro.
    - iApply (repₚ_inst_curval (T := SStore Γ) (w := wlctx (sep_contract_logic_variables c)) (t := sep_contract_localstore c) with "Hι").
    - iApply (refine_nil (AT := Chunk)).
  Qed.

  Lemma replay_sound {w : World} (s : 𝕊 w) ι (Hpc : instprop (wco w) ι) :
    safe (SPureSpec.replay s) ι -> safe s ι.
  Proof.
    intros H.
    apply CPureSpec.replay_sound.
    pose proof (PureSpec.refine_replay s ι).
    unfold RProp in H0; cbn in H0.
    rewrite psafe_safe in H0.
    now apply (fromEntails H0 ι).
  Qed.

  Lemma symbolic_vcgen_soundness {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContract c body ->
    Shallow.ValidContract c body.
  Proof.
    unfold Symbolic.ValidContract. intros [Hwp%postprocess_sound].
    apply (replay_sound (w:=wnil)) in Hwp; [|easy].
    apply postprocess_sound in Hwp.
    apply (fromEntails (refine_vcgen _ _ _) [env]); try done.
    now apply psafe_safe.
  Qed.

  Lemma symbolic_vcgen_fuel_soundness {Γ τ} (fuel : nat) (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContractWithFuel fuel c body ->
    Shallow.ValidContractWithFuel fuel c body.
  Proof.
    unfold Symbolic.ValidContractWithFuel. intros [Hwp%postprocess_sound].
    apply (replay_sound (w:=wnil)) in Hwp; [|easy].
    apply postprocess_sound in Hwp.
    apply (fromEntails (refine_vcgen fuel c body) [env]); try done.
    now apply (psafe_safe (w := wnil)).
  Qed.

  Print Assumptions symbolic_vcgen_soundness.

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
