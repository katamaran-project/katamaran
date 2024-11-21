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
     Classes.Morphisms
     Lists.List
     NArith.NArith
     Program.Tactics
     Relations.Relation_Definitions
     Strings.String
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations
     Prelude
     Program
     Signature.

From stdpp Require base list option.

Import ctx.notations.
Import env.notations.
Import ListNotations.
Import SignatureNotations.

Set Implicit Arguments.

Module Type ShallowExecOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B).

  Import CPureSpecM CHeapSpecM.
  Open Scope mut_scope.

  Notation MonotonicExecCall exec_call :=
    (forall Δ τ (f : 𝑭 Δ τ) (δ : CStore Δ),
        Monotonic (RM eq) (exec_call Δ τ f δ)).
  Notation MonotonicExecCallForeign exec_call_foreign :=
    (forall Δ τ (f : 𝑭𝑿 Δ τ) (δ : CStore Δ),
        Monotonic (RM eq) (exec_call_foreign Δ τ f δ)).
  Notation MonotonicExecLemma exec_lemma :=
    (forall Δ (l : 𝑳 Δ) (δ : CStore Δ),
        Monotonic (RM eq) (exec_lemma Δ l δ)).

  #[global] Typeclasses Opaque pure bind.

  Section Exec.

    Context {M : Type -> Type}
      {pureM : CPureSpecM M}
      {heapM : CHeapSpecM M}
      {relM : RelM M}
      {mpureM: MPureSpecM M}
      {mheapM: MHeapSpecM M}.

    Definition CStoreT (Γ1 Γ2 : PCtx) (A : Type) : Type :=
      CStore Γ1 -> M (A * CStore Γ2).

    Definition MStoreT {Γ1 Γ2} `(RA : relation A) : relation (CStoreT Γ1 Γ2 A) :=
      (eq ==> RM (RA * eq))%signature.

    Notation MonotonicExec exec :=
      (forall Γ τ (s : Stm Γ τ),
          Monotonic (MStoreT eq) (exec Γ τ s)).

    Definition liftM {Γ A} :
      M A -> CStoreT Γ Γ A.
    Proof.
      intros m δ. apply (bind m). intros a. apply pure.
      split; auto.
    Defined.

    #[export] Instance mon_liftM {Γ} `{RA : relation A} (m : M A) :
      Monotonic (RM RA) m ->
      Monotonic (MStoreT RA) (liftM (Γ:=Γ) m).
    Proof.
      unfold liftM. intros rm δ ? ?. eapply mon_bind. eauto.
      intros ? ? ra. apply mon_pure. now constructor.
    Qed.

    Definition evalCStoreT {Γ1 Γ2 A} : CStoreT Γ1 Γ2 A -> CStore Γ1 -> M A :=
      fun m δ1 => bind (m δ1) (fun '(a,_) => pure a).

    #[export] Instance mon_evalCStoreT {Γ1 Γ2} `{RA : relation A} :
      Monotonic (MStoreT RA ==> CStore Γ1 ::> RM RA) (@evalCStoreT Γ1 Γ2 A).
    Proof.
      intros m1 m2 rm δ1. unfold evalCStoreT.
      eapply mon_bind. now apply rm.
      intros [? ?] [? ?] [ra rδ].
      now apply mon_pure.
    Qed.

    Definition state {Γ1 Γ2 A} (f : CStore Γ1 -> A * CStore Γ2) : CStoreT Γ1 Γ2 A :=
      fun δ => pure (f δ).

    #[export] Instance mon_state {Γ1 Γ2} `{RA : relation A} f :
      Monotonic (eq ==> RA * eq) f ->
      Monotonic (MStoreT RA) (@state Γ1 Γ2 A f).
    Proof. intros rf ? ? rδ. now apply mon_pure, rf, rδ. Qed.

    Definition pure {Γ A} (a : A) : CStoreT Γ Γ A :=
      liftM (pure a).

    Definition bind {Γ1 Γ2 Γ3 A B} (m : CStoreT Γ1 Γ2 A) (f : A -> CStoreT Γ2 Γ3 B) : CStoreT Γ1 Γ3 B :=
      fun δ1 => bind (m δ1) (fun '(a,δ2) => f a δ2).

    Definition debug {Γ A} :
      CStoreT Γ Γ A -> CStoreT Γ Γ A :=
      fun m δ => CPureSpecM.debug (m δ).

    #[global] Typeclasses Opaque evalCReaderT.
    #[export] Instance mon_pure `{RA : relation A} {Γ} (a : A) :
      Monotonic RA a -> Monotonic (MStoreT RA) (pure (Γ := Γ) a).
    Proof. typeclasses eauto. Qed.
    #[global] Typeclasses Opaque pure.


    #[export] Instance mon_bind {Γ1 Γ2 Γ3} `{RA : relation A, RB : relation B} m f :
      Monotonic (MStoreT RA) m ->
      Monotonic (RA ==> MStoreT RB) f ->
      Monotonic (MStoreT RB) (@bind Γ1 Γ2 Γ3 A B m f).
    Proof.
      intros rm rf δ1 ? <-. unfold bind.
      eapply CPureSpecM.mon_bind. now apply rm.
      intros [] [] [ra Heq]. cbn in ra, Heq. subst.
      now apply rf.
    Qed.

    #[export] Instance mon_debug {Γ} `{RA : relation A} m :
      Monotonic (MStoreT RA) m ->
      Monotonic (MStoreT RA) (debug (Γ := Γ) m).
    Proof.
      intros rm δ1 ? <-. unfold debug. cbn.
      now apply mon_debug, rm.
    Qed.

    #[local] Notation "' x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
          format "' x  <-  ma  ;;  mb") : mut_scope.
    #[local] Notation "x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, ma at level 90, mb at level 200, right associativity) : mut_scope.
    #[local] Notation "ma ;; mb" := (bind ma (fun _ => mb)) : mut_scope.

    Definition pushpop {A Γ1 Γ2 x σ} :
      Val σ -> CStoreT (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A -> CStoreT Γ1 Γ2 A :=
      fun v m δ1 =>
        CPureSpecM.bind (m δ1.[x∷σ ↦ v])
          (fun '(a,δ2) => CPureSpecM.pure (a, env.tail δ2)).

    Definition pushspops {A Γ1 Γ2 Δ} :
      CStore Δ -> CStoreT (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A -> CStoreT Γ1 Γ2 A :=
      fun v m δ1 =>
        CPureSpecM.bind (m (env.cat δ1 v))
          (fun '(a,δ2) => CPureSpecM.pure (a, env.drop Δ δ2)).

    Definition put_local {Γ1 Γ2} : CStore Γ2 -> CStoreT Γ1 Γ2 (CStore Γ1) :=
      fun δ2 => state (fun δ1 => (δ1, δ2)).

    Definition eval_exp {Γ σ} (e : Exp Γ σ) : CStoreT Γ Γ (Val σ) :=
      state (fun δ => (eval e δ, δ)).
    #[global] Arguments eval_exp {Γ σ} e.

    Definition eval_exps {Γ σs} (es : NamedEnv (Exp Γ) σs) : CStoreT Γ Γ (CStore σs) :=
      state (fun δ => (evals es δ, δ)).
    #[global] Arguments eval_exps {Γ σs} es.

    Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} : Val σ -> CStoreT Γ Γ unit :=
      fun v => state (fun δ => (tt, δ ⟪ x ↦ v ⟫)).
    #[global] Arguments assign {Γ} x {σ xIn} v.

    #[export] Instance mon_pushpop {A} {RA : relation A}
      Γ1 Γ2 x σ v (m : CStoreT (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) :
      Monotonic (MStoreT RA) m -> Monotonic (MStoreT RA) (pushpop v m).
    Proof.
      intros rm. unfold MStoreT, pushpop.
      apply monotonic_specialize_eq_refl. intros δ1.
      eapply CPureSpecM.mon_bind'. now apply rm.
      intros [?a ?δ] [?a ?δ] [ra rδ]; cbn in ra, rδ. subst.
      apply CPureSpecM.mon_pure. now constructor.
    Qed.

    #[export] Instance mon_pushspops {A} {RA : relation A}
      Γ1 Γ2 Δ δ (m : CStoreT (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) :
      Monotonic (MStoreT RA) m -> Monotonic (MStoreT RA) (pushspops δ m).
    Proof.
      intros rm. unfold MStoreT, pushpop.
      apply monotonic_specialize_eq_refl. intros δ1.
      eapply CPureSpecM.mon_bind'. now apply rm.
      intros [?a ?δ] [?a ?δ] [ra rδ]; cbn in ra, rδ. subst.
      apply CPureSpecM.mon_pure. now constructor.
    Qed.

    #[export] Instance mon_put_local {Γ1 Γ2} (δ : CStore Γ2) :
      Monotonic (MStoreT eq) (@put_local Γ1 Γ2 δ).
    Proof. eapply mon_state. intros ? ? []; now split. Qed.

    #[export] Instance mon_eval_exp {Γ σ} (e : Exp Γ σ) :
      Monotonic (MStoreT eq) (@eval_exp Γ σ e).
    Proof. eapply mon_state. intros ? ? []; now split. Qed.

    #[export] Instance mon_eval_exps {Γ σs} (es : NamedEnv (Exp Γ) σs) :
      Monotonic (MStoreT eq) (@eval_exps Γ σs es).
    Proof. eapply mon_state. intros ? ? []; now split. Qed.

    #[export] Instance mon_assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : Val σ) :
      Monotonic (MStoreT eq) (@assign Γ x σ xIn v).
    Proof. eapply mon_state. intros ? ? []. now split. Qed.

    #[global] Typeclasses Opaque MStoreT eval_exp bind.

    (* The paper discusses the case that a function call is replaced by
       interpreting the contract instead. However, this is not always
       convenient. We therefore make contracts for functions optional and
       if a function does not have a contract, we continue executing
       the body of the called function. A paramter [inline_fuel] controls the
       number of levels this is allowed before failing execution. Therefore,
       we write the executor in an open-recusion style and [Exec] is the
       closed type of such an executor. *)
    Definition ExecCall := forall Δ τ, 𝑭 Δ τ -> CStore Δ -> M (Val τ).
    Definition ExecCallForeign := forall Δ τ, 𝑭𝑿 Δ τ -> CStore Δ -> M (Val τ).
    Definition ExecLemma := forall Δ, 𝑳 Δ -> CStore Δ -> M unit.
    Definition Exec := forall Γ τ (s : Stm Γ τ), CStoreT Γ Γ (Val τ).

    Definition exec_call_error : ExecCall :=
      fun Δ τ f args => error.

    Section WithExecs.

      Variable exec_call_foreign : ExecCallForeign.
      Variable exec_lemma : ExecLemma.
      Variable exec_call : ExecCall.

      Definition exec_aux : Exec :=
        fix exec_aux {Γ τ} s :=
          match s with
          | stm_val _ v => pure v
          | stm_exp e => eval_exp e
          | stm_let x σ s__σ s__τ =>
              t <- exec_aux s__σ;;
              pushpop t (exec_aux s__τ)
          | stm_block δ s =>
              pushspops δ (exec_aux s)
          | stm_assign x s =>
              t <- exec_aux s;;
              _ <- assign x t;;
              pure t
          | stm_call f es =>
              args <- eval_exps es ;;
              liftM (exec_call f args)
          | stm_call_frame δf s =>
              δ1  <- put_local δf;;
              res <- exec_aux s ;;
              _   <- put_local δ1 ;;
              pure res
          | stm_foreign f es =>
              args <- eval_exps es ;;
              liftM (exec_call_foreign f args)
          | stm_lemmak l es k =>
              args <- eval_exps es ;;
              _    <- liftM (exec_lemma l args) ;;
              exec_aux k
          | stm_seq s1 s2 =>
              _ <- exec_aux s1 ;;
              exec_aux s2
          | stm_assertk e _ k =>
              t <- eval_exp e ;;
              (* This uses assume_formula for a partial correctness *)
              (* interpretation of the object language failure effect. *)
              _ <- liftM (assume_formula (t = true)) ;;
              exec_aux k
          | stm_fail _ _ =>
              (* Same as stm_assert: partial correctness of failure. *)
              liftM block
          | stm_read_register reg =>
              t <- liftM (angelic _) ;;
              _ <- liftM (consume_chunk (scchunk_ptsreg reg t)) ;;
              _ <- liftM (produce_chunk (scchunk_ptsreg reg t)) ;;
              pure t
          | stm_write_register reg e =>
              told <- liftM (angelic _) ;;
              _    <- liftM (consume_chunk (scchunk_ptsreg reg told)) ;;
              tnew <- eval_exp e ;;
              _    <- liftM (produce_chunk (scchunk_ptsreg reg tnew)) ;;
              pure tnew
          | stm_pattern_match s pat rhs =>
              v  <- exec_aux s ;;
              '(existT pc δpc) <- liftM (demonic_pattern_match pat v) ;;
              pushspops δpc (exec_aux (rhs pc))
          | stm_bind s k =>
              v  <- exec_aux s ;;
              exec_aux (k v)
          | stm_debugk k =>
              debug (exec_aux k)
          end.

      Context
        (rexec_call_foreign : MonotonicExecCallForeign exec_call_foreign)
        (rexec_lemma : MonotonicExecLemma exec_lemma)
        (rexec_call : MonotonicExecCall exec_call).

      Typeclasses Opaque pure bind.
      #[export] Instance mon_exec_aux : MonotonicExec exec_aux.
      Proof. induction s; cbn - [Val]; typeclasses eauto. Qed.

    End WithExecs.
    #[global] Arguments mon_exec_aux [_ _ _] _ _ _ [Γ τ] s.

    Section WithExec.

      Context (exec : Exec).

      Import CPureSpecM.notations.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : M unit :=
        match c with
        | MkSepContract _ _ lvars pats req result ens =>
            lenv <- demonic_ctx lvars ;;
            _    <- evalCReaderT (cproduce req) lenv ;;
            v    <- evalCStoreT (exec s) (inst pats lenv) ;;
            evalCReaderT (cconsume ens) (env.snoc lenv (result∷τ) v)
        end.

    End WithExec.

  End Exec.
  #[global] Arguments CStoreT M Γ1 Γ2 A : clear implicits.
  #[global] Arguments MStoreT [M] _ Γ1 Γ2 {A} RA.
  #[global] Arguments ExecCallForeign M : clear implicits.
  #[global] Arguments ExecLemma M : clear implicits.
  #[global] Arguments ExecCall M : clear implicits.
  #[global] Arguments Exec M : clear implicits.

  Notation MonotonicExec exec :=
    (forall Γ τ (s : Stm Γ τ),
        Monotonic (MStoreT _ _ _ eq) (exec Γ τ s)).

End ShallowExecOn.
