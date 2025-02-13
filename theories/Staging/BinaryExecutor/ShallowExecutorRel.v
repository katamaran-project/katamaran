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
     Program.Basics
     Program.Tactics
     Strings.String
     Relations.Relation_Definitions
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Bitvector
     Notations
     Prelude
     Signature
     Symbolic.Propositions
     Syntax.BinOps
     Specification.

From stdpp Require base list option.

Import ctx.notations.
Import env.notations.
Import ListNotations.
Import SignatureNotations.

Set Implicit Arguments.

(* This is an adaptation of the regular shallow executor to do relational verification for
   verifying constant-timeness. It is intended to apply the same algorithm as BinSec/Rel
   by Lesly-Ann Daniel.
 *)

Module Type ShallowExecRelOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG).

  (* The following definitions are relational variants of the ones in ShallowExecutor.v.
   *)

  Inductive RelVal (τ : Ty) : Set :=
  | SyncVal : Val τ -> RelVal τ
  | NonSyncVal : Val τ -> Val τ -> RelVal τ
  .

  Definition projLeft {σ} (rv : RelVal σ) : Val σ :=
    match rv with
    | SyncVal _ v => v
    | NonSyncVal _ vl _ => vl
    end.

  Definition projRight {σ} (rv : RelVal σ) : Val σ :=
    match rv with
    | SyncVal _ v => v
    | NonSyncVal _ _ vr => vr
    end.

  Definition syncNamedEnv {N} {Γ : NCtx N Ty} : NamedEnv Val Γ -> NamedEnv RelVal Γ :=
    env.map (fun b => SyncVal _).

  Definition nonsyncNamedEnv {N} {Γ : NCtx N Ty} : NamedEnv Val Γ -> NamedEnv Val Γ -> NamedEnv RelVal Γ :=
    env.zipWith (fun b => NonSyncVal _).

  Fixpoint unliftNamedEnv {N} {Γ : NCtx N Ty} (vs : NamedEnv RelVal Γ) : NamedEnv Val Γ + (NamedEnv Val Γ * NamedEnv Val Γ) :=
    match vs with
    | []%env => inl []%env
    | env.snoc vs k v =>
        match (v , unliftNamedEnv vs) with
        | (SyncVal _ v' , inl vs') => inl (vs' .[ k ↦ v'])
        | (_ , inl vs') => inr (vs' .[ k ↦ projLeft v ] , (vs' .[ k ↦ projRight v ]))
        | (_ , inr (vs1' , vs2')) => inr (vs1' .[ k ↦ projLeft v ] , (vs2' .[ k ↦ projRight v ]))
        end
    end.

  Definition SCChunkRel := Chunk RelVal.
  Notation CStoreRel := (NamedEnv RelVal).
  Definition SCHeapRel := list SCChunkRel.

  Definition CStoreSpecRel (Γ1 Γ2 : PCtx) (A : Type) : Type :=
    (A -> CStoreRel Γ2 -> SCHeapRel -> Prop) -> CStoreRel Γ1 -> SCHeapRel -> Prop.

  Definition MStoreSpecRel (Γ1 Γ2 : PCtx) [A] (MA : relation A) :
    relation (CStoreSpecRel Γ1 Γ2 A) :=
    (MA ==> CStoreRel Γ2 ::> SCHeapRel ::> impl) ==> CStoreRel Γ1 ::> SCHeapRel ::> impl.
  #[global] Arguments MStoreSpecRel Γ1 Γ2 [A] MA.

  Definition CHeapSpecRel (A : Type) : Type :=
    (A -> SCHeapRel -> Prop) -> SCHeapRel -> Prop.

  Definition MHeapSpecRel [A] (MA : relation A) :
    relation (CHeapSpecRel A) :=
    (MA ==> SCHeapRel ::> impl) ==> SCHeapRel ::> impl.
  #[global] Arguments MHeapSpecRel [A] MA.

  Definition ExecCallRel := forall Δ τ, 𝑭 Δ τ -> CStoreRel Δ -> CHeapSpecRel (RelVal τ).
  Definition ExecCallForeignRel := forall Δ τ, 𝑭𝑿 Δ τ -> CStoreRel Δ -> CHeapSpecRel (RelVal τ).
  Definition ExecLemmaRel := forall Δ, 𝑳 Δ -> CStoreRel Δ -> CHeapSpecRel unit.
  Definition ExecRel := forall Γ τ (s : Stm Γ τ), CStoreSpecRel Γ Γ (RelVal τ).

  Notation MonotonicExecCallRel exec_call :=
    (forall Δ τ (f : 𝑭 Δ τ) (δ : CStoreRel Δ),
       Monotonic (MHeapSpecRel eq) (exec_call Δ τ f δ)).
  Notation MonotonicExecCallForeignRel exec_call_foreign :=
    (forall Δ τ (f : 𝑭𝑿 Δ τ) (δ : CStoreRel Δ),
       Monotonic (MHeapSpecRel eq) (exec_call_foreign Δ τ f δ)).
  Notation MonotonicExecLemmaRel exec_lemma :=
    (forall Δ (l : 𝑳 Δ) (δ : CStoreRel Δ),
       Monotonic (MHeapSpecRel eq) (exec_lemma Δ l δ)).
  Notation MonotonicExecRel exec :=
    (forall Γ τ (s : Stm Γ τ),
       Monotonic (MStoreSpecRel Γ Γ eq) (exec Γ τ s)).

  Module CPureSpecAdditions.
    Import CPureSpec.
    Import CPureSpec.notations.
    
    Definition MatchResultRel (N : Set) (σ : Ty) (pat : Pattern σ) : Type := {c : PatternCase pat & @NamedEnv N Ty RelVal (PatternCaseCtx c)}.

    Definition demonic_pattern_match_rel_pure {N σ} (pat : @Pattern N σ)
      (v : RelVal σ) : CPureSpec (MatchResultRel pat) :=
      match v with
      | SyncVal _ v => '(existT pc vals) <- CPureSpec.demonic_pattern_match pat v ;;
                       pure (existT pc (syncNamedEnv vals))
      | NonSyncVal _ vl vr =>
          '(existT pc valsl) <- CPureSpec.demonic_pattern_match pat vl ;;
          valsr <- angelic_ctx (PatternCaseCtx pc) ;;
          _  <- assert_formula (pattern_match_val_reverse pat pc valsr = vr);;
          pure (existT pc (nonsyncNamedEnv valsl valsr))
      end.
      #[global] Arguments demonic_pattern_match_rel_pure {N σ} pat v.

      #[export] Instance mon_demonic_pattern_match_rel_pure {N σ} (pat : @Pattern N σ) v :
        Monotonic (MPureSpec eq) (@demonic_pattern_match_rel_pure _ _ pat v).
      Proof. destruct v; typeclasses eauto. Qed.

    Fixpoint assert_eq_chunk (c1 c2 : SCChunkRel) : CPureSpec unit :=
      match c1 , c2 with
      | scchunkrel_user p1 vs1 , scchunkrel_user p2 vs2 =>
          match eq_dec p1 p2 with
          | left e => assert_eq_env (eq_rect p1 (fun p => Env Val (𝑯_Ty p)) vs1 p2 e) vs2
          | right _ => error
          end
      | scchunkrel_ptsreg r1 v1 , scchunkrel_ptsreg r2 v2 =>
          match eq_dec_het r1 r2 with
          | left e => assert_formula (eq_rect _ Val v1 _ (f_equal projT1 e) = v2)
          | right _ => error
          end
      | scchunkrel_conj c11 c12 , scchunkrel_conj c21 c22 =>
          assert_eq_chunk c11 c21 ;; assert_eq_chunk c12 c22
      | scchunkrel_wand c11 c12 , scchunkrel_wand c21 c22 =>
          assert_eq_chunk c11 c21 ;; assert_eq_chunk c12 c22
      | _ , _ => error
      end.

  End CPureSpecAdditions.

  Module CHeapSpecRel.

    Definition run : CHeapSpecRel unit -> Prop :=
      (* We use the FINISH alias of True for the purpose
         of counting nodes in a shallowly-generated VC. *)
      fun m => m (fun _ h1 => FINISH) List.nil.

    Definition lift_purespec {A : Type} :
      CPureSpec A -> CHeapSpecRel A :=
      fun m Φ h0 => m (fun a1 => Φ a1 h0).

    Definition pure {A} a := lift_purespec (@CPureSpec.pure A a).

    Definition bind {A B} : CHeapSpecRel A -> (A -> CHeapSpecRel B) -> CHeapSpecRel B :=
      fun m f Φ h => m (fun a1 => f a1 Φ) h.

    Module Import notations.
      Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
             format "' x  <-  ma  ;;  mb").
      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at level 90, mb at level 200, right associativity).
      Notation "ma ;; mb" := (bind ma (fun _ => mb)).
    End notations.

    Definition debug {A} : CHeapSpecRel A -> CHeapSpecRel A :=
      fun m => m.

    Definition angelic_binary {A} : CHeapSpecRel A -> CHeapSpecRel A -> CHeapSpecRel A :=
      fun m1 m2 Φ h => m1 Φ h \/ m2 Φ h.
    Definition demonic_binary {A} : CHeapSpecRel A -> CHeapSpecRel A -> CHeapSpecRel A :=
      fun m1 m2 Φ h => m1 Φ h /\ m2 Φ h.

    Definition angelic (σ : Ty) : CHeapSpecRel (Val σ) :=
      lift_purespec (CPureSpec.angelic σ).
    #[global] Arguments angelic σ Φ : rename.
    Definition demonic (σ : Ty) : CHeapSpecRel (Val σ) :=
      lift_purespec (CPureSpec.demonic σ).
    #[global] Arguments demonic σ Φ : rename.

    Definition angelic_ctx {N} (Δ : NCtx N Ty) : CHeapSpecRel (NamedEnv Val Δ) :=
      lift_purespec (CPureSpec.angelic_ctx Δ).
    #[global] Arguments angelic_ctx {N} Δ.
    Definition demonic_ctx {N} (Δ : NCtx N Ty) : CHeapSpecRel (NamedEnv Val Δ) :=
      lift_purespec (CPureSpec.demonic_ctx Δ).
    #[global] Arguments demonic_ctx {N} Δ.

    Definition assert_formula : Prop -> CHeapSpecRel unit :=
      fun fml => lift_purespec (CPureSpec.assert_formula fml).
    Definition assume_formula : Prop -> CHeapSpecRel unit :=
      fun fml => lift_purespec (CPureSpec.assume_formula fml).

    Definition produce_chunk (c : SCChunkRel) : CHeapSpecRel unit :=
      fun Φ h => CPureSpec.produce_chunk c h (Φ tt).
    Definition consume_chunk (c : SCChunk) : CHeapSpecRel unit :=
      fun Φ h => CPureSpec.consume_chunk c h (Φ tt).

    Definition read_register {τ} (reg : 𝑹𝑬𝑮 τ) : CHeapSpecRel (Val τ) :=
      fun Φ h => CPureSpec.read_register reg h (fun '(t,h') => Φ t h').
    Definition write_register {τ} (reg : 𝑹𝑬𝑮 τ) (v : Val τ) : CHeapSpecRel (Val τ) :=
      fun Φ h => CPureSpec.write_register reg v h (fun '(v',h') => Φ v' h').

    Fixpoint produce {Σ} (asn : Assertion Σ) (ι : Valuation Σ) : CHeapSpecRel unit :=
      match asn with
      | asn.formula fml =>
          assume_formula (instprop fml ι)
      | asn.chunk c =>
          produce_chunk (inst c ι)
      | asn.chunk_angelic c =>
          produce_chunk (inst c ι)
      | asn.pattern_match s pat rhs =>
          '(existT pc δpc) <-
            lift_purespec (CPureSpec.demonic_pattern_match pat (inst s ι)) ;;
          produce (rhs pc) (ι ►► δpc)
      | asn.sep a1 a2 =>
          _ <- produce a1 ι ;;
          produce a2 ι
      | asn.or a1 a2 =>
          demonic_binary (produce a1 ι) (produce a2 ι)
      | asn.exist ς τ a =>
          t <- demonic τ ;;
          produce a (env.snoc ι (ς∷τ) t)
      | asn.debug =>
          debug (pure tt)
      end.

    Fixpoint consume {Σ} (asn : Assertion Σ) (ι : Valuation Σ) : CHeapSpecRel unit :=
      match asn with
      | asn.formula fml =>
          assert_formula (instprop fml ι)
      | asn.chunk c =>
          consume_chunk (inst c ι)
      | asn.chunk_angelic c =>
          consume_chunk (inst c ι)
      | asn.pattern_match s pat rhs =>
          '(existT pc δpc) <-
            lift_purespec (CPureSpec.angelic_pattern_match pat (inst s ι)) ;;
          consume (rhs pc) (ι ►► δpc)
      | asn.sep a1 a2 =>
          _ <- consume a1 ι ;;
          consume a2 ι
      | asn.or a1 a2 =>
          angelic_binary (consume a1 ι) (consume a2 ι)
      | asn.exist ς τ a =>
          t <- angelic τ ;;
          consume a (env.snoc ι (ς∷τ) t)
      | asn.debug =>
          debug (pure tt)
      end.

    Definition call_contract [Δ τ] (c : SepContract Δ τ) (args : CStore Δ) : CHeapSpecRel (Val τ) :=
      match c with
      | MkSepContract _ _ Σe δ req result ens =>
          ι <- lift_purespec (CPureSpec.angelic_ctx Σe) ;;
          lift_purespec (CPureSpec.assert_eq_nenv (inst δ ι) args) ;;
          consume req ι ;;
          v <- demonic τ ;;
          produce ens (env.snoc ι (result∷τ) v) ;;
          pure v
      end.

    Definition call_lemma [Δ] (lem : Lemma Δ) (vs : CStore Δ) : CHeapSpecRel unit :=
      match lem with
      | MkLemma _ Σe δ req ens =>
          ι <- lift_purespec (CPureSpec.angelic_ctx Σe) ;;
          lift_purespec (CPureSpec.assert_eq_nenv (inst δ ι) vs) ;;
          consume req ι ;;
          produce ens ι
      end.

    #[export] Instance mon_run :
      Monotonic (MHeapSpec eq ==> impl) run.
    Proof. intros m1 m2 mm. now apply mm. Qed.

    Lemma mon_lift_purespec' `{MA : relation A} :
      Monotonic (MPureSpec MA ==> MHeapSpec MA) (lift_purespec).
    Proof. intros ? ? rm ? ? rΦ h. apply rm. intros ? ? ra. now apply rΦ. Qed.

    #[export] Instance mon_lift_purespec `{MA : relation A} m :
      Monotonic (MPureSpec MA) m -> Monotonic (MHeapSpec MA) (lift_purespec m).
    Proof. intros rm. now apply mon_lift_purespec'. Qed.

    Lemma mon_pure' `{MA : relation A} :
      Monotonic (MA ==> MHeapSpec MA) pure.
    Proof. firstorder. Qed.

    #[export] Instance mon_pure `{MA : relation A} x :
      Monotonic MA x -> Monotonic (MHeapSpec MA) (pure x).
    Proof. firstorder. Qed.

    Lemma mon_bind' `{MA : relation A, RB : relation B} :
      Monotonic (MHeapSpec MA ==> (MA ==> MHeapSpec RB) ==> MHeapSpec RB) bind.
    Proof.
      intros ? ? rm ? ? rf ? ? rΦ. apply rm. intros ? ? ra.
      apply rf. apply ra. intros ? ? rb. apply rΦ, rb.
    Qed.

    #[export] Instance mon_bind `{MA : relation A, RB : relation B}
      (m : CHeapSpecRel A) (f : A -> CHeapSpecRel B) :
      Monotonic (MHeapSpec MA) m ->
      Monotonic (MA ==> MHeapSpec RB) f ->
      Monotonic (MHeapSpec RB) (bind m f).
    Proof. intros rm rf. eapply mon_bind'; eauto. Qed.

    #[export] Instance mon_debug `{MA : relation A} m :
      Monotonic (MHeapSpec MA) m -> Monotonic (MHeapSpec MA) (debug m).
    Proof. now unfold debug. Qed.

    #[export] Instance mon_angelic_binary `{MA : relation A} m1 m2 :
      Monotonic (MHeapSpec MA) m1 -> Monotonic (MHeapSpec MA) m2 ->
      Monotonic (MHeapSpec MA) (angelic_binary m1 m2).
    Proof. firstorder. Qed.

    #[export] Instance mon_demonic_binary `{MA : relation A} m1 m2 :
      Monotonic (MHeapSpec MA) m1 -> Monotonic (MHeapSpec MA) m2 ->
      Monotonic (MHeapSpec MA) (demonic_binary m1 m2).
    Proof. firstorder. Qed.

    #[global] Typeclasses Opaque run lift_purespec pure bind debug angelic_binary
      demonic_binary.

    #[export] Instance mon_angelic σ :
      Monotonic (MHeapSpec eq) (angelic σ).
    Proof. typeclasses eauto. Qed.
    #[export] Instance mon_demonic σ :
      Monotonic (MHeapSpec eq) (demonic σ).
    Proof. typeclasses eauto. Qed.

    #[export] Instance mon_assert_formula fml :
      Monotonic (MHeapSpec eq) (assert_formula fml).
    Proof. firstorder. Qed.
    #[export] Instance mon_assume_formula fml :
      Monotonic (MHeapSpec eq) (assume_formula fml).
    Proof. firstorder. Qed.

    #[export] Instance mon_produce_chunk c : Monotonic (MHeapSpec eq) (produce_chunk c).
    Proof.
      intros Φ1 Φ2 mΦ h.
      apply CPureSpec.mon_produce_chunk.
      intros ? ? ->. now apply mΦ.
    Qed.

    #[export] Instance mon_consume_chunk c : Monotonic (MHeapSpec eq) (consume_chunk c).
    Proof.
      intros Φ1 Φ2 mΦ h.
      apply CPureSpec.mon_consume_chunk.
      intros ? ? ->. now apply mΦ.
    Qed.

    #[export] Instance mon_read_register {τ} (reg : 𝑹𝑬𝑮 τ) :
      Monotonic (MHeapSpec eq) (read_register reg).
    Proof.
      intros Φ1 Φ2 mΦ h.
      apply CPureSpec.mon_read_register.
      intros ? [] ->. now apply mΦ.
    Qed.

    #[export] Instance mon_write_register {τ} (reg : 𝑹𝑬𝑮 τ) (v : Val τ) :
      Monotonic (MHeapSpec eq) (write_register reg v).
    Proof.
      intros Φ1 Φ2 mΦ h.
      apply CPureSpec.mon_write_register.
      intros ? [] ->. now apply mΦ.
    Qed.

    #[global] Typeclasses Opaque angelic demonic assert_formula assume_formula
      produce_chunk consume_chunk read_register write_register.

    #[export] Instance mon_produce {Σ} (asn : Assertion Σ) ι :
      Monotonic (MHeapSpec eq) (produce asn ι).
    Proof. induction asn; cbn; typeclasses eauto. Qed.

    #[export] Instance mon_consume {Σ} (asn : Assertion Σ) ι :
      Monotonic (MHeapSpec eq) (consume asn ι).
    Proof. induction asn; cbn; typeclasses eauto. Qed.

    #[export] Instance mon_call_contract
      [Δ τ] (c : SepContract Δ τ) (args : CStore Δ) :
      Monotonic (MHeapSpec eq) (call_contract c args).
    Proof. destruct c; typeclasses eauto. Qed.

    #[export] Instance mon_call_lemma
      [Δ] (lem : Lemma Δ) (vs : CStore Δ) :
      Monotonic (MHeapSpec eq) (call_lemma lem vs).
    Proof. destruct lem; typeclasses eauto. Qed.

    #[global] Typeclasses Opaque produce consume call_contract call_lemma.

    Section WithBI.

      Import iris.proofmode.tactics.

      Context {L} {biA : BiAffine L} {PI : PredicateDef L}.

      #[local] Arguments CHeapSpecRel.bind {_ _} _ _ _ /.
      #[local] Arguments CHeapSpecRel.angelic_binary {_} _ _ /.
      #[local] Arguments CHeapSpecRel.demonic_binary {_} _ _ /.
      #[local] Arguments CHeapSpecRel.lift_purespec {_} _ _ /.

      Lemma consume_sound {Σ} {ι : Valuation Σ} {asn : Assertion Σ} :
        forall (Φ : unit -> SCHeap -> Prop) h,
          consume asn ι Φ h ->
          (interpret_scheap h ⊢ asn.interpret asn ι ∗ ∃ h', interpret_scheap h' ∧ ⌜ Φ tt h' ⌝)%I.
      Proof.
        induction asn; cbn - [inst inst_term]; intros Φ h1.
        - intros [Hfmle HΦ]. rewrite <-bi.emp_sep at 1. apply bi.sep_mono'.
          + rewrite bi.and_emp; auto.
          + apply bi.exist_intro' with h1. apply bi.and_intro; auto.
        - intros ->%CPureSpec.wp_consume_chunk. now rewrite interpret_scchunk_inst.
        - intros ->%CPureSpec.wp_consume_chunk. now rewrite interpret_scchunk_inst.
        - rewrite CPureSpec.wp_angelic_pattern_match.
          destruct pattern_match_val; auto.
        - intros ->%IHasn1. rewrite -bi.sep_assoc. apply bi.sep_mono'; [easy|].
          apply bi.exist_elim. intros h2. apply bi.pure_elim_r. apply IHasn2.
        - intros [->%IHasn1 | ->%IHasn2]; apply bi.sep_mono'; auto.
        - intros (v & ->%IHasn). apply bi.sep_mono'; [|easy].
          now apply bi.exist_intro' with v.
        - intros HΦ. rewrite bi.emp_sep. apply bi.exist_intro' with h1.
          apply bi.and_intro; auto.
      Qed.

      Lemma produce_sound {Σ} {ι : Valuation Σ} {asn : Assertion Σ} :
        forall (Φ : unit -> SCHeap -> Prop) h,
          produce asn ι Φ h ->
          (interpret_scheap h ⊢
             asn.interpret asn ι -∗ ∃ h', interpret_scheap h' ∧ ⌜Φ tt h'⌝).
      Proof.
        induction asn; cbn - [CPureSpec.assume_formula inst inst_term]; intros Φ h.
        - iIntros (HΦ) "Hh [%Hfml _]". iExists h. auto.
        - intros ->%CPureSpec.wp_produce_chunk; now rewrite interpret_scchunk_inst.
        - intros ->%CPureSpec.wp_produce_chunk; now rewrite interpret_scchunk_inst.
        - rewrite CPureSpec.wp_demonic_pattern_match.
          destruct pattern_match_val; auto.
        - iIntros (Hprod1) "H [Hasn1 Hasn2]".
          iPoseProof (IHasn1 _ _ _ Hprod1 with "H Hasn1") as "(%h2 & H & %Hprod2)".
          iPoseProof (IHasn2 _ _ _ Hprod2 with "H Hasn2") as "(%h3 & H & %HΦ)".
          iExists h3. auto.
        - iIntros ([HΦ1 HΦ2]) "Hh [Hasn1|Hasn2]".
          iApply (IHasn1 with "Hh Hasn1"); auto.
          iApply (IHasn2 with "Hh Hasn2"); auto.
        - iIntros (HΦ) "Hh [%v Hasn]".
          now iApply (IHasn with "Hh Hasn").
        - iIntros (HΦ) "Hh _". iExists h. auto.
      Qed.

    End WithBI.

  End CHeapSpecRel.
  Export (hints) CHeapSpecRel.

  Module CStoreSpecRel.

    Section Basic.

      Definition evalStoreSpecRel {Γ1 Γ2 A} :
        CStoreSpecRel Γ1 Γ2 A -> CStoreRel Γ1 -> CHeapSpecRel A :=
        fun m δ Φ => m (fun a1 _ => Φ a1) δ.

      Definition lift_purespecrel {Γ} {A : Type} :
        CPureSpec A -> CStoreSpecRel Γ Γ A :=
        fun m POST δ h => m (fun a => POST a δ h).
      Definition lift_heapspecrel {Γ} {A : Type} :
        CHeapSpecRel A -> CStoreSpecRel Γ Γ A :=
        fun m POST δ => m (fun a => POST a δ).

      Definition pure {Γ A} (a : A) : CStoreSpecRel Γ Γ A :=
        fun POST => POST a.
      Definition bind {Γ1 Γ2 Γ3 A B} (ma : CStoreSpecRel Γ1 Γ2 A) (f : A -> CStoreSpecRel Γ2 Γ3 B) : CStoreSpecRel Γ1 Γ3 B :=
        fun POST => ma (fun a => f a POST).

      Definition error {Γ1 Γ2 A} : CStoreSpecRel Γ1 Γ2 A :=
        fun POST δ h => FALSE.
      Definition block {Γ1 Γ2 A} : CStoreSpecRel Γ1 Γ2 A :=
        fun POST δ h => TRUE.

      Definition demonic_binary {Γ1 Γ2 A} (m1 m2 : CStoreSpecRel Γ1 Γ2 A) : CStoreSpecRel Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h /\ m2 POST δ h.
      Definition angelic_binary {Γ1 Γ2 A} (m1 m2 : CStoreSpecRel Γ1 Γ2 A) : CStoreSpecRel Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h \/ m2 POST δ h.

      Definition demonic {Γ} (σ : Ty) : CStoreSpecRel Γ Γ (Val σ) :=
        lift_purespecrel (CPureSpec.demonic σ).
      Definition angelic {Γ} (σ : Ty) : CStoreSpecRel Γ Γ (Val σ) :=
        lift_purespecrel (CPureSpec.angelic σ).

      Definition angelic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CStoreSpecRel Γ Γ (NamedEnv Val Δ) :=
        fun Δ => lift_purespecrel (CPureSpec.angelic_ctx Δ).
      #[global] Arguments angelic_ctx {N Γ} Δ.

      Definition demonic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CStoreSpecRel Γ Γ (NamedEnv Val Δ) :=
        fun Δ => lift_purespecrel (CPureSpec.demonic_ctx Δ).
      #[global] Arguments demonic_ctx {N Γ} Δ.

      Lemma mon_evalStoreSpecRel' {Γ1 Γ2} `{MA : relation A} :
        Monotonic (MStoreSpecRel Γ1 Γ2 MA ==> CStoreRel Γ1 ::> MHeapSpecRel MA) evalStoreSpecRel.
      Proof. intros ? ? rm δ ? ? rΦ. apply rm. intros ? ? ? _. now apply rΦ. Qed.

      #[export] Instance mon_evalStoreSpec {Γ1 Γ2} `{MA : relation A} ma δ1 :
        Monotonic (MStoreSpecRel Γ1 Γ2 MA) ma ->
        Monotonic (MHeapSpecRel MA) (evalStoreSpecRel ma δ1).
      Proof. intros rma. now apply mon_evalStoreSpecRel'. Qed.

      Lemma mon_lift_purespecrel' `{MA : relation A} {Γ} :
        Monotonic (MPureSpec MA ==> MStoreSpecRel Γ Γ MA) lift_purespecrel.
      Proof. intros ? ? rm ? ? rΦ ? ?. apply rm. intros ? ? ?. now apply rΦ. Qed.

      #[export] Instance mon_lift_purespecrel `{MA : relation A} {Γ} m :
        Monotonic (MPureSpec MA) m -> Monotonic (MStoreSpecRel Γ Γ MA) (lift_purespecrel m).
      Proof. intros rm. now apply mon_lift_purespecrel'. Qed.

      Lemma mon_lift_heapspecrel' `{MA : relation A} {Γ} :
        Monotonic (MHeapSpecRel MA ==> MStoreSpecRel Γ Γ MA) lift_heapspecrel.
      Proof. intros ? ? rm ? ? rΦ ?. apply rm. intros ? ? ?. now apply rΦ. Qed.

      #[export] Instance mon_lift_heapspecrel `{MA : relation A} {Γ} m :
        Monotonic (MHeapSpecRel MA) m -> Monotonic (MStoreSpecRel Γ Γ MA) (lift_heapspecrel m).
      Proof. intros rm. now apply mon_lift_heapspecrel'. Qed.

      Lemma mon_pure' `{MA : relation A} {Γ} :
        Monotonic (MA ==> MStoreSpecRel Γ Γ MA) pure.
      Proof. unfold pure. firstorder. Qed.

      #[export] Instance mon_pure `{MA : relation A} {Γ}  x :
        Monotonic MA x -> Monotonic (MStoreSpecRel Γ Γ MA) (pure x).
      Proof. unfold pure. firstorder. Qed.

      Lemma mon_bind' `{MA : relation A, RB : relation B} {Γ1 Γ2 Γ3} :
        Monotonic (MStoreSpecRel Γ1 Γ2 MA ==> (MA ==> MStoreSpecRel Γ2 Γ3 RB) ==> MStoreSpecRel Γ1 Γ3 RB) bind.
      Proof.
        intros ? ? rm ? ? rf ? ? rΦ. apply rm.
        intros ? ? ra. apply rf. apply ra. apply rΦ.
      Qed.

      #[export] Instance mon_bind `{MA : relation A, RB : relation B} {Γ1 Γ2 Γ3}
        (m : CStoreSpecRel Γ1 Γ2 A) (f : A -> CStoreSpecRel Γ2 Γ3 B) :
        Monotonic (MStoreSpecRel Γ1 Γ2 MA) m ->
        Monotonic (MA ==> MStoreSpecRel Γ2 Γ3 RB) f ->
        Monotonic (MStoreSpecRel Γ1 Γ3 RB) (bind m f).
      Proof. intros rm rf. eapply mon_bind'; eauto. Qed.

      #[export] Instance mon_error `{MA : relation A} {Γ1 Γ2} :
        Monotonic (MStoreSpecRel Γ1 Γ2 MA) error.
      Proof. easy. Qed.

      #[export] Instance mon_block `{MA : relation A} {Γ1 Γ2} :
        Monotonic (MStoreSpecRel Γ1 Γ2 MA) block.
      Proof. easy. Qed.

    End Basic.

    Module CStoreSpecRelNotations.

      Infix "⊗" := demonic_binary (at level 40, left associativity) : mut_scope.
      Infix "⊕" := angelic_binary (at level 50, left associativity) : mut_scope.

      Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
           format "' x  <-  ma  ;;  mb") : mut_scope.
      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at level 90, mb at level 200, right associativity) : mut_scope.
      Notation "ma ;; mb" := (bind ma (fun _ => mb)) : mut_scope.

    End CStoreSpecRelNotations.
    Import CStoreSpecRelNotations.
    Local Open Scope mut_scope.

    Section PatternMatching.

      Import CPureSpecAdditions.
      
      Definition demonic_pattern_match {N : Set} {Γ σ} (pat : @Pattern N σ) (v : RelVal σ) :
        CStoreSpecRel Γ Γ (MatchResultRel pat) :=
        lift_purespecrel (CPureSpecAdditions.demonic_pattern_match_rel_pure pat v).
      #[global] Arguments demonic_pattern_match {N Γ σ} pat v.

      (* Lemma wp_demonic_pattern_match {N : Set} {Γ σ} (pat : @Pattern N σ) (v : RelVal σ) *)
      (*   (Φ : MatchResultRel pat -> CStoreRel Γ -> SCHeapRel -> Prop) (δ : CStoreRel Γ) (h : SCHeapRel) : *)
      (*   demonic_pattern_match pat v Φ δ h <-> Φ (pattern_match_val pat v) δ h. *)
      (* Proof. *)
      (*   unfold demonic_pattern_match, lift_purespecrel. *)
      (*   now rewrite CPureSpec.wp_demonic_pattern_match. *)
      (* Qed. *)

    End PatternMatching.

    Section State.

      Definition pushpop {A Γ1 Γ2 x σ} (v : RelVal σ)
        (d : CStoreSpecRel (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) : CStoreSpecRel Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.tail δ1)) (δ0 ► (x∷σ ↦ v)).
      Definition pushspops {A} {Γ1 Γ2 Δ} (δΔ : CStoreRel Δ)
        (d : CStoreSpecRel (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) : CStoreSpecRel Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.drop Δ δ1)) (δ0 ►► δΔ).
      Definition get_local {Γ} : CStoreSpecRel Γ Γ (CStoreRel Γ) :=
        fun POST δ => POST δ δ.
      Definition put_local {Γ1 Γ2} (δ : CStoreRel Γ2) : CStoreSpecRel Γ1 Γ2 unit :=
        fun POST _ => POST tt δ.

      Definition liftBinOp {σ1 σ2 σ3} (f : Val σ1 -> Val σ2 -> Val σ3) (rv1 : RelVal σ1) (rv2 : RelVal σ2) : RelVal σ3 :=
        match (rv1 , rv2) with
        | (SyncVal _ v1 , SyncVal _ v2) => SyncVal _ (f v1 v2)
        | (_ , _) => NonSyncVal _ (f (projLeft rv1) (projLeft rv2)) (f (projRight rv1) (projRight rv2))
        end.

      Definition liftUnOp {σ1 σ2} (f : Val σ1 -> Val σ2) (rv : RelVal σ1) : RelVal σ2 :=
        match rv with
        | (SyncVal _ v) => SyncVal _ (f v)
        | (NonSyncVal _ vl vr) => NonSyncVal _ (f vl) (f vr)
        end.
      Print Scope env_scope.

      Definition liftNAryOp {N} {σ} {Γ : NCtx N Ty} (f : NamedEnv Val Γ -> Val σ) (args : NamedEnv RelVal Γ) : RelVal σ :=
        match unliftNamedEnv args with
        | inl args' => SyncVal _ (f args')
        | inr (args1' , args2') => NonSyncVal _ (f args1') (f args2')
        end.

      Definition bopEvalRel {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) := liftBinOp (bop.eval op).

      Definition uopEvalRel {σ1 σ2} (op : UnOp σ1 σ2) := liftUnOp (uop.eval op).
        
      Fixpoint evalRel {Γ σ} (e : Exp Γ σ) (δ : CStoreRel Γ) {struct e} : RelVal σ :=
        match e in (Exp _ t) return (RelVal t) with
        | exp_var x           => δ.[??x]
        | exp_val _ l         => SyncVal _ l
        | exp_binop op e1 e2  => bopEvalRel op (evalRel e1 δ) (evalRel e2 δ)
        | exp_unop op e       => uopEvalRel op (evalRel e δ)
        | exp_list es         => list.foldr
                                   (fun e => @liftBinOp _ (ty.list _) (ty.list _) cons (evalRel e δ))
                                   (SyncVal _ ([]%list : Val (ty.list _)))
                                   es
        | exp_bvec es         => Vector.t_rect
                                   _ (fun m (_ : Vector.t (Exp Γ ty.bool) m) => RelVal (ty.bvec m))
                                   (SyncVal (ty.bvec 0) bv.nil)
                                   (fun eb m _ => liftBinOp (@bv.cons m : Val ty.bool -> Val (ty.bvec m) -> Val (ty.bvec (S m))) (evalRel eb δ))
                                   _ es
        | exp_tuple es        => env.Env_rect
                                   (fun σs _ => RelVal (ty.tuple σs))
                                   (SyncVal _ (tt : Val (ty.tuple [])))
                                   (fun σs _ (vs : RelVal (ty.tuple σs)) σ e => @liftBinOp σ (ty.tuple σs) (ty.tuple _) (fun x y => (y , x) : Val (ty.tuple (ctx.snoc σs σ))) (evalRel e δ) vs)
                                   es
        | exp_union U K e     => @liftUnOp (unionk_ty U K) (ty.union U)
                                   (fun v => unionv_fold U (existT K v)) (evalRel e δ)
        | exp_record R es     => @liftNAryOp _ (ty.record R) _ (recordv_fold R)
                                   (env.map (fun xτ e => evalRel e δ) es)
        end.

      Definition evalsRel {Γ Δ : PCtx} (es : NamedEnv (Exp Γ) Δ) (δ : CStoreRel Γ) : CStoreRel Δ :=
        env.map (fun xτ e => evalRel e δ) es.

      Definition eval_exp {Γ σ} (e : Exp Γ σ) : CStoreSpecRel Γ Γ (RelVal σ) :=
        fun POST δ => POST (evalRel e δ) δ.
      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) : CStoreSpecRel Γ Γ (CStoreRel σs) :=
        fun POST δ => POST (evalsRel es δ) δ.
      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : RelVal σ) : CStoreSpecRel Γ Γ unit :=
        fun POST δ => POST tt (δ ⟪ x ↦ v ⟫).
      Global Arguments assign {Γ} x {σ xIn} v.

      #[export] Instance mon_pushpop `{MA : relation A} {Γ1 Γ2 x σ} (v : RelVal σ)
        (d : CStoreSpecRel (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) :
        Monotonic (MStoreSpecRel (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) MA) d ->
        Monotonic (MStoreSpecRel Γ1 Γ2 MA) (pushpop v d).
      Proof. intros md P Q PQ ?. apply md. intros ? ? ma ?. now apply PQ. Qed.

      #[export] Instance mon_pushspops `{MA : relation A} {Γ1 Γ2 Δ} (δΔ : CStoreRel Δ)
        (d : CStoreSpecRel (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) :
        Monotonic (MStoreSpecRel (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) MA) d ->
        Monotonic (MStoreSpecRel Γ1 Γ2 MA) (pushspops δΔ d).
      Proof. intros md P Q PQ ?. apply md. intros ? ? ma ?. now apply PQ. Qed.

      #[export] Instance mon_get_local {Γ} :
        Monotonic (MStoreSpecRel Γ Γ eq) get_local.
      Proof. intros P Q PQ ?. now apply PQ. Qed.

      #[export] Instance mon_put_local {Γ1 Γ2} (δ : CStoreRel Γ2) :
        Monotonic (MStoreSpecRel Γ1 Γ2 eq) (put_local δ).
      Proof. intros P Q PQ ?. now apply PQ. Qed.

      #[export] Instance mon_eval_exp {Γ σ} (e : Exp Γ σ) :
        Monotonic (MStoreSpecRel Γ Γ eq) (eval_exp e).
      Proof. intros P Q PQ ?. now apply PQ. Qed.

      #[export] Instance mon_eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        Monotonic (MStoreSpecRel Γ Γ eq) (eval_exps es).
      Proof. intros P Q PQ ?. now apply PQ. Qed.

      #[export] Instance mon_assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : RelVal σ) :
        Monotonic (MStoreSpecRel Γ Γ eq) (assign x v).
      Proof. intros P Q PQ ?. now apply PQ. Qed.

    End State.

    Section ExecAux.

      Variable exec_call_foreign : ExecCallForeignRel.
      Variable exec_lemma : ExecLemmaRel.
      Variable exec_call : ExecCallRel.

      (* The openly-recursive executor. *)
      Definition exec_aux : ExecRel :=
        fix exec_aux {Γ τ} (s : Stm Γ τ) : CStoreSpecRel Γ Γ (RelVal τ) :=
          match s with
          | stm_val _ l => pure (SyncVal _ l)
          | stm_exp e => eval_exp e
          | stm_let x σ s k =>
              v <- exec_aux s ;;
              pushpop v (exec_aux k)
          | stm_block δ k =>
              (* runtime-only syntax, no need to support here *)
              error
          | stm_assign x e =>
              v <- exec_aux e ;;
              _ <- assign x v ;;
              pure v
          | stm_call f es =>
              args <- eval_exps es ;;
              lift_heapspecrel (exec_call f args)
          | stm_foreign f es =>
              ts <- eval_exps es ;;
              lift_heapspecrel (exec_call_foreign f ts)
          | stm_lemmak l es k =>
              ts <- eval_exps es ;;
              _  <- lift_heapspecrel (exec_lemma l ts) ;;
              exec_aux k
          | stm_call_frame δ' s =>
              (* runtime-only syntax, no need to support here *)
              error
          | stm_seq e k => _ <- exec_aux e ;; exec_aux k
          | stm_assertk e1 _ k =>
              v <- eval_exp e1 ;;
              _ <- lift_purespecrel (CPureSpec.assume_formula (v = SyncVal ty.bool true)) ;;
              exec_aux k
          | stm_fail _ s =>
              block
          | stm_pattern_match s pat rhs =>
              (* v  <- exec_aux s ;; *)
              (* TODO  *)
              v  <- exec_aux s ;;
              '(existT pc δpc) <- demonic_pattern_match pat v ;;
              pushspops δpc (exec_aux (rhs pc))
          | stm_read_register reg =>
              (* TODO  *)
              error
          (* lift_heapspecrel (CHeapSpec.read_register reg) *)
          | stm_write_register reg e =>
              (* TODO  *)
              error
          (* v__new <- eval_exp e ;; *)
          (* lift_heapspecrel (CHeapSpec.write_register reg v__new) *)
          | stm_bind s k =>
              (* shallow bind unsupportable in the relational version but shouldn't appear in the source *)
              error
          | stm_debugk k =>
              exec_aux k
          end.

      Context
        (mexec_call_foreign : MonotonicExecCallForeignRel exec_call_foreign)
        (mexec_lemma : MonotonicExecLemmaRel exec_lemma)
        (mexec_call : MonotonicExecCallRel exec_call).

      Import CPureSpecAdditions.
      
      #[export] Instance mon_exec_aux : MonotonicExecRel exec_aux.
      Proof. induction s; typeclasses eauto. Qed.

    End ExecAux.
    #[global] Arguments exec_aux _ _ _ [Γ τ] !s.

  End CStoreSpecRel.

  Section WithExec.

    Context (exec : ExecRel) (mexec : MonotonicExecRel exec).

    Import (hints) CStoreSpecRel.
    Import CHeapSpec.notations.

    Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : CHeapSpecRel unit :=
      match c with
      | MkSepContract _ _ lvars pats req result ens =>
          lenv <- CHeapSpec.demonic_ctx lvars ;;
          _    <- CHeapSpec.produce req lenv ;;
          v    <- CStoreSpecRel.evalStoreSpecRel (exec s) (inst pats lenv) ;;
          CHeapSpec.consume ens (env.snoc lenv (result∷τ) v)
      end.

    Lemma mon_exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
      Monotonic (MHeapSpecRel eq) (exec_contract c s).
    Proof. destruct c. typeclasses eauto. Qed.

  End WithExec.

  Section WithSpec.

    Definition exec_call_error : ExecCall :=
      fun Δ τ f args => CHeapSpec.lift_purespecrel CPureSpec.error.

    Definition cexec_call_foreign : ExecCallForeign :=
      fun Δ τ f args =>
        CHeapSpec.call_contract (CEnvEx f) args.

    Definition cexec_lemma : ExecLemma :=
      fun Δ l args =>
        CHeapSpec.call_lemma (LEnv l) args.

    Import CHeapSpec.notations.

    Definition debug_call [Δ τ] (f : 𝑭 Δ τ) (args : CStoreRel Δ) : CHeapSpec unit :=
      CHeapSpec.pure tt.

    (* If a function does not have a contract, we continue executing the body of
       the called function. A parameter [inline_fuel] bounds the number of
       allowed levels before failing execution. *)
    Fixpoint cexec_call (inline_fuel : nat) : ExecCall :=
      fun Δ τ f args =>
        _ <- debug_call f args ;;
        (* Let's first see if we have a contract defined for function [f]
           and then if we have enough fuel for inlining. *)
        match CEnv f , inline_fuel with
        | Some c , _ =>
            (* YES: Execute the call by interpreting the contract. *)
            CHeapSpec.call_contract c args
        | None   , 0 =>
            (* Out of fuel *)
            exec_call_error f args
        | None   , S n =>
            CStoreSpecRel.evalStoreSpecRel
              (CStoreSpecRel.exec_aux cexec_call_foreign cexec_lemma (cexec_call n) (FunDef f))
              args
        end.

    Definition cexec (inline_fuel : nat) : Exec :=
      @CStoreSpecRel.exec_aux cexec_call_foreign cexec_lemma (cexec_call inline_fuel).
    #[global] Arguments cexec _ [_ _] s _ _ _ : simpl never.

    Definition vcgen (inline_fuel : nat) {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      CHeapSpec.run (exec_contract (cexec inline_fuel) c body).

    Import (hints) CStoreSpecRel.

    Lemma mon_exec_call_error : MonotonicExecCall exec_call_error.
    Proof. typeclasses eauto. Qed.

    Lemma mon_cexec_call_foreign : MonotonicExecCallForeign cexec_call_foreign.
    Proof. typeclasses eauto. Qed.

    Lemma mon_cexec_lemma : MonotonicExecLemma cexec_lemma.
    Proof. typeclasses eauto. Qed.

    #[export] Instance mon_cexec_call (fuel : nat) : MonotonicExecCall (cexec_call fuel).
    Proof. induction fuel; intros; cbn; destruct CEnv; typeclasses eauto. Qed.

    Lemma mon_cexec (fuel : nat) : MonotonicExec (cexec fuel).
    Proof. typeclasses eauto. Qed.

  End WithSpec.

  Module Shallow.

    Definition ValidContractWithFuel {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      vcgen fuel c body.

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      (* Use inline_fuel = 1 by default. *)
      ValidContractWithFuel 1 c body.

    Module Statistics.

      Ltac calc fnc :=
        let P := eval compute - [FALSE TRUE FINISH
                                 negb Z.mul Z.opp Z.compare Z.add Z.geb Z.eqb
                                 Z.leb Z.gtb Z.ltb Z.le Z.lt Z.gt Z.ge Z.of_nat
                                 List.app List.length rev rev_append
            ] in
                   (match CEnv fnc with
                    | Some c => Shallow.ValidContract c (FunDef fnc)
                    | None => False
                    end) in
        let s := eval compute in (CStatistics.stats P) in s.

    End Statistics.

  End Shallow.

End ShallowExecOn.

Module MakeShallowExecutor
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG).

  Include ShallowExecOn B SIG PROG SPEC.

End MakeShallowExecutor.
