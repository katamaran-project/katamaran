(******************************************************************************)
(* Copyright (c) 2019 Dominique Devriese, Georgy Lukyanov,                    *)
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

From Equations Require Import
     Equations.
From stdpp Require Import vector.
From Katamaran Require Import
     Context
     Environment
     Notations
     Prelude
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDecl
     Syntax.Variables
     Symbolic.GenOccursCheck
     Symbolic.Instantiation
     Tactics
     VectorUtils.
From Stdlib Require Import NArith.BinNat NArith.Nnat.

Import ctx.notations.
Import env.notations.
Import option.
Import option.notations.

Local Set Implicit Arguments.

Module Type QuoteOn
  (Import TY : Types)
  (Import TM : TermsOn TY)
  (Import IN : InstantiationOn TY TM)
  (Import GOC : GenOccursCheckOn TY TM).

  Local Abbreviation LCtx := (NCtx LVar Ty).

  Section InToBoundedN.
    Context {B : Type}.

    Lemma in_at_lt_length {Γ} {b : B} (bIn : ctx.In b Γ) :
      (N.of_nat (ctx.in_at bIn) < ctx.lengthN Γ)%N.
    Proof.
      unfold N.lt, ctx.lengthN. rewrite <- Nat2N.inj_compare.
      apply Nat.compare_lt_iff, (ctx.nth_is_lt_length (ctx.in_valid bIn)).
    Qed.

    (* The position of a variable counted from the end of the context, i.e.
       the most recently bound variable is at index 0, as a number bounded
       by the length of the context. *)
    Definition inToBoundedN {Γ} {b : B} (bIn : ctx.In b Γ) :
      { n : N | (n < ctx.lengthN Γ)%N } :=
      exist _ (N.of_nat (ctx.in_at bIn)) (in_at_lt_length bIn).
  End InToBoundedN.

  Section LinearTerms.
    Definition Poly n := vec Z (S n).

    Definition constant {n} (c : Z) : Poly n := c ::: vreplicate n 0%Z.

    Definition zero {n} : Poly n := constant 0.

    (* Natural numbers below a bound n, used to index the variables of a
       polynomial over n variables. *)
    Definition BoundedN (n : nat) : Type := { i : N | (i < N.of_nat n)%N }.

    Definition boundedZero {n} : BoundedN (S n) := exist _ 0%N eq_refl.

    (* The coefficient vector with a 1 at index i and 0 elsewhere. *)
    Fixpoint unitVec (n : nat) (i : N) : vec Z n :=
      match n with
      | 0 => [#]
      | S n => match i with
               | N0 => 1%Z ::: vreplicate n 0%Z
               | Npos _ => 0%Z ::: unitVec n (N.pred i)
               end
      end.

    Definition var {n} (i : BoundedN n) : Poly n := 0%Z ::: unitVec n (proj1_sig i).

    (* Constant (variable-free) integer expressions. These record the syntax
       of the constant factor of a product. *)
    Inductive ConstExpr : Set :=
    | CConst (c : Z)
    | CAdd (c1 c2 : ConstExpr)
    | CSub (c1 c2 : ConstExpr)
    | CMul (c1 c2 : ConstExpr).

    Fixpoint evalConst (c : ConstExpr) : Z :=
      match c with
      | CConst c => c
      | CAdd c1 c2 => (evalConst c1 + evalConst c2)%Z
      | CSub c1 c2 => (evalConst c1 - evalConst c2)%Z
      | CMul c1 c2 => (evalConst c1 * evalConst c2)%Z
      end.

    (* Linear arithmetic expressions over n variables, as produced by quoting
       and before normalization to polynomial form. A product is linear when
       one of its factors is constant; LinMulL and LinMulR record on which
       side that constant factor appears. *)
    Inductive LinExpr (n : nat) : Type :=
    | LinConst (c : Z)
    | LinVar (i : BoundedN n)
    | LinAdd (e1 e2 : LinExpr n)
    | LinSub (e1 e2 : LinExpr n)
    | LinMulL (c : ConstExpr) (e : LinExpr n)
    | LinMulR (e : LinExpr n) (c : ConstExpr).
    #[global] Arguments LinConst {n} c.
    #[global] Arguments LinVar {n} i.
    #[global] Arguments LinAdd {n} e1 e2.
    #[global] Arguments LinSub {n} e1 e2.
    #[global] Arguments LinMulL {n} c e.
    #[global] Arguments LinMulR {n} e c.

    Fixpoint evalLin {n} (e : LinExpr n) (xs : vec Z n) : Z :=
      match e with
      | LinConst c => c
      | LinVar i => dot (unitVec n (proj1_sig i)) xs
      | LinAdd e1 e2 => (evalLin e1 xs + evalLin e2 xs)%Z
      | LinSub e1 e2 => (evalLin e1 xs - evalLin e2 xs)%Z
      | LinMulL c e => (evalConst c * evalLin e xs)%Z
      | LinMulR e c => (evalLin e xs * evalConst c)%Z
      end.

    (* Normalization of a linear expression to polynomial form. This is the
       second step after quoteTerm, applied to the expression it returns. *)
    Fixpoint normalize {n} (e : LinExpr n) : Poly n :=
      match e with
      | LinConst c => constant c
      | LinVar i => var i
      | LinAdd e1 e2 => vzip_with Z.add (normalize e1) (normalize e2)
      | LinSub e1 e2 => vzip_with Z.sub (normalize e1) (normalize e2)
      | LinMulL c e => vmap (Z.mul (evalConst c)) (normalize e)
      | LinMulR e c => vmap (Z.mul (evalConst c)) (normalize e)
      end.

    (* An expression that contains no variables, as a constant expression
       with the same structure. *)
    Fixpoint linConst {n} (e : LinExpr n) : option ConstExpr :=
      match e with
      | LinConst c => Some (CConst c)
      | LinVar _ => None
      | LinAdd e1 e2 => match linConst e1 , linConst e2 with
                        | Some c1 , Some c2 => Some (CAdd c1 c2)
                        | _ , _ => None
                        end
      | LinSub e1 e2 => match linConst e1 , linConst e2 with
                        | Some c1 , Some c2 => Some (CSub c1 c2)
                        | _ , _ => None
                        end
      | LinMulL c e => option.map (CMul c) (linConst e)
      | LinMulR e c => option.map (fun c' => CMul c' c) (linConst e)
      end.

    Lemma dot_replicate_zero {n} (xs : vec Z n) : dot (vreplicate n 0%Z) xs = 0%Z.
    Proof. induction xs as [|x n xs IHxs]; cbn; simp dot; [easy|now rewrite IHxs]. Qed.

    Lemma dot_zip_with (op : Z -> Z -> Z)
      (Hmul : forall a b x, (op a b * x = op (a * x) (b * x))%Z)
      (Hadd : forall a b c d, (op a b + op c d = op (a + c) (b + d))%Z)
      (H0 : op 0%Z 0%Z = 0%Z) {n} (c1 c2 xs : vec Z n) :
      dot (vzip_with op c1 c2) xs = op (dot c1 xs) (dot c2 xs).
    Proof.
      revert c1 c2; induction xs as [|x n xs IHxs]; intros c1 c2.
      - inv_vec c1; inv_vec c2. cbn; now simp dot.
      - inv_vec c1; intros a1 c1; inv_vec c2; intros a2 c2.
        cbn; simp dot. now rewrite IHxs, Hmul, Hadd.
    Qed.

    Lemma dot_scale c {n} (v xs : vec Z n) :
      dot (vmap (Z.mul c) v) xs = (c * dot v xs)%Z.
    Proof.
      revert v; induction xs as [|x n xs IHxs]; intros v.
      - inv_vec v. cbn; simp dot. lia.
      - inv_vec v; intros a v. cbn; simp dot.
        rewrite IHxs. lia.
    Qed.

    (* Normalization preserves the value of a linear expression. *)
    Lemma normalize_sound {n} (e : LinExpr n) (xs : vec Z n) :
      (Vector.hd (normalize e) + dot (Vector.tl (normalize e)) xs)%Z = evalLin e xs.
    Proof.
      induction e as [c|i|e1 IH1 e2 IH2|e1 IH1 e2 IH2|c e IH|e IH c];
        cbn [normalize evalLin].
      - cbn -[dot vreplicate]. rewrite dot_replicate_zero. lia.
      - cbn -[dot unitVec]. lia.
      - rewrite <-IH1, <-IH2.
        generalize (normalize e1) (normalize e2); intros v1 v2.
        inv_vec v1; intros a1 v1; inv_vec v2; intros a2 v2; cbn.
        rewrite (dot_zip_with Z.add); intros; lia.
      - rewrite <-IH1, <-IH2.
        generalize (normalize e1) (normalize e2); intros v1 v2.
        inv_vec v1; intros a1 v1; inv_vec v2; intros a2 v2; cbn.
        rewrite (dot_zip_with Z.sub); intros; lia.
      - rewrite <-IH.
        generalize (normalize e); intros v.
        inv_vec v; intros a v; cbn.
        rewrite dot_scale. lia.
      - rewrite <-IH.
        generalize (normalize e); intros v.
        inv_vec v; intros a v; cbn.
        rewrite dot_scale. lia.
    Qed.
  End LinearTerms.

  Section Quote.
    Definition AllType (σ : Ty) : LCtx -> Type := ctx.All (fun b => type b = σ).
    Definition AllInts := AllType ty.int.
    Definition AllBvecs n := AllType (ty.bvec n).

    Definition BoxRp τ (T : LCtx -> Type) (Σ : LCtx) : Type :=
      forall {Σ1} (AI1 : AllType τ Σ1) (ζ : Sub Σ1 Σ), { Σ2 & (AllType τ Σ2 * WeakensTo Σ1 Σ2 * Sub Σ2 Σ * T Σ2)%type}.
    #[global] Arguments BoxRp τ T Σ.

    Definition liftNullOpBoxRp {τ T} {sSU : SubstSU WeakensTo T} {sSUL : SubstSULaws WeakensTo T} {Σ} (v : T [ctx]) : BoxRp τ T Σ :=
      fun Σ iΣ ζ => existT Σ (iΣ , wkRefl , ζ , substSU v initSU).

    Definition liftUnOpBoxRp {τ T1 T2 Σ} {_ : SubstSU WeakensTo T1} {_ : SubstSU WeakensTo T2}
      (f : forall {Σ'}, T1 Σ' -> T2 Σ')
      (fS : forall {Σ1 Σ2} (ζ : WeakensTo Σ1 Σ2) t, f (substSU t ζ) = substSU (f t) ζ)
      (wv1 : BoxRp τ T1 Σ) : BoxRp τ T2 Σ :=
      fun Σ1 iΣ1 ζ1 =>
      match wv1 Σ1 iΣ1 ζ1 with
      | existT Σ2 (iΣ2 , ζ12 , ζ , t) => existT Σ2 (iΣ2 , ζ12 , ζ , f t)
      end.

    Program Definition liftBinOpBoxRp {τ T1 T2 T3 Σ}
      {sSbT1 : SubstSU WeakensTo T1} {sSbT2 : SubstSU WeakensTo T2} {sSbT3 : SubstSU WeakensTo T3}
      (f : forall {Σ'}, AllType τ Σ' -> T1 Σ' -> T2 Σ' -> T3 Σ')
      (* (fS : forall {Σ1 Σ2} (iΣ1 : AllInts Σ1) (iΣ2 : AllInts Σ2) (ζ : WeakensTo Σ1 Σ2) v1 v2, substSU (f iΣ1 v1 v2) ζ = f iΣ2 (substSU v1 ζ) (substSU v2 ζ)) *)
      (wv1 : BoxRp τ T1 Σ) (wv2 : BoxRp τ T2 Σ) : BoxRp τ T3 Σ :=
      fun Σ1 iΣ1 ζ1 =>
      match wv1 Σ1 iΣ1 ζ1 with
      | existT Σ2 (iΣ2 , ζ12 , ζ2 , v1)=>
          match wv2 _ iΣ2 ζ2 with
          | existT Σ3 (iΣ3 , ζ23 , ζ3 , v2) =>
              existT Σ3 (iΣ3 , transSU ζ12 ζ23 , ζ3 , f iΣ3 (substSU v1 ζ23) v2)
          end
      end.

    Section MonoSubst.

      Definition MonoSb (Σ1 Σ2 : LCtx) : Type := { _ : Sub Σ1 Σ2 & AllInts Σ1 }.

      Definition initMonoSb {Σ} : MonoSb [ctx] Σ := existT initSU (ctx.all_nil (fun b => type b = ty.int)).
      Definition composeMonoSb {Σ1 Σ2 Σ3} (ζ1 : MonoSb Σ1 Σ2) (ζ2 : MonoSb Σ2 Σ3) : MonoSb Σ1 Σ3 :=
        match ζ1 , ζ2 with
          (existT ζ1' ai1) , (existT ζ2' ai2) => existT (transSU ζ1' ζ2') ai1
        end.
      #[export] Instance substUniv_MonoSb : SubstUniv MonoSb := MkSubstUniv MonoSb (fun _ => initMonoSb) (fun _ _ _ => composeMonoSb) (fun _ _ => projT1).
    End MonoSubst.

    Inductive MonoTm (T : nat -> Type) (Σ : LCtx) : Type :=
      MkMonoTm : T (ctx.length Σ) -> MonoTm T Σ.

    (* Coefficients are ordered with the most recently bound variable first,
       matching inToBoundedN. Skipped variables get coefficient 0. *)
    Fixpoint weakenCoeffs {Σ1 Σ2} (ζ : WeakensTo Σ1 Σ2) :
      vec Z (ctx.length Σ1) -> vec Z (ctx.length Σ2) :=
      match ζ in WeakensTo Σ1 Σ2 return vec Z (ctx.length Σ1) -> vec Z (ctx.length Σ2) with
      | WkNil => fun v => v
      | WkSkipVar _ ζ => fun v => 0%Z ::: weakenCoeffs ζ v
      | WkKeepVar _ ζ => fun v => Vector.hd v ::: weakenCoeffs ζ (Vector.tl v)
      end.

    #[export] Instance substSU_MonoTm_Poly : SubstSU WeakensTo (MonoTm Poly) :=
      fun Σ1 Σ2 '(MkMonoTm _ _ p) ζ =>
        MkMonoTm Poly Σ2 (Vector.hd p ::: weakenCoeffs ζ (Vector.tl p)).

    Lemma weakenCoeffs_trans {Σ1 Σ2 Σ3} (ζ1 : WeakensTo Σ1 Σ2) (ζ2 : WeakensTo Σ2 Σ3) v :
      weakenCoeffs (transWk ζ1 ζ2) v = weakenCoeffs ζ2 (weakenCoeffs ζ1 v).
    Proof.
      revert Σ1 ζ1 v. induction ζ2; intros Σ1' ζ1 v.
      - destruct (weakenNilView ζ1). now simp transWk.
      - simp transWk. cbn. now rewrite IHζ2.
      - destruct (weakenZeroView ζ1); simp transWk; cbn; now rewrite IHζ2.
    Qed.

    #[export] Instance substSULaws_MonoTm_Poly : SubstSULaws WeakensTo (MonoTm Poly).
    Proof.
      intros Σ1 Σ2 Σ3 ζ1 ζ2 [p]. cbn.
      change (transSU ζ1 ζ2) with (transWk ζ1 ζ2).
      now rewrite weakenCoeffs_trans.
    Qed.

    Section WeakenLinExpr.
      (* Where a variable index ends up after weakening, matching weakenCoeffs. *)
      Fixpoint weakenIdx {Σ1 Σ2} (ζ : WeakensTo Σ1 Σ2) (i : N) : N :=
        match ζ with
        | WkNil => i
        | WkSkipVar _ ζ => N.succ (weakenIdx ζ i)
        | WkKeepVar _ ζ => match i with
                           | N0 => N0
                           | Npos _ => N.succ (weakenIdx ζ (N.pred i))
                           end
        end.

      Lemma weakenIdx_lt {Σ1 Σ2} (ζ : WeakensTo Σ1 Σ2) i :
        (i < N.of_nat (ctx.length Σ1))%N -> (weakenIdx ζ i < N.of_nat (ctx.length Σ2))%N.
      Proof.
        revert i; induction ζ; intros i Hi; cbn [weakenIdx ctx.length] in *;
          rewrite ?Nat2N.inj_succ in *.
        - easy.
        - specialize (IHζ i Hi). lia.
        - destruct i as [|p]; first lia.
          pose proof (IHζ (N.pred (N.pos p)) ltac:(lia)). lia.
      Qed.

      Definition weakenBounded {Σ1 Σ2} (ζ : WeakensTo Σ1 Σ2)
        (i : BoundedN (ctx.length Σ1)) : BoundedN (ctx.length Σ2) :=
        exist _ (weakenIdx ζ (proj1_sig i)) (weakenIdx_lt ζ (proj2_sig i)).

      Fixpoint weakenLinExpr {Σ1 Σ2} (ζ : WeakensTo Σ1 Σ2)
        (e : LinExpr (ctx.length Σ1)) : LinExpr (ctx.length Σ2) :=
        match e with
        | LinConst c => LinConst c
        | LinVar i => LinVar (weakenBounded ζ i)
        | LinAdd e1 e2 => LinAdd (weakenLinExpr ζ e1) (weakenLinExpr ζ e2)
        | LinSub e1 e2 => LinSub (weakenLinExpr ζ e1) (weakenLinExpr ζ e2)
        | LinMulL c e => LinMulL c (weakenLinExpr ζ e)
        | LinMulR e c => LinMulR (weakenLinExpr ζ e) c
        end.

      #[export] Instance substSU_MonoTm_LinExpr : SubstSU WeakensTo (MonoTm LinExpr) :=
        fun Σ1 Σ2 '(MkMonoTm _ _ e) ζ => MkMonoTm LinExpr Σ2 (weakenLinExpr ζ e).
    End WeakenLinExpr.

    Definition QuotedTerm (T : nat -> Type) Σ σ : Type :=
      match σ with
      | ty.int => BoxRp (ty.int) (MonoTm T) Σ
      | u => Term Σ σ
      end.

    Definition Term_eqb_het {Σ σ1 σ2} (t1 : Term Σ σ1) (t2 : Term Σ σ2) : bool :=
      match ty.Ty_eq_dec σ1 σ2 with
        left Heq => Term_eqb (eq_rect σ1 (Term _) t1 _ Heq) t2
      | right _ => false
      end.

    Lemma allTypeSnoc {Γ σ x} : AllType σ Γ -> AllType σ (Γ ▻ x :: σ).
    Proof. intros. now eapply ctx.all_snoc. Qed.

    Class MonoVar (T : nat -> Type) : Type :=
      MkMonoVar {
          monoVar : forall n, BoundedN n -> T n
        }.

    #[export] Instance monoVar_Poly : MonoVar Poly := MkMonoVar Poly (@var).
    #[export] Instance monoVar_LinExpr : MonoVar LinExpr := MkMonoVar LinExpr (@LinVar).

    Definition boxRpTerm `{MonoVar T} {τ Σ} (t : Term Σ τ) : BoxRp τ (MonoTm T) Σ :=
      fun Σ1 iΣ1 ζ =>
        match env.find (fun b => Term_eqb_het t) ζ with
          None => let b := fresh_lvar Σ1 None in
                 existT (Σ1 ▻ b :: τ)
                   (allTypeSnoc iΣ1 , wk1 , ζ.[ b :: τ ↦ t ] ,
                     MkMonoTm T _ (monoVar boundedZero))
        | Some (existT x xIn) =>
            existT Σ1 (iΣ1 , wkRefl , ζ ,
                MkMonoTm T _ (monoVar (inToBoundedN xIn)))
        end.

    Definition boxRpConst {T τ Σ} (t : forall {n}, T n) : BoxRp τ (MonoTm T) Σ :=
      fun Σ1 iΣ1 ζ => existT Σ1 (iΣ1 , wkRefl , ζ , MkMonoTm T Σ1 t).

    Definition quoteTermDefault `{MonoVar T} {τ Σ} : Term Σ τ -> QuotedTerm T Σ τ :=
        match τ with
        | ty.int => boxRpTerm
        | _ => id
        end.

    Definition liftLinOp (k : forall {n}, LinExpr n -> LinExpr n -> LinExpr n)
      {Σ} (_ : AllInts Σ) (e1 e2 : MonoTm LinExpr Σ) : MonoTm LinExpr Σ :=
      match e1 , e2 with
      | MkMonoTm _ _ e1 , MkMonoTm _ _ e2 => MkMonoTm LinExpr Σ (k e1 e2)
      end.

    Definition linConstTm {Σ} (e : MonoTm LinExpr Σ) : option ConstExpr :=
      match e with MkMonoTm _ _ e => linConst e end.

    Definition linMulLTm {Σ} (c : ConstExpr) (e : MonoTm LinExpr Σ) : MonoTm LinExpr Σ :=
      match e with MkMonoTm _ _ e => MkMonoTm LinExpr Σ (LinMulL c e) end.

    Definition linMulRTm {Σ} (e : MonoTm LinExpr Σ) (c : ConstExpr) : MonoTm LinExpr Σ :=
      match e with MkMonoTm _ _ e => MkMonoTm LinExpr Σ (LinMulR e c) end.

    (* Like liftBinOpBoxRp, but a product of two non-constant expressions is
       not linear, so in that case we fall back to treating t as opaque. *)
    Definition timesBoxRp {Σ} (t : Term Σ ty.int)
      (wv1 wv2 : BoxRp ty.int (MonoTm LinExpr) Σ) : BoxRp ty.int (MonoTm LinExpr) Σ :=
      fun Σ1 iΣ1 ζ1 =>
      match wv1 Σ1 iΣ1 ζ1 with
      | existT Σ2 (iΣ2 , ζ12 , ζ2 , v1) =>
          match wv2 _ iΣ2 ζ2 with
          | existT Σ3 (iΣ3 , ζ23 , ζ3 , v2) =>
              let v1' : MonoTm LinExpr Σ3 := substSU v1 ζ23 in
              match linConstTm v1' , linConstTm v2 with
              | Some c , _ => existT Σ3 (iΣ3 , transSU ζ12 ζ23 , ζ3 , linMulLTm c v2)
              | _ , Some c => existT Σ3 (iΣ3 , transSU ζ12 ζ23 , ζ3 , linMulRTm v1' c)
              | None , None => boxRpTerm t iΣ1 ζ1
              end
          end
      end.

    Definition quoteTerm_binop {Σ σ1 σ2 σ3} (bop : BinOp σ1 σ2 σ3) :
      Term Σ σ1 -> Term Σ σ2 ->
      QuotedTerm LinExpr Σ σ1 -> QuotedTerm LinExpr Σ σ2 -> QuotedTerm LinExpr Σ σ3 :=
      match bop in BinOp σ1 σ2 σ3
        return Term Σ σ1 -> Term Σ σ2 ->
               QuotedTerm LinExpr Σ σ1 -> QuotedTerm LinExpr Σ σ2 -> QuotedTerm LinExpr Σ σ3 with
      | bop.plus => fun _ _ q1 q2 => liftBinOpBoxRp (@liftLinOp (@LinAdd)) q1 q2
      | bop.minus => fun _ _ q1 q2 => liftBinOpBoxRp (@liftLinOp (@LinSub)) q1 q2
      | bop.times => fun t1 t2 q1 q2 => timesBoxRp (term_binop bop.times t1 t2) q1 q2
      | bop =>fun t1 t2 _ _ => quoteTermDefault (term_binop bop t1 t2)
      end.

    (* First step: quote a term into a (non-normalized) linear expression. *)
    Fixpoint quoteTerm {Σ σ} (t : Term Σ σ) {struct t} : QuotedTerm LinExpr Σ σ :=
      match t in Term _ σ return QuotedTerm LinExpr Σ σ with
      | term_var xIn => quoteTermDefault (term_var xIn)
      | term_val ty.int v => boxRpConst (fun _ => LinConst v)
      | term_val σ v => quoteTermDefault (term_val σ v)
      | term_binop bop t1 t2 => quoteTerm_binop bop t1 t2 (quoteTerm t1) (quoteTerm t2)
      | t => quoteTermDefault t
      end.

    Section Refinement.
      Local Abbreviation Valuation Σ := (Env (fun xt : Binding LVar Ty => Val (type xt)) Σ).

      Definition valToZ {σ} : Val σ -> Z :=
        match σ with
        | ty.int => fun v => v
        | _ => fun _ => 0%Z
        end.

      (* The integer values of a valuation, most recently bound variable first
         (matching inToBoundedN and weakenCoeffs). *)
      Fixpoint intVals {Σ} (ι : Valuation Σ) : vec Z (ctx.length Σ) :=
        match ι with
        | env.nil => [#]
        | env.snoc ι _ v => valToZ v ::: intVals ι
        end.

      Definition termToInt {Σ σ} : Term Σ σ -> Term Σ ty.int :=
        match σ with
        | ty.int => fun t => t
        | _ => fun _ => term_val ty.int 0%Z
        end.

      (* The term at index i of a substitution, counting from the most
         recently bound variable (matching inToBoundedN). *)
      Fixpoint subLookupInt {Σ2 Σ} (ζ : Sub Σ2 Σ) (i : N) : Term Σ ty.int :=
        match ζ with
        | env.nil => term_val ty.int 0%Z
        | env.snoc ζ _ t => match i with
                            | N0 => termToInt t
                            | Npos _ => subLookupInt ζ (N.pred i)
                            end
        end.

      Fixpoint constToTerm {Σ} (c : ConstExpr) : Term Σ ty.int :=
        match c with
        | CConst c => term_val ty.int c
        | CAdd c1 c2 => term_binop bop.plus (constToTerm c1) (constToTerm c2)
        | CSub c1 c2 => term_binop bop.minus (constToTerm c1) (constToTerm c2)
        | CMul c1 c2 => term_binop bop.times (constToTerm c1) (constToTerm c2)
        end.

      (* Read a linear expression back as a term, instantiating its variables
         with the substitution ζ. *)
      Fixpoint linToTerm {Σ2 Σ} (e : LinExpr (ctx.length Σ2)) (ζ : Sub Σ2 Σ) : Term Σ ty.int :=
        match e with
        | LinConst c => term_val ty.int c
        | LinVar i => subLookupInt ζ (proj1_sig i)
        | LinAdd e1 e2 => term_binop bop.plus (linToTerm e1 ζ) (linToTerm e2 ζ)
        | LinSub e1 e2 => term_binop bop.minus (linToTerm e1 ζ) (linToTerm e2 ζ)
        | LinMulL c e => term_binop bop.times (constToTerm c) (linToTerm e ζ)
        | LinMulR e c => term_binop bop.times (linToTerm e ζ) (constToTerm c)
        end.

      Definition linToTermTm {Σ2 Σ} (e : MonoTm LinExpr Σ2) (ζ : Sub Σ2 Σ) : Term Σ ty.int :=
        match e with MkMonoTm _ _ e => linToTerm e ζ end.

      (* b refines t if, for every abstraction ζ1 of integer variables, the
         returned expression v reads back as exactly t under the returned
         substitution ζ2, and ζ2 agrees with ζ1 on the variables that were
         already there. *)
      Definition BoxRpRefines {Σ} (b : BoxRp ty.int (MonoTm LinExpr) Σ) (t : Term Σ ty.int) : Prop :=
        forall Σ1 (iΣ1 : AllInts Σ1) (ζ1 : Sub Σ1 Σ),
          let '(existT Σ2 (_ , ζ12 , ζ2 , v)) := b Σ1 iΣ1 ζ1 in
          subst (interpWk ζ12) ζ2 = ζ1 /\ linToTermTm v ζ2 = t.

      Definition QuotedTermRefines {Σ σ} : QuotedTerm LinExpr Σ σ -> Term Σ σ -> Prop :=
        match σ with
        | ty.int => BoxRpRefines
        | _ => eq
        end.

      Lemma subLookupInt_succ {Σ2 Σ b} (ζ : Sub Σ2 Σ) (t : Term Σ (type b)) k :
        subLookupInt (env.snoc ζ b t) (N.succ k) = subLookupInt ζ k.
      Proof.
        cbn [subLookupInt].
        destruct (N.succ k) as [|q] eqn:E; first now apply N.neq_succ_0 in E.
        now rewrite <-E, N.pred_succ.
      Qed.

      Lemma subLookupInt_lookup {Σ2 Σ b} (bIn : b ∈ Σ2) (ζ : Sub Σ2 Σ) :
        subLookupInt ζ (N.of_nat (ctx.in_at bIn)) = termToInt (env.lookup ζ bIn).
      Proof.
        induction ζ; first destruct (ctx.view bIn).
        destruct (ctx.view bIn) as [|b' bIn]; first reflexivity.
        change (ctx.in_at (ctx.in_succ bIn)) with (S (ctx.in_at bIn)).
        rewrite Nat2N.inj_succ, subLookupInt_succ. apply IHζ.
      Qed.

      Lemma subLookupInt_weaken {Σ1 Σ2 Σ} (ζ : WeakensTo Σ1 Σ2) (ζ' : Sub Σ2 Σ) i :
        subLookupInt ζ' (weakenIdx ζ i) = subLookupInt (subst (interpWk ζ) ζ') i.
      Proof.
        revert ζ' i; induction ζ; intros ζ' i; cbn [weakenIdx interpWk].
        - now destruct (env.view ζ').
        - destruct (env.view ζ') as [ζ' t].
          rewrite subLookupInt_succ, IHζ, sub_comp_assoc, sub_comp_wk1_tail.
          reflexivity.
        - destruct (env.view ζ') as [ζ' t].
          destruct x as [x τ]. rewrite <-sub_snoc_comp.
          destruct i as [|p]; cbn [weakenIdx]; first reflexivity.
          now rewrite subLookupInt_succ, IHζ.
      Qed.

      Lemma linToTerm_weaken {Σ1 Σ2 Σ} (ζ : WeakensTo Σ1 Σ2) (e : LinExpr (ctx.length Σ1))
        (ζ' : Sub Σ2 Σ) :
        linToTerm (weakenLinExpr ζ e) ζ' = linToTerm e (subst (interpWk ζ) ζ').
      Proof.
        induction e; cbn [weakenLinExpr linToTerm]; try (now rewrite ?IHe1, ?IHe2, ?IHe).
        apply subLookupInt_weaken.
      Qed.

      Lemma linToTermTm_substSU {Σ1 Σ2 Σ} (e : MonoTm LinExpr Σ1) (ζ : WeakensTo Σ1 Σ2)
        (ζ' : Sub Σ2 Σ) :
        linToTermTm (substSU e ζ) ζ' = linToTermTm e (subst (interpWk ζ) ζ').
      Proof. destruct e as [e]. apply linToTerm_weaken. Qed.

      Lemma linConst_toTerm {Σ2 Σ} (e : LinExpr (ctx.length Σ2)) (ζ : Sub Σ2 Σ) c :
        linConst e = Some c -> linToTerm e ζ = constToTerm c.
      Proof.
        revert c; induction e as [c0|i|e1 IH1 e2 IH2|e1 IH1 e2 IH2|c0 e IH|e IH c0];
          intros c H; cbn [linConst linToTerm] in *.
        - now injection H as <-.
        - discriminate.
        - destruct (linConst e1) as [c1|], (linConst e2) as [c2|]; try discriminate.
          injection H as <-. cbn. now rewrite (IH1 c1 eq_refl), (IH2 c2 eq_refl).
        - destruct (linConst e1) as [c1|], (linConst e2) as [c2|]; try discriminate.
          injection H as <-. cbn. now rewrite (IH1 c1 eq_refl), (IH2 c2 eq_refl).
        - destruct (linConst e) as [c1|]; cbn in H; try discriminate.
          injection H as <-. cbn. now rewrite (IH c1 eq_refl).
        - destruct (linConst e) as [c1|]; cbn in H; try discriminate.
          injection H as <-. cbn. now rewrite (IH c1 eq_refl).
      Qed.

      Lemma linConstTm_toTerm {Σ2 Σ} (e : MonoTm LinExpr Σ2) (ζ : Sub Σ2 Σ) c :
        linConstTm e = Some c -> linToTermTm e ζ = constToTerm c.
      Proof. destruct e as [e]. apply linConst_toTerm. Qed.

      Lemma linToTermTm_liftLinOp (k : forall {n}, LinExpr n -> LinExpr n -> LinExpr n)
        (op : BinOp ty.int ty.int ty.int)
        (Hk : forall Σ2 Σ (e1 e2 : LinExpr (ctx.length Σ2)) (ζ : Sub Σ2 Σ),
            linToTerm (k e1 e2) ζ = term_binop op (linToTerm e1 ζ) (linToTerm e2 ζ))
        {Σ2 Σ} (iΣ : AllInts Σ2) (e1 e2 : MonoTm LinExpr Σ2) (ζ : Sub Σ2 Σ) :
        linToTermTm (liftLinOp (@k) iΣ e1 e2) ζ =
          term_binop op (linToTermTm e1 ζ) (linToTermTm e2 ζ).
      Proof. destruct e1, e2. apply Hk. Qed.

      (* Reading back and then evaluating agrees with evaluating the linear
         expression directly, so together with normalize_sound the normalized
         polynomial evaluates to the original term. *)
      Lemma inst_termToInt {Σ σ} (t : Term Σ σ) (ι : Valuation Σ) :
        inst (A := Val ty.int) (termToInt t) ι = valToZ (inst t ι).
      Proof. now destruct σ. Qed.

      Lemma inst_subLookupInt {Σ2 Σ} (ζ : Sub Σ2 Σ) i (ι : Valuation Σ) :
        inst (A := Val ty.int) (subLookupInt ζ i) ι =
          dot (unitVec (ctx.length Σ2) i) (intVals (inst ζ ι)).
      Proof.
        revert i; induction ζ as [|Γ ζ IHζ b t]; intros i; first reflexivity.
        change (inst (env.snoc ζ b t) ι) with (env.snoc (inst ζ ι) b (inst t ι)).
        destruct i as [|p]; cbn [ctx.length unitVec subLookupInt intVals]; simp dot.
        - rewrite inst_termToInt, dot_replicate_zero. lia.
        - rewrite IHζ. lia.
      Qed.

      Lemma inst_constToTerm {Σ} (c : ConstExpr) (ι : Valuation Σ) :
        inst (A := Val ty.int) (constToTerm c) ι = evalConst c.
      Proof. induction c; cbn; f_equal; assumption. Qed.

      Lemma inst_linToTerm {Σ2 Σ} (e : LinExpr (ctx.length Σ2)) (ζ : Sub Σ2 Σ) (ι : Valuation Σ) :
        inst (A := Val ty.int) (linToTerm e ζ) ι = evalLin e (intVals (inst ζ ι)).
      Proof.
        induction e; cbn [linToTerm evalLin]; try apply inst_subLookupInt;
          cbn; f_equal; auto using inst_constToTerm.
      Qed.

      Lemma interpWk_trans_extends {Σ1 Σ2 Σ3 Σ} (ζ12 : WeakensTo Σ1 Σ2) (ζ23 : WeakensTo Σ2 Σ3)
        (ζ2 : Sub Σ2 Σ) (ζ3 : Sub Σ3 Σ) :
        subst (interpWk ζ23) ζ3 = ζ2 ->
        subst (interpWk (transSU ζ12 ζ23)) ζ3 = subst (interpWk ζ12) ζ2.
      Proof.
        intros <-. change (transSU ζ12 ζ23) with (transWk ζ12 ζ23).
        now rewrite interpTransWk, sub_comp_assoc.
      Qed.

      Lemma boxRpTerm_refines {Σ} (t : Term Σ ty.int) :
        BoxRpRefines (boxRpTerm (T := LinExpr) t) t.
      Proof.
        intros Σ1 iΣ1 ζ1. unfold boxRpTerm.
        generalize (env.find_spec (fun b s => Term_eqb_het t s = true) (fun b => Term_eqb_het t)
                      (fun b s => ssrbool.idP) ζ1).
        destruct env.find as [[[x σx] xIn]|]; intros Hfind.
        - rewrite option.wlp_some in Hfind; cbn in Hfind.
          unfold Term_eqb_het in Hfind.
          destruct (ty.Ty_eq_dec ty.int σx) as [Heq|]; last discriminate.
          subst σx; cbn in Hfind.
          apply (ssrbool.elimT (Term_eqb_spec _ _)) in Hfind; subst t.
          split.
          + now rewrite interpWk_wkRefl, sub_comp_id_left.
          + cbn [linToTermTm linToTerm monoVar monoVar_LinExpr proj1_sig inToBoundedN].
            exact (subLookupInt_lookup xIn ζ1).
        - split; last reflexivity.
          unfold wk1; cbn [interpWk].
          now rewrite interpWk_wkRefl, sub_comp_id_left, sub_comp_wk1_tail.
      Qed.

      Lemma quoteTermDefault_refines {Σ σ} (t : Term Σ σ) :
        QuotedTermRefines (quoteTermDefault (T := LinExpr) t) t.
      Proof. destruct σ; try reflexivity. apply boxRpTerm_refines. Qed.

      Lemma liftBinOpBoxRp_refines (k : forall {n}, LinExpr n -> LinExpr n -> LinExpr n)
        (op : BinOp ty.int ty.int ty.int) {Σ}
        (Hk : forall Σ2 Σ (e1 e2 : LinExpr (ctx.length Σ2)) (ζ : Sub Σ2 Σ),
            linToTerm (k e1 e2) ζ = term_binop op (linToTerm e1 ζ) (linToTerm e2 ζ))
        (t1 t2 : Term Σ ty.int) (q1 q2 : BoxRp ty.int (MonoTm LinExpr) Σ) :
        BoxRpRefines q1 t1 -> BoxRpRefines q2 t2 ->
        BoxRpRefines (liftBinOpBoxRp (@liftLinOp (@k)) q1 q2) (term_binop op t1 t2).
      Proof.
        intros Hq1 Hq2 Σ1 iΣ1 ζ1. unfold liftBinOpBoxRp.
        specialize (Hq1 Σ1 iΣ1 ζ1).
        destruct (q1 Σ1 iΣ1 ζ1) as (Σ2 & [[[iΣ2 ζ12] ζ2] v1]).
        destruct Hq1 as [Hζ2 Hv1].
        specialize (Hq2 Σ2 iΣ2 ζ2).
        destruct (q2 Σ2 iΣ2 ζ2) as (Σ3 & [[[iΣ3 ζ23] ζ3] v2]).
        destruct Hq2 as [Hζ3 Hv2].
        split.
        - now rewrite (interpWk_trans_extends ζ12 _ _ Hζ3).
        - rewrite (linToTermTm_liftLinOp (@k) Hk), linToTermTm_substSU, Hζ3.
          now rewrite Hv1, Hv2.
      Qed.

      Lemma linToTermTm_linMulLTm {Σ2 Σ} c (e : MonoTm LinExpr Σ2) (ζ : Sub Σ2 Σ) :
        linToTermTm (linMulLTm c e) ζ = term_binop bop.times (constToTerm c) (linToTermTm e ζ).
      Proof. now destruct e. Qed.

      Lemma linToTermTm_linMulRTm {Σ2 Σ} (e : MonoTm LinExpr Σ2) c (ζ : Sub Σ2 Σ) :
        linToTermTm (linMulRTm e c) ζ = term_binop bop.times (linToTermTm e ζ) (constToTerm c).
      Proof. now destruct e. Qed.

      Lemma timesBoxRp_refines {Σ} (t1 t2 : Term Σ ty.int) (q1 q2 : BoxRp ty.int (MonoTm LinExpr) Σ) :
        BoxRpRefines q1 t1 -> BoxRpRefines q2 t2 ->
        BoxRpRefines (timesBoxRp (term_binop bop.times t1 t2) q1 q2)
          (term_binop bop.times t1 t2).
      Proof.
        intros Hq1 Hq2 Σ1 iΣ1 ζ1. unfold timesBoxRp.
        pose proof (boxRpTerm_refines (term_binop bop.times t1 t2) iΣ1 ζ1) as Hdef.
        specialize (Hq1 Σ1 iΣ1 ζ1).
        destruct (q1 Σ1 iΣ1 ζ1) as (Σ2 & [[[iΣ2 ζ12] ζ2] v1]).
        destruct Hq1 as [Hζ2 Hv1].
        specialize (Hq2 Σ2 iΣ2 ζ2).
        destruct (q2 Σ2 iΣ2 ζ2) as (Σ3 & [[[iΣ3 ζ23] ζ3] v2]).
        destruct Hq2 as [Hζ3 Hv2].
        assert (Hv1' : linToTermTm (substSU v1 ζ23) ζ3 = t1)
          by now rewrite linToTermTm_substSU, Hζ3.
        destruct (linConstTm (substSU v1 ζ23)) as [c|] eqn:Hc1;
          [|destruct (linConstTm v2) as [c|] eqn:Hc2]; try exact Hdef;
          (split; first now rewrite (interpWk_trans_extends ζ12 _ _ Hζ3)).
        - rewrite linToTermTm_linMulLTm, Hv2, <-Hv1'.
          now rewrite (linConstTm_toTerm _ ζ3 Hc1).
        - rewrite linToTermTm_linMulRTm, Hv1', <-Hv2.
          now rewrite (linConstTm_toTerm _ ζ3 Hc2).
      Qed.

      Lemma quoteTerm_binop_refines {Σ σ1 σ2 σ3} (bop : BinOp σ1 σ2 σ3)
        (t1 : Term Σ σ1) (t2 : Term Σ σ2) q1 q2 :
        QuotedTermRefines q1 t1 -> QuotedTermRefines q2 t2 ->
        QuotedTermRefines (quoteTerm_binop bop t1 t2 q1 q2) (term_binop bop t1 t2).
      Proof.
        destruct bop; intros Hq1 Hq2; try apply quoteTermDefault_refines.
        - now apply (liftBinOpBoxRp_refines (@LinAdd)).
        - now apply (liftBinOpBoxRp_refines (@LinSub)).
        - now apply timesBoxRp_refines.
      Qed.

      Lemma quoteTerm_refines {Σ σ} (t : Term Σ σ) :
        QuotedTermRefines (quoteTerm t) t.
      Proof.
        induction t; cbn [quoteTerm]; try apply quoteTermDefault_refines.
        - destruct σ; try apply quoteTermDefault_refines.
          intros Σ1 iΣ1 ζ1; cbn. split; last easy.
          now rewrite interpWk_wkRefl, sub_comp_id_left.
        - now apply quoteTerm_binop_refines.
      Qed.
    End Refinement.
  End Quote.

End QuoteOn.
