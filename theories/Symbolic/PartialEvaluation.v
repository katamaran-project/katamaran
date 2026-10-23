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

From Coq Require Import
     Arith.PeanoNat
     Bool.Bool
     Classes.Morphisms
     Classes.RelationClasses
     List
     NArith.BinNat
     ZArith.BinInt
     ZArith.Zdiv
     ZArith.Znat
     NArith.Nnat
     Sorting.Permutation
     PArith
     Ring
     Ring_polynom
     micromega.Lia.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Bitvector
     Symbolic.Instantiation
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDecl
     Syntax.UnOps
     Syntax.Variables.

Import (notations) stdpp.base.
Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
Local Unset Elimination Schemes.
Local Set Equations Transparent.

Section Util.
  Lemma jump_of_succ_nat_length {A : Type} {def : A} {lo l : list A} :
    BinList.jump (Pos.of_succ_nat (length lo)) (def :: lo ++ l) = l.
  Proof.
    revert def.
    induction lo; intros def; cbn; [easy|].
    rewrite BinList.jump_succ; cbn.
    rewrite BinList.jump_tl; cbn.
    now apply IHlo.
  Qed.

  Lemma nth_length_prefix {o} {A} {def} {lo l : list A} : o = Pos.of_succ_nat (length lo) -> BinList.nth def o (lo ++ l) = hd def l.
  Proof.
    intros ->.
    change (lo ++ l) with (tl (def ::(lo ++ l))).
    rewrite BinList.nth_jump.
    f_equal.
    now apply jump_of_succ_nat_length.
  Qed.

  Lemma nth_succ {i} {A} {def t} {ts : list A} :
    BinList.nth def (Pos.succ i) (t :: ts) = BinList.nth def i ts.
  Proof.
    change (t :: ts)%list with (tl (def :: t :: ts)).
    rewrite BinList.nth_jump.
    replace ((Pos.succ i)) with (i + 1)%positive by lia.
    rewrite BinList.jump_add.
    cbn.
    now rewrite <-BinList.nth_jump.
  Qed.

  Lemma nth_lookup {i} {A} {def} {ts la : list A} {t} :
      ts !! i = Some t ->
      BinList.nth def (Pos.of_succ_nat i) (ts ++ la) = t.
  Proof.
    revert i.
    induction ts; intros i; first inversion 1.
    destruct i; inversion 1; first easy; cbn.
    rewrite nth_succ.
    now eapply IHts.
  Qed.

  Fixpoint plusNatPos (n : nat) (p : positive) : positive :=
    match n with
    | 0 => p
    | S n => Pos.succ (plusNatPos n p)
    end.

  Lemma plusNatPos_of_succ_nat {n m} : plusNatPos n (Pos.of_succ_nat m) = Pos.of_succ_nat (n + m).
  Proof. induction n; cbn; now f_equal. Qed.

  (* The identity cast between two equal widths, by structural recursion
     rather than an equality proof, so it reduces under vm_compute with no
     opaque proof term in the way (peval_sext). *)
  Fixpoint width_cast (m n : nat) : option (forall A : nat -> Type, A m -> A n) :=
    match m, n with
    | O, O => Some (fun A x => x)
    | S m', S n' =>
        match width_cast m' n' with
        | Some f => Some (fun A x => f (fun k => A (S k)) x)
        | None => None
        end
    | _, _ => None
    end.

  Lemma width_cast_spec m n f : width_cast m n = Some f ->
    exists e : m = n, forall A x, f A x = eq_rect m A x n e.
  Proof.
    revert n f. induction m as [|m IH]; intros [|n] f; cbn; try discriminate.
    - intros [= <-]. exists eq_refl. reflexivity.
    - destruct (width_cast m n) as [g|] eqn:E; [|discriminate]. intros [= <-].
      destruct (IH n g E) as [e He]. subst n. exists eq_refl. intros A x.
      cbn. exact (He (fun k => A (S k)) x).
  Qed.
End Util.

Module Type PartialEvaluationOn
  (Import TY : Types)
  (Import TM : TermsOn TY)
  (Import IN : InstantiationOn TY TM).

  Local Notation LCtx := (NCtx LVar Ty).
  Local Notation Valuation Σ := (Env (fun xt : Binding LVar Ty => Val (type xt)) Σ).

  (* ===================================================================== *)
  (* CANONICAL RING FORMS for bitvector terms: UPSTREAM's ring normalisation *)
  (* (Ring_polynom norm_aux + Pphi_dev, as used by main's peval2), made      *)
  (* sound over RelVal (PLAN-bv-arith-solver; developed and self-tested in   *)
  (* CFGVer/Example/ZZBvRing.v).  Upstream proves it modulo ≡, where the ring *)
  (* axioms FAIL (x - x is NonSyncVal 0 0 for a secret x; this fork disabled *)
  (* TermRing_bv for that reason in 196eae12).  Here the SAME Ring_polynom   *)
  (* lemmas are instantiated modulo `teq side` (equal on one projection),    *)
  (* where they hold; SyncVal-ness is settled by a computable leaf           *)
  (* certificate (every op lifts, so a term is SyncVal iff its leaves are);  *)
  (* an atom the normal form drops is padded back as `0 * a`.                *)
  (* ===================================================================== *)
  Local Notation RValuation Σ := (Env (fun xt : Binding LVar Ty => RelVal (type xt)) Σ).
  Local Open Scope Z_scope.

Definition rv_proj (side : bool) {σ} (v : RelVal σ) : Val σ :=
  if side then ty.projLeft v else ty.projRight v.

Section Teq.
  Context {Σ : LCtx}.

  (* equal on projection `side`, for every valuation *)
  Definition teq (side : bool) {σ} (t u : Term Σ σ) : Prop :=
    forall ι : RValuation Σ, rv_proj side (inst t ι) = rv_proj side (inst u ι).

  (* every op is liftBinOp / liftUnOp (eval op): projections commute *)
  Lemma rv_proj_bin side {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) (a : Term Σ σ1) (b : Term Σ σ2) ι :
    rv_proj side (inst (term_binop op a b) ι) = bop.eval op (rv_proj side (inst a ι)) (rv_proj side (inst b ι)).
  Proof. destruct side; cbn; [apply bop.comProjLeftRVEvalRel|apply bop.comProjRightRVEvalRel]. Qed.

  Lemma rv_proj_un side {σ1 σ2} (op : UnOp σ1 σ2) (a : Term Σ σ1) ι :
    rv_proj side (inst (term_unop op a) ι) = uop.eval op (rv_proj side (inst a ι)).
  Proof. destruct side; cbn; [apply uop.comProjLeftRVEvalRel|apply uop.comProjRightRVEvalRel]. Qed.

  Lemma rv_proj_val side {σ} (v : Val σ) (ι : RValuation Σ) : rv_proj side (inst (term_val σ v) ι) = v.
  Proof. destruct side; reflexivity. Qed.

  #[export] Instance teq_equiv side σ : Equivalence (@teq side σ).
  Proof.
    constructor; [intros x ι; reflexivity | intros x y H ι; symmetry; apply H
                 | intros x y z H1 H2 ι; rewrite H1; apply H2].
  Qed.

  #[export] Instance teq_bin side {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) :
    Proper (teq side ==> teq side ==> teq side) (@term_binop Σ _ _ _ op).
  Proof. intros a a' Ha b b' Hb ι. rewrite !rv_proj_bin. rewrite Ha. rewrite Hb. reflexivity. Qed.

  #[export] Instance teq_un side {σ1 σ2} (op : UnOp σ1 σ2) :
    Proper (teq side ==> teq side) (@term_unop Σ _ _ op).
  Proof. intros a a' Ha ι. rewrite !rv_proj_un. rewrite Ha. reflexivity. Qed.

  (* the ring axioms DO hold modulo teq (each projection is a plain bv ring) *)
  Lemma bv_term_ring side n :
    ring_theory (term_val (Σ := Σ) (ty.bvec n) bv.zero) (term_val (ty.bvec n) bv.one)
      (term_binop bop.bvadd) (term_binop bop.bvmul) (term_binop bop.bvsub) (term_unop uop.negate) (teq side).
  Proof.
    pose proof (bv.ring_theory n) as R.
    constructor; intros; intros ι; rewrite ?rv_proj_bin; rewrite ?rv_proj_un; rewrite ?rv_proj_val;
      cbn [bop.eval uop.eval]; rewrite ?rv_proj_bin; rewrite ?rv_proj_un; rewrite ?rv_proj_val;
      cbn [bop.eval uop.eval].
    all: first [ apply (Radd_0_l R) | apply (Radd_comm R) | apply (Radd_assoc R) | apply (Rmul_1_l R)
               | apply (Rmul_comm R) | apply (Rmul_assoc R) | apply (Rdistr_l R) | apply (Rsub_def R)
               | apply (Ropp_def R) ].
  Qed.

  Lemma bv_term_eq_ext side n :
    ring_eq_ext (term_binop (Σ := Σ) (bop.bvadd (n := n))) (term_binop bop.bvmul) (term_unop uop.negate) (teq side).
  Proof. constructor; typeclasses eauto. Qed.

  Lemma bv_term_morph side n :
    ring_morph (term_val (Σ := Σ) (ty.bvec n) bv.zero) (term_val (ty.bvec n) bv.one)
      (term_binop bop.bvadd) (term_binop bop.bvmul) (term_binop bop.bvsub) (term_unop uop.negate) (teq side)
      0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool (fun c => term_val (ty.bvec n) (bv.of_Z c)).
  Proof.
    constructor; intros; intros ι; rewrite ?rv_proj_bin; rewrite ?rv_proj_un; rewrite ?rv_proj_val;
      cbn [bop.eval uop.eval].
    all: try (apply Zbool.Zeq_bool_eq in H; subst; reflexivity).
    all: first [ reflexivity | apply bv.of_Z_one | symmetry; apply bv.of_Z_one
               | apply bv.of_Z_add | symmetry; apply bv.of_Z_add | apply bv.of_Z_sub | symmetry; apply bv.of_Z_sub
               | apply bv.of_Z_mul | symmetry; apply bv.of_Z_mul | apply bv.of_Z_negate | symmetry; apply bv.of_Z_negate ].
  Qed.
End Teq.

Section Norm.
  Context {Σ : LCtx} {n : nat}.
  Local Notation T := (Term Σ (ty.bvec n)).

  (* upstream's evalPExprTm / evalPolTm, at bvec n *)
  Definition evalPE (l : list T) : PExpr Z -> T :=
    PEeval (term_val (ty.bvec n) bv.zero) (term_val (ty.bvec n) bv.one)
      (term_binop bop.bvadd) (term_binop bop.bvmul) (term_binop bop.bvsub) (term_unop uop.negate)
      (fun c => term_val (ty.bvec n) (bv.of_Z c)) id_phi_N
      (pow_N (term_val (ty.bvec n) bv.one) (term_binop bop.bvmul)) l.

  Definition evalPol (l : list T) : Pol Z -> T :=
    Pphi_dev (term_val (ty.bvec n) bv.zero) (term_val (ty.bvec n) bv.one)
      (term_binop bop.bvadd) (term_binop bop.bvmul) (term_binop bop.bvsub) (term_unop uop.negate)
      0%Z 1%Z Zbool.Zeq_bool (fun c => term_val (ty.bvec n) (bv.of_Z c)) get_signZ l.

  Definition normZ (p : PExpr Z) : Pol Z := norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool p.

  (* upstream's evalPol_norm_aux, modulo teq side: the SAME two Ring_polynom
     lemmas, a weaker setoid *)
  Lemma norm_teq side (l : list T) (p : PExpr Z) : teq side (evalPol l (normZ p)) (evalPE l p).
  Proof.
    pose proof (bv_term_ring (Σ := Σ) side n) as Rth.
    pose proof (bv_term_eq_ext (Σ := Σ) side n) as Reqe.
    pose proof (bv_term_morph (Σ := Σ) side n) as Rmorph.
    unfold evalPol, evalPE, normZ.
    etransitivity.
    { exact (@Pphi_dev_ok _ _ _ _ _ _ _ (teq side) (teq_equiv side _) Reqe
               (@Rth_ARth _ _ _ _ _ _ _ _ (teq_equiv side _) Reqe Rth) _ _ _ _ _ _ _ _ _
               Rmorph _ get_signZ_th _ l). }
    symmetry.
    exact (@norm_aux_spec _ _ _ _ _ _ _ (teq side) (teq_equiv side _) Reqe
             (@Rth_ARth _ _ _ _ _ _ _ _ (teq_equiv side _) Reqe Rth) _ _ _ _ _ _ _ _ _
             Rmorph _ _ _ (@pow_N_th _ _ _ _ (teq_equiv side _)) l p).
  Qed.
End Norm.

(* ========================================================================= *)
(* Part 2: SyncVal-ness by a leaf certificate.  Every op lifts, so a term is  *)
(* SyncVal iff all its LEAVES (the non-operator subterms) are.  After         *)
(* normalising, compare the leaf sets of input and output.                    *)
(* ========================================================================= *)
Definition is_sync {σ} (v : RelVal σ) : bool :=
  match v with ty.SyncVal _ => true | ty.NonSyncVal _ _ => false end.

Lemma relval_ext {σ} (u v : RelVal σ) :
  is_sync u = is_sync v -> ty.projLeft u = ty.projLeft v -> ty.projRight u = ty.projRight v -> u = v.
Proof. destruct u, v; cbn; intros; try discriminate; subst; reflexivity. Qed.

Section Leaves.
  Context {Σ : LCtx}.
  Local Notation Leaf := {σ : Ty & Term Σ σ}.

  Fixpoint leaves {σ} (t : Term Σ σ) : list Leaf :=
    match t with
    | term_binop _ a b => List.app (leaves a) (leaves b)
    | term_unop _ a => leaves a
    | term_val _ _ => nil
    | t => cons (existT _ t) nil
    end.

  Definition leaf_sync (ι : RValuation Σ) (x : Leaf) : bool := is_sync (inst (projT2 x) ι).

  Lemma sync_leaves (ι : RValuation Σ) {σ} (t : Term Σ σ) :
    is_sync (inst t ι) = List.forallb (leaf_sync ι) (leaves t).
  Proof.
    induction t; cbn [leaves]; try (unfold leaf_sync; cbn; rewrite ?Bool.andb_true_r; reflexivity).
    - rewrite List.forallb_app. rewrite <- IHt1. rewrite <- IHt2. cbn.
      unfold bop.evalRel. destruct (inst t1 ι), (inst t2 ι); reflexivity.
    - rewrite <- IHt. cbn. unfold uop.evalRel. destruct (inst t ι); reflexivity.
  Qed.

  Definition leaf_eqb (x y : Leaf) : bool :=
    match x, y with
    | existT σ t, existT τ u =>
        match eq_dec σ τ with
        | left e => Term_eqb (eq_rect σ (Term Σ) t τ e) u
        | right _ => false
        end
    end.

  Lemma leaf_eqb_spec x y : leaf_eqb x y = true -> x = y.
  Proof.
    destruct x as [σ t], y as [τ u]; cbn.
    destruct (eq_dec σ τ) as [e|]; [|discriminate]. subst τ. cbn.
    destruct (Term_eqb_spec t u); [|discriminate]. intros _. subst. reflexivity.
  Qed.

  Definition leaves_incl (xs ys : list Leaf) : bool :=
    List.forallb (fun x => List.existsb (leaf_eqb x) ys) xs.

  Lemma leaves_incl_sync ι xs ys :
    leaves_incl xs ys = true -> List.forallb (leaf_sync ι) ys = true -> List.forallb (leaf_sync ι) xs = true.
  Proof.
    unfold leaves_incl. intros Hi Hy. apply List.forallb_forall. intros x Hx.
    apply List.forallb_forall with (x := x) in Hi; [|exact Hx].
    apply List.existsb_exists in Hi. destruct Hi as [y [Hy' Hxy]].
    apply leaf_eqb_spec in Hxy. subst y.
    apply List.forallb_forall with (x := x) in Hy; [exact Hy|exact Hy'].
  Qed.

  (* the certificate: same leaf SET both ways => same SyncVal-ness *)
  Definition same_leaves {σ} (t u : Term Σ σ) : bool :=
    andb (leaves_incl (leaves t) (leaves u)) (leaves_incl (leaves u) (leaves t)).

  Lemma same_leaves_sync ι {σ} (t u : Term Σ σ) :
    same_leaves t u = true -> is_sync (inst t ι) = is_sync (inst u ι).
  Proof.
    unfold same_leaves. intros H. apply andb_prop in H. destruct H as [H1 H2].
    rewrite !sync_leaves.
    destruct (List.forallb (leaf_sync ι) (leaves u)) eqn:Eu.
    - apply (leaves_incl_sync ι _ _ H1) in Eu. exact Eu.
    - destruct (List.forallb (leaf_sync ι) (leaves t)) eqn:Et; [|reflexivity].
      apply (leaves_incl_sync ι _ _ H2) in Et. congruence.
  Qed.

  (* both projections agree + same leaves: EXACT RelVal equality *)
  Lemma teq_leaves_inst {σ} (t u : Term Σ σ) :
    teq true t u -> teq false t u -> same_leaves t u = true -> forall ι, inst t ι = inst u ι.
  Proof.
    intros HL HR HS ι. apply relval_ext.
    - apply same_leaves_sync. exact HS.
    - exact (HL ι).
    - exact (HR ι).
  Qed.
End Leaves.

(* ========================================================================= *)
(* Part 2b: clean up Pphi_dev's leftovers: `t + 0`, `0 + t`, `t * 1`, `1 * t` *)
(* for LITERAL constants.  Exact over RelVal (a literal is SyncVal, so it adds *)
(* no taint) and leaf-preserving (constants are not leaves).  Never touches  *)
(* `0 * a` with an atom a: that is the taint-keeping padding.                 *)
(* ========================================================================= *)
Inductive CView {Σ : LCtx} {n : nat} : Type :=
| CAdd (a b : Term Σ (ty.bvec n))
| CMul (a b : Term Σ (ty.bvec n))
| CSub (a b : Term Σ (ty.bvec n))
| CNeg (a : Term Σ (ty.bvec n))
| COther.
Arguments CView : clear implicits.

Equations c_view {Σ n} (t : Term Σ (ty.bvec n)) : CView Σ n :=
  c_view (term_binop bop.bvadd a b) := CAdd a b;
  c_view (term_binop bop.bvmul a b) := CMul a b;
  c_view (term_binop bop.bvsub a b) := CSub a b;
  c_view (term_unop uop.negate a) := CNeg a;
  c_view _ := COther.

Lemma c_view_spec {Σ n} (t : Term Σ (ty.bvec n)) :
  match c_view t with
  | CAdd a b => t = term_binop bop.bvadd a b
  | CMul a b => t = term_binop bop.bvmul a b
  | CSub a b => t = term_binop bop.bvsub a b
  | CNeg a => t = term_unop uop.negate a
  | COther => True
  end.
Proof. funelim (c_view t); try reflexivity; exact I. Qed.

Section Clean.
  Context {Σ : LCtx} {n : nat}.
  Local Notation T := (Term Σ (ty.bvec n)).

  Definition is_lit (c : bv n) (t : T) : bool :=
    match term_get_val t with Some v => bv.eqb v c | None => false end.

  Definition is_val (t : T) : bool :=
    match term_get_val t with Some _ => true | None => false end.

  Lemma rel_add_comm (u v : RelVal (ty.bvec n)) :
    bop.evalRel bop.bvadd u v = bop.evalRel bop.bvadd v u.
  Proof. destruct u, v; cbn; f_equal; apply bv.add_comm. Qed.

  Lemma is_lit_spec c t : is_lit c t = true -> t = term_val (ty.bvec n) c.
  Proof.
    unfold is_lit. destruct (term_get_val_spec t) as [v ->|]; [|discriminate].
    destruct (bv.eqb_spec v c) as [->|]; [reflexivity|discriminate].
  Qed.

  Fixpoint clean (fuel : nat) (t : T) : T :=
    match fuel with
    | O => t
    | S f =>
        match c_view t with
        | CAdd a b => let a' := clean f a in let b' := clean f b in
                      if is_lit bv.zero b' then a' else if is_lit bv.zero a' then b'
                      (* a literal constant goes LEFT, as the solver's rules expect *)
                      else if is_val b' then term_binop bop.bvadd b' a'
                      else term_binop bop.bvadd a' b'
        | CMul a b => let a' := clean f a in let b' := clean f b in
                      if is_lit bv.one b' then a' else if is_lit bv.one a' then b'
                      else term_binop bop.bvmul a' b'
        | CSub a b => term_binop bop.bvsub (clean f a) (clean f b)
        | CNeg a => term_unop uop.negate (clean f a)
        | COther => t
        end
    end.

  Lemma rel_add_zero (v : RelVal (ty.bvec n)) :
    bop.evalRel bop.bvadd v (ty.SyncVal bv.zero) = v /\ bop.evalRel bop.bvadd (ty.SyncVal bv.zero) v = v.
  Proof.
    destruct v; cbn; split; f_equal;
      first [ apply bv.add_zero_r | apply bv.add_zero_l ].
  Qed.

  Add Ring bvr : (bv.ring_theory n).
  Lemma mul_one_r (x : bv n) : bv.mul x bv.one = x. Proof. ring. Qed.
  Lemma mul_one_l (x : bv n) : bv.mul bv.one x = x. Proof. ring. Qed.

  Lemma rel_mul_one (v : RelVal (ty.bvec n)) :
    bop.evalRel bop.bvmul v (ty.SyncVal bv.one) = v /\ bop.evalRel bop.bvmul (ty.SyncVal bv.one) v = v.
  Proof.
    destruct v; cbn; split; f_equal; first [ apply mul_one_r | apply mul_one_l ].
  Qed.

  (* rewriting with these keeps `inst` folded (a bare cbn unfolds the class
     method, and then rewrites with IH no longer match) *)
  Lemma inst_binop {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) (a : Term Σ σ1) (b : Term Σ σ2) (ι : RValuation Σ) :
    inst (term_binop op a b) ι = bop.evalRel op (inst a ι) (inst b ι).
  Proof. reflexivity. Qed.
  Lemma inst_unop {σ1 σ2} (op : UnOp σ1 σ2) (a : Term Σ σ1) (ι : RValuation Σ) :
    inst (term_unop op a) ι = uop.evalRel op (inst a ι).
  Proof. reflexivity. Qed.
  (* the equation's type pinned to RelVal: stated at RV (Val σ) it does not
     match goals spelled RelVal (a rewrite matches the type argument too) *)
  Lemma inst_val (v : bv n) (ι : RValuation Σ) :
    @eq (RelVal (ty.bvec n)) (inst (term_val (ty.bvec n) v) ι) (ty.SyncVal v).
  Proof. reflexivity. Qed.

  Lemma clean_sound fuel t (ι : RValuation Σ) : inst (clean fuel t) ι = inst t ι.
  Proof.
    revert t; induction fuel as [|f IH]; intros t; [reflexivity|]. cbn [clean].
    pose proof (c_view_spec t) as Hv. destruct (c_view t) as [a b|a b|a b|a|]; subst; try reflexivity.
    - rewrite inst_binop. destruct (is_lit bv.zero (clean f b)) eqn:Hb.
      + apply is_lit_spec in Hb. rewrite IH. rewrite <- (IH b). rewrite Hb. rewrite inst_val.
        symmetry. apply rel_add_zero.
      + destruct (is_lit bv.zero (clean f a)) eqn:Ha.
        * apply is_lit_spec in Ha. rewrite IH. rewrite <- (IH a). rewrite Ha. rewrite inst_val.
          symmetry. apply rel_add_zero.
        * destruct (is_val (clean f b)); rewrite inst_binop; rewrite !IH; [apply rel_add_comm|reflexivity].
    - rewrite inst_binop. destruct (is_lit bv.one (clean f b)) eqn:Hb.
      + apply is_lit_spec in Hb. rewrite IH. rewrite <- (IH b). rewrite Hb. rewrite inst_val.
        symmetry. apply rel_mul_one.
      + destruct (is_lit bv.one (clean f a)) eqn:Ha.
        * apply is_lit_spec in Ha. rewrite IH. rewrite <- (IH a). rewrite Ha. rewrite inst_val.
          symmetry. apply rel_mul_one.
        * rewrite inst_binop. rewrite !IH. reflexivity.
    - rewrite !inst_binop. rewrite !IH. reflexivity.
    - rewrite !inst_unop. rewrite IH. reflexivity.
  Qed.

  Lemma clean_teq side fuel t : teq side (clean fuel t) t.
  Proof. intros ι. rewrite clean_sound. reflexivity. Qed.
End Clean.

(* ========================================================================= *)
(* Part 3: the normaliser.  Given a quotation (p, env) of t -- i.e. evalPE   *)
(* env p reconstructs t -- normalise with upstream's norm_aux/Pphi_dev, pad  *)
(* each env atom that the normal form lost as `0 * a`, and accept the result *)
(* only if the leaf certificate holds; otherwise keep t (always sound).      *)
(* ========================================================================= *)
Section Canon.
  Context {Σ : LCtx} {n : nat}.
  Local Notation T := (Term Σ (ty.bvec n)).
  Add Ring bvr : (bv.ring_theory n).

  (* stated over bv n and APPLIED: ring refuses the Val (ty.bvec n) spelling *)
  Lemma add_mul0 (x y : bv n) : bv.add x (bv.mul bv.zero y) = x.
  Proof. ring. Qed.

  Definition pad_atom (u a : T) : T :=
    if leaves_incl (leaves a) (leaves u) then u
    else term_binop bop.bvadd u (term_binop bop.bvmul (term_val (ty.bvec n) bv.zero) a).

  Definition pad (env : list T) (u : T) : T := List.fold_left pad_atom env u.

  Lemma pad_atom_teq side u a : teq side (pad_atom u a) u.
  Proof.
    unfold pad_atom. destruct (leaves_incl _ _); [reflexivity|].
    intros ι. rewrite !rv_proj_bin. rewrite rv_proj_val. cbn [bop.eval].
    apply add_mul0.
  Qed.

  Lemma pad_teq side env u : teq side (pad env u) u.
  Proof.
    revert u. induction env as [|a env IH]; intros u; cbn; [reflexivity|].
    etransitivity; [apply IH|]. apply pad_atom_teq.
  Qed.

  Definition canon_with (env : list T) (p : PExpr Z) (t : T) : T :=
    let u := clean 64 (pad env (evalPol env (normZ p))) in
    if same_leaves t u then u else t.

  (* EXACT soundness over RelVal, given that (p, env) quotes t on both sides *)
  Theorem canon_with_sound env p t :
    (forall side, teq side (evalPE env p) t) ->
    forall ι, inst (canon_with env p t) ι = inst t ι.
  Proof.
    intros Hq ι. unfold canon_with.
    destruct (same_leaves t _) eqn:Hs; [|reflexivity].
    symmetry. apply teq_leaves_inst; [| |exact Hs];
      (etransitivity; [symmetry; apply Hq|]);
      (etransitivity; [symmetry; apply norm_teq|]);
      (etransitivity; [symmetry; apply pad_teq|]); symmetry; apply (clean_teq _ 64).
  Qed.
End Canon.

(* ========================================================================= *)
(* Part 4 (U2): quotation, a canonical atom order, << as multiplication.     *)
(* canon_term: quote once to collect the atoms, SORT them by a structural    *)
(* key, quote again with the sorted list as the starting environment (so    *)
(* each atom's index is its sorted position -- no permutation lemma), then   *)
(* canon_with.                                                               *)
(* ========================================================================= *)
Inductive QView {Σ : LCtx} {n : nat} : Type :=
| QAdd (a b : Term Σ (ty.bvec n))
| QSub (a b : Term Σ (ty.bvec n))
| QMul (a b : Term Σ (ty.bvec n))
| QNeg (a : Term Σ (ty.bvec n))
| QShl (a : Term Σ (ty.bvec n)) (k : nat)
| QVal (v : bv n)
| QAtom.
Arguments QView : clear implicits.

Equations q_view {Σ n} (t : Term Σ (ty.bvec n)) : QView Σ n :=
  q_view (term_val _ v) := QVal v;
  q_view (term_binop bop.bvadd a b) := QAdd a b;
  q_view (term_binop bop.bvsub a b) := QSub a b;
  q_view (term_binop bop.bvmul a b) := QMul a b;
  q_view (term_unop uop.negate a) := QNeg a;
  q_view (term_binop bop.shiftl a (term_val _ k)) := QShl a (N.to_nat (bv.bin k));
  q_view _ := QAtom.

Lemma q_view_spec {Σ n} (t : Term Σ (ty.bvec n)) :
  match q_view t with
  | QAdd a b => t = term_binop bop.bvadd a b
  | QSub a b => t = term_binop bop.bvsub a b
  | QMul a b => t = term_binop bop.bvmul a b
  | QNeg a => t = term_unop uop.negate a
  | QShl a k => exists m (kv : bv m), t = term_binop bop.shiftl a (term_val (ty.bvec m) kv)
                /\ k = N.to_nat (bv.bin kv)
  | QVal v => t = term_val (ty.bvec n) v
  | QAtom => True
  end.
Proof. funelim (q_view t); try reflexivity; try exact I. eexists _, _; split; reflexivity. Qed.

(* << by a constant IS multiplication by 2^k, per projection *)
Lemma shiftl_as_mul {n m} (x : bv n) (kv : bv m) :
  bv.shiftl x kv = bv.mul x (bv.of_Z (2 ^ Z.of_nat (N.to_nat (bv.bin kv)))).
Proof.
  apply bv.unsigned_inj. unfold bv.shiftl. rewrite bv.unsigned_of_Z. rewrite bv.unsigned_mul.
  rewrite bv.unsigned_of_Z. unfold bv.truncz.
  rewrite Z.shiftl_mul_pow2; [|unfold bv.unsigned; lia]. rewrite N_nat_Z.
  rewrite Z.mul_mod_idemp_r; [reflexivity|]. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n)). lia.
Qed.

Section Quote.
  Context {Σ : LCtx} {n : nat}.
  Local Notation T := (Term Σ (ty.bvec n)).

  Definition q_atom (env : list T) (t : T) : PExpr Z * list T :=
    match find_index (Term_eqb t) env with
    | Some i => (PEX Z (Pos.of_succ_nat i), env)
    | None => (PEX Z (Pos.of_succ_nat (length env)), List.app env (cons t nil))
    end.

  Fixpoint quote (fuel : nat) (env : list T) (t : T) : PExpr Z * list T :=
    match fuel with
    | O => q_atom env t
    | S f =>
        match q_view t with
        | QVal v => (PEc (bv.unsigned v), env)
        | QAdd a b => let '(p1, e1) := quote f env a in let '(p2, e2) := quote f e1 b in (PEadd p1 p2, e2)
        | QSub a b => let '(p1, e1) := quote f env a in let '(p2, e2) := quote f e1 b in (PEsub p1 p2, e2)
        | QMul a b => let '(p1, e1) := quote f env a in let '(p2, e2) := quote f e1 b in (PEmul p1 p2, e2)
        | QNeg a => let '(p1, e1) := quote f env a in (PEopp p1, e1)
        | QShl a k => let '(p1, e1) := quote f env a in (PEmul p1 (PEc (2 ^ Z.of_nat k)%Z), e1)
        | QAtom => q_atom env t
        end
    end.

  Definition QValid (env : list T) (t : T) (r : PExpr Z * list T) : Prop :=
    (exists ext, @eq (list T) (snd r) (List.app env ext)) /\
    forall la side, teq side (evalPE (List.app (snd r) la) (fst r)) t.

  Lemma q_atom_valid env t : QValid env t (q_atom env t).
  Proof.
    unfold q_atom, QValid. destruct (find_index_spec (Term_eqb t) env) as [i Hi|].
    - split; [exists nil; cbn; symmetry; apply List.app_nil_r|]. intros la side ι.
      remember (env !! i) as o eqn:E. destruct Hi as [u Hu].
      destruct (Term_eqb_spec t u) as [->|]; [|destruct Hu].
      cbn. rewrite (nth_lookup (eq_sym E)). reflexivity.
    - split; [eexists; reflexivity|]. intros la side ι. cbn.
      rewrite <- List.app_assoc. rewrite (nth_length_prefix eq_refl). reflexivity.
  Qed.

  Lemma quote_valid fuel env t : QValid env t (quote fuel env t).
  Proof.
    revert env t; induction fuel as [|f IH]; intros env t; [apply q_atom_valid|]. cbn [quote].
    pose proof (q_view_spec t) as Hv.
    destruct (q_view t) as [a b|a b|a b|a|a k|v|]; cbn in Hv; try (apply q_atom_valid).
    1-3: subst t; destruct (IH env a) as [[e1x He1] Hq1]; destruct (quote f env a) as [p1 e1]; cbn in He1, Hq1;
      destruct (IH e1 b) as [[e2x He2] Hq2]; destruct (quote f e1 b) as [p2 e2]; cbn in He2, Hq2 |- *;
      subst e2 e1; unfold QValid; cbn [fst snd];
      (split; [exists (List.app e1x e2x); symmetry; apply List.app_assoc|]);
      intros la side; cbn; apply teq_bin; [rewrite <- List.app_assoc; apply Hq1|apply Hq2].
    - subst t. destruct (IH env a) as [[e1x He1] Hq1]. destruct (quote f env a) as [p1 e1]. cbn in He1, Hq1 |- *.
      unfold QValid; cbn [fst snd]. split; [exists e1x; exact He1|].
      intros la side. cbn. apply teq_un. apply Hq1.
    - destruct Hv as (m & kv & -> & ->). destruct (IH env a) as [[e1x He1] Hq1]. destruct (quote f env a) as [p1 e1].
      cbn in He1, Hq1 |- *. unfold QValid; cbn [fst snd]. split; [exists e1x; exact He1|].
      intros la side ι.
      change (evalPE (List.app e1 la) (PEmul p1 (PEc (2 ^ Z.of_nat (N.to_nat (bv.bin kv)))%Z)))
        with (term_binop bop.bvmul (evalPE (List.app e1 la) p1)
                (term_val (ty.bvec n) (bv.of_Z (2 ^ Z.of_nat (N.to_nat (bv.bin kv)))%Z))).
      rewrite !rv_proj_bin. rewrite !rv_proj_val. cbn [bop.eval].
      rewrite (Hq1 la side ι). symmetry. apply shiftl_as_mul.
    - subst t. unfold QValid; cbn [fst snd]. split; [exists nil; symmetry; apply List.app_nil_r|].
      intros la side ι. cbn. rewrite bv.of_Z_unsigned. reflexivity.
  Qed.
End Quote.

(* ---- the canonical atom order: a structural key (needs no proof) ---- *)
Definition binop_tag {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) : Z :=
  match op with
  | bop.bvadd => 1 | bop.bvsub => 2 | bop.bvmul => 3 | bop.bvand => 4
  | bop.bvor => 5 | bop.bvxor => 6 | bop.shiftr => 7 | bop.shiftl => 8
  | _ => 0
  end.

Definition unop_tag {σ1 σ2} (op : UnOp σ1 σ2) : Z :=
  match op with
  | uop.negate => 1 | uop.bvnot => 2 | uop.sext => 3 | uop.zext => 4
  | _ => 0
  end.

Definition val_key (σ : Ty) : Val σ -> list Z :=
  match σ with
  | ty.bvec m => fun v => cons (bv.unsigned v) nil
  | _ => fun _ => nil
  end.

Fixpoint term_key {Σ σ} (t : Term Σ σ) : list Z :=
  match t with
  | @term_var _ _ _ lIn => cons 0%Z (cons (Z.of_nat (ctx.in_at lIn)) nil)
  | term_val σ v => cons 1%Z (val_key σ v)
  | term_relval _ _ => cons 2%Z nil
  | term_binop op t1 t2 => cons 3%Z (cons (binop_tag op) (List.app (term_key t1) (term_key t2)))
  | term_unop op t => cons 4%Z (cons (unop_tag op) (term_key t))
  | _ => cons 9%Z nil
  end.

Fixpoint key_le (a b : list Z) : bool :=
  match a, b with
  | nil, _ => true
  | cons _ _, nil => false
  | cons x a', cons y b' => if (x <? y)%Z then true else if (y <? x)%Z then false else key_le a' b'
  end.

Section CanonTerm.
  Context {Σ : LCtx} {n : nat}.
  Local Notation T := (Term Σ (ty.bvec n)).

  Fixpoint ins (a : T) (l : list T) : list T :=
    match l with
    | nil => cons a nil
    | cons b l' => if key_le (term_key a) (term_key b) then cons a l else cons b (ins a l')
    end.
  Fixpoint isort (l : list T) : list T := match l with nil => nil | cons a l' => ins a (isort l') end.

  Definition qfuel : nat := 64.

  (* collect the atoms, sort them, re-quote with the SORTED environment *)
  Definition canon_term (t : T) : T :=
    let envs := isort (snd (quote qfuel nil t)) in
    let '(p, env) := quote qfuel envs t in
    canon_with env p t.

  Theorem canon_term_sound (t : T) ι : inst (canon_term t) ι = inst t ι.
  Proof.
    unfold canon_term.
    destruct (quote_valid qfuel (isort (snd (quote qfuel nil t))) t) as [_ Hq].
    destruct (quote qfuel _ t) as [p env]. cbn in Hq.
    apply canon_with_sound. intros side.
    specialize (Hq nil side). rewrite List.app_nil_r in Hq. exact Hq.
  Qed.
End CanonTerm.


  Local Close Scope Z_scope.


  Section WithLCtx.
    Context {Σ : LCtx}.

    #[local] Ltac lsolve :=
      try progress cbn;
      try (progress autorewrite with katamaran);
      try easy;
      auto with core katamaran.

    Class TermRing (σ : Ty) :=
      MkTermRing {
          tmr_zero : Val σ
        ; tmr_one : Val σ
        ; tmr_plus : BinOp σ σ σ
        ; tmr_times : BinOp σ σ σ
        ; tmr_minus : BinOp σ σ σ
        ; tmr_negate : UnOp σ σ
        ; tmr_of_Z : Z -> Val σ
        }.
    (* OPS ONLY.  Upstream also carried ring_theory / ring_morph modulo ≡,
       which are FALSE over RelVal (x - x is NonSyncVal 0 0 for a secret x);
       the quotation lemmas below use only the ops and ≡-properness (exact
       reconstruction), and the normaliser is proved sound modulo `teq side`
       plus a leaf certificate (CANONICAL RING FORMS, top of the file). *)
    #[export] Instance TermRing_bv {n} : TermRing (ty.bvec n) :=
      @MkTermRing (ty.bvec n) (bv.zero (n := n)) (bv.one (n := n))
        (bop.bvadd (n := n)) (bop.bvmul (n := n)) (bop.bvsub (n := n))
        (uop.negate (n := n)) (bv.of_Z (n := n)).

    (* #[program,export] Instance TermRing_int : TermRing ty.int := { *)
    (*     tmr_zero := 0%Z *)
    (*   ; tmr_one := 1%Z *)
    (*   ; tmr_plus := bop.plus *)
    (*   ; tmr_times := bop.times *)
    (*   ; tmr_minus := bop.minus *)
    (*   ; tmr_negate := uop.neg *)
    (*   ; tmr_of_Z := id *)
    (*   ; tmr_ring_theory := Term_int_ring_theory *)
    (*   ; tmr_ring_eq_ext := Term_int_ring_eq_ext *)
    (*   }. *)
    (* Next Obligation. *)
    (*   constructor; try reflexivity; intros; *)
    (*     rewrite ?term_binop_val, ?term_unop_val; try reflexivity. *)
    (*   apply Zbool.Zeq_bool_eq in H. *)
    (*   subst. *)
    (*   reflexivity. *)
    (* Qed. *)

    (* #[program, export] Instance TermRing_bv {n} : TermRing (ty.bvec n) := { *)
    (*     tmr_zero := bv.zero *)
    (*   ; tmr_one := bv.one *)
    (*   ; tmr_plus := bop.bvadd *)
    (*   ; tmr_times := bop.bvmul *)
    (*   ; tmr_minus := bop.bvsub *)
    (*   ; tmr_negate := uop.negate *)
    (*   ; tmr_of_Z := bv.of_Z *)
    (*   ; tmr_ring_theory := Term_bv_ring_theory Σ n *)
    (*   ; tmr_ring_eq_ext := Term_bv_ring_eq_ext Σ n *)
    (*   }. *)
    (* Next Obligation. *)
    (*   constructor; try reflexivity; rewrite ?term_binop_val, ?term_unop_val; intros. *)
    (*   - now rewrite bv.of_Z_one. *)
    (*   - rewrite term_binop_val; cbn; now rewrite bv.of_Z_add. *)
    (*   - rewrite term_binop_val; cbn; now rewrite bv.of_Z_sub. *)
    (*   - rewrite term_binop_val; cbn; now rewrite bv.of_Z_mul. *)
    (*   - rewrite term_unop_val; cbn; now rewrite bv.of_Z_negate. *)
    (*   - apply Zbool.Zeq_bool_eq in H; now subst. *)
    (* Qed. *)

    Definition evalPExprTm `{TermRing σ} : list (Term Σ σ) -> PExpr Z -> Term Σ σ :=
      PEeval (term_val σ tmr_zero)
        (term_val σ tmr_one)
        (term_binop tmr_plus)
        (term_binop tmr_times)
        (term_binop tmr_minus)
        (term_unop tmr_negate)
        (fun c => term_val σ (tmr_of_Z c))
        id_phi_N (pow_N (term_val (Σ := Σ) σ tmr_one) (term_binop tmr_times)).

    Definition RQuote (σ : Ty) : Type := list (Term Σ σ) -> positive -> PExpr Z * list (Term Σ σ).

    Definition RQuoteValid `{TermRing σ} (t : Term Σ σ) (q : RQuote σ): Prop :=
      forall lo o, match q lo o with
                     (poly , ln) => o = Pos.of_succ_nat (length lo) -> forall la, evalPExprTm (lo ++ ln ++ la) poly ≡ t
                  end.

    Definition Term_Quote_def {σ} (t : Term Σ σ) : RQuote σ :=
      fun ts o =>
        match find_index (fun t' => Term_eqb t t') ts with
        | None => (PEX Z o , [ t ]%list)
        | Some i => (PEX Z (Pos.of_succ_nat i) , []%list)
        end.

    Lemma Term_Quote_def_Valid `{TermRing σ} {t : Term Σ σ} : RQuoteValid t (Term_Quote_def t).
    Proof.
      intros ts o.
      unfold Term_Quote_def.
      destruct (find_index_spec (fun t' => Term_eqb t t') ts) as [i Hlkpi|];
        intros Ho la; cbn.
      - rewrite (nth_lookup (t := t)); first reflexivity.
        destruct Hlkpi as [a Ha].
        destruct (Term_eqb_spec t a); inversion Ha; now subst.
      - now rewrite nth_length_prefix.
    Qed.

    Definition Term_Quote_unop {n} (comb : PExpr Z -> PExpr Z) (q1 : RQuote n) : RQuote n :=
      fun ts o => let (pol1 , ts1) := q1 ts o in
                  (comb pol1 , ts1).

    Lemma Term_Quote_unop_Valid `{TermRing σ} {op : UnOp σ σ}
      {comb} {t1} {q1} :
      (forall env pol1, evalPExprTm env (comb pol1) = term_unop op (evalPExprTm env pol1)) ->
      RQuoteValid t1 q1 ->
      RQuoteValid (term_unop op t1) (Term_Quote_unop comb q1).
    Proof.
      intros Hcomb Hq1 ts o; unfold Term_Quote_unop; cbn.
      generalize (Hq1 ts o); destruct q1 as [pol1 l1].
      intros.
      now rewrite Hcomb, H0.
    Qed.

    Definition Term_Quote_bin `{TermRing σ} (comb : PExpr Z -> PExpr Z -> PExpr Z) (q1 : RQuote σ) (q2 : RQuote σ) : RQuote σ :=
      fun ts o => let (pol1 , ts1) := q1 ts o in
                  let (pol2 , ts2) := q2 (app ts ts1) (plusNatPos (length ts1) o) in
                  ((comb pol1 pol2) , app ts1 ts2).

    Lemma Term_Quote_bin_Valid `{TermRing σ} {op : BinOp σ σ σ}
      {comb} {t1 t2} {q1 q2} :
      (forall env pol1 pol2, evalPExprTm env (comb pol1 pol2) = term_binop op (evalPExprTm env pol1) (evalPExprTm env pol2)) ->
      RQuoteValid t1 q1 -> RQuoteValid t2 q2 ->
      RQuoteValid (term_binop op t1 t2) (Term_Quote_bin comb q1 q2).
    Proof.
      intros Hcomb Hq1 Hq2 ts o; unfold Term_Quote_bin; cbn.
      generalize (Hq1 ts o); destruct q1 as [pol1 l1].
      intros Hl1.
      generalize (Hq2 (ts ++ l1) (plusNatPos (length l1) o)); destruct q2 as [pol2 l2].
      intros Hl2 Ho l3.
      rewrite Hcomb.
      eapply proper_term_binop.
      - now rewrite <-List.app_assoc, (Hl1 Ho _).
      - rewrite !List.app_assoc, <-List.app_assoc.
        apply Hl2.
        subst.
        now rewrite plusNatPos_of_succ_nat, app_length, Nat.add_comm.
    Qed.

    (* bvec only: int stays a Term (the solver's int rules, e.g.
       try_fetch_bound's `L - (K + unsigned s)`, match specific shapes) *)
    Definition CanonTerm σ : Type :=
      match σ with
      | ty.bvec n => RQuote σ
      | _ => Term Σ σ
      end.

    #[export] Instance equiv_CanonTerm {σ} : base.Equiv (CanonTerm σ)
      := match σ with
         | ty.bvec n => (eq ==> eq ==> base.prod_relation eq base.equiv)%signature
         | _ => base.equiv
         end.

    (* Definition CanonTermRep {σ : Ty} : CanonTerm σ -> Term Σ σ -> Prop := *)
    (*   match σ with *)
    (*   | ty.bvec n => fun ct t => RQuoteValid t ct *)
    (*   | ty.int => fun ct t => RQuoteValid t ct *)
    (*   | _ => fun ct t => ct ≡ t *)
    (*   end. *)

    #[export] Instance proper_tl_equiv `{base.Equiv A} :
      Proper (base.equiv ==> base.equiv) (@tl A).
    Proof. intros l1 l2 Hl. destruct Hl; cbn; [constructor|easy]. Qed.

    #[export] Instance proper_hd_equiv {A} {_ : base.Equiv A} :
      Proper (base.equiv ==> base.equiv ==> base.equiv) (@hd A).
    Proof. intros def1 def2 Hdef l1 l2 Hl. now destruct Hl. Qed.

    #[export] Instance proper_jump_equiv `{base.Equiv A} :
      Proper (eq ==> base.equiv ==> base.equiv) (@BinList.jump A).
    Proof.
      intros p ? <-.
      induction p; cbn;
        intros l1 l2 Hl;
        try do 2 apply IHp;
        now try apply proper_tl_equiv.
    Qed.

    Lemma proper_pow_pos `{base.Equiv A} :
      Proper ((base.equiv ==> base.equiv ==> base.equiv) ==> base.equiv ==> eq ==> base.equiv) (@pow_pos A).
    Proof.
      intros m1 m2 Hm x1 x2 Hx n ? <-.
      revert m1 m2 Hm x1 x2 Hx.
      induction n; cbn.
      - intros m1 m2 Hm x1 x2 Hx.
        apply Hm; [easy|].
        apply Hm; now apply IHn.
      - intros m1 m2 Hm x1 x2 Hx.
        apply Hm; now apply IHn.
      - now intros.
    Qed.

    Lemma proper_pow_N `{base.Equiv A} :
      Proper (base.equiv ==> (base.equiv ==> base.equiv ==> base.equiv) ==> base.equiv ==> eq ==> base.equiv) (@pow_N A).
    Proof.
      intros o1 o2 Ho m1 m2 Hm x1 x2 Hx n ? <-.
      revert o1 o2 Ho m1 m2 Hm x1 x2 Hx.
      destruct n; cbn.
      - now intros.
      - intros o1 o2 Ho m1 m2 Hm x1 x2 Hx.
        now apply proper_pow_pos.
    Qed.

    #[export] Instance proper_nth_equiv `{base.Equiv A} :
      Proper (base.equiv ==> eq ==> base.equiv ==> base.equiv) (@BinList.nth A).
    Proof.
      intros def1 def2 Hdef x ? <-.
      induction x; intros l1 l2 Hl; cbn.
      - apply IHx, proper_jump_equiv; first easy.
        now apply proper_tl_equiv.
      - now apply IHx, proper_jump_equiv.
      - now apply proper_hd_equiv.
    Qed.

    #[export] Instance proper_evalPExprTm `{TermRing σ} :
      Proper (base.equiv ==> eq ==> base.equiv) (evalPExprTm (σ := σ)).
    Proof.
      intros env1 env2 Henv expr ? <-.
      induction expr; cbn; try easy.
      - now rewrite Henv.
      - now rewrite IHexpr1, IHexpr2.
      - now rewrite IHexpr1, IHexpr2.
      - now rewrite IHexpr1, IHexpr2.
      - now rewrite IHexpr.
      - apply proper_pow_N; try easy.
        apply proper_term_binop.
    Qed.

    (* Instance proper_CanonTermRep `{TermRing σ} : Proper (base.equiv ==> base.equiv ==> iff) (@CanonTermRep σ). *)
    (* Proof. *)
    (*   intros x1 x2 Hx y1 y2 Hy. *)
    (*   destruct σ; cbn; try now rewrite Hx, Hy; *)
    (*     cbn. *)
    (*   - split; intros Hrqv lo o; specialize (Hrqv lo o); specialize (Hx lo _ eq_refl o _ eq_refl); *)
    (*     destruct (x1 lo o), (x2 lo o), Hx; cbn in *; subst. *)
    (*     + intros -> la. *)
    (*       rewrite <-Hy, <-H1. *)
    (*       now apply Hrqv. *)
    (*     + intros -> la. *)
    (*       rewrite Hy, H1. *)
    (*       now apply Hrqv. *)
    (*   - split; intros Hrqv lo o; specialize (Hrqv lo o); specialize (Hx lo _ eq_refl o _ eq_refl); *)
    (*     destruct (x1 lo o), (x2 lo o), Hx; cbn in *; subst. *)
    (*     + intros -> la. *)
    (*       rewrite <-Hy, <-H1. *)
    (*       now apply Hrqv. *)
    (*     + intros -> la. *)
    (*       rewrite Hy, H1. *)
    (*       now apply Hrqv. *)
    (* Qed. *)

    (* Equations(noeqns) peval_append {σ} (t1 t2 : Term Σ (ty.list σ)) : Term Σ (ty.list σ) := *)
    (* | term_val _ v1                 | term_val _ v2 := term_val (ty.list σ) (app v1 v2); *)
    (* (* TODO: recurse over the value instead *) *)
    (* | term_val _ nil                | t2 := t2; *)
    (* | term_val _ (cons v vs)        | t2 := term_binop bop.cons (term_val σ v) (term_binop bop.append (term_val (ty.list σ) vs) t2); *)
    (* | term_binop bop.cons t11 t12 | t2 := term_binop bop.cons t11 (term_binop bop.append t12 t2); *)
    (* | t1                            | t2 := term_binop bop.append t1 t2. *)

    Definition peval_and_val (t : Term Σ ty.bool) (v : Val ty.bool) :
      Term Σ ty.bool := if v then t else term_and t (term_val ty.bool false).
    Definition peval_or_val (t : Term Σ ty.bool) (v : Val ty.bool) :
      Term Σ ty.bool := if v then term_or t (term_val ty.bool true) else t.

    (* TODO: These lemmas are not true anymore. *)
    Lemma peval_and_val_sound (t : Term Σ ty.bool)
      (v : Val ty.bool) :
      peval_and_val t v ≡ term_binop bop.and t (term_val ty.bool v).
    Proof.
      destruct v; cbn; intros ι; cbn.
      - destructInsts; cbn; now repeat rewrite andb_true_r.
      - destructInsts; cbn. now repeat rewrite andb_false_r.
        auto.
    Qed.

    Lemma peval_or_val_sound (t : Term Σ ty.bool)
      (v : Val ty.bool) :
      peval_or_val t v ≡ term_binop bop.or t (term_val ty.bool v).
    Proof.
      destruct v; cbn; intros ι; cbn.
      - auto. (* now rewrite orb_true_r. *)
      - destruct inst; cbn; now rewrite !orb_false_r.        
    Qed.

    Equations(noeqns) peval_and (t1 t2 : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ b  , t2            => peval_and_val t2 b
    | t1            , term_val _ b  => peval_and_val t1 b
    | t1            , t2            => term_binop bop.and t1 t2.

    Equations(noeqns) peval_or (t1 t2 : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ b  , t2            => peval_or_val t2 b
    | t1            , term_val _ b  => peval_or_val t1 b
    | t1            , t2            => term_binop bop.or t1 t2.

    Equations peval_plus (t1 t2 : Term Σ ty.int) : Term Σ ty.int :=
    | term_val _ v1  , term_val _ v2    => term_val ty.int (v1 + v2)%Z
    | term_val _ 0%Z , t2               => t2
    | t1             , term_val _ 0%Z   => t1
    | t1             , term_val _ v2    => term_binop bop.plus (term_val ty.int v2) t1
    | t1             , t2               => term_binop bop.plus t1 t2.

    Equations peval_minus (t1 t2 : Term Σ ty.int) : Term Σ ty.int :=
    | term_val _ v1  , term_val _ v2    => term_val ty.int (v1 - v2)%Z
    | t1             , term_val _ 0%Z   => t1
    | t1             , term_val _ v2    => term_binop bop.minus t1 (term_val ty.int v2)
    | t1             , t2               => term_binop bop.minus t1 t2.

    (* ---- branchless-mask recognition (uop.expand) --------------------------
       Constant-time code turns a predicate into a full-word 0/~0 mask and
       ANDs it into an arithmetic expression instead of branching.  Every
       compiler spelling of that ends the same way: put the comparison's 0/1
       result in a register, then `addi -1`, since [b] - 1 = -[¬b].  Folding
       the resulting 3-node chain into one `uop.expand` node is the point of
       this recognizer.

       GROUND TRUTH, dumped from the executor (Example/ZZExpandDump.v) for
       `snez a2,a0; addi a2,a2,-1`:

         bvadd (val 0xffffffff) (zext (bvcons (bvult (val 0) C) (val nil)))

       — the immediate is already folded to all-ones and the constant has been
       normalized to the LEFT of the sum by the `t1, term_val v2` clause
       below.  A peval rule whose pattern never fires is INVISIBLE (everything
       still compiles, there is simply no effect), so re-dump that probe
       before touching the pattern.

       The recognizer deliberately stops at the comparison BIT and does not
       look at what is compared: `uop.expand` takes the predicate itself, so
       `snez` (= sltu rd,x0,rs), `seqz` (= sltiu rd,rs,1) and any other
       comparison all fold through this one rule, and no width relation
       between the compared operands and the mask has to be decided.  The
       predicate stays a pure term, so a comparison over secret data is fine
       here — a NonSyncVal bool is only fatal in a formula/secLeak position.

       NOT covered (needs its own rule): the arithmetic bit-extraction form
       `ones ⊕ ((((Z&1) - 1) & ~(Z&1)) >> 31)` = `-(Z & 1)`, which is how the
       GHASH/`mulx` round selects on a single bit rather than on a bool. *)

    (* Recognize the widened comparison bit `zext (bvcons b w)` with w's VALUE
       zero, i.e. the 0/1 term [b], and return b.  Requiring `bin w = 0`
       rather than w's WIDTH to be 0 is both the condition the identity
       actually needs and a way to avoid pinning that width inside a pattern. *)
    Equations bvmask_indicator {n} (t : Term Σ (ty.bvec n)) : option (Term Σ ty.bool) :=
    | term_unop uop.zext (term_binop bop.bvcons b (term_val _ w)) =>
        if N.eqb (bv.bin w) 0%N then Some b else None ;
    | _ => None.

    (* Recognize a MASK, i.e. `expand b`, and hand back its predicate. *)
    Equations bvmask_try_expand {n} (t : Term Σ (ty.bvec n)) : option (Term Σ ty.bool) :=
    | term_unop uop.expand b => Some b ;
    | _ => None.

    Definition peval_bvadd_val_default {n} (t : Term Σ (ty.bvec n))
      (v : Val (ty.bvec n)) : Term Σ (ty.bvec n) :=
      term_binop bop.bvadd (term_val (ty.bvec n) v) t.

    (* all-ones ⊕ [b] = [b] - 1 = -[¬b] = bvnot (expand b).
       Soundness is bv.add_zext_cons_ones, a plain `bv` identity — which is all
       that is needed even though the predicate `b` may be a comparison over
       SECRET data: both sides are pure terms, so the relational obligation
       follows from the Val-level one by homomorphism of `inst`/liftBinOp (see
       the `relval-rewrite-over-secrets` skill).  No NonSyncVal case analysis
       enters the *statement*; the two constructors show up in the proof only
       because `cbn` exposes liftUnOp. *)
    Definition peval_bvadd_mask {n} (t : Term Σ (ty.bvec n))
      (v : Val (ty.bvec n)) : Term Σ (ty.bvec n) :=
      if eq_dec v (bv.ones n) then
        match bvmask_indicator t with
        (* `expand (not b)`, NOT `bvnot (expand b)`: peval is bottom-up, so a
           bvnot node built here would never be revisited by peval_bvnot and the
           complement would stay stuck in the bitvector layer.  Emitting it on
           the bool side puts the term in canonical shape immediately.  The
           `not` is left unsimplified because peval_not is defined further down
           this file; anything that later pevals the predicate absorbs it. *)
        | Some b => term_unop uop.expand (term_unop uop.not b)
        | None   => peval_bvadd_val_default t v
        end
      else peval_bvadd_val_default t v.

    (* ---- SELF-TESTS for the mask rules ------------------------------------
       A peval rule whose pattern never matches is INVISIBLE: the file still
       compiles and the rule silently does nothing.  These are conversion
       checks (`reflexivity`, no proof search) pinning each rule's firing AND
       non-firing shapes, so that a later edit to a pattern — or to what
       peval_bvadd normalizes its arguments to — breaks the build instead of
       quietly disabling the rule.  Written after the corresponding rule 1-4
       were each found, by dumping a real VC, to fire on executor output;
       these keep that true.  See Example/ZZExpandDump.v and
       Example/ZZMaskAlgebra.v for the dumps themselves. *)

    (* FIRES: `<compare> ; addi -1` over a widened 1-bit comparison result. *)
    Lemma selftest_bvadd_mask_fires (b : Term Σ ty.bool) :
      peval_bvadd_mask
        (term_unop (uop.zext (m := 1) (n := 32))
           (term_binop bop.bvcons b (term_val (ty.bvec 0) bv.nil)))
        (bv.ones 32)
      = term_unop uop.expand (term_unop uop.not b).
    Proof. reflexivity. Qed.

    (* INERT unless the constant is all-ones (guard 1).  `t` is never inspected
       here, which is exactly the point: the constant is checked first. *)
    Lemma selftest_bvadd_mask_needs_ones (t : Term Σ (ty.bvec 32)) :
      peval_bvadd_mask t bv.zero
      = term_binop bop.bvadd (term_val (ty.bvec 32) bv.zero) t.
    Proof. reflexivity. Qed.

    (* INERT unless the operand is the indicator shape (guard 2). *)
    Lemma selftest_bvadd_mask_needs_indicator (t : Term Σ (ty.bvec 32)) :
      peval_bvadd_mask (term_unop uop.bvnot t) (bv.ones 32)
      = term_binop bop.bvadd (term_val (ty.bvec 32) (bv.ones 32))
          (term_unop uop.bvnot t).
    Proof. reflexivity. Qed.

    (* The folded constant of the two clauses below can come out ZERO, as in
       (x ⊕ 4) ⊕ -4.  Without this check that gave `0 ⊕ x`, which is not
       canonical: the direct `0 ⊕ t` clause already returns `t`, so the same
       address had two spellings and a precise chunk match on it failed
       (PLAN-array-invariants: a walking pointer's cell, re-derived from an
       array's start as (dp ⊕ 4) ⊕ -4, against the heap's bare `dp`). *)
    Definition peval_bvadd_fold {n} (v : Val (ty.bvec n)) (t : Term Σ (ty.bvec n))
      : Term Σ (ty.bvec n) :=
      if eq_dec v bv.zero then t else term_binop bop.bvadd (term_val (ty.bvec n) v) t.

    (* FLOAT a nested constant to the head (PLAN-array-invariants,
       parametric mlen): one address must have ONE spelling, and the same
       word is reached both as `x + (M << 2)` and as its neighbour plus 4,
       `(x + ((M - 1) << 2)) + 4`, which peval_shiftl turns into
       `x + (-4 + (M << 2)) + 4`.  Unconditional mod 2^n (assoc/comm), both
       sides pure, so sound over secrets.  Arguments are canonical (peval is
       bottom-up), so the remainders have no constant head.  A one-clause
       matcher, not nested Equations patterns: those three overlapping
       clauses made Equations fail to build a covering. *)
    Equations bvadd_head {n} (t : Term Σ (ty.bvec n))
      : option (Val (ty.bvec n) * Term Σ (ty.bvec n)) :=
      bvadd_head (term_binop bop.bvadd (term_val _ v) t') := Some (v, t');
      bvadd_head _ := None.

    Definition peval_bvadd_float {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
      match bvadd_head t1, bvadd_head t2 with
      | Some (v1, a), Some (v2, b) => peval_bvadd_fold (bv.add v1 v2) (term_binop bop.bvadd a b)
      | Some (v1, a), None => term_binop bop.bvadd (term_val (ty.bvec n) v1) (term_binop bop.bvadd a t2)
      | None, Some (v2, b) => term_binop bop.bvadd (term_val (ty.bvec n) v2) (term_binop bop.bvadd t1 b)
      | None, None => term_binop bop.bvadd t1 t2
      end.

    Equations peval_bvadd {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
    | term_val _ v1          , term_val _ v2          => term_val (ty.bvec _) (bv.add v1 v2)
    | term_val _ (bv.mk 0 _) , t2                     => t2
    | t1                     , term_val _ (bv.mk 0 _) => t1
    (* Fold a constant into a constant-headed sum, so repeated increments of a
       symbolic base collapse: c2 ⊕ (c1 ⊕ t) and (c1 ⊕ t) ⊕ c2 both become
       (c1+c2) ⊕ t.  Arguments are already peval-canonical (peval is bottom-up),
       so t has no constant head and the result stays canonical. *)
    | term_binop bop.bvadd (term_val _ v1) t' , term_val _ v2 =>
        peval_bvadd_fold (bv.add v1 v2) t'
    | term_val _ v1          , term_binop bop.bvadd (term_val _ v2) t' =>
        peval_bvadd_fold (bv.add v1 v2) t'
    | t1                     , term_val _ v2          => peval_bvadd_mask t1 v2
    (* everything else: the canonical ring form (see CANONICAL RING FORMS) *)
    | t1                     , t2                     => canon_term (term_binop bop.bvadd t1 t2).

    Definition peval_bvand_val_default {m} (t : Term Σ (ty.bvec m))
      (v : Val (ty.bvec m)) : Term Σ (ty.bvec m) :=
      let z := bv.zero in
      if eq_dec z v
      then term_val (ty.bvec m) z
      else
        if eq_dec (bv.ones m) v
        then t
        else term_binop bop.bvand t (term_val (ty.bvec m) v).

    Section WithPevalBvandVal.

      Variable peval_bvand_val :
        (forall [m],  Term Σ (ty.bvec m) → Val (ty.bvec m) → Term Σ (ty.bvec m)).

      Definition peval_bvand_bvapp_val {m1 m2} (t1 : Term Σ (ty.bvec m1))
        (t2 : Term Σ (ty.bvec m2)) (v : Val (ty.bvec (m1+m2))) :
        Term Σ (ty.bvec (m1+m2)) :=
        let (v1,v2) := bv.appView m1 m2 v in
        term_bvapp (peval_bvand_val t1 v1) (peval_bvand_val t2 v2).

      Definition peval_bvand_bvcons_val {m} (t1 : Term Σ ty.bool)
        (t2 : Term Σ (ty.bvec m)) (v : Val (ty.bvec (S m))) :
        Term Σ (ty.bvec (S m)) :=
        let (v1,v2) := bv.view v in
        term_binop bop.bvcons (peval_and_val t1 v1) (peval_bvand_val t2 v2).

    End WithPevalBvandVal.

    Equations peval_bvand_val [m] (t : Term Σ (ty.bvec m)) (v : Val (ty.bvec m)) :
      Term Σ (ty.bvec m) :=
    | term_val _ v1               , v2 => term_val (ty.bvec _) (bv.land v1 v2)
    | term_binop bop.bvapp t1 t2  , v  => peval_bvand_bvapp_val peval_bvand_val t1 t2 v
    | term_binop bop.bvcons t1 t2 , v  => peval_bvand_bvcons_val peval_bvand_val t1 t2 v
    | t , v  => peval_bvand_val_default t v.

    Equations peval_bvand {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
    | term_val _ v1               , term_val _ v2 => term_val (ty.bvec _) (bv.land v1 v2)
    | term_binop bop.bvapp t1 t2  , term_val _ v  => peval_bvand_bvapp_val peval_bvand_val t1 t2 v
    | term_binop bop.bvcons t1 t2 , term_val _ v  => peval_bvand_bvcons_val peval_bvand_val t1 t2 v
    | term_val _ v                , term_binop bop.bvapp t1 t2 => peval_bvand_bvapp_val peval_bvand_val t1 t2 v
    | term_val _ v                , term_binop bop.bvcons t1 t2 => peval_bvand_bvcons_val peval_bvand_val t1 t2 v
    | t1 , t2  => term_binop bop.bvand t1 t2.

    Definition peval_bvor_val_default {m} (t : Term Σ (ty.bvec m))
      (v : Val (ty.bvec m)) : Term Σ (ty.bvec m) :=
      let o := bv.ones m in
      if eq_dec o v
      then term_val (ty.bvec m) o
      else
        if eq_dec bv.zero v
        then t
        else term_binop bop.bvor t (term_val (ty.bvec m) v).

    Section WithPevalBvorVal.

      Variable peval_bvor_val :
        (forall [m],  Term Σ (ty.bvec m) → Val (ty.bvec m) → Term Σ (ty.bvec m)).

      Definition peval_bvor_bvapp_val {m1 m2} (t1 : Term Σ (ty.bvec m1))
        (t2 : Term Σ (ty.bvec m2)) (v : Val (ty.bvec (m1+m2))) :
        Term Σ (ty.bvec (m1+m2)) :=
        let (v1,v2) := bv.appView m1 m2 v in
        term_bvapp (peval_bvor_val t1 v1) (peval_bvor_val t2 v2).

      Definition peval_bvor_bvcons_val {m} (t1 : Term Σ ty.bool)
        (t2 : Term Σ (ty.bvec m)) (v : Val (ty.bvec (S m))) :
        Term Σ (ty.bvec (S m)) :=
        let (v1,v2) := bv.view v in
        term_binop bop.bvcons (peval_or_val t1 v1) (peval_bvor_val t2 v2).

    End WithPevalBvorVal.

    Equations peval_bvor_val [m] (t : Term Σ (ty.bvec m)) (v : Val (ty.bvec m)) :
      Term Σ (ty.bvec m) :=
    | term_val _ v1               , v2 => term_val (ty.bvec _) (bv.lor v1 v2)
    | term_binop bop.bvapp t1 t2  , v  => peval_bvor_bvapp_val peval_bvor_val t1 t2 v
    | term_binop bop.bvcons t1 t2 , v  => peval_bvor_bvcons_val peval_bvor_val t1 t2 v
    | t , v  => peval_bvor_val_default t v.

    Equations peval_bvor {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
    | term_val _ v1               , term_val _ v2 => term_val (ty.bvec _) (bv.lor v1 v2)
    | term_binop bop.bvapp t1 t2  , term_val _ v  => peval_bvor_bvapp_val peval_bvor_val t1 t2 v
    | term_binop bop.bvcons t1 t2 , term_val _ v  => peval_bvor_bvcons_val peval_bvor_val t1 t2 v
    | term_val _ v                , term_binop bop.bvapp t1 t2 => peval_bvor_bvapp_val peval_bvor_val t1 t2 v
    | term_val _ v                , term_binop bop.bvcons t1 t2 => peval_bvor_bvcons_val peval_bvor_val t1 t2 v
    | t1 , t2  => term_binop bop.bvor t1 t2.

    Definition peval_bvapp_val_r {m n} (t1 : Term Σ (ty.bvec m)) (v : Val (ty.bvec n)) : Term Σ (ty.bvec (m+n)) :=
      match eq_dec n 0 with
      | left e =>
          eq_rect_r (fun l => Term Σ (ty.bvec l)) t1
            (eq_trans (f_equal (Nat.add m) e) (transparent.nat_add_0_r m))
      | right _ => term_bvapp t1 (term_val (ty.bvec n) v)
      end.

    Equations peval_bvapp {m n} (t1 : Term Σ (ty.bvec m)) (t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec (m+n)) :=
    | term_val _ v1 | term_val _ v2 => term_val (ty.bvec _) (bv.app v1 v2)
    | term_bvapp t11 t12 , t2 => eq_rect _ (fun l => Term Σ (ty.bvec l))
                                   (term_bvapp t11 (term_bvapp t12 t2)) _
                                   (transparent.nat_add_assoc _ _ _)
    | t1 , term_val _ v2 => peval_bvapp_val_r t1 v2
    | t1 , t2 => term_bvapp t1 t2.

    Section WithPevalBvdrop.

      Variable peval_bvdrop_eq :
        ∀ m n mn : nat, Term Σ (ty.bvec mn) → m + n = mn → Term Σ (ty.bvec n).

      Definition peval_bvdrop_bvapp {m n} [k l] :
        Term Σ (ty.bvec k) → Term Σ (ty.bvec l) → m + n = k + l → Term Σ (ty.bvec n) :=
        match nat_compare m k with
        | EQ mk   => fun _ t2 e =>
                       eq_rect_r (fun l => Term Σ (ty.bvec l)) t2
                         (transparent.nat_add_cancel_l n l mk e)
        | LT m' d => fun t1 t2 e =>
                       eq_rect_r (fun l => Term Σ (ty.bvec l))
                         (term_bvapp (peval_bvdrop_eq m' (S d) t1 eq_refl) t2)
                         (transparent.nat_add_cancel_l n (S d + l) m'
                            (eq_trans e (eq_sym (transparent.nat_add_assoc m' (S d) l))))
        | GT k' d => fun t1 t2 e =>
                       eq_rect (S d + n) (fun l => Term Σ (ty.bvec l) → Term Σ (ty.bvec n))
                         (fun t3 => peval_bvdrop_eq (S d) n t3 eq_refl)
                         l
                         (transparent.nat_add_cancel_l (S d + n) l k'
                            (eq_trans (transparent.nat_add_assoc k' (S d) n) e)) t2
        end.

      Definition peval_bvdrop_bvcons {m n} [k] (t1 : Term Σ ty.bool)
        (t2 : Term Σ (ty.bvec k)) : m + n = S k → Term Σ (ty.bvec n) :=
        match m with
        | 0   => fun e => eq_rect_r (fun l => Term Σ (ty.bvec l)) (term_bvcons t1 t2) e
        | S m => fun e => peval_bvdrop_eq m n t2 (eq_add_S (m + n) k e)
        end.

      Definition peval_bvdrop_bvdrop {m n} [k l] (t1 : Term Σ (ty.bvec (k + l)))
        (e : m + n = l) : Term Σ (ty.bvec n) :=
        peval_bvdrop_eq (k + m) n t1
          (eq_trans
             (eq_sym (transparent.nat_add_assoc k m n))
             (f_equal (Init.Nat.add k) e)).

    End WithPevalBvdrop.

    Definition peval_bvdrop_val {m n} [k] (v : Val (ty.bvec k))
      (e : m + n = k) : Term Σ (ty.bvec n) :=
      term_val (ty.bvec _) (bv.drop m (eq_rect_r bv v e)).

    Definition peval_bvdrop_relval {m n} [k] (rv : RelVal (ty.bvec k))
      (e : m + n = k) : Term Σ (ty.bvec n) :=
      term_relval (ty.bvec _) (ty.liftUnOp (σ1 := ty.bvec (m + n)) (σ2 := ty.bvec n) (bv.drop m) (ty.liftUnOp (σ2 := ty.bvec (m + n)) (fun v : Val (ty.bvec k) => (eq_rect_r bv v e)) rv)).

    Definition peval_bvdrop_default m {n} mn (t : Term Σ (ty.bvec mn)) (e : m + n = mn) :
      Term Σ (ty.bvec n) :=
      match eq_dec 0 m with
      | left em0 => eq_rect_r (fun l => Term Σ (ty.bvec l)) t
                      (eq_trans (f_equal (fun m => m + n) em0) e)
      | right _ =>
          match eq_dec n 0 with
          | left e0n => term_val (ty.bvec n) (eq_rect_r bv bv.nil e0n)
          | right _ => term_bvdrop m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e)
          end
      end.

    Fixpoint peval_bvdrop_eq m {n} mn (t : Term Σ (ty.bvec mn)) (e : m + n = mn) {struct t} :
      Term Σ (ty.bvec n) :=
      Term_bvec_case (fun mn _ => m + n = mn → Term Σ (ty.bvec n))
        (fun (*var*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*val*) k v e => peval_bvdrop_val v e)
        (fun (*relval*) k v e => peval_bvdrop_relval v e)
        (fun (*bvadd*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvsub*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvmul*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvand*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvor*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvxor*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*shiftr*) _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*shift*) _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvapp*) k l t1 t2 e => peval_bvdrop_bvapp peval_bvdrop_eq t1 t2 e)
        (fun (*bvcons*) k t1 t2 e => peval_bvdrop_bvcons peval_bvdrop_eq t1 t2 e)
        (fun (*u_v_s*) _ _ _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvnot*) _ _ _ => peval_bvdrop_default _ t e)
        (fun (*negate*) _ _ _ => peval_bvdrop_default _ t e)
        (fun (*sext*) _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*zext*) _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*g_s_i*) _ _ _ => peval_bvdrop_default _ t e)
        (fun (*truncate*) _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*v_s*) _ _ _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*bvdrop*) k l t1 e => peval_bvdrop_bvdrop peval_bvdrop_eq t1 e)
        (fun (*bvtake*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*expand*) _ _ _ => peval_bvdrop_default _ t e)
        (fun (*coalesce*) _ _ _ _ => peval_bvdrop_default _ t e)
        (fun (*mulx*) _ _ _ _ => peval_bvdrop_default _ t e)
        t e.

    Definition peval_bvdrop m {n} (t : Term Σ (ty.bvec (m + n))) :
      Term Σ (ty.bvec n) := peval_bvdrop_eq m t eq_refl.

    Section WithPevalBvtake.

      Variable peval_bvtake_eq :
        ∀ m n mn : nat, Term Σ (ty.bvec mn) → m + n = mn → Term Σ (ty.bvec m).

      Definition peval_bvtake_bvapp {m n} [k l] :
        Term Σ (ty.bvec k) → Term Σ (ty.bvec l) → m + n = k + l → Term Σ (ty.bvec m) :=
        match nat_compare m k with
        | EQ mk   => fun t1 _ _ => t1
        | LT m' d => fun t1 _ _ => peval_bvtake_eq m' (S d) t1 eq_refl
        | GT k' d => fun t1 t2 e =>
                       term_bvapp t1
                         (peval_bvtake_eq (S d) n t2
                            (transparent.nat_add_cancel_l (S d + n) l k'
                               (eq_trans (transparent.nat_add_assoc k' (S d) n) e)))
        end.

      Definition peval_bvtake_bvcons {m n} [k] (t1 : Term Σ ty.bool)
        (t2 : Term Σ (ty.bvec k)) : m + n = S k → Term Σ (ty.bvec m) :=
        match m with
        | 0   => fun _ => term_val (ty.bvec 0) bv.nil
        | S m => fun e => term_bvcons t1
                            (peval_bvtake_eq m n t2 (eq_add_S (m + n) k e))
        end.

      Definition peval_bvtake_bvtake {m n} [k l]
        (t1 : Term Σ (ty.bvec (k + l))) (e : m + n = k) : Term Σ (ty.bvec m) :=
        let e1 : (m+n)+l = k+l := f_equal (fun j => j + l) e in
        let e2 : m+(n+l) = k+l := eq_trans (transparent.nat_add_assoc m n l) e1 in
        peval_bvtake_eq m (n + l) t1 e2.

    End WithPevalBvtake.

    Definition peval_bvtake_val {m n} [k] (v : Val (ty.bvec k))
      (e : m + n = k) : Term Σ (ty.bvec m) :=
      term_val (ty.bvec _) (bv.take m (eq_rect_r bv v e)).

    Definition peval_bvtake_relval {m n} [k] (rv : RelVal (ty.bvec k))
      (e : m + n = k) : Term Σ (ty.bvec m) :=
    term_relval (ty.bvec _) (ty.liftUnOp (σ1 := ty.bvec (m + n)) (σ2 := ty.bvec m) (bv.take m) (ty.liftUnOp (σ2 := ty.bvec (m + n)) (fun v : Val (ty.bvec k) => (eq_rect_r bv v e)) rv)).

    Definition peval_bvtake_default m {n} mn (t : Term Σ (ty.bvec mn))
      (e : m + n = mn) : Term Σ (ty.bvec m) :=
      match eq_dec m 0 with
      | left em0 => eq_rect_r (fun l => Term Σ (ty.bvec l))
                      (term_val (ty.bvec 0) bv.nil) em0
      | right _ =>
          match eq_dec 0 n with
          | left e0n =>
              eq_rect_r (fun l => Term Σ (ty.bvec l)) t
                (eq_trans
                   (eq_trans (eq_sym (transparent.nat_add_0_r m))
                      (f_equal (Nat.add m) e0n)) e)
          | right _ => term_bvtake m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e)
          end
      end.

    Fixpoint peval_bvtake_eq m {n} mn (t : Term Σ (ty.bvec mn)) (e : m + n = mn) {struct t} :
      Term Σ (ty.bvec m) :=
      Term_bvec_case (fun (**) n0 _ => m + n = n0 → Term Σ (ty.bvec m))
        (fun (*var*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*val*) k v e => peval_bvtake_val v e)
        (fun (*relval*) k v e => peval_bvtake_relval v e)
        (fun (*bvadd*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvsub*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvmul*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvand*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvor*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvxor*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*shiftr*) _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*shift*) _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvapp*) k l t1 t2 e => peval_bvtake_bvapp peval_bvtake_eq t1 t2 e)
        (fun (*bvcons*) k t1 t2 e => peval_bvtake_bvcons peval_bvtake_eq t1 t2 e)
        (fun (*u_v_s*) _ _ _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvnot*) _ _ _ => peval_bvtake_default _ t e)
        (fun (*negate*) _ _ _ => peval_bvtake_default _ t e)
        (fun (*sext*) _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*zext*) _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*g_s_i*) _ _ _ => peval_bvtake_default _ t e)
        (fun (*truncate*) _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*v_s*) _ _ _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvdrop*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*bvtake*) k l t1 e1 => peval_bvtake_bvtake peval_bvtake_eq t1 e1)
        (fun (*expand*) _ _ _ => peval_bvtake_default _ t e)
        (fun (*coalesce*) _ _ _ _ => peval_bvtake_default _ t e)
        (fun (*mulx*) _ _ _ _ => peval_bvtake_default _ t e)
        t e.

    Definition peval_bvtake m {n} (t : Term Σ (ty.bvec (m + n))) :
      Term Σ (ty.bvec m) := peval_bvtake_eq m t eq_refl.

    Definition peval_update_vector_subrange {n} s l {p : IsTrue (s + l <=? n)%nat} :
      Term Σ (ty.bvec n) -> Term Σ (ty.bvec l) -> Term Σ (ty.bvec n) :=
      match bv.leview (s + l) n with
      | bv.is_le k =>
          fun tslk tl =>
            peval_bvapp
              (peval_bvapp (peval_bvtake s (peval_bvtake (s+l) tslk)) tl)
              (peval_bvdrop (s+l) tslk)
      end.
    #[global] Arguments peval_update_vector_subrange {n} s l {p}.

    Equations(noeqns) peval_binop' {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | op | term_val _ v1 | term_val _ v2 := term_val σ (bop.eval op v1 v2);
    | op | t1            | t2            := term_binop op t1 t2.

    (* ---- expand is a homomorphism ------------------------------------------
       `uop.expand` maps the boolean algebra on `bool` TERMS to the bitwise
       algebra on 0/~0 masks:

         expand b & expand b'  =  expand (b && b')
         expand b | expand b'  =  expand (b || b')
         bvnot (expand b)      =  expand (not b)          [see peval_bvnot]

       Collapsing mask-only subexpressions this way pushes the logic down into
       the bool layer, where peval_and / peval_or / peval_not (which already
       does De Morgan and negates relops via term_relop_neg) can work on it,
       and leaves standing only the genuine mask-times-DATA `bvand` — the one
       that cannot collapse and shouldn't.

       Grafted as NARROW dispatches that fall through to peval_binop', rather
       than by enabling peval_bvand / peval_bvor: those are commented out of
       peval_binop below because their soundness lemmas were never proved, and
       this keeps the bill to just the new rules.

       The bvxor twin needs no new bool operation, contrary to an earlier note
       here: RelOp is sigma-POLYMORPHIC, so `bop.relop bop.neq` instantiated at
       sigma = ty.bool IS xor (`neq true true = false`, `neq true false =
       true`).  Its result is a positive relop, which is exactly the canonical
       form wanted — where encoding xorb through and/or/not would have cost 5-6
       nodes against a 3-node input.  (`bop.eq` at bool is the xnor twin, if a
       use ever appears.) *)

    Definition peval_bvand_mask {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
      match bvmask_try_expand t1 , bvmask_try_expand t2 with
      | Some b1 , Some b2 => term_unop uop.expand (peval_and b1 b2)
      | _ , _             => peval_binop' bop.bvand t1 t2
      end.

    (* ---- coalesce recognition ----------------------------------------------
       The sticky accumulator `c |= -EQ0(c) & CMP(...)` of a constant-time
       lexicographic compare (BearSSL check_scalar, ec_p256_m62.c:1610).  clang
       compiles the step to `snez; addi -1; and; or`, which the mask rules above
       have already reduced to

         bvor (bvand (expand (C ≤ᵘ 0)) S) C

       — one mask node over one POSITIVE relop (see
       selftest_bvnot_expand_negates_relop for why the relop comes out as
       `C ≤ᵘ 0` rather than `¬(0 <ᵘ C)`).

       WHY THIS RULE EXISTS AT ALL.  `C` occurs TWICE above, so an accumulator
       fed by this step satisfies count(k+1) = 2·count(k) + 1 and the raw term
       doubles every trip: 2^N − 1 nodes, measured 1 → 3 `expand` nodes and
       9k → 44k printed chars from one unrolled copy to two
       (Example/ZZCsUnroll.v).  At P-256's mandated N = 32 that is ~4.3e9 nodes.
       `bop.coalesce C S` mentions `C` ONCE — the zero test lives inside the
       op's eval instead of as a second subterm — so the accumulator becomes a
       chain of N nodes.  Term SHARING cannot substitute for this: peval and
       Term_eqb still traverse the structure, so what is needed is opacity, and
       an op provides it by fiat (PLAN-term-sharing.md).

       Grafted AFTER the rule-3 mask homomorphism, which cannot conflict: rule 3
       needs both operands to be masks, and operand 1 here is a `bvand`, so
       bvmask_try_expand returns None on it and control reaches this rule. *)

    (* The zero test as peval canonicalizes it.  Built at the OUTER width and
       compared with the homogeneous Term_eqb at ty.bool, rather than
       destructuring the relop and transporting its operand: the inner relop's
       width is not forced by typing to equal n, and comparing whole bool terms
       makes any width mismatch simply return false instead of needing an
       eq_rect. *)
    Definition bvzero_pred {n} (c : Term Σ (ty.bvec n)) : Term Σ ty.bool :=
      term_binop (bop.relop bop.bvule) c (term_val (ty.bvec n) bv.zero).

    (* Is `t` the mask `expand (c ≤ᵘ 0)`, i.e. -[c = 0]? *)
    Definition bvmask_is_zero_test {n} (c t : Term Σ (ty.bvec n)) : bool :=
      match bvmask_try_expand t with
      | Some b => Term_eqb b (bvzero_pred c)
      | None   => false
      end.

    (* Split a `bvand`.  A separate one-clause matcher (rather than pattern
       matching inline inside bvcoalesce_arg) so that its inversion lemma
       returns the EQUATION linking t to the split — the `generalize`-style
       matcher that discards it leaves the Some branch unprovable as posed
       (PLAN-ksl64.md §2). *)
    Equations bvand_split {n} (t : Term Σ (ty.bvec n)) :
      option (Term Σ (ty.bvec n) * Term Σ (ty.bvec n)) :=
    | term_binop bop.bvand t1 t2 => Some (t1, t2) ;
    | _ => None.

    (* Recognize `bvand MASK S` for the given c's zero-test mask and hand back
       S.  BOTH operand orders: clang emits `and a1,a2,a1` = `bvand MASK S`, and
       nothing in peval normalizes bvand's commutative arguments, so a compiler
       emitting the other order must still be caught. *)
    Definition bvcoalesce_arg {n} (c t : Term Σ (ty.bvec n)) :
      option (Term Σ (ty.bvec n)) :=
      match bvand_split t with
      | Some (u1, u2) =>
          if bvmask_is_zero_test c u1 then Some u2
          else if bvmask_is_zero_test c u2 then Some u1
               else None
      | None => None
      end.

    (* `bvor t1 t2` is a coalesce step?  Try both outer orders too. *)
    Definition bvcoalesce_try {n} (t1 t2 : Term Σ (ty.bvec n)) :
      option (Term Σ (ty.bvec n)) :=
      match bvcoalesce_arg t2 t1 with
      | Some s => Some (term_binop bop.coalesce t2 s)
      | None   =>
          match bvcoalesce_arg t1 t2 with
          | Some s => Some (term_binop bop.coalesce t1 s)
          | None   => None
          end
      end.

    Definition peval_bvor_coalesce {n} (t1 t2 : Term Σ (ty.bvec n)) :
      Term Σ (ty.bvec n) :=
      match bvcoalesce_try t1 t2 with
      | Some t => t
      | None   => peval_binop' bop.bvor t1 t2
      end.

    (* ---- mulx recognition ---------------------------------------------
       H's GF(2) "multiply by x" step (GHASH-style key schedule, see
       Example/KeyScheduleLoop.v): `H := (H >> 1) ^ (H&1 ? R : 0)`, which the
       real compiled body leaves (after clang's bit-trick for the mask) as

         bvxor (shiftr H one) (bvand (negate (bvand H one)) R)

       -- `uop.expand`'s own recognizer (bvmask_indicator, above) explicitly
       stops at widened COMPARISON bits and flags this raw arithmetic
       `-(Z&1)` shape as its own not-yet-covered case, so this is matched
       directly rather than through bvmask_try_expand.  `H` occurs TWICE
       (once in the shift, once inside the mask), so an accumulator built
       from this doubles every trip (measured genuinely O(2^n),
       Example/ZZTermSim.v, diagnostics/key-schedule-loop2-cost-drivers.md)
       -- same mechanism bop.coalesce already fixes for check_scalar's `c`,
       which this cannot reach: mulx's outer op is XOR over a SHIFT and an
       AND, not coalesce's OR over an AND and a plain operand. *)

    (* Recognize `shiftr h s` where s's own value is literally 1
       (width-independent, exactly like bvmask_indicator's zero test).
       Hands back h. *)
    Equations bvmulx_shiftr1 {n} (t : Term Σ (ty.bvec n)) : option (Term Σ (ty.bvec n)) :=
    | term_binop bop.shiftr h (term_val _ s) => if N.eqb (bv.bin s) 1 then Some h else None ;
    | _ => None.

    (* Recognize `negate (bvand h (val v))`, v's value literally 1 -- H's
       own bit-0 test in the raw, un-collapsed arithmetic form.  Hands back
       h.

       SECOND clause: the REAL compiled shape (Example/ZZMulxDump.v, dumped
       2026-08-13, from key_schedule_loop2's actual masking prefix) is NOT
       this simple 2-node form -- clang's sign-extraction bit-trick is

         ones + shiftr(land(ones + bvand(h,1), bvxor(bvand(h,1), ones)), shamt)

       (shamt's value = n-1), six nodes with `h` referenced twice already
       INSIDE the mask alone. bv.mulx_realmask_sound (Bitvector.v) proves
       this collapses to the SAME `if bit0(h)=0 then zero else ones n`
       predicate the simple clause's identity (negate_land_bit1_mask) does
       -- so both clauses hand back the same `h`, and bvmulx_mask_arg_inv
       below closes both against their own bv identity. *)
    Equations bvmulx_mask_arg {n} (t : Term Σ (ty.bvec n)) : option (Term Σ (ty.bvec n)) :=
    | term_unop uop.negate (term_binop bop.bvand h (term_val _ v)) =>
        if N.eqb (bv.bin v) 1 then Some h else None ;
    | term_binop bop.bvadd (term_val _ o1)
        (term_binop bop.shiftr
           (term_binop bop.bvand
              (term_binop bop.bvadd (term_val _ o2) (term_binop bop.bvand h (term_val _ v1)))
              (term_binop bop.bvxor (term_binop bop.bvand h' (term_val _ v2)) (term_val _ o3)))
           (term_val _ sh)) =>
        if bv.eqb o1 (bv.ones n) && bv.eqb o2 (bv.ones n) && bv.eqb o3 (bv.ones n)
           && N.eqb (bv.bin v1) 1 && N.eqb (bv.bin v2) 1 && Term_eqb h h'
           && (match n with 0%nat => false | S n0 => N.eqb (bv.bin sh) (N.of_nat n0) end)
        then Some h else None ;
    | _ => None.

    (* `bvand mask r` or `bvand r mask` where mask tests the SAME h --
       same same-operand discipline as bvcoalesce_arg. *)
    Definition bvmulx_arg {n} (h t : Term Σ (ty.bvec n)) : option (Term Σ (ty.bvec n)) :=
      match bvand_split t with
      | Some (u1, u2) =>
          match bvmulx_mask_arg u1 with
          | Some h' => if Term_eqb h h' then Some u2 else None
          | None =>
              match bvmulx_mask_arg u2 with
              | Some h' => if Term_eqb h h' then Some u1 else None
              | None => None
              end
          end
      | None => None
      end.

    (* `bvxor t1 t2` is a mulx step?  Try both outer orders too. *)
    Definition bvmulx_try {n} (t1 t2 : Term Σ (ty.bvec n)) : option (Term Σ (ty.bvec n)) :=
      match bvmulx_shiftr1 t1 with
      | Some h =>
          match bvmulx_arg h t2 with
          | Some r => Some (term_binop bop.mulx h r)
          | None   => None
          end
      | None =>
          match bvmulx_shiftr1 t2 with
          | Some h =>
              match bvmulx_arg h t1 with
              | Some r => Some (term_binop bop.mulx h r)
              | None   => None
              end
          | None => None
          end
      end.

    Definition peval_bvxor_mulx {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
      match bvmulx_try t1 t2 with
      | Some t => t
      | None   => peval_binop' bop.bvxor t1 t2
      end.

    Definition peval_bvor_mask {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
      match bvmask_try_expand t1 , bvmask_try_expand t2 with
      | Some b1 , Some b2 => term_unop uop.expand (peval_or b1 b2)
      | _ , _             => peval_bvor_coalesce t1 t2
      end.

    Definition peval_bvxor_mask {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
      match bvmask_try_expand t1 , bvmask_try_expand t2 with
      | Some b1 , Some b2 =>
          term_unop uop.expand (term_binop (bop.relop bop.neq) b1 b2)
      | _ , _             => peval_bvxor_mulx t1 t2
      end.

    (* SELF-TESTS (see the block above peval_bvadd for why these exist).  These
       three rules have no customer in any current example — nothing in the
       corpus composes two masks — so without them the patterns are entirely
       unexercised by the build. *)
    Lemma selftest_bvand_mask_fires {n} (b1 b2 : Term Σ ty.bool) :
      peval_bvand_mask (term_unop (uop.expand (n := n)) b1) (term_unop uop.expand b2)
      = term_unop uop.expand (peval_and b1 b2).
    Proof. reflexivity. Qed.

    Lemma selftest_bvor_mask_fires {n} (b1 b2 : Term Σ ty.bool) :
      peval_bvor_mask (term_unop (uop.expand (n := n)) b1) (term_unop uop.expand b2)
      = term_unop uop.expand (peval_or b1 b2).
    Proof. reflexivity. Qed.

    (* bop.relop bop.neq at sigma = ty.bool is xor; a positive relop, not an
       and/or/not encoding. *)
    Lemma selftest_bvxor_mask_fires {n} (b1 b2 : Term Σ ty.bool) :
      peval_bvxor_mask (term_unop (uop.expand (n := n)) b1) (term_unop uop.expand b2)
      = term_unop uop.expand (term_binop (bop.relop bop.neq) b1 b2).
    Proof. reflexivity. Qed.

    (* INERT on non-masks: constant folding still reaches peval_binop'. *)
    Lemma selftest_bvand_mask_inert {n} (v1 v2 : Val (ty.bvec n)) :
      peval_bvand_mask (term_val (ty.bvec n) v1) (term_val (ty.bvec n) v2)
      = term_val (ty.bvec n) (bv.land v1 v2).
    Proof. reflexivity. Qed.

    Lemma selftest_bvor_mask_inert {n} (v1 v2 : Val (ty.bvec n)) :
      peval_bvor_mask (term_val (ty.bvec n) v1) (term_val (ty.bvec n) v2)
      = term_val (ty.bvec n) (bv.lor v1 v2).
    Proof. reflexivity. Qed.

    Lemma selftest_bvxor_mask_inert {n} (v1 v2 : Val (ty.bvec n)) :
      peval_bvxor_mask (term_val (ty.bvec n) v1) (term_val (ty.bvec n) v2)
      = term_val (ty.bvec n) (bv.lxor v1 v2).
    Proof. reflexivity. Qed.

    (* Only ONE side being a mask must not fire. *)
    Lemma selftest_bvand_mask_needs_both {n} (b : Term Σ ty.bool) (v : Val (ty.bvec n)) :
      peval_bvand_mask (term_unop (uop.expand (n := n)) b) (term_val (ty.bvec n) v)
      = term_binop bop.bvand (term_unop uop.expand b) (term_val (ty.bvec n) v).
    Proof. reflexivity. Qed.

    (* ---- SELF-TESTS for the coalesce recognizer ---------------------------
       Both operands are CONCRETE here, unavoidably: the recognizer decides
       "same C on both sides" with Term_eqb and asks bvmask_try_expand about the
       other bvand operand, and neither can reduce on an opaque term variable.
       So these are conversion tests of the PATTERN only — that the rule fires
       on a real term_var-headed VC is what Example/ZZCsRun1.v measures.
       (`selftest_bvor_mask_fires` above doubles as the pin that the rule-3 mask
       homomorphism still wins when BOTH operands are masks: the coalesce
       attempt is grafted after it, not in front of it.) *)
    #[local] Notation zzC := (term_val (ty.bvec 32) (bv.ones 32)).
    #[local] Notation zzS := (term_val (ty.bvec 32) bv.one).
    #[local] Notation zzMask :=
      (term_unop uop.expand
         (term_binop (bop.relop bop.bvule) zzC (term_val (ty.bvec 32) bv.zero))).

    (* FIRES on the shape the executor actually dumps for clang's
       `snez; addi -1; and; or` (PLAN-coalesce.md §3): the mask is ONE node over
       ONE POSITIVE relop, `C ≤ᵘ 0`, because peval_bvnot negates the relop
       rather than leaving a bvnot — see selftest_bvnot_expand_negates_relop. *)
    Lemma selftest_coalesce_fires :
      peval_bvor_mask (term_binop bop.bvand zzMask zzS) zzC
      = term_binop bop.coalesce zzC zzS.
    Proof. reflexivity. Qed.

    (* All three commuted spellings, since bvand/bvor are commutative and
       nothing upstream normalizes their operand order. *)
    Lemma selftest_coalesce_fires_andr :
      peval_bvor_mask (term_binop bop.bvand zzS zzMask) zzC
      = term_binop bop.coalesce zzC zzS.
    Proof. reflexivity. Qed.

    Lemma selftest_coalesce_fires_orl :
      peval_bvor_mask zzC (term_binop bop.bvand zzMask zzS)
      = term_binop bop.coalesce zzC zzS.
    Proof. reflexivity. Qed.

    Lemma selftest_coalesce_fires_orl_andr :
      peval_bvor_mask zzC (term_binop bop.bvand zzS zzMask)
      = term_binop bop.coalesce zzC zzS.
    Proof. reflexivity. Qed.

    (* INERT when the mask tests a DIFFERENT term than the one being OR'd in.
       This is the guard that makes the rule sound rather than merely plausible:
       `c | (m & s)` is NOT a select in general — with c = 1, m = ~0, s = 0 the
       OR gives 1 while coalesce would give 0.  It is only equal because the
       mask is derived from c itself. *)
    Lemma selftest_coalesce_needs_same_operand :
      peval_bvor_mask (term_binop bop.bvand zzMask zzS) (term_val (ty.bvec 32) bv.zero)
      = term_binop bop.bvor (term_binop bop.bvand zzMask zzS)
          (term_val (ty.bvec 32) bv.zero).
    Proof. reflexivity. Qed.

    (* INERT when the predicate is not the zero test — here `C ≤ᵘ C`. *)
    Lemma selftest_coalesce_needs_zero_test :
      peval_bvor_mask
        (term_binop bop.bvand
           (term_unop uop.expand (term_binop (bop.relop bop.bvule) zzC zzC)) zzS)
        zzC
      = term_binop bop.bvor
          (term_binop bop.bvand
             (term_unop uop.expand (term_binop (bop.relop bop.bvule) zzC zzC)) zzS)
          zzC.
    Proof. reflexivity. Qed.

    (* ---- SELF-TESTS for the mulx recognizer -------------------------------
       FIRES on the raw shape a real `andi;xori;addi;and;srli;addi;srli;xor`
       key-schedule step reduces to, given concrete operands (Term_eqb can't
       reduce on an opaque term_var -- same caveat as the coalesce
       self-tests above; that this reaches a real term_var-headed VC is
       what a genuine key_schedule_loop2 dump would measure, not pinned
       here). *)
    Lemma selftest_mulx_fires :
      peval_bvxor_mulx
        (term_binop bop.shiftr zzC (term_val (ty.bvec 32) bv.one))
        (term_binop bop.bvand
           (term_unop uop.negate (term_binop bop.bvand zzC (term_val (ty.bvec 32) bv.one)))
           zzS)
      = term_binop bop.mulx zzC zzS.
    Proof. reflexivity. Qed.

    (* Commuted outer xor order and commuted inner bvand order both fire too --
       neither the outer bvxor nor the mask's bvand is normalized upstream. *)
    Lemma selftest_mulx_fires_xor_comm :
      peval_bvxor_mulx
        (term_binop bop.bvand
           (term_unop uop.negate (term_binop bop.bvand zzC (term_val (ty.bvec 32) bv.one)))
           zzS)
        (term_binop bop.shiftr zzC (term_val (ty.bvec 32) bv.one))
      = term_binop bop.mulx zzC zzS.
    Proof. reflexivity. Qed.

    (* INERT when the two `bvand h one` occurrences reference DIFFERENT h's --
       the same-operand discipline that makes the rule sound rather than
       merely plausible. *)
    Lemma selftest_mulx_needs_same_operand :
      peval_bvxor_mulx
        (term_binop bop.shiftr zzC (term_val (ty.bvec 32) bv.one))
        (term_binop bop.bvand
           (term_unop uop.negate (term_binop bop.bvand zzS (term_val (ty.bvec 32) bv.one)))
           zzS)
      = term_binop bop.bvxor
          (term_binop bop.shiftr zzC (term_val (ty.bvec 32) bv.one))
          (term_binop bop.bvand
             (term_unop uop.negate (term_binop bop.bvand zzS (term_val (ty.bvec 32) bv.one)))
             zzS).
    Proof. reflexivity. Qed.

    (* ---- REAL-SHAPE self-tests --------------------------------------------
       Everything above tests the SIMPLE `negate (bvand h one)` mask.  A dump
       of the actual executor against the real key_schedule_loop2 instruction
       sequence (Example/ZZMulxDump.v) showed the compiler does NOT emit that:
       it emits a SIX-node sign-extraction idiom referencing `h` THREE times,

         mask := ones + ((ones + (h & 1)) & ((h & 1) ^ ones)) >> 31
         step := (mask & r) ^ (h >> 1)

       which is the whole reason bvmulx_mask_arg has a second clause.  Without
       these two lemmas that clause is entirely unexercised by the build --
       the same gap the coalesce/mask self-tests above exist to close for
       their own rules, and the more important one here, since this is the
       shape the corpus actually contains.

       Note the operand order: the real dump puts the masked-r term FIRST and
       `h >> 1` second, i.e. this exercises bvmulx_try's t2-shift branch,
       whereas selftest_mulx_fires above exercises t1-shift.

       `zzH` is deliberately NOT zzC (= ones 32): the recognizer's guard
       checks o1/o2/o3 against `bv.ones n`, so reusing an all-ones value for
       `h` would let a positional mix-up pass unnoticed. `bv.zero` cannot
       satisfy that guard, so the test discriminates. *)
    #[local] Notation zzH     := (term_val (ty.bvec 32) bv.zero).
    #[local] Notation zzOnes  := (term_val (ty.bvec 32) (bv.ones 32)).
    #[local] Notation zzOne   := (term_val (ty.bvec 32) bv.one).
    #[local] Notation zzSh31  := (term_val (ty.bvec 32) (bv.of_N (N.of_nat 31))).

    #[local] Notation zzRealMask h :=
      (term_binop bop.bvadd zzOnes
         (term_binop bop.shiftr
            (term_binop bop.bvand
               (term_binop bop.bvadd zzOnes (term_binop bop.bvand h zzOne))
               (term_binop bop.bvxor (term_binop bop.bvand h zzOne) zzOnes))
            zzSh31)).

    Lemma selftest_mulx_fires_real_shape :
      peval_bvxor_mulx
        (term_binop bop.bvand (zzRealMask zzH) zzS)
        (term_binop bop.shiftr zzH zzOne)
      = term_binop bop.mulx zzH zzS.
    Proof. reflexivity. Qed.

    (* Same same-operand discipline as the simple shape: the mask's two
       `bvand h one` occurrences must reference the SAME h as the shift. *)
    Lemma selftest_mulx_real_shape_needs_same_operand :
      peval_bvxor_mulx
        (term_binop bop.bvand (zzRealMask zzS) zzS)
        (term_binop bop.shiftr zzH zzOne)
      = term_binop bop.bvxor
          (term_binop bop.bvand (zzRealMask zzS) zzS)
          (term_binop bop.shiftr zzH zzOne).
    Proof. reflexivity. Qed.

    (* DISTRIBUTE a constant-shift over a constant-headed sum:
       (c ⊕ t) << k  ~>  (c << k) ⊕ (t << k).  Unconditional mod 2^m (a left
       shift is a multiplication by 2^k), pure on both sides, so sound over
       secrets.  Together with peval_bvadd's floating clauses it gives an
       array element ONE spelling: `x + ((M - 1) << 2) + 4` and `x + (M << 2)`
       both become `x + (M << 2)` (PLAN-array-invariants, parametric mlen).
       Built through peval_bvadd, so a zero `c << k` vanishes and the new
       constant head can float in the enclosing sum. *)
    (* A left shift by a constant is a multiplication by 2^k: part of the
       canonical ring form.  (Replaces the earlier ad-hoc distribution of
       << over a constant-headed sum.) *)
    Definition peval_shiftl {m n} (t1 : Term Σ (ty.bvec m)) (t2 : Term Σ (ty.bvec n))
      : Term Σ (ty.bvec m) :=
      match term_get_val t2 with
      | Some k => canon_term (term_binop bop.shiftl t1 (term_val (ty.bvec _) k))
      | None => peval_binop' bop.shiftl t1 t2
      end.

    Definition peval_bvsub {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
      canon_term (term_binop bop.bvsub t1 t2).

    (* Self-tests of the canonical form (the neighbour pair, commuted sums,
       x - x, idempotence, the mask shapes) live in CFGVer/Example/ZZBvCore.v:
       inside this functor the terms are abstract, so they cannot compute. *)

    (* List append, right-associated with conses pulled out:
         [] ++ t ~> t,  (x :: t) ++ u ~> x :: (t ++ u),  (a ++ b) ++ u ~> a ++ (b ++ u).
       A value-carrying array's loop invariant `vs = done ++ rest` is
       re-established after one step only if (done ++ [x]) ++ rest' and
       done ++ (x :: rest') meet syntactically (CFGVer `arrv`, PLAN-rsa.md,
       Phase 2).  Same leaves on both sides; two values still fold through
       peval_binop'.  Self-tests over concrete terms are in
       CFGVer/Example/Rsa/RsaSpikeArrv.v (here the terms are abstract). *)
    Equations peval_append {σ} (t1 t2 : Term Σ (ty.list σ)) : Term Σ (ty.list σ) by struct t1 :=
    | term_val _ v, t2 => match v with
                          | nil => t2
                          | _   => peval_binop' bop.append (term_val (ty.list σ) v) t2
                          end
    | term_binop bop.cons x t, t2      => term_binop bop.cons x (peval_append t t2)
    | term_binop bop.append a b, t2    => peval_append a (peval_append b t2)
    | t1, t2                           => term_binop bop.append t1 t2.

    (* TODO: Comment out some stuff because I am too lazy to prove their soundness *)
    Definition peval_binop {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) :
      Term Σ σ1 → Term Σ σ2 → Term Σ σ :=
      match op with
      | bop.append => peval_append
      | bop.and    => peval_and
      | bop.or     => peval_or
      | bop.plus   => peval_plus
      | bop.minus  => peval_minus
      | bop.bvadd  => peval_bvadd
      | bop.bvand  => peval_bvand_mask
      | bop.bvor   => peval_bvor_mask
      | bop.bvxor  => peval_bvxor_mask
      | bop.shiftl => peval_shiftl
      | bop.bvsub  => peval_bvsub
      (* | bop.bvand  => peval_bvand *)
      (* | bop.bvor   => peval_bvor *)
      (* | bop.bvapp  => peval_bvapp *)
      (* | bop.update_vector_subrange s l => peval_update_vector_subrange s l *)
      | op         => peval_binop' op
      end.

    (* Lemma peval_append_sound {σ} (t1 t2 : Term Σ (ty.list σ)) : *)
    (*   peval_append t1 t2 ≡ term_binop bop.append t1 t2. *)
    (* Proof. *)
    (*   destruct t1 using Term_list_case; try constructor. *)
    (*   destruct t2 using Term_list_case; *)
    (*     first [constructor | destruct v; constructor]. *)
    (* Qed. *)

    Lemma term_and_comm (t1 t2 : Term Σ ty.bool) :
      term_and t1 t2 ≡ term_and t2 t1.
    Proof.
      intro ι.
      cbn. destruct inst, inst; cbn;
        rewrite andb_comm.
      auto.
      all: apply f_equal2; rewrite andb_comm; auto.
    Qed.

    Lemma term_or_comm (t1 t2 : Term Σ ty.bool) :
      term_or t1 t2 ≡ term_or t2 t1.
    Proof.
      intro ι.
      cbn. destruct inst, inst; cbn;
        rewrite orb_comm.
      auto.
      all: apply f_equal2; rewrite orb_comm; auto.
    Qed.

    Lemma peval_and_sound (t1 t2 : Term Σ ty.bool) :
      peval_and t1 t2 ≡ term_binop bop.and t1 t2.
    Proof with lsolve.
      depelim t1.
      - depelim t2... apply peval_and_val_sound.
      - cbn. rewrite term_and_comm. apply peval_and_val_sound.
      - depelim t2... apply peval_and_val_sound.
      - depelim t2... apply peval_and_val_sound.
      - depelim t2... apply peval_and_val_sound.
    Qed.

    Lemma peval_or_sound (t1 t2 : Term Σ ty.bool) :
      peval_or t1 t2 ≡ term_binop bop.or t1 t2.
    Proof with lsolve.
      depelim t1.
      - depelim t2...
        apply peval_or_val_sound.
      - rewrite term_or_comm. apply peval_or_val_sound.
      - depelim t2... apply peval_or_val_sound.
      - depelim t2... apply peval_or_val_sound.
      - depelim t2... apply peval_or_val_sound.
    Qed.

    Lemma peval_plus_sound (t1 t2 : Term Σ ty.int) :
      peval_plus t1 t2 ≡ term_binop bop.plus t1 t2.
    Proof. funelim (peval_plus t1 t2); lsolve; intros ι; cbn;
           match goal with
           | |- context[bop.evalRel ?op ?a ?b] =>
               (destruct a; cbn; (apply f_equal; lia) || (apply f_equal2; lia; lia))
                                 ||
                                 (destruct b; cbn; (apply f_equal; lia) || (apply f_equal2; lia; lia))
           end.
    Qed.

    Lemma peval_minus_sound (t1 t2 : Term Σ ty.int) :
      peval_minus t1 t2 ≡ term_binop bop.minus t1 t2.
    Proof. funelim (peval_minus t1 t2); lsolve; intros ι; cbn;
             match goal with
             | |- context[bop.evalRel ?op ?a ?b] =>
                 (destruct a; cbn; (apply f_equal; lia) || (apply f_equal2; lia; lia))
                 ||
                 (destruct b; cbn; (apply f_equal; lia) || (apply f_equal2; lia; lia))
             end.
    Qed.

    (* Inversion for the mask recognizer.  NOTE the shape of this statement:
       it returns the EQUATION linking t to the recognized shape.  The removed
       select_last_k fold got this wrong by using `generalize` on its matcher,
       which discards exactly that equation and leaves the Some-branch
       unprovable as posed (PLAN-ksl64.md §2).  Use `destruct … eqn:` plus this
       lemma, never `generalize`. *)
    Lemma bvmask_indicator_inv {n} (t : Term Σ (ty.bvec n)) (b : Term Σ ty.bool) :
      bvmask_indicator t = Some b ->
      exists m (pf : IsTrue (S m <=? n)) (w : Val (ty.bvec m)),
        bv.bin w = 0%N /\
        t = term_unop (uop.zext (m := S m) (n := n) (p := pf))
              (term_binop bop.bvcons b (term_val (ty.bvec m) w)).
    Proof.
      funelim (bvmask_indicator t); intros Heq; try discriminate.
      destruct (N.eqb (bv.bin w) 0%N) eqn:Hw; [|discriminate].
      injection Heq as <-. apply N.eqb_eq in Hw.
      do 3 eexists. split; [eassumption|reflexivity].
    Qed.

    Lemma peval_bvadd_val_default_sound {n} (t : Term Σ (ty.bvec n)) (v : Val (ty.bvec n)) :
      peval_bvadd_val_default t v ≡ term_binop bop.bvadd t (term_val (ty.bvec n) v).
    Proof.
      unfold peval_bvadd_val_default. intros ι; cbn.
      match goal with
      | |- context[bop.evalRel bop.bvadd _ ?r] =>
          destruct r; cbn; (apply f_equal; now apply bv.add_comm)
                           || (apply f_equal2; now apply bv.add_comm)
      end.
    Qed.

    Lemma peval_bvadd_mask_sound {n} (t : Term Σ (ty.bvec n)) (v : Val (ty.bvec n)) :
      peval_bvadd_mask t v ≡ term_binop bop.bvadd t (term_val (ty.bvec n) v).
    Proof.
      unfold peval_bvadd_mask.
      destruct (eq_dec v (bv.ones n)) as [->|]; [|apply peval_bvadd_val_default_sound].
      destruct (bvmask_indicator t) as [b|] eqn:Hb; [|apply peval_bvadd_val_default_sound].
      apply bvmask_indicator_inv in Hb as (m & pf & w & Hw & ->).
      intros ι; cbn.
      (* [b] - 1 = ~(b ? ~0 : 0) = (~b ? ~0 : 0): add_zext_cons_ones then
         not_if_ones, both in Bitvector.v's mask-algebra block. *)
      destruct (inst b ι); cbn;
        f_equal; rewrite bv.add_zext_cons_ones by assumption;
        now rewrite bv.not_if_ones.
    Qed.

    (* The RelVal shapes the constant-floating clauses of peval_bvadd and
       peval_shiftl leave after `cbn`: plain bv identities lifted through
       liftBinOp, no two-world case split needed beyond the destruct. *)
    Lemma bvadd_float {n} (a c b : bv n) : bv.add a (bv.add c b) = bv.add c (bv.add a b).
    Proof. rewrite !bv.add_assoc. f_equal. apply bv.add_comm. Qed.

    Lemma rv_bvadd_assoc3 {n} (v : bv n) (A T : RelVal (ty.bvec n)) :
      bop.evalRel bop.bvadd (SyncVal v) (bop.evalRel bop.bvadd A T)
      = bop.evalRel bop.bvadd (bop.evalRel bop.bvadd (SyncVal v) A) T.
    Proof. destruct A, T; cbn; f_equal; apply bv.add_assoc. Qed.

    Lemma rv_bvadd_float {n} (v : bv n) (T B : RelVal (ty.bvec n)) :
      bop.evalRel bop.bvadd (SyncVal v) (bop.evalRel bop.bvadd T B)
      = bop.evalRel bop.bvadd T (bop.evalRel bop.bvadd (SyncVal v) B).
    Proof. destruct T, B; cbn; f_equal; symmetry; apply bvadd_float. Qed.

    Lemma rv_bvadd_4 {n} (v1 v2 : bv n) (A B : RelVal (ty.bvec n)) :
      bop.evalRel bop.bvadd (SyncVal (bv.add v1 v2)) (bop.evalRel bop.bvadd A B)
      = bop.evalRel bop.bvadd (bop.evalRel bop.bvadd (SyncVal v1) A)
          (bop.evalRel bop.bvadd (SyncVal v2) B).
    Proof.
      destruct A, B; cbn; f_equal; rewrite <- !bv.add_assoc; f_equal;
        rewrite (bvadd_float _ v2); reflexivity.
    Qed.

    Lemma shiftl_add_distr {m n} (c t : bv m) (k : bv n) :
      bv.shiftl (bv.add c t) k = bv.add (bv.shiftl c k) (bv.shiftl t k).
    Proof.
      apply bv.unsigned_inj. unfold bv.shiftl.
      rewrite (bv.unsigned_add (bv.of_Z _) (bv.of_Z _)).
      rewrite !bv.unsigned_of_Z. rewrite (bv.unsigned_add c t).
      unfold bv.truncz.
      assert (Hk : (0 <= bv.unsigned k)%Z) by (unfold bv.unsigned; lia).
      rewrite !Z.shiftl_mul_pow2 by exact Hk.
      set (P := (2 ^ Z.of_nat m)%Z).
      assert (HP : P <> 0%Z) by (unfold P; apply Z.pow_nonzero; lia).
      rewrite Z.mul_mod_idemp_l by exact HP.
      rewrite <- Z.add_mod by exact HP. f_equal. apply Z.mul_add_distr_r.
    Qed.

    Lemma rv_shiftl_distr {m n} (v : bv m) (k : bv n) (T : RelVal (ty.bvec m)) :
      bop.evalRel bop.bvadd (SyncVal (bv.shiftl v k)) (bop.evalRel bop.shiftl T (SyncVal k))
      = bop.evalRel bop.shiftl (bop.evalRel bop.bvadd (SyncVal v) T) (SyncVal k).
    Proof. destruct T; cbn; f_equal; symmetry; apply shiftl_add_distr. Qed.

    Lemma peval_bvadd_fold_sound {n} (v : Val (ty.bvec n)) (t : Term Σ (ty.bvec n)) :
      peval_bvadd_fold v t ≡ term_binop bop.bvadd (term_val (ty.bvec n) v) t.
    Proof.
      unfold peval_bvadd_fold. destruct (eq_dec v bv.zero) as [->|]; [|reflexivity].
      intros ι; cbn. destruct (inst t ι); cbn; f_equal; symmetry; apply bv.add_zero_l.
    Qed.

    Lemma bvadd_head_spec {n} (t : Term Σ (ty.bvec n)) v t' :
      bvadd_head t = Some (v, t') -> t = term_binop bop.bvadd (term_val _ v) t'.
    Proof.
      funelim (bvadd_head t); intros Heq; try discriminate.
      inversion Heq; subst; auto.
    Qed.

    Lemma peval_bvadd_float_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvadd_float t1 t2 ≡ term_binop bop.bvadd t1 t2.
    Proof.
      unfold peval_bvadd_float.
      destruct (bvadd_head t1) as [[v1 a]|] eqn:H1;
        destruct (bvadd_head t2) as [[v2 b]|] eqn:H2;
        try (apply bvadd_head_spec in H1; subst t1);
        try (apply bvadd_head_spec in H2; subst t2).
      - etransitivity; [apply peval_bvadd_fold_sound|]. intros ι; cbn. apply rv_bvadd_4.
      - intros ι; cbn. apply rv_bvadd_assoc3.
      - intros ι; cbn. apply rv_bvadd_float.
      - reflexivity.
    Qed.

    Lemma canon_term_equiv {n} (t : Term Σ (ty.bvec n)) : canon_term t ≡ t.
    Proof. intros ι. apply canon_term_sound. Qed.

    Lemma peval_bvadd_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvadd t1 t2 ≡ term_binop bop.bvadd t1 t2.
    Proof.
      funelim (peval_bvadd t1 t2); try apply peval_bvadd_mask_sound;
        try apply canon_term_equiv;
        (* the two folding clauses: strip peval_bvadd_fold, leaving the goal
           the script below was written for *)
        try (etransitivity; [apply peval_bvadd_fold_sound|]);
        lsolve; intros ι; cbn; auto.
      (* New constant-folding clauses: goal is
         evalRel bvadd (SyncVal (c1+c2)) r = evalRel bvadd (SyncVal c1) (evalRel bvadd (SyncVal c2) r)
         (or the mirrored (c1 ⊕ t) ⊕ c2 form); close by bv.add associativity/commutativity
         after splitting the relational value r. *)
      all: try (match goal with
          | |- context[bop.evalRel bop.bvadd (SyncVal (bv.add _ _)) ?r] =>
              destruct r; cbn; f_equal; rewrite <- !bv.add_assoc;
              (reflexivity || (f_equal; apply bv.add_comm))
          end).
      all: match goal with
           | |- context[bop.evalRel ?op ?a ?b] =>
               (destruct a; cbn; (apply f_equal; first
                                                   [ symmetry; apply bv.add_zero_l
                                                   | symmetry; apply bv.add_zero_r
                                                   | now apply bv.add_comm
                                 ]) || (apply f_equal2; first
                                                          [ symmetry; apply bv.add_zero_l
                                                          | symmetry; apply bv.add_zero_r
                                                          | now apply bv.add_comm
               ]))
               ||
               (destruct b; cbn; (apply f_equal; first
                                                   [ symmetry; apply bv.add_zero_l
                                                   | symmetry; apply bv.add_zero_r
                                                   | now apply bv.add_comm
                                 ]) || (apply f_equal2; first
                                                          [ symmetry; apply bv.add_zero_l
                                                          | symmetry; apply bv.add_zero_r
                                                          | now apply bv.add_comm
               ]))
           end.
        (* first *)
        (*   [ symmetry; apply bv.add_zero_l *)
        (*   | symmetry; apply bv.add_zero_r *)
        (*   | now apply bv.add_comm *)
        (*   ]. *)
    Qed.

    (* Lemma peval_bvand_val_default_sound {n} (t : Term Σ (ty.bvec n)) *)
    (*   (v : Val (ty.bvec n)) : *)
    (*   peval_bvand_val_default t v ≡ *)
    (*   term_binop bop.bvand t (term_val (ty.bvec n) v). *)
    (* Proof. *)
    (*   unfold peval_bvand_val_default. *)
    (*   destruct (eq_dec bv.zero v). *)
    (*   { subst. intros ι; cbn. now rewrite bv.land_zero_r. } *)
    (*   destruct (eq_dec (bv.ones n) v). *)
    (*   { subst. intros ι; cbn. now rewrite bv.land_ones_r. } *)
    (*   { reflexivity. } *)
    (* Qed. *)

    (* Hint Resolve peval_bvand_val_default_sound : core. *)

    (* Fixpoint peval_bvand_val_sound {n} (t : Term Σ (ty.bvec n)) *)
    (*   (v : Val (ty.bvec n)) {struct t} : *)
    (*   peval_bvand_val t v ≡ term_binop bop.bvand t (term_val (ty.bvec n) v). *)
    (* Proof. *)
    (*   destruct n, t using Term_bvec_case; cbn - [bv.cons]; lsolve. *)
    (*   - unfold peval_bvand_bvapp_val. destruct bv.appView. *)
    (*     rewrite !peval_bvand_val_sound. *)
    (*     intros ι. cbn. now rewrite bv.land_app. *)
    (*   - unfold peval_bvand_bvcons_val. destruct bv.view. *)
    (*     rewrite peval_and_val_sound, peval_bvand_val_sound. *)
    (*     intros ι. cbn - [bv.cons]. now rewrite bv.land_cons. *)
    (* Qed. *)

    (* Lemma peval_bvand_sound {n} (t1 t2 : Term Σ (ty.bvec n)) : *)
    (*   peval_bvand t1 t2 ≡ term_binop bop.bvand t1 t2. *)
    (* Proof. *)
    (*   funelim (peval_bvand t1 t2); lsolve. *)
    (*   - unfold peval_bvand_bvapp_val. destruct bv.appView. *)
    (*     rewrite !peval_bvand_val_sound. *)
    (*     intros ι. cbn. rewrite bv.land_app. *)
    (*     f_equal; now rewrite bv.land_comm. *)
    (*   - unfold peval_bvand_bvcons_val. destruct bv.view. *)
    (*     rewrite peval_and_val_sound, peval_bvand_val_sound. *)
    (*     intros ι. cbn - [bv.cons]. rewrite bv.land_cons. *)
    (*     f_equal. now rewrite andb_comm. *)
    (*     now rewrite bv.land_comm. *)
    (*   - unfold peval_bvand_bvapp_val. destruct bv.appView. *)
    (*     rewrite !peval_bvand_val_sound. *)
    (*     intros ι. cbn. now rewrite bv.land_app. *)
    (*   - unfold peval_bvand_bvcons_val. destruct bv.view. *)
    (*     rewrite peval_and_val_sound, peval_bvand_val_sound. *)
    (*     intros ι. cbn - [bv.cons]. now rewrite bv.land_cons. *)
    (* Qed. *)

    (* Lemma peval_bvor_val_default_sound {n} (t : Term Σ (ty.bvec n)) *)
    (*   (v : Val (ty.bvec n)) : *)
    (*   peval_bvor_val_default t v ≡ *)
    (*   term_binop bop.bvor t (term_val (ty.bvec n) v). *)
    (* Proof. *)
    (*   unfold peval_bvor_val_default. *)
    (*   destruct (eq_dec (bv.ones n) v). *)
    (*   { subst. intros ι; cbn. now rewrite bv.lor_ones_r. } *)
    (*   destruct (eq_dec bv.zero v). *)
    (*   { subst. intros ι; cbn. now rewrite bv.lor_zero_r. } *)
    (*   { reflexivity. } *)
    (* Qed. *)

    (* Hint Resolve peval_bvor_val_default_sound : core. *)

    (* Fixpoint peval_bvor_val_sound {n} (t : Term Σ (ty.bvec n)) *)
    (*   (v : Val (ty.bvec n)) {struct t} : *)
    (*   peval_bvor_val t v ≡ term_binop bop.bvor t (term_val (ty.bvec n) v). *)
    (* Proof. *)
    (*   destruct n, t using Term_bvec_case; cbn - [bv.cons]; lsolve. *)
    (*   - unfold peval_bvor_bvapp_val. destruct bv.appView. *)
    (*     rewrite !peval_bvor_val_sound. *)
    (*     intros ι. cbn. now rewrite bv.lor_app. *)
    (*   - unfold peval_bvor_bvcons_val. destruct bv.view. *)
    (*     rewrite peval_or_val_sound, peval_bvor_val_sound. *)
    (*     intros ι. cbn - [bv.cons]. now rewrite bv.lor_cons. *)
    (* Qed. *)

    (* Lemma peval_bvor_sound {n} (t1 t2 : Term Σ (ty.bvec n)) : *)
    (*   peval_bvor t1 t2 ≡ term_binop bop.bvor t1 t2. *)
    (* Proof. *)
    (*   funelim (peval_bvor t1 t2); lsolve. *)
    (*   - unfold peval_bvor_bvapp_val. destruct bv.appView. *)
    (*     rewrite !peval_bvor_val_sound. *)
    (*     intros ι. cbn. rewrite bv.lor_app. *)
    (*     f_equal; now rewrite bv.lor_comm. *)
    (*   - unfold peval_bvor_bvcons_val. destruct bv.view. *)
    (*     rewrite peval_or_val_sound, peval_bvor_val_sound. *)
    (*     intros ι. cbn - [bv.cons]. rewrite bv.lor_cons. *)
    (*     f_equal. now rewrite orb_comm. *)
    (*     now rewrite bv.lor_comm. *)
    (*   - unfold peval_bvor_bvapp_val. destruct bv.appView. *)
    (*     rewrite !peval_bvor_val_sound. *)
    (*     intros ι. cbn. now rewrite bv.lor_app. *)
    (*   - unfold peval_bvor_bvcons_val. destruct bv.view. *)
    (*     rewrite peval_or_val_sound, peval_bvor_val_sound. *)
    (*     intros ι. cbn - [bv.cons]. now rewrite bv.lor_cons. *)
    (* Qed. *)

    (* Lemma peval_bvapp_val_r_sound [m n] (t1 : Term Σ (ty.bvec m)) *)
    (*   (v : Val (ty.bvec n)) : *)
    (*   peval_bvapp_val_r t1 v ≡ term_bvapp t1 (term_val (ty.bvec n) v). *)
    (* Proof. *)
    (*   unfold peval_bvapp_val_r. destruct eq_dec. *)
    (*   - intros ι. cbn. subst. rewrite eq_trans_refl_l. *)
    (*     rewrite (inst_eq_rect_indexed_r *)
    (*                (instTA := fun l => @inst_term (ty.bvec l))). *)
    (*     destruct (bv.view v). now rewrite bv.app_nil_r. *)
    (*   - reflexivity. *)
    (* Qed. *)

    (* #[local] Hint Resolve peval_bvapp_val_r_sound : core. *)

    (* Lemma peval_bvapp_sound {m n} (t1 : Term Σ (ty.bvec m)) (t2 : Term Σ (ty.bvec n)) : *)
    (*   peval_bvapp t1 t2 ≡ term_bvapp t1 t2. *)
    (* Proof. *)
    (*   funelim (peval_bvapp t1 t2); lsolve; *)
    (*     try now rewrite peval_bvapp_val_r_sound. *)
    (*   - try clear Heqcall. (* equations >= 1.3.1 *) *)
    (*     intros ι. cbn. rewrite bv.app_app. *)
    (*     now destruct transparent.nat_add_assoc. *)
    (* Qed. *)

    (* Lemma peval_bvdrop_default_sound {m n mn} (t : Term Σ (ty.bvec mn)) *)
    (*   (e : m + n = mn) : *)
    (*   peval_bvdrop_default m t e ≡ *)
    (*   term_bvdrop m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e). *)
    (* Proof. *)
    (*   unfold peval_bvdrop_default. *)
    (*   destruct eq_dec. *)
    (*    { now subst. } *)
    (*   destruct eq_dec. *)
    (*   { subst; intros ι; cbn - [Val]. *)
    (*     now destruct (bv.view (bv.drop m (inst (Inst := inst_term) t ι))). } *)
    (*   reflexivity. *)
    (* Qed. *)

    (* #[local] Hint Resolve peval_bvdrop_default_sound : core. *)

    (* Lemma peval_bvdrop_eq_sound [mn : nat] (t : Term Σ (ty.bvec mn)) : *)
    (*   ∀ m n (e : m + n = mn), *)
    (*     peval_bvdrop_eq m t e ≡ *)
    (*     term_bvdrop m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e). *)
    (* Proof. *)
    (*   induction mn , t using Term_bvec_rect; cbn - [Val]; intros m0 n0 e; auto. *)
    (*   - (*val*) *)
    (*     now subst. *)
    (*   - (*bvapp*) *)
    (*     unfold peval_bvdrop_bvapp. destruct nat_compare. *)
    (*     + pose proof (transparent.nat_add_cancel_l _ _ _ e). subst. *)
    (*       destruct (uip eq_refl (transparent.nat_add_cancel_l n n n1 e)). *)
    (*       destruct (uip eq_refl e); cbn. *)
    (*       intros ι. cbn - [Val]. now rewrite bv.drop_app. *)
    (*     + revert t1 IHt1 e. generalize (S m). clear m. intros m t1 IHt1 e. *)
    (*       assert (n0 = m + n) as ->. *)
    (*       { rewrite <- transparent.nat_add_assoc in e. *)
    (*         now apply transparent.nat_add_cancel_l in e. } *)
    (*       destruct (uip (transparent.nat_add_assoc n1 m n) e). *)
    (*       rewrite eq_trans_sym_inv_r. *)
    (*       destruct (uip eq_refl (transparent.nat_add_cancel_l (m + n) (m + n) n1 eq_refl)). *)
    (*       cbn. rewrite IHt1. intros ι; cbn - [Val]. clear. *)
    (*       rewrite (inst_eq_rect_indexed_r *)
    (*                  (instTA := fun l => @inst_term (ty.bvec l))). *)
    (*       cbn - [Val]. generalize (inst t2 ι). generalize (inst t1 ι). *)
    (*       intros y z. clear. destruct (bv.appView n1 m y) as [x y]. *)
    (*       rewrite bv.app_app. rewrite rew_opp_l. now rewrite !bv.drop_app. *)
    (*     + revert e. generalize (S m). clear m. intros m e. *)
    (*       assert (m + n0 = n) as <-. *)
    (*       { rewrite <- transparent.nat_add_assoc in e. *)
    (*         now apply transparent.nat_add_cancel_l in e. } *)
    (*       destruct (uip (eq_sym (transparent.nat_add_assoc n1 m n0)) e). *)
    (*       rewrite eq_trans_sym_inv_r. *)
    (*       destruct (uip eq_refl (transparent.nat_add_cancel_l (m + n0) (m + n0) n1 eq_refl)). *)
    (*       cbn. rewrite IHt2. cbn. intros ι. cbn - [Val]. *)
    (*       rewrite !(inst_eq_rect_indexed_r *)
    (*                   (instTA := fun l => @inst_term (ty.bvec l))). *)
    (*       cbn - [Val]. generalize (inst t2 ι). generalize (inst t1 ι). clear. *)
    (*       intros x y. *)
    (*       destruct (bv.appView m n0 y) as [y z]. *)
    (*       rewrite !bv.drop_app. *)
    (*       rewrite <- (bv.drop_app (bv.app x y) z) at 1. f_equal. *)
    (*       rewrite bv.app_app. *)
    (*       unfold eq_rect_r. now rewrite eq_sym_involutive. *)
    (*   - (*bvcons*) *)
    (*     destruct m0; cbn. *)
    (*     + easy. *)
    (*     + rewrite IHt1. clear IHt1. *)
    (*       assert (f_equal S (eq_add_S (m0 + n0) n e) = e) by apply uip. *)
    (*       rewrite <- H at 2. *)
    (*       destruct (eq_add_S (m0 + n0) n e). cbn. *)
    (*       intros ι; cbn. now rewrite bv.drop_cons. *)
    (*   - (*bvdrop*) *)
    (*     unfold peval_bvdrop_bvdrop. rewrite IHt. clear IHt. subst. cbn. *)
    (*     intros ι; cbn - [Val]. *)
    (*     rewrite !(inst_eq_rect_indexed_r *)
    (*                 (instTA := fun l => @inst_term (ty.bvec l))). *)
    (*     rewrite bv.drop_drop. f_equal. *)
    (*     unfold eq_rect_r. now rewrite eq_sym_involutive. *)
    (* Qed. *)

    (* Lemma peval_bvdrop_sound {m n} (t : Term Σ (ty.bvec (m + n))) : *)
    (*   peval_bvdrop m t ≡ term_bvdrop m t. *)
    (* Proof. unfold peval_bvdrop. apply peval_bvdrop_eq_sound. Qed. *)

    (* Lemma peval_bvtake_default_sound {m n mn} (t : Term Σ (ty.bvec mn)) : *)
    (*   forall (e : m + n = mn), *)
    (*     peval_bvtake_default m t e ≡ *)
    (*     term_bvtake m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e). *)
    (* Proof. *)
    (*   unfold peval_bvtake_default. intros e. *)
    (*   destruct eq_dec. *)
    (*   { now subst. } *)
    (*   destruct eq_dec. *)
    (*   { subst; intros ι; cbn. rewrite bv.take_full. *)
    (*     generalize (transparent.nat_add_0_r m). revert t. *)
    (*     generalize (m+0). now intros; subst. } *)
    (*   reflexivity. *)
    (* Qed. *)

    (* #[local] Hint Resolve peval_bvtake_default_sound : core. *)

    (* Lemma peval_bvtake_eq_sound {mn} (t : Term Σ (ty.bvec mn)) : *)
    (*   forall m n (e : m + n = mn), *)
    (*     peval_bvtake_eq m t e ≡ *)
    (*     term_bvtake m (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e). *)
    (* Proof. *)
    (*   induction mn ,t using Term_bvec_rect; cbn - [Val]; intros m0 n0 e; auto. *)
    (*   - (*val*) *)
    (*     now subst. *)
    (*   - (*bvapp*) *)
    (*     unfold peval_bvtake_bvapp. destruct nat_compare. *)
    (*     + pose proof (transparent.nat_add_cancel_l _ _ _ e). subst. *)
    (*       destruct (uip eq_refl e); cbn. *)
    (*       intros ι. cbn - [Val]. now rewrite bv.take_app. *)
    (*     + rewrite IHt1. clear IHt1 IHt2. *)
    (*       assert (n0 = S m + n) as ->. *)
    (*       { rewrite <- transparent.nat_add_assoc in e. *)
    (*         now apply transparent.nat_add_cancel_l in e. } *)
    (*       destruct (uip (transparent.nat_add_assoc n1 (S m) n) e). *)
    (*       intros ι. cbn - [Val]. *)
    (*       rewrite (inst_eq_rect_indexed_r *)
    (*                  (instTA := fun l => @inst_term (ty.bvec l))). *)
    (*       cbn - [Val]. generalize (inst t2 ι). generalize (inst t1 ι). *)
    (*       intros v1 v2. *)
    (*       rewrite <- (bv.take_app v1 v2) at 1. now rewrite bv.take_take. *)
    (*     + rewrite IHt2. clear IHt1 IHt2. *)
    (*       revert e. generalize (S m). clear m. intros m e. *)
    (*       assert (m + n0 = n) as <-. *)
    (*       { rewrite <- transparent.nat_add_assoc in e. *)
    (*         now apply transparent.nat_add_cancel_l in e. } *)
    (*       destruct (uip (eq_sym (transparent.nat_add_assoc n1 m n0)) e). *)
    (*       rewrite eq_trans_sym_inv_r. *)
    (*       destruct (uip eq_refl (transparent.nat_add_cancel_l (m + n0) (m + n0) n1 eq_refl)). *)
    (*       intros ι. cbn - [Val]. *)
    (*       rewrite !(inst_eq_rect_indexed_r *)
    (*                   (instTA := fun l => @inst_term (ty.bvec l))). *)
    (*       cbn - [Val]. generalize (inst t2 ι). generalize (inst t1 ι). clear. *)
    (*       intros x y. *)
    (*       destruct (bv.appView m n0 y) as [y z]. *)
    (*       rewrite bv.take_app. *)
    (*       rewrite <- (bv.take_app (bv.app x y) z). f_equal. *)
    (*       rewrite bv.app_app. *)
    (*       unfold eq_rect_r. now rewrite eq_sym_involutive. *)
    (*   - (*bvcons*) *)
    (*     destruct m0; cbn. *)
    (*     + easy. *)
    (*     + rewrite IHt1. clear IHt1. *)
    (*       assert (f_equal S (eq_add_S (m0 + n0) n e) = e) by apply uip. *)
    (*       rewrite <- H at 2. *)
    (*       destruct (eq_add_S (m0 + n0) n e). cbn. *)
    (*       intros ι; cbn. now rewrite bv.take_cons. *)
    (*   - (*bvtake*) *)
    (*     unfold peval_bvtake_bvtake. rewrite IHt. clear IHt. subst. cbn. *)
    (*     intros ι; cbn - [Val]. rewrite bv.take_take. f_equal. *)
    (*     now rewrite !(inst_eq_rect_indexed_r *)
    (*                 (instTA := fun l => @inst_term (ty.bvec l))). *)
    (* Qed. *)

    (* Lemma peval_bvtake_sound {m n} (t : Term Σ (ty.bvec (m + n))) : *)
    (*   peval_bvtake m t ≡ term_bvtake m t. *)
    (* Proof. unfold peval_bvtake. apply peval_bvtake_eq_sound. Qed. *)

    (* Lemma peval_update_vector_subrange_sound {n s l} (p : IsTrue (s + l <=? n)) *)
    (*   (t1 : Term Σ (ty.bvec n)) (t2 : Term Σ (ty.bvec l)) : *)
    (*   peval_update_vector_subrange s l t1 t2 ≡ *)
    (*   term_binop (bop.update_vector_subrange s l) t1 t2. *)
    (* Proof. *)
    (*   intros ι. cbn - [Val]. *)
    (*   unfold peval_update_vector_subrange, bv.update_vector_subrange. *)
    (*   destruct bv.leview; cbn - [Val]. *)
    (*   repeat *)
    (*     (rewrite ?peval_bvapp_sound, ?peval_bvtake_sound, *)
    (*        ?peval_bvdrop_sound; cbn - [Val]). *)
    (*   destruct bv.appView. *)
    (*   destruct bv.appView. *)
    (*   now rewrite ?bv.take_app, ?bv.drop_app. *)
    (* Qed. *)

    Lemma peval_binop'_sound {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      peval_binop' op t1 t2 ≡ term_binop op t1 t2.
    Proof.
      unfold peval_binop'.
      now repeat
        match goal with
        | |- context[match ?t with _ => _ end] => destruct t
        end.
    Qed.

    Lemma bvmask_try_expand_inv {n} (t : Term Σ (ty.bvec n)) (b : Term Σ ty.bool) :
      bvmask_try_expand t = Some b -> t = term_unop uop.expand b.
    Proof.
      funelim (bvmask_try_expand t); intros Heq; try discriminate.
      now injection Heq as <-.
    Qed.

    Lemma peval_bvand_mask_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvand_mask t1 t2 ≡ term_binop bop.bvand t1 t2.
    Proof.
      unfold peval_bvand_mask.
      destruct (bvmask_try_expand t1) as [b1|] eqn:H1; [|apply peval_binop'_sound].
      destruct (bvmask_try_expand t2) as [b2|] eqn:H2; [|apply peval_binop'_sound].
      apply bvmask_try_expand_inv in H1 as ->; apply bvmask_try_expand_inv in H2 as ->.
      intros ι; cbn. rewrite (peval_and_sound b1 b2 ι); cbn.
      destruct (inst b1 ι), (inst b2 ι); cbn;
        f_equal; now rewrite bv.land_if_ones.
    Qed.

    (* ---- coalesce soundness -------------------------------------------------
       Both sides are pure terms, so the obligation is a plain `bv` identity and
       it covers NonSyncVal (secret) inputs with NO two-world case split — the
       homomorphism argument of the `relval-rewrite-over-secrets` skill.  The
       SyncVal/NonSyncVal constructors show up in the proofs below only because
       `cbn` exposes liftBinOp, never in a statement. *)

    Lemma bvand_split_inv {n} (t t1 t2 : Term Σ (ty.bvec n)) :
      bvand_split t = Some (t1, t2) -> t = term_binop bop.bvand t1 t2.
    Proof.
      funelim (bvand_split t); intros Heq; try discriminate.
      now injection Heq as <- <-.
    Qed.

    Lemma bvmask_is_zero_test_inv {n} (c t : Term Σ (ty.bvec n)) :
      bvmask_is_zero_test c t = true ->
      t = term_unop uop.expand (bvzero_pred c).
    Proof.
      unfold bvmask_is_zero_test. intros H.
      destruct (bvmask_try_expand t) as [b|] eqn:Hb; [|discriminate].
      apply bvmask_try_expand_inv in Hb as ->. f_equal.
      destruct (Term_eqb_spec b (bvzero_pred c)) as [Heq|_];
        [exact Heq|discriminate].
    Qed.

    Lemma bvcoalesce_arg_inv {n} (c t s : Term Σ (ty.bvec n)) :
      bvcoalesce_arg c t = Some s ->
      t = term_binop bop.bvand (term_unop uop.expand (bvzero_pred c)) s \/
      t = term_binop bop.bvand s (term_unop uop.expand (bvzero_pred c)).
    Proof.
      unfold bvcoalesce_arg. intros H.
      destruct (bvand_split t) as [[u1 u2]|] eqn:Ht; [|discriminate].
      apply bvand_split_inv in Ht as ->.
      destruct (bvmask_is_zero_test c u1) eqn:H1.
      - apply bvmask_is_zero_test_inv in H1 as ->.
        injection H as <-. now left.
      - destruct (bvmask_is_zero_test c u2) eqn:H2; [|discriminate].
        apply bvmask_is_zero_test_inv in H2 as ->.
        injection H as <-. now right.
    Qed.

    (* `≤ᵘ 0` IS the zero test — there is nothing below 0 to be strictly less
       than.  Kept folded through `cbn - [bop.eval_relop_val]` because cbn
       reduces eval_relop_val away for a concrete relop and then no bridging
       lemma matches the shape. *)
    Lemma eval_relop_bvule_zero {n} (x : Val (ty.bvec n)) :
      bop.eval_relop_val (bop.bvule (n := n)) x bv.zero = bv.eqb x bv.zero.
    Proof. apply bv.uleb_zero. Qed.

    (* The four operand orders the recognizer accepts collapse onto the four
       bv.coalesce_mask* corollaries; the patterns are mutually exclusive, so
       exactly one of the four rewrites fires per goal. *)
    #[local] Ltac coalesce_bv :=
      rewrite ?eval_relop_bvule_zero;
      now rewrite ?bv.coalesce_mask, ?bv.coalesce_mask_andr,
        ?bv.coalesce_mask_orl, ?bv.coalesce_mask_orl_andr.

    Lemma bvcoalesce_try_inv {n} (t1 t2 t : Term Σ (ty.bvec n)) :
      bvcoalesce_try t1 t2 = Some t -> t ≡ term_binop bop.bvor t1 t2.
    Proof.
      unfold bvcoalesce_try. intros H.
      destruct (bvcoalesce_arg t2 t1) as [s|] eqn:H1.
      - injection H as <-.
        apply bvcoalesce_arg_inv in H1 as [-> | ->]; intros ι;
          cbn - [bop.eval_relop_val];
          destruct (inst t2 ι), (inst s ι);
          cbn - [bop.eval_relop_val]; f_equal; coalesce_bv.
      - destruct (bvcoalesce_arg t1 t2) as [s|] eqn:H2; [|discriminate].
        injection H as <-.
        apply bvcoalesce_arg_inv in H2 as [-> | ->]; intros ι;
          cbn - [bop.eval_relop_val];
          destruct (inst t1 ι), (inst s ι);
          cbn - [bop.eval_relop_val]; f_equal; coalesce_bv.
    Qed.

    Lemma peval_bvor_coalesce_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvor_coalesce t1 t2 ≡ term_binop bop.bvor t1 t2.
    Proof.
      unfold peval_bvor_coalesce.
      destruct (bvcoalesce_try t1 t2) as [t|] eqn:Ht; [|apply peval_binop'_sound].
      now apply bvcoalesce_try_inv.
    Qed.

    (* ---- mulx soundness ------------------------------------------------
       Both sides are pure terms, so (relval-rewrite-over-secrets) the
       obligation is a plain `bv` identity with no NonSyncVal case split;
       `mulx_raw_sound_gen` (Bitvector.v) is exactly that identity. *)

    Lemma bv_bin_one {m} (v : Val (ty.bvec m)) (H : bv.bin v = 1%N) : v = bv.of_N 1.
    Proof. rewrite <- H. now rewrite bv.of_N_bin. Qed.

    Lemma bvmulx_shiftr1_inv {n} (t h : Term Σ (ty.bvec n)) :
      bvmulx_shiftr1 t = Some h ->
      exists m (v : Val (ty.bvec m)),
        bv.bin v = 1%N /\ t = term_binop bop.shiftr h (term_val (ty.bvec m) v).
    Proof.
      funelim (bvmulx_shiftr1 t); intros Heq; try discriminate.
      destruct (N.eqb (bv.bin s) 1) eqn:Hcond; [|discriminate].
      injection Heq as <-. exists n0, s. split; [now apply N.eqb_eq | reflexivity].
    Qed.

    (* Two possible shapes now (simple negate(bvand h one), or the real
       compiled 6-node sign-extraction idiom) -- a disjunction, with the
       second disjunct's witnesses left at the AMBIENT width n (not S n0)
       to avoid transporting h/o1/o2/o3/v1/v2 along a dependent match on n;
       `n0` and the equation `n = S n0` are carried as plain data instead. *)
    Lemma bvmulx_mask_arg_inv {n} (t h : Term Σ (ty.bvec n)) :
      bvmulx_mask_arg t = Some h ->
      (exists (v : Val (ty.bvec n)),
         bv.bin v = 1%N /\
         t = term_unop uop.negate (term_binop bop.bvand h (term_val (ty.bvec n) v)))
      \/ (exists n0 (_ : n = S n0) (o1 o2 o3 v1 v2 : Val (ty.bvec n)) k (sh : Val (ty.bvec k)),
            bv.eqb o1 (bv.ones n) = true /\ bv.eqb o2 (bv.ones n) = true /\
            bv.eqb o3 (bv.ones n) = true /\
            bv.bin v1 = 1%N /\ bv.bin v2 = 1%N /\ bv.bin sh = N.of_nat n0 /\
            t = term_binop bop.bvadd (term_val (ty.bvec n) o1)
                  (term_binop bop.shiftr
                     (term_binop bop.bvand
                        (term_binop bop.bvadd (term_val (ty.bvec n) o2)
                           (term_binop bop.bvand h (term_val (ty.bvec n) v1)))
                        (term_binop bop.bvxor
                           (term_binop bop.bvand h (term_val (ty.bvec n) v2))
                           (term_val (ty.bvec n) o3)))
                     (term_val (ty.bvec k) sh))).
    Proof.
      funelim (bvmulx_mask_arg t); intros Heq; try discriminate.
      - destruct (bv.eqb o1 (bv.ones n) && bv.eqb o2 (bv.ones n) && bv.eqb o3 (bv.ones n)
                  && N.eqb (bv.bin v1) 1 && N.eqb (bv.bin v2) 1 && Term_eqb h h'
                  && match n with 0%nat => false | S n0 => N.eqb (bv.bin sh) (N.of_nat n0) end)
          eqn:Hcond; [|discriminate].
        injection Heq as <-.
        apply Bool.andb_true_iff in Hcond as [Hcond Hn0].
        apply Bool.andb_true_iff in Hcond as [Hcond Hh].
        apply Bool.andb_true_iff in Hcond as [Hcond Hv2].
        apply Bool.andb_true_iff in Hcond as [Hcond Hv1].
        apply Bool.andb_true_iff in Hcond as [Hcond Ho3].
        apply Bool.andb_true_iff in Hcond as [Ho1 Ho2].
        destruct (Term_eqb_spec h h') as [<-|]; [|discriminate].
        destruct n as [|nS]; [discriminate|].
        right. exists nS, eq_refl, o1, o2, o3, v1, v2, n0, sh.
        repeat split; try assumption; now apply N.eqb_eq.
      - destruct (N.eqb (bv.bin v) 1) eqn:Hcond; [|discriminate].
        injection Heq as <-. left. exists v. split; [now apply N.eqb_eq | reflexivity].
    Qed.

    (* Carries the "recognized" fact ABSTRACTLY (bvmulx_mask_arg mask_term =
       Some h) rather than re-exposing its witnesses here -- the final
       consumer (bvmulx_try_inv) invokes bvmulx_mask_arg_inv itself when it
       needs to case on which of the two shapes actually matched. Keeps this
       lemma, and its proof, unchanged by the second shape entirely. *)
    Lemma bvmulx_arg_inv {n} (h t r : Term Σ (ty.bvec n)) :
      bvmulx_arg h t = Some r ->
      exists mask_term, bvmulx_mask_arg mask_term = Some h /\
        (t = term_binop bop.bvand mask_term r \/
         t = term_binop bop.bvand r mask_term).
    Proof.
      unfold bvmulx_arg. intros H.
      destruct (bvand_split t) as [[u1 u2]|] eqn:Ht; [|discriminate].
      apply bvand_split_inv in Ht as ->.
      destruct (bvmulx_mask_arg u1) as [h1|] eqn:H1.
      - destruct (Term_eqb_spec h h1) as [<-|]; [|discriminate].
        injection H as <-.
        exists u1. split; [exact H1 | now left].
      - destruct (bvmulx_mask_arg u2) as [h2|] eqn:H2; [|discriminate].
        destruct (Term_eqb_spec h h2) as [<-|]; [|discriminate].
        injection H as <-.
        exists u2. split; [exact H2 | now right].
    Qed.

    (* Both mask shapes close the SAME four (order x commutation)
       combinations; factored into one tactic since bvmulx_try_inv needs it
       at all four call sites (t1-shift/t2-shift x mask-left/mask-right). *)
    Ltac bvmulx_close_simple v Hv :=
      first
        [ symmetry; apply bv.mulx_raw_sound_gen
        | symmetry; rewrite bv.land_comm; apply bv.mulx_raw_sound_gen
        | rewrite bv.lxor_comm; symmetry; apply bv.mulx_raw_sound_gen
        | rewrite bv.lxor_comm; symmetry; rewrite bv.land_comm;
          apply bv.mulx_raw_sound_gen ].

    (* T2-shift's simple-shape closer: mask-and-r comes BEFORE the shift
       (the reverse outer-lxor order from T1-shift), so this needs the
       "_swap" family instead -- via four NAMED lemmas, never a blind
       `rewrite lxor_comm`/`land_comm` (which matches the goal's own
       unresolved `if ... else lxor (shiftr h _) r` first and leaves the
       intended outer occurrence untouched; confirmed empirically, see
       Bitvector.v's mulx_raw_sound_gen_swap header comment). *)
    Ltac bvmulx_close_simple_swapped :=
      first
        [ symmetry; apply bv.mulx_raw_sound_gen_swap
        | symmetry; apply bv.mulx_raw_sound_gen_landswap_swap ].

    (* Same shape as bvmulx_close_simple, now that bv.mulx_realmask_full_sound
       states the WHOLE goal equation (not just the mask sub-term): a single
       `apply` per commutativity/direction alternative, closing every
       SyncVal/NonSyncVal instance uniformly instead of a `rewrite` followed
       by a `match goal`/`destruct` finishing step (the latter doesn't
       survive being run via `;` across the many goals a relational
       peval-soundness proof produces -- see bv.mulx_realmask_full_sound's
       header comment). NOTE the direction here is the OPPOSITE of
       bvmulx_close_simple's `mulx_raw_sound_gen`: this lemma states
       `mulx-eval = verbose-shape`, matching the ≡ goal's own orientation
       (`inst t = inst (bvxor t1 t2)`, `t` on the left) directly, so no
       `symmetry` is needed here (`mulx_raw_sound_gen` happens to be stated
       the other way around). All four outer-operand-order combinations
       (`lxor`'s and `land`'s) are tried via FOUR NAMED lemmas, never via a
       blind `rewrite lxor_comm`/`land_comm` -- the goal's other side
       (`bop.mulx`'s `eval`) contains its own unresolved
       `if ... else lxor (shiftr h _) r`, itself built from a `land h _`
       guard, and an unqualified `lxor_comm`/`land_comm` rewrite matches
       and flips those inner occurrences first (confirmed: both silently
       "succeed" while leaving the intended outer occurrence completely
       untouched, so the subsequent `apply` fails on every one of the many
       relational goals -- see the four lemmas' header comments in
       Bitvector.v). *)
    Ltac bvmulx_close_real :=
      first
        [ apply bv.mulx_realmask_full_sound; assumption
        | apply bv.mulx_realmask_full_sound_swap; assumption
        | apply bv.mulx_realmask_full_sound_landswap; assumption
        | apply bv.mulx_realmask_full_sound_landswap_lxorswap; assumption ].

    Lemma bvmulx_try_inv {n} (t1 t2 t : Term Σ (ty.bvec n)) :
      bvmulx_try t1 t2 = Some t -> t ≡ term_binop bop.bvxor t1 t2.
    Proof.
      unfold bvmulx_try. intros H.
      destruct (bvmulx_shiftr1 t1) as [h|] eqn:Hs1.
      - apply bvmulx_shiftr1_inv in Hs1 as (m1 & vsh & Hvsh & ->).
        destruct (bvmulx_arg h t2) as [r|] eqn:Ha; [|discriminate].
        injection H as <-.
        apply bvmulx_arg_inv in Ha as (mask_term & Hmask & Hord).
        apply bvmulx_mask_arg_inv in Hmask
          as [(v & Hv & ->)
             |(n0 & -> & o1 & o2 & o3 & v1 & v2 & k & sh
               & Ho1 & Ho2 & Ho3 & Hv1 & Hv2 & Hsh & ->)].
        + destruct Hord as [-> | ->];
            intros ι; cbn;
            destruct (inst h ι), (inst r ι); cbn; f_equal;
            rewrite (bv.shiftr_bin_eq _ vsh v (eq_trans Hvsh (eq_sym Hv)));
            rewrite (bv_bin_one v Hv);
            bvmulx_close_simple v Hv.
        + destruct Hord as [-> | ->];
            intros ι; cbn;
            destruct (inst h ι), (inst r ι); cbn; f_equal;
            bvmulx_close_real.
      - destruct (bvmulx_shiftr1 t2) as [h|] eqn:Hs2; [|discriminate].
        apply bvmulx_shiftr1_inv in Hs2 as (m1 & vsh & Hvsh & ->).
        destruct (bvmulx_arg h t1) as [r|] eqn:Ha; [|discriminate].
        injection H as <-.
        apply bvmulx_arg_inv in Ha as (mask_term & Hmask & Hord).
        apply bvmulx_mask_arg_inv in Hmask
          as [(v & Hv & ->)
             |(n0 & -> & o1 & o2 & o3 & v1 & v2 & k & sh
               & Ho1 & Ho2 & Ho3 & Hv1 & Hv2 & Hsh & ->)].
        + destruct Hord as [-> | ->];
            intros ι; cbn;
            destruct (inst h ι), (inst r ι); cbn; f_equal;
            rewrite (bv.shiftr_bin_eq _ vsh v (eq_trans Hvsh (eq_sym Hv)));
            rewrite (bv_bin_one v Hv);
            bvmulx_close_simple_swapped.
        + destruct Hord as [-> | ->];
            intros ι; cbn;
            destruct (inst h ι), (inst r ι); cbn; f_equal;
            bvmulx_close_real.
    Qed.

    Lemma peval_bvxor_mulx_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvxor_mulx t1 t2 ≡ term_binop bop.bvxor t1 t2.
    Proof.
      unfold peval_bvxor_mulx.
      destruct (bvmulx_try t1 t2) as [t|] eqn:Ht; [|apply peval_binop'_sound].
      now apply bvmulx_try_inv.
    Qed.

    Lemma peval_bvor_mask_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvor_mask t1 t2 ≡ term_binop bop.bvor t1 t2.
    Proof.
      unfold peval_bvor_mask.
      destruct (bvmask_try_expand t1) as [b1|] eqn:H1; [|apply peval_bvor_coalesce_sound].
      destruct (bvmask_try_expand t2) as [b2|] eqn:H2; [|apply peval_bvor_coalesce_sound].
      apply bvmask_try_expand_inv in H1 as ->; apply bvmask_try_expand_inv in H2 as ->.
      intros ι; cbn. rewrite (peval_or_sound b1 b2 ι); cbn.
      destruct (inst b1 ι), (inst b2 ι); cbn;
        f_equal; now rewrite bv.lor_if_ones.
    Qed.

    (* `bop.relop bop.neq` at sigma = ty.bool is xor. *)
    Lemma eval_relop_neq_bool (b1 b2 : bool) :
      bop.eval_relop_val (bop.neq (σ := ty.bool)) b1 b2 = xorb b1 b2.
    Proof. now destruct b1, b2. Qed.

    Lemma peval_bvxor_mask_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvxor_mask t1 t2 ≡ term_binop bop.bvxor t1 t2.
    Proof.
      unfold peval_bvxor_mask.
      destruct (bvmask_try_expand t1) as [b1|] eqn:H1; [|apply peval_bvxor_mulx_sound].
      destruct (bvmask_try_expand t2) as [b2|] eqn:H2; [|apply peval_bvxor_mulx_sound].
      apply bvmask_try_expand_inv in H1 as ->; apply bvmask_try_expand_inv in H2 as ->.
      intros ι; cbn - [bop.eval_relop_val].
      destruct (inst b1 ι), (inst b2 ι); cbn - [bop.eval_relop_val];
        f_equal; rewrite eval_relop_neq_bool; now rewrite bv.lxor_if_ones.
    Qed.

    Lemma peval_shiftl_sound {m n} (t1 : Term Σ (ty.bvec m)) (t2 : Term Σ (ty.bvec n)) :
      peval_shiftl t1 t2 ≡ term_binop bop.shiftl t1 t2.
    Proof.
      unfold peval_shiftl.
      destruct (term_get_val_spec t2) as [k Hk|]; [|apply peval_binop'_sound].
      subst t2. apply canon_term_equiv.
    Qed.

    Lemma peval_bvsub_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvsub t1 t2 ≡ term_binop bop.bvsub t1 t2.
    Proof. apply canon_term_equiv. Qed.

    Lemma peval_append_sound {σ} (t1 t2 : Term Σ (ty.list σ)) :
      peval_append t1 t2 ≡ term_binop bop.append t1 t2.
    Proof.
      funelim (peval_append t1 t2); intros ι; try reflexivity.
      - (* before any cbn: it would unfold peval_binop' *)
        destruct v; [|exact (peval_binop'_sound _ _ _ ι)].
        cbn. destruct (inst t2 ι); reflexivity.
      - cbn. rewrite H. cbn. destruct (inst x ι), (inst t ι), (inst t2 ι); reflexivity.
      - cbn. rewrite H0. cbn. rewrite H. cbn.
        destruct (inst a ι), (inst b ι), (inst t2 ι); cbn; f_equal; try apply app_assoc;
          f_equal; apply app_assoc.
    Qed.

    Hint Resolve peval_binop'_sound peval_append_sound peval_and_sound
      peval_or_sound peval_plus_sound peval_minus_sound peval_bvadd_sound
      peval_bvand_mask_sound peval_bvor_mask_sound peval_bvxor_mask_sound
      peval_shiftl_sound peval_bvsub_sound
      (* peval_bvand_sound *)
      (* peval_bvor_sound *) (* peval_bvapp_sound *) (* peval_update_vector_subrange_sound *)
      : core.

    Lemma peval_binop_sound {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      peval_binop op t1 t2 ≡ term_binop op t1 t2.
    Proof. destruct op; cbn [peval_binop]; auto. Qed.

    Equations peval_not (t : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ v                    => term_val ty.bool (negb v)
    | term_binop bop.and t1 t2        => term_binop bop.or (peval_not t1) (peval_not t2)
    | term_binop bop.or t1 t2         => term_binop bop.and (peval_not t1) (peval_not t2)
    | term_binop (bop.relop op) t1 t2 => term_relop_neg op t1 t2
    | t                               => term_unop uop.not t.

    Definition peval_unsigned_bvapp {m1 m2} (t1 : Term Σ (ty.bvec m1))
      (t2 : Term Σ (ty.bvec m2)) : Term Σ ty.int :=
      term_binop bop.plus (term_unsigned t1)
        (term_binop bop.times (term_unsigned t2)
           (term_val ty.int (2 ^ Z.of_nat m1)%Z)).

    Equations peval_unsigned {m} (t : Term Σ (ty.bvec m)) : Term Σ ty.int :=
    | term_val _ v                => term_val ty.int (bv.unsigned v)
    | term_binop bop.bvapp t1 t2  => peval_unsigned_bvapp t1 t2
    | t                           => term_unop uop.unsigned t.


    Definition peval_vector_subrange {n} start len {p : IsTrue (start + len <=? n)} :
      Term Σ (ty.bvec n) -> Term Σ (ty.bvec len) :=
      match bv.leview (start + len) n with
      | bv.is_le k => fun t => peval_bvdrop start
                                 (peval_bvtake (start + len) t)
      end.

    Definition peval_unop' {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) : Term Σ σ2 :=
      match term_get_val t with
      | Some v => term_val σ2 (uop.eval op v)
      | None   => term_unop op t
      end.

    (* Complement of a mask is the mask of the complemented predicate:
       ~(b ? ~0 : 0) = (~b ? ~0 : 0).  This moves negation out of the bitvector
       layer into the bool layer, where peval_not immediately absorbs it — for a
       relop predicate it becomes the negated relop (term_relop_neg), so no
       `not` node survives at all.  Concretely it turns the mask peval_bvadd
       builds for clang's `snez; addi -1` from `bvnot (expand (0 <ᵘ C))` into
       `expand (C ≤ᵘ 0)`, i.e. literally "the mask of C being zero". *)
    Definition peval_bvnot {n} (t : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
      match bvmask_try_expand t with
      | Some b => term_unop uop.expand (peval_not b)
      | None   => peval_unop' uop.bvnot t
      end.

    (* SELF-TESTS (see the block above peval_bvadd for why these exist). *)
    Lemma selftest_bvnot_expand_fires {n} (b : Term Σ ty.bool) :
      peval_bvnot (term_unop (uop.expand (n := n)) b)
      = term_unop uop.expand (peval_not b).
    Proof. reflexivity. Qed.

    (* The composition that matters, and the one I initially predicted WRONG:
       for a relop predicate, peval_not does not leave a `not` node — it negates
       the relop (term_relop_neg).  So clang's `snez ; addi -1` mask ends up as
       `expand (C <=u 0)`, one node over one POSITIVE relop, which is what
       Example/ZZExpandDump.v dumps.  If this test ever fails, that dump has
       changed shape and any recognizer written against it (e.g. coalesce) needs
       re-checking. *)
    Lemma selftest_bvnot_expand_negates_relop {n} (t : Term Σ (ty.bvec n)) :
      peval_bvnot
        (term_unop (uop.expand (n := n))
           (term_binop (bop.relop bop.bvult) (term_val (ty.bvec n) bv.zero) t))
      = term_unop (uop.expand (n := n))
          (term_relop_neg bop.bvult (term_val (ty.bvec n) bv.zero) t).
    Proof. reflexivity. Qed.

    Lemma selftest_bvnot_inert {n} (v : Val (ty.bvec n)) :
      peval_bvnot (term_val (ty.bvec n) v) = term_val (ty.bvec n) (bv.not v).
    Proof. reflexivity. Qed.

    (* A same-width sign extension is the identity (bv.sext_same).  A RISC-V
       `lw` on RV32 produces one on every load (Machine.v's extend_value widens
       4 bytes to xlenbytes = 4), so without this rule a return address saved
       with `sw ra` and restored with `lw ra` comes back as `sext r`, and the
       syntactic exit test against `r` misses (PLAN-rsa.md, spike S1b). *)
    Definition peval_sext {m n} {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec m)) :
        Term Σ (ty.bvec n) :=
      match width_cast m n with
      | Some f => f (fun k => Term Σ (ty.bvec k)) t
      | None   => peval_unop' (uop.sext (m := m) (n := n) (p := p)) t
      end.

    Lemma selftest_sext_same (t : Term Σ (ty.bvec 32)) p :
      peval_sext (m := 32) (n := 32) (p := p) t = t.
    Proof. reflexivity. Qed.

    (* Truncating a zero extension back to its source width is the identity
       (bv.take_zext).  A RISC-V `lbu` widens the byte with zext 8 -> 32 and
       `sb` truncates with bvtake 8, so a byte copied by lbu; sb (memcpy,
       memmove, br_ccopy) would otherwise be stored as `bvtake 8 (zext x)`,
       not `x`, and a value-carrying array (CFGVer `arrv`) would not see the
       copy as the same value (PLAN-rsa.md, Phase 2).  Same leaves on both
       sides, so sound over secrets with no case split.  Distinct from the
       unwired general peval_bvtake above. *)
    Equations peval_zext_arg {k} (t : Term Σ (ty.bvec k)) :
        option {m' & {p : IsTrue (m' <=? k) & Term Σ (ty.bvec m')}} :=
    | term_unop (@uop.zext m' _ p) x => Some (existT m' (existT p x))
    | _ => None.

    Definition peval_bvtake_zext m {n} (t : Term Σ (ty.bvec (m + n))) : Term Σ (ty.bvec m) :=
      match peval_zext_arg t with
      | Some (existT m' (existT _ x)) =>
          match width_cast m' m with
          | Some f => f (fun k => Term Σ (ty.bvec k)) x
          | None   => peval_unop' (uop.bvtake m) t
          end
      | None => peval_unop' (uop.bvtake m) t
      end.

    Lemma selftest_bvtake_zext (x : Term Σ (ty.bvec 8)) :
      peval_bvtake_zext 8 (n := 24) (term_unop (uop.zext (m := 8) (n := 32)) x) = x.
    Proof. reflexivity. Qed.

    (* List reversal pushed to the leaves, in peval_append's snoc form:
         rev (x :: t) ~> rev t ++ [x],  rev (a ++ b) ~> rev b ++ rev a,
         rev (rev v) ~> v.
       A DONE array built by add_first at stride -s and then flipped holds
       `rev done` (CFGVer `arrv_flip`, PLAN-arrv.md O1); after one more
       add_first, rev (x :: done) must meet rev done ++ [x] syntactically.
       Same leaves on both sides, so sound over secrets without a case
       split.  Self-tests on concrete terms: CFGVer/Example/Rsa/. *)
    Equations peval_rev {σ} (t : Term Σ (ty.list σ)) : Term Σ (ty.list σ) by struct t :=
    | term_binop bop.cons x t   => peval_append (peval_rev t)
                                     (term_binop bop.cons x (term_val (ty.list σ) nil))
    | term_binop bop.append a b => peval_append (peval_rev b) (peval_rev a)
    | term_unop uop.rev v       => v
    | t                         => peval_unop' uop.rev t.

    Definition peval_unop {σ1 σ2} (op : UnOp σ1 σ2) : Term Σ σ1 -> Term Σ σ2 :=
      match op with
      | uop.not                       => peval_not
      | uop.bvnot                     => peval_bvnot
      | @uop.sext _ m n p             => @peval_sext m n p
      | uop.negate                    => fun t => canon_term (term_unop uop.negate t)
      (* | uop.unsigned                  => peval_unsigned *)
      (* | uop.vector_subrange start len => peval_vector_subrange start len *)
      (* | uop.bvdrop m                  => peval_bvdrop m *)
      | uop.bvtake m                  => peval_bvtake_zext m
      | uop.rev                       => peval_rev
      | op                            => peval_unop' op
      end.

    (* Definition CanonTerm_to_Term {σ} : CanonTerm σ -> Term Σ σ := *)
    (*   match σ return CanonTerm σ -> Term Σ σ with *)
    (*   | ty.bvec n => fun ct => *)
    (*                    match ct nil 1%positive with *)
    (*                    | (pexpr , env) => *)
    (*                        evalPolTm (H := TermRing_bv) env (norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool pexpr) *)
    (*                    end *)
    (*   | ty.int => fun ct => *)
    (*                 match ct nil 1%positive with *)
    (*                 | (pexpr , env) => *)
    (*                     evalPolTm env (norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool pexpr) *)
    (*                 end *)
    (*   | _σ => fun t => t *)
    (*   end. *)

    Lemma peval_not_sound (t : Term Σ ty.bool) :
      peval_not t ≡ term_unop uop.not t.
    Proof. funelim (peval_not t); lsolve; now apply proper_term_binop. Qed.

    (* Lemma peval_unsigned_bvapp_sound [m1 m2] (t1 : Term Σ (ty.bvec m1)) *)
    (*   (t2 : Term Σ (ty.bvec m2)) : *)
    (*   peval_unsigned_bvapp t1 t2 ≡ term_unsigned (term_bvapp t1 t2). *)
    (* Proof. intros ι; cbn. now rewrite bv.unsigned_app. Qed. *)
    (* #[local] Hint Resolve peval_unsigned_bvapp_sound : core. *)

    (* Lemma peval_unsigned_sound {m} (t : Term Σ (ty.bvec m)) : *)
    (*   peval_unsigned t ≡ term_unop uop.unsigned t. *)
    (* Proof. funelim (peval_unsigned t); lsolve. Qed. *)

    Lemma peval_unop'_sound {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) :
      peval_unop' op t ≡ term_unop op t.
    Proof. unfold peval_unop'; destruct (term_get_val_spec t); subst; easy. Qed.

    (* Lemma peval_vector_subrange_sound' {n} start len {p : IsTrue (start + len <=? n)} *)
    (*   (t : Term Σ (ty.bvec n)) : *)
    (*   peval_vector_subrange start len t ≡ *)
    (*   term_vector_subrange start len t. *)
    (* Proof. *)
    (*   unfold peval_vector_subrange, term_vector_subrange. destruct bv.leview. *)
    (*   now rewrite peval_bvdrop_sound, peval_bvtake_sound. *)
    (* Qed. *)

    (* Lemma peval_vector_subrange_sound {n} start len {p : IsTrue (start + len <=? n)} *)
    (*   (t : Term Σ (ty.bvec n)) : *)
    (*   peval_vector_subrange start len t ≡ *)
    (*   term_unop (uop.vector_subrange start len) t. *)
    (* Proof. *)
    (*   rewrite peval_vector_subrange_sound'. intros ι; cbn. *)
    (*   unfold term_vector_subrange, bv.vector_subrange. *)
    (*   now destruct bv.leview. *)
    (* Qed. *)

    Lemma peval_bvnot_sound {n} (t : Term Σ (ty.bvec n)) :
      peval_bvnot t ≡ term_unop uop.bvnot t.
    Proof.
      unfold peval_bvnot.
      destruct (bvmask_try_expand t) as [b|] eqn:Hb; [|apply peval_unop'_sound].
      apply bvmask_try_expand_inv in Hb as ->.
      intros ι; cbn. rewrite (peval_not_sound b ι); cbn.
      destruct (inst b ι); cbn;
        f_equal; now rewrite bv.not_if_ones.
    Qed.

    Lemma peval_sext_sound {m n} {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec m)) :
      peval_sext (p := p) t ≡ term_unop (uop.sext (m := m) (n := n) (p := p)) t.
    Proof.
      unfold peval_sext.
      destruct (width_cast m n) as [f|] eqn:E; [|apply peval_unop'_sound].
      destruct (width_cast_spec E) as [e He]. rewrite He. subst n. cbn.
      intros ι; cbn. destruct (inst t ι) as [v|v1 v2]; cbn;
        f_equal; try f_equal; symmetry; apply bv.sext_same.
    Qed.

    (* IsTrue b wraps Is_true b, which is True or False: one proof at most *)
    Lemma istrue_irr {b} (p q : IsTrue b) : p = q.
    Proof. destruct p as [p], q as [q]. destruct b; [destruct p, q|destruct p]; reflexivity. Qed.

    Lemma peval_zext_arg_inv {k} (t : Term Σ (ty.bvec k)) m' p x :
      peval_zext_arg t = Some (existT m' (existT p x)) ->
      t = term_unop (uop.zext (m := m') (n := k) (p := p)) x.
    Proof.
      funelim (peval_zext_arg t); intros Heq; try discriminate.
      injection Heq as Heq. subst m'0.
      apply Eqdep_dec.inj_pair2_eq_dec in H; [|exact Nat.eq_dec]. subst x0.
      rewrite (istrue_irr p p0). reflexivity.
    Qed.

    Lemma peval_bvtake_zext_sound m {n} (t : Term Σ (ty.bvec (m + n))) :
      peval_bvtake_zext m t ≡ term_unop (uop.bvtake m) t.
    Proof.
      unfold peval_bvtake_zext.
      destruct (peval_zext_arg t) as [[m' [p x]]|] eqn:Hz; [|apply peval_unop'_sound].
      destruct (width_cast m' m) as [f|] eqn:Hw; [|apply peval_unop'_sound].
      apply peval_zext_arg_inv in Hz. subst t.
      destruct (width_cast_spec Hw) as [e Hf]. subst m'. rewrite Hf. cbn.
      intros ι; cbn. destruct (inst x ι); cbn; f_equal; symmetry; apply bv.take_zext.
    Qed.

    Lemma peval_rev_sound {σ} (t : Term Σ (ty.list σ)) :
      peval_rev t ≡ term_unop uop.rev t.
    Proof.
      funelim (peval_rev t); try apply peval_unop'_sound; intros ι.
      - rewrite (peval_append_sound _ _ ι). cbn. rewrite H. cbn.
        destruct (inst x ι), (inst t ι); reflexivity.
      - rewrite (peval_append_sound _ _ ι). cbn. rewrite H; rewrite H0. cbn.
        destruct (inst a ι), (inst b ι); cbn; f_equal; rewrite ?rev_app_distr; reflexivity.
      - cbn. destruct (inst v ι); cbn; f_equal; rewrite ?rev_involutive; reflexivity.
    Qed.

    Lemma peval_unop_sound {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) :
      peval_unop op t ≡ term_unop op t.
    Proof.
      destruct op; cbn [peval_unop];
        auto using peval_unop'_sound, peval_not_sound, peval_bvnot_sound, peval_sext_sound, peval_bvtake_zext_sound, peval_rev_sound, canon_term_equiv(* , peval_unsigned_sound, *)
                 (* peval_bvdrop_sound, peval_bvtake_sound, *)
                 (*   peval_vector_subrange_sound *).
    Qed.

    Definition peval_union {U K} (t : Term Σ (unionk_ty U K)) : Term Σ (ty.union U) :=
      match term_get_val t with
      | Some v => term_val (ty.union U) (unionv_fold U (existT K v))
      | None   => term_union U K t
      end.

    Lemma peval_union_sound {U K} (t : Term Σ (unionk_ty U K)) :
      peval_union t ≡ term_union U K t.
    Proof. unfold peval_union. destruct (term_get_val_spec t); now subst. Qed.

    Import option.notations.
    Fixpoint peval_record' {rfs : NCtx recordf Ty} (ts : NamedEnv (Term Σ) rfs) {struct ts} : option (NamedEnv RelVal rfs) :=
      match ts with
      | env.nil         => Some [env]
      | env.snoc ts _ t => vs <- peval_record' ts ;;
                           v  <- term_get_val t ;;
                           Some (env.snoc vs _ (SyncVal v))
      end.

    Definition peval_record R (ts : NamedEnv (Term Σ) (recordf_ty R)) : Term Σ (ty.record R) :=
      match peval_record' ts with
      | Some a => term_relval (ty.record R) (ty.recordv_fold_rel R a)
      | None => term_record R ts
      end.

    Lemma peval_record'_sound {rfs : NCtx recordf Ty} (ts : NamedEnv (Term Σ) rfs) :
      option.wlp (fun vs => forall ι, inst ts ι = vs) (peval_record' ts).
    Proof.
      induction ts; cbn.
      - now constructor.
      - rewrite option.wlp_bind. revert IHts.
        apply option.wlp_monotonic. intros vs IHvs.
        rewrite option.wlp_bind. generalize (term_get_val_spec db).
        apply option.wlp_monotonic. intros v IHv. constructor.
        intros ι. specialize (IHvs ι). subst. reflexivity.
    Qed.

    Lemma peval_record_sound {R} ts :
      peval_record R ts ≡ term_record R ts.
    Proof.
      unfold peval_record. destruct (peval_record'_sound ts); [|reflexivity].
      intros ι; cbn. now f_equal.
    Qed.

    (* ================================================================== *)
    (* main's peval2 (Dominique, fa563609/b226c5d9/98916b52), reinstated:   *)
    (* ring islands (bvadd/bvsub/bvmul/negate, and << by a constant as      *)
    (* multiplication by 2^k) are kept QUOTED until a non-ring operator     *)
    (* consumes them; CanonTerm_to_Term then normalises (canon_term, sound  *)
    (* over RelVal) and the fork's own rules (peval_binop / peval_unop:     *)
    (* mask algebra, coalesce, mulx) run on canonical children.             *)
    (* ================================================================== *)
    Definition CanonTermRep {σ : Ty} : CanonTerm σ -> Term Σ σ -> Prop :=
      match σ with
      | ty.bvec n => fun ct t => RQuoteValid t ct
      | _ => fun ct t => ct ≡ t
      end.

    Lemma CanonTermRep_equiv {σ} {ct : CanonTerm σ} {t t'} :
      CanonTermRep ct t -> t ≡ t' -> CanonTermRep ct t'.
    Proof.
      destruct σ; cbn; try (intros H1 H2; etransitivity; eassumption).
      intros H Ht lo o. specialize (H lo o). destruct (ct lo o) as [p l].
      intros Ho la. etransitivity; [apply H; exact Ho|exact Ht].
    Qed.

    (* the mask algebra's `ones + indicator` rule, on the canonical output *)
    Definition post_mask {n} (t : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
      match bvadd_head t with
      | Some (v, a) => peval_bvadd_mask a v
      | None => t
      end.

    Lemma post_mask_sound {n} (t : Term Σ (ty.bvec n)) : post_mask t ≡ t.
    Proof.
      unfold post_mask. destruct (bvadd_head t) as [[v a]|] eqn:E; [|reflexivity].
      apply bvadd_head_spec in E. subst t.
      etransitivity; [apply peval_bvadd_mask_sound|].
      intros ι. cbn. destruct (inst a ι); cbn; f_equal; apply bv.add_comm.
    Qed.

    Definition CanonTerm_to_Term {σ} : CanonTerm σ -> Term Σ σ :=
      match σ return CanonTerm σ -> Term Σ σ with
      | ty.bvec n => fun ct =>
          match ct nil 1%positive with
          | (pexpr , env) => post_mask (canon_term (evalPExprTm env pexpr))
          end
      | _ => fun t => t
      end.

    Lemma CanonTermRep_adeq {σ : Ty} {ct : CanonTerm σ} {t} :
      CanonTermRep ct t -> CanonTerm_to_Term ct ≡ t.
    Proof.
      destruct σ; cbn; try (intros H; exact H).
      intros H. specialize (H nil 1%positive). destruct (ct nil 1%positive) as [p env].
      specialize (H eq_refl nil). cbn in H. rewrite List.app_nil_r in H.
      etransitivity; [apply post_mask_sound|].
      etransitivity; [|exact H]. intros ι. apply canon_term_sound.
    Qed.

    Definition CanonTerm_def {σ : Ty} : Term Σ σ -> CanonTerm σ :=
      match σ with
      | ty.bvec n => Term_Quote_def
      | _ => fun t => t
      end.

    Lemma CanonTerm_def_sound {σ : Ty} {t : Term Σ σ} : CanonTermRep (CanonTerm_def t) t.
    Proof. destruct σ; try reflexivity. apply Term_Quote_def_Valid. Qed.

    Definition peval2_val {σ : Ty} : Val σ -> CanonTerm σ :=
      match σ with
      | ty.bvec n => fun v l p => (PEc (bv.unsigned v) , nil)
      | _ => term_val _
      end.

    Lemma peval2_val_sound {σ : Ty} {v : Val σ} : CanonTermRep (peval2_val v) (term_val _ v).
    Proof.
      destruct σ; try reflexivity. intros lo ? -> la; cbn.
      now rewrite bv.of_Z_unsigned.
    Qed.

    Definition peval2_binop_default {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3)
      (c1 : CanonTerm σ1) (c2 : CanonTerm σ2) : CanonTerm σ3 :=
      CanonTerm_def (peval_binop op (CanonTerm_to_Term c1) (CanonTerm_to_Term c2)).

    Lemma peval2_binop_default_sound {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3)
      {c1 : CanonTerm σ1} {t1} {c2 : CanonTerm σ2} {t2} :
      CanonTermRep c1 t1 -> CanonTermRep c2 t2 ->
      CanonTermRep (peval2_binop_default op c1 c2) (term_binop op t1 t2).
    Proof.
      intros H1 H2. unfold peval2_binop_default.
      eapply CanonTermRep_equiv; [apply CanonTerm_def_sound|].
      etransitivity; [apply peval_binop_sound|].
      apply proper_term_binop; apply CanonTermRep_adeq; assumption.
    Qed.

    (* << by a constant, quoted as multiplication by 2^k: EXACT over RelVal
       (both projections by shiftl_as_mul; a constant adds no taint) *)
    Lemma quote_shiftl_valid {n m} (kv : bv m) {t1 : Term Σ (ty.bvec n)} {q1 : RQuote (ty.bvec n)} :
      RQuoteValid t1 q1 ->
      RQuoteValid (term_binop bop.shiftl t1 (term_val (ty.bvec m) kv))
        (Term_Quote_unop (fun p => PEmul p (PEc (2 ^ Z.of_nat (N.to_nat (bv.bin kv)))%Z)) q1).
    Proof.
      intros H lo o. specialize (H lo o). unfold Term_Quote_unop.
      destruct (q1 lo o) as [p1 l1]. intros Ho la. specialize (H Ho la).
      change (evalPExprTm (lo ++ l1 ++ la) (PEmul p1 (PEc (2 ^ Z.of_nat (N.to_nat (bv.bin kv)))%Z)))
        with (term_binop bop.bvmul (evalPExprTm (lo ++ l1 ++ la) p1)
                (term_val (ty.bvec n) (bv.of_Z (2 ^ Z.of_nat (N.to_nat (bv.bin kv)))%Z))).
      intros ι. rewrite !inst_binop. rewrite (H ι).
      change (inst (term_val (ty.bvec n) (bv.of_Z (2 ^ Z.of_nat (N.to_nat (bv.bin kv)))%Z)) ι)
        with (ty.SyncVal (bv.of_Z (n := n) (2 ^ Z.of_nat (N.to_nat (bv.bin kv)))%Z)).
      change (inst (term_val (ty.bvec m) kv) ι) with (ty.SyncVal kv).
      destruct (inst t1 ι); cbn; f_equal; symmetry; apply shiftl_as_mul.
    Qed.

    Definition peval2_binop {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) :
      CanonTerm σ1 -> CanonTerm σ2 -> CanonTerm σ3 :=
      match op in BinOp s1 s2 s3 return BinOp s1 s2 s3 -> CanonTerm s1 -> CanonTerm s2 -> CanonTerm s3 with
      | bop.bvadd  => fun _ => Term_Quote_bin (@PEadd _)
      | bop.bvsub  => fun _ => Term_Quote_bin (@PEsub _)
      | bop.bvmul  => fun _ => Term_Quote_bin (@PEmul _)
      | bop.shiftl => fun op' c1 c2 =>
          match term_get_val (CanonTerm_to_Term c2) with
          | Some kv => Term_Quote_unop (fun p => PEmul p (PEc (2 ^ Z.of_nat (N.to_nat (bv.bin kv)))%Z)) c1
          | None => peval2_binop_default op' c1 c2
          end
      | _          => fun op' => peval2_binop_default op'
      end op.

    Lemma peval2_binop_sound {σ1 σ2 σ3 : Ty} {op : BinOp σ1 σ2 σ3}
      {ct1 : CanonTerm σ1} {t1} {ct2 : CanonTerm σ2} {t2} :
      CanonTermRep ct1 t1 -> CanonTermRep ct2 t2 ->
      CanonTermRep (peval2_binop op ct1 ct2) (term_binop op t1 t2).
    Proof.
      intros H1 H2. destruct op; cbn [peval2_binop];
        try (now apply peval2_binop_default_sound);
        (* order-independent: the ring cases, and << *)
        first
          [ now eapply Term_Quote_bin_Valid
          | destruct (term_get_val_spec (CanonTerm_to_Term ct2)) as [kv Hkv|];
              [|now apply peval2_binop_default_sound];
            eapply CanonTermRep_equiv; [apply (quote_shiftl_valid kv H1)|];
            apply proper_term_binop; [reflexivity|];
            rewrite <- Hkv; apply CanonTermRep_adeq; exact H2 ].
    Qed.

    Definition peval2_unop_default {σ1 σ2} (op : UnOp σ1 σ2) (c : CanonTerm σ1) : CanonTerm σ2 :=
      CanonTerm_def (peval_unop op (CanonTerm_to_Term c)).

    Definition peval2_unop {σ1 σ2 : Ty} (op : UnOp σ1 σ2) : CanonTerm σ1 -> CanonTerm σ2 :=
      match op in UnOp s1 s2 return UnOp s1 s2 -> CanonTerm s1 -> CanonTerm s2 with
      | uop.negate => fun _ => Term_Quote_unop (@PEopp _)
      | _          => fun op' => peval2_unop_default op'
      end op.

    Lemma peval2_unop_sound {σ1 σ2 : Ty} {op : UnOp σ1 σ2} {ct1 : CanonTerm σ1} {t1} :
      CanonTermRep ct1 t1 -> CanonTermRep (peval2_unop op ct1) (term_unop op t1).
    Proof.
      intros H1. destruct op; cbn [peval2_unop];
        try (unfold peval2_unop_default;
             eapply CanonTermRep_equiv; [apply CanonTerm_def_sound|];
             etransitivity; [apply peval_unop_sound|];
             apply proper_term_unop; apply CanonTermRep_adeq; exact H1).
      now eapply Term_Quote_unop_Valid.
    Qed.

    Fixpoint peval2 [σ] (t : Term Σ σ) : CanonTerm σ :=
      match t with
      | term_var ς                 => CanonTerm_def (term_var ς)
      | term_val _ v               => peval2_val v
      | term_relval _ rv           => CanonTerm_def (term_relval _ rv)
      | term_binop op t1 t2        => peval2_binop op (peval2 t1) (peval2 t2)
      | term_unop op t             => peval2_unop op (peval2 t)
      | term_tuple ts              => term_tuple (env.map (fun b t => CanonTerm_to_Term (peval2 t)) ts)
      | term_union U K t           => peval_union (CanonTerm_to_Term (peval2 t))
      | term_record R ts           => peval_record R (env.map (fun b t => CanonTerm_to_Term (peval2 t)) ts)
      end.

    Lemma peval2_sound [σ] (t : Term Σ σ) : CanonTermRep (peval2 t) t.
    Proof.
      induction t; cbn.
      - now eapply CanonTerm_def_sound.
      - eapply peval2_val_sound.
      - now eapply CanonTerm_def_sound.
      - now eapply peval2_binop_sound.
      - now eapply peval2_unop_sound.
      - apply proper_term_tuple.
        induction IH; [reflexivity|]; cbn.
        apply proper_env_snoc; first trivial.
        now apply CanonTermRep_adeq.
      - etransitivity; [apply peval_union_sound|apply proper_term_union].
        now apply CanonTermRep_adeq.
      - rewrite peval_record_sound.
        apply proper_term_record.
        induction IH; cbn; [reflexivity|].
        apply proper_namedenv_snoc; first trivial.
        now apply CanonTermRep_adeq.
    Qed.

    (* main's top level: peval2 does the work, except on variables, values
       and list elements, whose type may be polymorphic in Gallina (see main's
       comment on valid_contract_length). *)
    Fixpoint peval [σ] (t : Term Σ σ) : Term Σ σ :=
      let res_poly :=
        match t in Term _ σ return option (Term Σ σ) with
        | term_var x => Some (term_var x)
        | term_val σ v => Some (term_val _ v)
        | term_relval σ rv => Some (term_relval _ rv)
        | @term_binop _ σ1 σ2 _ op t1 t2 =>
            (match op in BinOp σ1 σ2 σ3 return Term Σ σ1 -> Term Σ σ2 -> option (Term Σ σ3) with
             | bop.cons => fun t1 t2 => Some (peval_binop' bop.cons (peval t1) (peval t2))
             | _ => fun _ _ => None
             end) t1 t2
        | _ => None
        end in
      match res_poly with
      | Some t => t
      | None => CanonTerm_to_Term (peval2 t)
      end.

    Lemma peval_sound [σ] (t : Term Σ σ) : peval t ≡ t.
    Proof.
      induction t; try reflexivity.
      - destruct op; try (eapply CanonTermRep_adeq; eapply peval2_sound).
        cbn. now rewrite peval_binop'_sound, IHt1, IHt2.
      - eapply CanonTermRep_adeq; eapply peval2_sound.
      - eapply CanonTermRep_adeq; eapply peval2_sound.
      - eapply CanonTermRep_adeq; eapply peval2_sound.
      - eapply CanonTermRep_adeq; eapply peval2_sound.
    Qed.
    #[global] Arguments peval [σ] t : simpl never.

    (* Lemma peval_sound [σ] (t : Term Σ σ) : *)
    (*   peval t ≡ t. *)
    (* Proof. *)
    (*   induction t; try reflexivity. *)
    (*   - destruct op; try (eapply CanonTermRep_adeq; eapply peval2_sound); *)
    (*     cbn. *)
    (*     all: auto. *)
    (*     now rewrite peval_binop'_sound, IHt1, IHt2. *)
    (*   (* - eapply CanonTermRep_adeq; eapply peval2_sound. *) *)
    (* (*   - eapply CanonTermRep_adeq; eapply peval2_sound. *) *)
    (* (*   - eapply CanonTermRep_adeq; eapply peval2_sound. *) *)
    (* (*   - eapply CanonTermRep_adeq; eapply peval2_sound. *) *)
    (* Qed. *)
    (* #[global] Arguments peval [σ] t : simpl never. *)

    Definition pevals [Δ] : Env (Term Σ) Δ -> Env (Term Σ) Δ :=
      env.map (fun σ  t => peval t).

    Lemma pevals_sound [Δ] (ts : Env (Term Σ) Δ) :
      pevals ts ≡ ts.
    Proof.
      induction ts; [reflexivity|]; cbn.
      apply proper_env_snoc; auto using peval_sound.
    Qed.
  End WithLCtx.
End PartialEvaluationOn.


(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)


