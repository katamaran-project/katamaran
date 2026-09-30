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
End Util.

Module Type PartialEvaluationOn
  (Import TY : Types)
  (Import TM : TermsOn TY)
  (Import IN : InstantiationOn TY TM).

  Local Notation LCtx := (NCtx LVar Ty).
  Local Notation Valuation Σ := (Env (fun xt : Binding LVar Ty => Val (type xt)) Σ).

  (* ===================================================================== *)
  (* CANONICAL RING FORMS for bitvector terms (PLAN-bv-arith-solver, option *)
  (* 1; developed and self-tested in CFGVer/Example/ZZBvCore.v).  Upstream  *)
  (* had ring canonicalisation modulo ≡ (TermRing_bv, disabled in 196eae12: *)
  (* its ring_theory fails over RelVal, e.g. x - x ≢ 0 for a secret x).    *)
  (* What DOES hold, and is used here: two ring-fragment terms are equal as *)
  (* RelVals iff both PROJECTIONS agree (ring identities mod 2^n, per       *)
  (* projection) and they agree on SyncVal-ness, i.e. the same ATOMS occur  *)
  (* -- so a cancelled atom keeps coefficient 0 (x - x becomes 0 * x).      *)
  (* Atoms are ordered by a structural key; the order needs no proof       *)
  (* (merging uses Term_eqb, and reordering a sum preserves its value).    *)
  (* ===================================================================== *)
  Local Notation RValuation Σ := (Env (fun xt : Binding LVar Ty => RelVal (type xt)) Σ).
  Local Open Scope Z_scope.

Lemma small_diff_zero (K u1 u2 : Z) : 0 < K -> 0 <= u1 < K -> 0 <= u2 < K -> (u1 - u2) mod K = 0 -> u1 = u2.
Proof.
  intros HM H1 H2 H.
  destruct (Z_le_gt_dec u2 u1) as [Hle|Hgt].
  - rewrite Z.mod_small in H; lia.
  - assert (H' : (u2 - u1) mod K = 0).
    { replace (u2 - u1) with (- (u1 - u2)) by lia. apply Z_mod_zero_opp_full. exact H. }
    rewrite Z.mod_small in H'; lia.
Qed.

Definition rv_proj (side : bool) {σ} (v : RelVal σ) : Val σ :=
  if side then ty.projLeft v else ty.projRight v.

(* ---- the view: one Equations matcher, NON-dependent result.  The width is
   the matcher's OWN implicit argument: as a Section parameter Equations
   cannot build the covering (the width-index trap). ---- *)
Inductive LinView {Σ : LCtx} {n : nat} : Type :=
| VAdd (a b : Term Σ (ty.bvec n))
| VSub (a b : Term Σ (ty.bvec n))
| VNeg (a : Term Σ (ty.bvec n))
| VShl (a : Term Σ (ty.bvec n)) (k : nat)
| VMulC (c : bv n) (a : Term Σ (ty.bvec n))
| VVal (v : bv n)
| VAtom.
Arguments LinView : clear implicits.

Equations lin_view {Σ n} (t : Term Σ (ty.bvec n)) : LinView Σ n :=
  lin_view (term_val _ v) := VVal v;
  lin_view (term_binop bop.bvadd a b) := VAdd a b;
  lin_view (term_binop bop.bvsub a b) := VSub a b;
  lin_view (term_unop uop.negate a) := VNeg a;
  lin_view (term_binop bop.shiftl a (term_val _ k)) := VShl a (N.to_nat (bv.bin k));
  lin_view (term_binop bop.bvmul (term_val _ c) a) := VMulC c a;
  lin_view _ := VAtom.

Lemma lin_view_spec {Σ n} (t : Term Σ (ty.bvec n)) :
  match lin_view t with
  | VAdd a b => t = term_binop bop.bvadd a b
  | VSub a b => t = term_binop bop.bvsub a b
  | VNeg a => t = term_unop uop.negate a
  | VShl a k => exists m (kv : bv m), t = term_binop bop.shiftl a (term_val (ty.bvec m) kv)
                                /\ k = N.to_nat (bv.bin kv)
  | VMulC c a => t = term_binop bop.bvmul (term_val (ty.bvec n) c) a
  | VVal v => t = term_val (ty.bvec n) v
  | VAtom => True
  end.
Proof. funelim (lin_view t); try reflexivity; try exact I. eexists _, _; split; reflexivity. Qed.

Section Lin.
  Context {Σ : LCtx} {n : nat}.

  Local Notation T := (Term Σ (ty.bvec n)).

  (* ---- linear forms ---- *)
  Definition LinForm : Type := (Z * list (Z * T))%type.

  Definition lf_const (c : Z) : LinForm := (c, nil).
  Definition lf_atom (t : T) : LinForm := (0, cons (1, t) nil).
  Definition lf_add (f g : LinForm) : LinForm := (fst f + fst g, List.app (snd f) (snd g)).
  Definition lf_scale (k : Z) (f : LinForm) : LinForm :=
    (k * fst f, List.map (fun '(a, t) => (k * a, t)) (snd f)).

  Fixpoint lin (fuel : nat) (t : T) : LinForm :=
    match fuel with
    | O => lf_atom t
    | S f =>
        match lin_view t with
        | VVal v => lf_const (bv.unsigned v)
        | VAdd a b => lf_add (lin f a) (lin f b)
        | VSub a b => lf_add (lin f a) (lf_scale (-1) (lin f b))
        | VNeg a => lf_scale (-1) (lin f a)
        | VShl a k => lf_scale (2 ^ Z.of_nat k) (lin f a)
        | VMulC c a => lf_scale (bv.unsigned c) (lin f a)
        | VAtom => lf_atom t
        end
    end.

  (* ---- semantics, per projection ---- *)
  Definition uval (side : bool) (ι : RValuation Σ) (t : T) : Z :=
    bv.unsigned (rv_proj side (inst t ι)).

  Fixpoint lf_sum (side : bool) (ι : RValuation Σ) (l : list (Z * T)) : Z :=
    match l with
    | nil => 0
    | cons (a, t) l => a * uval side ι t + lf_sum side ι l
    end.

  Definition lf_z (side : bool) (ι : RValuation Σ) (f : LinForm) : Z :=
    fst f + lf_sum side ι (snd f).

  Lemma lf_sum_app side ι l1 l2 : lf_sum side ι (List.app l1 l2) = lf_sum side ι l1 + lf_sum side ι l2.
  Proof. induction l1 as [|[a t] l1 IH]; cbn; [lia|]. rewrite IH. lia. Qed.

  Lemma lf_sum_scale side ι k l :
    lf_sum side ι (List.map (fun '(a, t) => (k * a, t)) l) = k * lf_sum side ι l.
  Proof. induction l as [|[a t] l IH]; cbn; [lia|]. rewrite IH. lia. Qed.

  Lemma lf_z_add side ι f g : lf_z side ι (lf_add f g) = lf_z side ι f + lf_z side ι g.
  Proof. unfold lf_z, lf_add; cbn. rewrite lf_sum_app. lia. Qed.

  Lemma lf_z_scale side ι k f : lf_z side ι (lf_scale k f) = k * lf_z side ι f.
  Proof. unfold lf_z, lf_scale; cbn. rewrite lf_sum_scale. lia. Qed.

  Local Notation M := (2 ^ Z.of_nat n).

  (* ---- the per-constructor facts on unsigned values ---- *)
  Lemma uval_bvadd side ι a b :
    uval side ι (term_binop bop.bvadd a b) = (uval side ι a + uval side ι b) mod M.
  Proof.
    unfold uval. destruct side; cbn; destruct (inst a ι), (inst b ι);
      cbn; apply bv.unsigned_add.
  Qed.
  Lemma lf_M_pos : 0 < M.
  Proof. apply Z.pow_pos_nonneg; lia. Qed.

  Lemma uval_bounds side ι t : 0 <= uval side ι t < M.
  Proof. unfold uval. apply bv.unsigned_bounds. Qed.

  Lemma uval_val side ι (v : bv n) : uval side ι (term_val (ty.bvec n) v) = bv.unsigned v.
  Proof. unfold uval. destruct side; reflexivity. Qed.

  Lemma uval_bvsub side ι a b :
    uval side ι (term_binop bop.bvsub a b) = (uval side ι a - uval side ι b) mod M.
  Proof.
    unfold uval. destruct side; cbn; destruct (inst a ι), (inst b ι);
      cbn; apply bv.unsigned_sub.
  Qed.

  Lemma uval_negate side ι a :
    uval side ι (term_unop uop.negate a) = (- uval side ι a) mod M.
  Proof.
    unfold uval. destruct side; cbn; destruct (inst a ι); cbn; apply bv.unsigned_negate.
  Qed.

  Lemma uval_shiftl side ι a {m} (kv : bv m) :
    uval side ι (term_binop bop.shiftl a (term_val (ty.bvec m) kv))
    = (uval side ι a * 2 ^ Z.of_nat (N.to_nat (bv.bin kv))) mod M.
  Proof.
    unfold uval.
    assert (E : forall x : bv n, bv.unsigned (bv.shiftl x kv)
                  = (bv.unsigned x * 2 ^ Z.of_nat (N.to_nat (bv.bin kv))) mod M).
    { intros x. unfold bv.shiftl. rewrite bv.unsigned_of_Z. unfold bv.truncz.
      rewrite Z.shiftl_mul_pow2; [|unfold bv.unsigned; lia].
      rewrite N_nat_Z. reflexivity. }
    destruct side; cbn; destruct (inst a ι); cbn; apply E.
  Qed.

  Lemma uval_bvmul side (ι : RValuation Σ) (x : bv n) (a : T) :
    uval side ι (term_binop bop.bvmul (term_val (ty.bvec n) x) a) = (bv.unsigned x * uval side ι a) mod M.
  Proof. unfold uval. destruct side; cbn; destruct (inst a ι); cbn; apply bv.unsigned_mul. Qed.

  Lemma lf_atom_z side ι t : lf_z side ι (lf_atom t) = uval side ι t.
  Proof. unfold lf_z, lf_atom; cbn. lia. Qed.

  (* THE soundness of the normal form, per projection *)
  Lemma lin_sound side ι fuel t : lf_z side ι (lin fuel t) mod M = uval side ι t.
  Proof.
    pose proof lf_M_pos as HM.
    revert t; induction fuel as [|f IH]; intros t; cbn [lin].
    { rewrite lf_atom_z. apply Z.mod_small, uval_bounds. }
    pose proof (lin_view_spec t) as Hv.
    destruct (lin_view t) as [a b|a b|a|a k|c a|v|]; cbn in Hv.
    - subst t. rewrite lf_z_add. rewrite uval_bvadd. rewrite Z.add_mod; [|lia].
      rewrite !IH. reflexivity.
    - subst t. rewrite lf_z_add. rewrite lf_z_scale. rewrite uval_bvsub.
      replace (lf_z side ι (lin f a) + -1 * lf_z side ι (lin f b))
        with (lf_z side ι (lin f a) - lf_z side ι (lin f b)) by lia.
      rewrite Zminus_mod. rewrite !IH. reflexivity.
    - subst t. rewrite lf_z_scale. rewrite uval_negate.
      replace (-1 * lf_z side ι (lin f a)) with (- lf_z side ι (lin f a)) by lia.
      rewrite <- IH.
      set (X := lf_z side ι (lin f a)).
      replace (- X) with (0 - X) by lia. replace (- (X mod M)) with (0 - X mod M) by lia.
      rewrite (Zminus_mod 0 X). rewrite (Zminus_mod 0 (X mod M)).
      rewrite Z.mod_mod; [|lia]. reflexivity.
    - destruct Hv as (m & kv & -> & ->). rewrite lf_z_scale. rewrite uval_shiftl.
      rewrite Z.mul_comm. rewrite Z.mul_mod; [|lia]. rewrite IH.
      rewrite Z.mul_mod_idemp_r; [reflexivity|lia].
    - subst t. rewrite lf_z_scale. rewrite uval_bvmul.
      rewrite <- (Z.mul_mod_idemp_r (bv.unsigned c) (lf_z side ι (lin f a))); [|lia].
      rewrite IH. reflexivity.
    - subst t. unfold lf_z, lf_const; cbn. rewrite uval_val. rewrite Z.add_0_r.
      apply Z.mod_small, bv.unsigned_bounds.
    - rewrite lf_atom_z. apply Z.mod_small, uval_bounds.
  Qed.

  (* ---- merging equal atoms (Term_eqb), dropping zero coefficients ---- *)
  Fixpoint lf_insert (a : Z) (t : T) (l : list (Z * T)) : list (Z * T) :=
    match l with
    | nil => cons (a, t) nil
    | cons (b, u) l' => if Term_eqb t u then cons (a + b, u) l'
                        else cons (b, u) (lf_insert a t l')
    end.

  Lemma lf_insert_sum side ι a t l :
    lf_sum side ι (lf_insert a t l) = a * uval side ι t + lf_sum side ι l.
  Proof.
    induction l as [|[b u] l IH]; cbn; [lia|].
    destruct (Term_eqb_spec t u) as [->|_]; cbn; [lia|]. rewrite IH. lia.
  Qed.

  Fixpoint lf_merge (l : list (Z * T)) : list (Z * T) :=
    match l with
    | nil => nil
    | cons (a, t) l' => lf_insert a t (lf_merge l')
    end.

  Lemma lf_merge_sum side ι l : lf_sum side ι (lf_merge l) = lf_sum side ι l.
  Proof.
    induction l as [|[a t] l IH]; cbn; [lia|]. rewrite lf_insert_sum. rewrite IH. lia.
  Qed.

  Definition lf_drop0 (l : list (Z * T)) : list (Z * T) :=
    List.filter (fun '(a, _) => negb (a mod M =? 0)) l.

  Lemma lf_drop0_sum side ι l : lf_sum side ι (lf_drop0 l) mod M = lf_sum side ι l mod M.
  Proof.
    pose proof lf_M_pos as HM. unfold lf_drop0 in *.
    induction l as [|[a t] l IH]; [reflexivity|]. cbn [List.filter].
    destruct (Z.eqb_spec (a mod M) 0) as [Ha|Ha]; cbn [negb lf_sum].
    - rewrite IH. rewrite (Z.add_mod (a * uval side ι t)); [|lia].
      rewrite (Z.mul_mod a); [|lia]. rewrite Ha. rewrite Z.mul_0_l.
      rewrite (Z.mod_0_l M); [|lia]. rewrite Z.add_0_l. rewrite Z.mod_mod; [reflexivity|lia].
    - rewrite Z.add_mod; [|lia]. rewrite IH. rewrite <- Z.add_mod; [reflexivity|lia].
  Qed.

  Definition lf_norm (f : LinForm) : LinForm := (fst f, lf_drop0 (lf_merge (snd f))).

  Lemma lf_norm_z side ι f : lf_z side ι (lf_norm f) mod M = lf_z side ι f mod M.
  Proof.
    pose proof lf_M_pos as HM. unfold lf_z, lf_norm; cbn.
    rewrite Z.add_mod; [|lia]. rewrite lf_drop0_sum. rewrite lf_merge_sum.
    rewrite <- Z.add_mod; [reflexivity|lia].
  Qed.

  (* ---- the difference of two terms, normalised ---- *)
  Definition lin_fuel : nat := 64.
  Definition lin_diff (t1 t2 : T) : LinForm :=
    lf_norm (lf_add (lin lin_fuel t1) (lf_scale (-1) (lin lin_fuel t2))).

  Lemma lin_diff_z side ι t1 t2 :
    lf_z side ι (lin_diff t1 t2) mod M = (uval side ι t1 - uval side ι t2) mod M.
  Proof.
    pose proof lf_M_pos as HM. unfold lin_diff. rewrite lf_norm_z. rewrite lf_z_add. rewrite lf_z_scale.
    replace (lf_z side ι (lin lin_fuel t1) + -1 * lf_z side ι (lin lin_fuel t2))
      with (lf_z side ι (lin lin_fuel t1) - lf_z side ι (lin lin_fuel t2)) by lia.
    rewrite Zminus_mod. rewrite !lin_sound. reflexivity.
  Qed.

  Definition lf_closed (f : LinForm) : bool :=
    match snd f with nil => true | _ => false end.

  (* The decisions go through lf_closed_z, so no cbn ever meets lin_diff:
     unfolding its fuel-64 recursion made even Qed hang. *)
  Lemma lf_closed_z side ι (f : LinForm) : lf_closed f = true -> lf_z side ι f = fst f.
  Proof. intros H. destruct f as [c [|]]; unfold lf_z; cbn in *; [lia|discriminate]. Qed.

  (* equal normal forms: equal values, on BOTH projections *)
  Lemma lin_diff_zero side ι t1 t2 :
    lf_closed (lin_diff t1 t2) = true -> fst (lin_diff t1 t2) mod M = 0 ->
    uval side ι t1 = uval side ι t2.
  Proof.
    pose proof lf_M_pos as HM. intros Hc H0.
    pose proof (lin_diff_z side ι t1 t2) as Hz.
    rewrite (lf_closed_z side ι _ Hc) in Hz. rewrite H0 in Hz.
    apply (small_diff_zero (K := M)); [lia|apply uval_bounds|apply uval_bounds|lia].
  Qed.

  (* forms differing by a constant that is nonzero mod 2^n: different values *)
  Lemma lin_diff_const side ι t1 t2 :
    lf_closed (lin_diff t1 t2) = true -> fst (lin_diff t1 t2) mod M <> 0 ->
    uval side ι t1 <> uval side ι t2.
  Proof.
    pose proof lf_M_pos as HM. intros Hc H0 E.
    pose proof (lin_diff_z side ι t1 t2) as Hz.
    rewrite (lf_closed_z side ι _ Hc) in Hz. rewrite E in Hz. rewrite Z.sub_diag in Hz.
    rewrite Z.mod_0_l in Hz; lia.
  Qed.
End Lin.

(* ========================================================================= *)
(* Part 3 (R1): SyncVal-ness.  A lifted op is SyncVal iff its operands are, so *)
(* a ring-fragment term is SyncVal iff every ATOM of its linear form is.  With *)
(* the projections (lin_sound) this pins down the RelVal exactly.             *)
(* ========================================================================= *)
Definition is_sync {σ} (v : RelVal σ) : bool :=
  match v with ty.SyncVal _ => true | ty.NonSyncVal _ _ => false end.

Lemma relval_ext {σ} (u v : RelVal σ) :
  is_sync u = is_sync v -> ty.projLeft u = ty.projLeft v -> ty.projRight u = ty.projRight v -> u = v.
Proof. destruct u, v; cbn; intros; try discriminate; subst; reflexivity. Qed.

Section Sync.
  Context {Σ : LCtx} {n : nat}.
  Local Notation T := (Term Σ (ty.bvec n)).

  Definition lf_sync (ι : RValuation Σ) (l : list (Z * T)) : bool :=
    List.forallb (fun p => is_sync (inst (snd p) ι)) l.

  Lemma lf_sync_app ι l1 l2 : lf_sync ι (List.app l1 l2) = andb (lf_sync ι l1) (lf_sync ι l2).
  Proof. unfold lf_sync. apply List.forallb_app. Qed.

  Lemma lf_sync_scale ι k l :
    lf_sync ι (List.map (fun '(a, t) => (k * a, t)) l) = lf_sync ι l.
  Proof. unfold lf_sync. induction l as [|[a t] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

  Lemma sync_bin (ι : RValuation Σ) (op : BinOp (ty.bvec n) (ty.bvec n) (ty.bvec n)) (a b : T) :
    is_sync (inst (term_binop op a b) ι) = andb (is_sync (inst a ι)) (is_sync (inst b ι)).
  Proof. cbn. destruct (inst a ι), (inst b ι); reflexivity. Qed.

  Lemma sync_shl (ι : RValuation Σ) (a : T) {m} (kv : bv m) :
    is_sync (inst (term_binop bop.shiftl a (term_val (ty.bvec m) kv)) ι) = is_sync (inst a ι).
  Proof. cbn. destruct (inst a ι); reflexivity. Qed.

  Lemma sync_neg (ι : RValuation Σ) (a : T) :
    is_sync (inst (term_unop uop.negate a) ι) = is_sync (inst a ι).
  Proof. cbn. destruct (inst a ι); reflexivity. Qed.

  Lemma lin_sync ι fuel t : is_sync (inst t ι) = lf_sync ι (snd (lin fuel t)).
  Proof.
    revert t; induction fuel as [|f IH]; intros t; cbn [lin].
    { unfold lf_sync, lf_atom; cbn. rewrite Bool.andb_true_r. reflexivity. }
    pose proof (lin_view_spec t) as Hv.
    destruct (lin_view t) as [a b|a b|a|a k|c a|v|]; cbn in Hv.
    - subst t. rewrite sync_bin. unfold lf_add; cbn [snd]. rewrite lf_sync_app. rewrite !IH. reflexivity.
    - subst t. rewrite sync_bin. unfold lf_add, lf_scale; cbn [snd]. rewrite lf_sync_app.
      rewrite lf_sync_scale. rewrite !IH. reflexivity.
    - subst t. rewrite sync_neg. unfold lf_scale; cbn [snd]. rewrite lf_sync_scale. apply IH.
    - destruct Hv as (m & kv & -> & ->). rewrite sync_shl. unfold lf_scale; cbn [snd].
      rewrite lf_sync_scale. apply IH.
    - subst t. rewrite sync_bin. unfold lf_scale; cbn [snd]. rewrite lf_sync_scale. apply IH.
    - subst t. reflexivity.
    - unfold lf_sync, lf_atom; cbn. rewrite Bool.andb_true_r. reflexivity.
  Qed.
End Sync.

(* ========================================================================= *)
(* Part 4 (R1): the canonical form.  Order atoms by a structural key (needs   *)
(* NO correctness proof: reordering a sum never changes its value), reduce    *)
(* coefficients mod 2^n KEEPING zeros (so the atom set, hence SyncVal-ness,   *)
(* is preserved), and rebuild: constant leftmost, right-nested sum, k*a      *)
(* spelled a (k = 1), a << j (k = 2^j), else bvmul (val k) a.                *)
(* ========================================================================= *)
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
  | @term_var _ _ _ lIn => cons 0 (cons (Z.of_nat (ctx.in_at lIn)) nil)
  | term_val σ v => cons 1 (val_key σ v)
  | term_relval _ _ => cons 2 nil
  | term_binop op t1 t2 => cons 3 (cons (binop_tag op) (List.app (term_key t1) (term_key t2)))
  | term_unop op t => cons 4 (cons (unop_tag op) (term_key t))
  | _ => cons 9 nil
  end.

Fixpoint key_le (a b : list Z) : bool :=
  match a, b with
  | nil, _ => true
  | cons _ _, nil => false
  | cons x a', cons y b' => if x <? y then true else if y <? x then false else key_le a' b'
  end.

Section Canon.
  Context {Σ : LCtx} {n : nat}.
  Local Notation T := (Term Σ (ty.bvec n)).
  Local Notation M := (2 ^ Z.of_nat n).
  Implicit Types (ι : RValuation Σ) (l : list (Z * T)) (t : T) (f : @LinForm Σ n) (p q : Z * T).

  Fixpoint lf_ins (p : Z * T) (l : list (Z * T)) : list (Z * T) :=
    match l with
    | nil => cons p nil
    | cons q l' => if key_le (term_key (snd p)) (term_key (snd q)) then cons p l else cons q (lf_ins p l')
    end.

  Fixpoint isort (l : list (Z * T)) : list (Z * T) :=
    match l with nil => nil | cons p l' => lf_ins p (isort l') end.

  Lemma ins_perm p l : Permutation (cons p l) (lf_ins p l).
  Proof.
    induction l as [|q l IH]; cbn; [reflexivity|].
    destruct (key_le _ _); [reflexivity|].
    etransitivity; [apply perm_swap|]. apply perm_skip. exact IH.
  Qed.

  Lemma isort_perm l : Permutation l (isort l).
  Proof.
    induction l as [|p l IH]; cbn; [reflexivity|].
    etransitivity; [apply perm_skip; exact IH|]. apply ins_perm.
  Qed.

  Lemma lf_sum_perm side ι (l1 l2 : list (Z * T)) : Permutation l1 l2 -> lf_sum side ι l1 = lf_sum side ι l2.
  Proof. induction 1 as [|[a t] l1 l2 _ IH|[a t] [b u] l|]; cbn; lia. Qed.

  Lemma lf_sync_perm ι (l1 l2 : list (Z * T)) : Permutation l1 l2 -> lf_sync ι l1 = lf_sync ι l2.
  Proof.
    unfold lf_sync. induction 1 as [|x l1 l2 _ IH|x y l|l1 l2 l3 _ IH1 _ IH2]; cbn.
    - reflexivity.
    - rewrite IH. reflexivity.
    - destruct (is_sync (inst (snd x) ι)), (is_sync (inst (snd y) ι)); reflexivity.
    - etransitivity; [exact IH1|exact IH2].
  Qed.

  Lemma lf_sync_insert ι a t l :
    lf_sync ι (lf_insert a t l) = andb (is_sync (inst t ι)) (lf_sync ι l).
  Proof.
    unfold lf_sync. induction l as [|[b u] l IH]; cbn; [reflexivity|].
    destruct (Term_eqb_spec t u) as [->|_]; cbn.
    - destruct (is_sync (inst u ι)); reflexivity.
    - rewrite IH. destruct (is_sync (inst t ι)), (is_sync (inst u ι)); reflexivity.
  Qed.

  Lemma lf_sync_merge ι l : lf_sync ι (lf_merge l) = lf_sync ι l.
  Proof.
    induction l as [|[a t] l IH]; cbn [lf_merge]; [reflexivity|].
    rewrite lf_sync_insert. rewrite IH. reflexivity.
  Qed.

  Definition lf_modk (l : list (Z * T)) : list (Z * T) :=
    List.map (fun '(k, a) => (k mod M, a)) l.

  Lemma lf_modk_sum side ι l : lf_sum side ι (lf_modk l) mod M = lf_sum side ι l mod M.
  Proof.
    pose proof (@lf_M_pos n) as HM. unfold lf_modk in *.
    induction l as [|[k a] l IH]; cbn; [reflexivity|].
    rewrite Z.add_mod; [|lia]. rewrite IH. rewrite (Z.mul_mod (k mod M)); [|lia].
    rewrite Z.mod_mod; [|lia]. rewrite <- Z.mul_mod; [|lia]. rewrite <- Z.add_mod; [reflexivity|lia].
  Qed.

  Lemma lf_modk_sync ι l : lf_sync ι (lf_modk l) = lf_sync ι l.
  Proof. unfold lf_sync, lf_modk. induction l as [|[k a] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

  Definition canon_lf (f : LinForm) : LinForm :=
    (fst f mod M, isort (lf_modk (lf_merge (snd f)))).

  Lemma canon_lf_z side ι f : lf_z side ι (canon_lf f) mod M = lf_z side ι f mod M.
  Proof.
    pose proof (@lf_M_pos n) as HM. unfold lf_z, canon_lf; cbn [fst snd].
    rewrite <- (lf_sum_perm side ι (isort_perm _)).
    rewrite Z.add_mod; [|lia]. rewrite Z.mod_mod; [|lia].
    rewrite (lf_modk_sum side ι (lf_merge (snd f))).
    rewrite (lf_merge_sum side ι (snd f)). rewrite <- Z.add_mod; [reflexivity|lia].
  Qed.

  Lemma canon_lf_sync ι f : lf_sync ι (snd (canon_lf f)) = lf_sync ι (snd f).
  Proof.
    unfold canon_lf; cbn [snd]. rewrite <- (lf_sync_perm ι (isort_perm _)).
    rewrite lf_modk_sync. apply lf_sync_merge.
  Qed.

  (* ---- rebuilding ---- *)
  Definition pow2_exp (k : Z) : option nat :=
    let j := Z.to_nat (Z.log2 k) in
    if andb (andb (1 <? k) (2 ^ Z.of_nat j =? k)) (Nat.ltb j 32) then Some j else None.

  Lemma pow2_exp_spec k j : pow2_exp k = Some j -> 2 ^ Z.of_nat j = k /\ (j < 32)%nat.
  Proof.
    unfold pow2_exp. destruct (1 <? k), (Z.eqb_spec (2 ^ Z.of_nat (Z.to_nat (Z.log2 k))) k),
      (Nat.ltb_spec (Z.to_nat (Z.log2 k)) 32); cbn; intros Hs; try discriminate.
    inversion Hs; subst. auto.
  Qed.

  Definition lf_sc (p : Z * T) : T :=
    let '(k, a) := p in
    if k =? 1 then a
    else if k =? M - 1 then term_unop uop.negate a
    else match pow2_exp k with
         | Some j => term_binop bop.shiftl a (term_val (ty.bvec 5) (bv.of_nat j))
         | None => term_binop bop.bvmul (term_val (ty.bvec n) (bv.of_Z k)) a
         end.

  Lemma sc_uval side ι k a : uval side ι (lf_sc (k, a)) = (k * uval side ι a) mod M.
  Proof.
    pose proof (@lf_M_pos n) as HM. unfold lf_sc.
    destruct (Z.eqb_spec k 1) as [->|Hk].
    { rewrite Z.mul_1_l. symmetry. apply Z.mod_small, uval_bounds. }
    destruct (Z.eqb_spec k (M - 1)) as [->|Hk'].
    { rewrite uval_negate. replace ((M - 1) * uval side ι a) with (- uval side ι a + uval side ι a * M) by lia.
      rewrite Z.mod_add; [reflexivity|lia]. }
    destruct (pow2_exp k) as [j|] eqn:Ej.
    - destruct (pow2_exp_spec k Ej) as [Hj Hj32]. rewrite uval_shiftl.
      rewrite bv.bin_of_nat_small.
      + rewrite Nat2N.id. rewrite Hj. rewrite Z.mul_comm. reflexivity.
      + cbn. lia.
    - rewrite uval_bvmul. rewrite bv.unsigned_of_Z. unfold bv.truncz.
      rewrite Z.mul_mod_idemp_l; [reflexivity|lia].
  Qed.

  Lemma sc_sync ι k a : is_sync (inst (lf_sc (k, a)) ι) = is_sync (inst a ι).
  Proof.
    unfold lf_sc. destruct (k =? 1); [reflexivity|].
    destruct (k =? M - 1); [apply sync_neg|].
    destruct (pow2_exp k); [apply sync_shl|]. rewrite sync_bin. reflexivity.
  Qed.

  Fixpoint sum_of (p : Z * T) (l : list (Z * T)) : T :=
    match l with
    | nil => lf_sc p
    | cons q l' => term_binop bop.bvadd (lf_sc p) (sum_of q l')
    end.

  Lemma sum_of_uval side ι p l : uval side ι (sum_of p l) = lf_sum side ι (cons p l) mod M.
  Proof.
    pose proof (@lf_M_pos n) as HM. revert p. induction l as [|q l IH]; intros [k a]; cbn [sum_of].
    - rewrite sc_uval. cbn. rewrite Z.add_0_r. reflexivity.
    - rewrite uval_bvadd. rewrite sc_uval. rewrite IH. destruct q as [k' a'].
      cbn [lf_sum]. rewrite <- Z.add_mod; [reflexivity|lia].
  Qed.

  Lemma sum_of_sync ι p l : is_sync (inst (sum_of p l) ι) = lf_sync ι (cons p l).
  Proof.
    revert p. induction l as [|q l IH]; intros [k a]; cbn [sum_of].
    - rewrite sc_sync. unfold lf_sync; cbn. rewrite Bool.andb_true_r. reflexivity.
    - rewrite sync_bin. rewrite sc_sync. rewrite IH. reflexivity.
  Qed.

  Definition rebuild (f : @LinForm Σ n) : T :=
    match snd f with
    | nil => term_val (ty.bvec n) (bv.of_Z (fst f))
    | cons p l =>
        if fst f mod M =? 0 then sum_of p l
        else term_binop bop.bvadd (term_val (ty.bvec n) (bv.of_Z (fst f))) (sum_of p l)
    end.

  Lemma rebuild_uval side ι f : uval side ι (rebuild f) = lf_z side ι f mod M.
  Proof.
    pose proof (@lf_M_pos n) as HM. unfold rebuild, lf_z. destruct f as [c l]; cbn [fst snd].
    destruct l as [|p l].
    - rewrite uval_val. rewrite bv.unsigned_of_Z. unfold bv.truncz. cbn. rewrite Z.add_0_r. reflexivity.
    - destruct (Z.eqb_spec (c mod M) 0) as [Hc|Hc].
      + rewrite sum_of_uval. rewrite Z.add_mod; [|lia]. rewrite Hc. rewrite Z.add_0_l.
        rewrite Z.mod_mod; [reflexivity|lia].
      + rewrite uval_bvadd. rewrite uval_val. rewrite sum_of_uval. rewrite bv.unsigned_of_Z.
        unfold bv.truncz. rewrite <- Z.add_mod; [reflexivity|lia].
  Qed.

  Lemma rebuild_sync ι f : is_sync (inst (rebuild f) ι) = lf_sync ι (snd f).
  Proof.
    unfold rebuild. destruct f as [c l]; cbn [fst snd]. destruct l as [|p l]; [reflexivity|].
    destruct (c mod M =? 0); [apply sum_of_sync|]. rewrite sync_bin. apply sum_of_sync.
  Qed.

  (* ---- THE canonical form, and its exact soundness over RelVal ---- *)
  Definition canon_term (t : T) : T := rebuild (canon_lf (lin lin_fuel t)).

  Lemma uval_ext (u v : T) ι :
    (forall side, uval side ι u = uval side ι v) -> is_sync (inst u ι) = is_sync (inst v ι) ->
    inst u ι = inst v ι.
  Proof.
    intros Hu Hs. apply relval_ext; [exact Hs| |].
    - apply bv.unsigned_inj. exact (Hu true).
    - apply bv.unsigned_inj. exact (Hu false).
  Qed.

  Theorem canon_sound ι t : inst (canon_term t) ι = inst t ι.
  Proof.
    apply uval_ext.
    - intros side. unfold canon_term. rewrite rebuild_uval. rewrite canon_lf_z. apply lin_sound.
    - unfold canon_term. rewrite rebuild_sync. rewrite canon_lf_sync. symmetry. apply lin_sync.
  Qed.
End Canon.


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
        ; tmr_ring_morph : ring_morph (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one)
                             (term_binop tmr_plus) (term_binop tmr_times) (term_binop tmr_minus)
                             (term_unop tmr_negate) base.equiv 0%Z 1%Z
                             Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool (λ c : Z, term_val σ (tmr_of_Z c))
        ; tmr_ring_theory : ring_theory (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one) (term_binop tmr_plus) (term_binop tmr_times) (term_binop tmr_minus) (term_unop tmr_negate) base.equiv
        ; tmr_ring_eq_ext : ring_eq_ext (term_binop (Σ := Σ) tmr_plus) (term_binop tmr_times) (term_unop tmr_negate) base.equiv
        }.

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

    Definition CanonTerm σ : Type :=
      match σ with
      | ty.bvec n => RQuote σ
      | ty.int => RQuote σ
      | _ => Term Σ σ
      end.

    #[export] Instance equiv_CanonTerm {σ} : base.Equiv (CanonTerm σ)
      := match σ with
         | ty.bvec n => (eq ==> eq ==> base.prod_relation eq base.equiv)%signature
         | ty.int => (eq ==> eq ==> base.prod_relation eq base.equiv)%signature
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

    (* TODO: Comment out some stuff because I am too lazy to prove their soundness *)
    Definition peval_binop {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) :
      Term Σ σ1 → Term Σ σ2 → Term Σ σ :=
      match op with
      (* | bop.append => peval_append *)
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
    Proof. intros ι. apply canon_sound. Qed.

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

    Hint Resolve peval_binop'_sound (* peval_append_sound *) peval_and_sound
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

    Definition peval_unop {σ1 σ2} (op : UnOp σ1 σ2) : Term Σ σ1 -> Term Σ σ2 :=
      match op with
      | uop.not                       => peval_not
      | uop.bvnot                     => peval_bvnot
      | uop.negate                    => fun t => canon_term (term_unop uop.negate t)
      (* | uop.unsigned                  => peval_unsigned *)
      (* | uop.vector_subrange start len => peval_vector_subrange start len *)
      (* | uop.bvdrop m                  => peval_bvdrop m *)
      (* | uop.bvtake m                  => peval_bvtake m *)
      | op                            => peval_unop' op
      end.

    (* Note that we evaluate polynomials using the peval_binop' functions.
     * This gets rid of some remaining redexes left by the ring solver, particularly it tends to produce
     * `term_unop uop.negate (term_val ty.int 1%Z)` rather than `(term_val ty.int (-1)%Z)`.
     *)
    Definition evalPolTm `{TermRing σ} : list (Term Σ σ) -> Pol Z -> Term Σ σ :=
      Pphi_dev (term_val σ tmr_zero)
        (term_val σ tmr_one)
        (peval_binop' tmr_plus)
        (peval_binop' tmr_times)
        (peval_binop' tmr_minus)
        (peval_unop' tmr_negate)
        0%Z 1%Z Zbool.Zeq_bool
        (fun c => term_val σ (tmr_of_Z c))
        get_signZ.

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

    Lemma peval_unop_sound {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) :
      peval_unop op t ≡ term_unop op t.
    Proof.
      destruct op; cbn [peval_unop];
        auto using peval_unop'_sound, peval_not_sound, peval_bvnot_sound, canon_term_equiv(* , peval_unsigned_sound, *)
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

    Lemma tmr_ring_morph_peval' `{TermRing σ}
      {rm : ring_morph (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one)
         (term_binop tmr_plus) (term_binop tmr_times) (term_binop tmr_minus)
         (term_unop tmr_negate) base.equiv 0%Z 1%Z
         Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool (λ c : Z, term_val σ (tmr_of_Z c))} :
      ring_morph (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one)
        (peval_binop' tmr_plus) (peval_binop' tmr_times) (peval_binop' tmr_minus)
        (peval_unop' tmr_negate) base.equiv 0%Z 1%Z
        Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool (λ c : Z, term_val σ (tmr_of_Z c)).
    Proof.
      constructor; intros; rewrite ?peval_binop'_sound, ?peval_unop'_sound.
      - apply (morph0 rm).
      - apply (morph1 rm).
      - apply (morph_add rm).
      - apply (morph_sub rm).
      - apply (morph_mul rm).
      - apply (morph_opp rm).
      - now apply (morph_eq rm).
    Qed.

    Lemma tmr_ring_theory_peval' `{TermRing σ}
      {rt : ring_theory (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one) (term_binop tmr_plus) (term_binop tmr_times) (term_binop tmr_minus) (term_unop tmr_negate) base.equiv} :
      ring_theory (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one) (peval_binop' tmr_plus) (peval_binop' tmr_times) (peval_binop' tmr_minus) (peval_unop' tmr_negate) base.equiv.
    Proof.
      constructor; intros; rewrite ?peval_binop'_sound, ?peval_unop'_sound.
      - apply (Radd_0_l rt).
      - apply (Radd_comm rt).
      - apply (Radd_assoc rt).
      - apply (Rmul_1_l rt).
      - apply (Rmul_comm rt).
      - apply (Rmul_assoc rt).
      - apply (Rdistr_l rt).
      - apply (Rsub_def rt).
      - apply (Ropp_def rt).
    Qed.

    Lemma tmr_ring_eq_ext_peval' `{TermRing σ}
      {ree : ring_eq_ext (term_binop (Σ := Σ) tmr_plus) (term_binop tmr_times) (term_unop tmr_negate) base.equiv} :
      ring_eq_ext (peval_binop' tmr_plus) (peval_binop' tmr_times) (peval_unop' tmr_negate) base.equiv.
    Proof.
      constructor; repeat intros ? ? ?; rewrite ?peval_binop'_sound, ?peval_unop'_sound.
      - now apply (Radd_ext ree).
      - now apply (Rmul_ext ree).
      - now apply (Ropp_ext ree).
    Qed.

    Lemma Pphi_more_proper `{equivR : base.Equiv R, !Reflexive (≡@{R})} :
      Proper (eq ==> (base.equiv ==> base.equiv ==> base.equiv) ==> (base.equiv ==> base.equiv ==> base.equiv) ==> forall_relation (fun C => eq ==> base.equiv ==> eq ==> base.equiv)) (@Pphi R).
    Proof.
      intros r0 ? <- radd1 radd2 Hradd rmul1 rmul2 Hrmul C phi1 ? <- env1 env2 Henv pol ? <-.
      revert r0 radd1 radd2 Hradd rmul1 rmul2 Hrmul phi1 env1 env2 Henv.
      induction pol;
        intros r0 radd1 radd2 Hradd rmul1 rmul2 Hrmul phi1 env1 env2 Henv;
        cbn.
      - reflexivity.
      - apply IHpol; eauto; now apply proper_jump_equiv.
      - apply Hradd.
        apply Hrmul.
        now apply IHpol1.
        apply proper_pow_pos; try easy.
        now apply proper_hd_equiv.
        apply IHpol2; try easy.
        now apply proper_tl_equiv.
    Qed.

    Lemma evalPol_norm_aux `{tmr : TermRing σ} {p : PExpr Z} (l : list (Term Σ σ)) :
      evalPolTm l (norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool p) ≡ evalPExprTm l p.
    Proof.
      unfold evalPolTm, evalPExprTm.
      rewrite Pphi_dev_ok;
        try eauto using tmr_ring_morph_peval', tmr_ring_theory_peval', tmr_ring_eq_ext_peval', tmr_ring_eq_ext, Rth_ARth, tmr_ring_theory, tmr_ring_morph, get_signZ_th with typeclass_instances.
      rewrite norm_aux_spec;
        try eauto using tmr_ring_eq_ext, Rth_ARth, tmr_ring_theory, tmr_ring_morph, get_signZ_th, pow_N_th with typeclass_instances.
      apply Pphi_more_proper; try easy.
      - repeat intros ? ? ?.
        rewrite peval_binop'_sound.
        now apply proper_term_binop.
      - repeat intros ? ? ?.
        rewrite peval_binop'_sound.
        now apply proper_term_binop.
    Qed.

    (* Lemma CanonTermRep_adeq {σ : Ty} {ct : CanonTerm σ} {t} : CanonTermRep ct t -> CanonTerm_to_Term ct ≡ t. *)
    (* Proof. *)
    (*   destruct σ; intros; cbn; try trivial; *)
    (*     specialize (H []%list 1%positive); *)
    (*     destruct (ct []%list 1%positive); *)
    (*     rewrite evalPol_norm_aux; *)
    (*     now rewrite <-(H eq_refl nil), app_nil_r. *)
    (* Qed. *)

    (* Lemma Term_Quote_bin_sound {n} {op : BinOp (ty.bvec n) (ty.bvec n) (ty.bvec n)} *)
    (*   {comb} {ct1 t1 ct2 t2} : *)
    (*   (forall env pol1 pol2, evalPExprTm env (comb pol1 pol2) = term_binop op (evalPExprTm env pol1) (evalPExprTm env pol2)) -> *)
    (*   CanonTermRep (σ := ty.bvec n) ct1 t1 -> *)
    (*   CanonTermRep (σ := ty.bvec n) ct2 t2 -> *)
    (*   CanonTermRep (σ := ty.bvec n) (Term_Quote_bin comb ct1 ct2) (term_binop op t1 t2). *)
    (* Proof. *)
    (*   intros Hcomb. *)
    (*   now eapply Term_Quote_bin_Valid. *)
    (* Qed. *)

    Definition CanonTerm_def {σ : Ty} : Term Σ σ -> CanonTerm σ :=
      match σ with
      | ty.bvec n => Term_Quote_def
      | ty.int => Term_Quote_def
      | _ => fun t => t
      end.

    (* Lemma CanonTerm_def_sound {σ : Ty} {t : Term Σ σ} : *)
    (*   CanonTermRep (CanonTerm_def t) t. *)
    (* Proof. *)
    (*   destruct σ; try reflexivity; *)
    (*   apply Term_Quote_def_Valid. *)
    (* Qed. *)

    Definition peval2_val {σ : Ty} : Val σ -> CanonTerm σ :=
      match σ with
      | ty.bvec n => fun v l p => (PEc (bv.unsigned v) , nil)
      | ty.int => fun v l p => (PEc v , nil)
      | _ => term_val _
      end.

    (* Lemma peval2_val_sound {σ : Ty} {v : Val σ} : CanonTermRep (peval2_val v) (term_val _ v). *)
    (* Proof. destruct σ; try reflexivity; *)
    (*        intros lo ? -> la; cbn; try reflexivity. *)
    (*        now rewrite bv.of_Z_unsigned. *)
    (* Qed. *)

    (* Definition peval2_binop {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) : *)
    (*   CanonTerm σ1 -> CanonTerm σ2 -> CanonTerm σ3 := *)
    (*   match op in BinOp σ1 σ2 σ3 return CanonTerm σ1 -> CanonTerm σ2 -> CanonTerm σ3 with *)
    (*   | bop.plus => Term_Quote_bin (@PEadd _) *)
    (*   | bop.minus => Term_Quote_bin (@PEsub _) *)
    (*   | bop.times => Term_Quote_bin (@PEmul _) *)
    (*   | bop.land => fun t1 t2 => CanonTerm_def (peval_binop bop.land (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)) *)
    (*   | bop.and => peval_binop bop.and *)
    (*   | bop.or => peval_binop bop.or *)
    (*   | bop.pair => fun t1 t2 => peval_binop bop.pair (CanonTerm_to_Term t1) (CanonTerm_to_Term t2) *)
    (*   (* | bop.cons => fun t1 t2 => peval_binop bop.cons (CanonTerm_to_Term t1) t2 *) *)
    (*   (* | bop.append => fun t1 t2 => peval_binop bop.append t1 t2 *) *)
    (*   | bop.shiftr => fun t1 t2 => CanonTerm_def (peval_binop bop.shiftr (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)) *)
    (*   | bop.shiftl => fun t1 t2 => CanonTerm_def (peval_binop bop.shiftl (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)) *)
    (*   | bop.bvadd => Term_Quote_bin (@PEadd _) *)
    (*   | bop.bvsub => Term_Quote_bin (@PEsub _) *)
    (*   | bop.bvmul => Term_Quote_bin (@PEmul _) *)
    (*   | bop.bvand => fun t1 t2 => CanonTerm_def (peval_binop bop.bvand (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)) *)
    (*   | bop.bvor => fun t1 t2 => CanonTerm_def (peval_binop bop.bvor (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)) *)
    (*   | bop.bvxor => fun t1 t2 => CanonTerm_def (peval_binop bop.bvxor (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)) *)
    (*   | bop.bvapp => fun t1 t2 => CanonTerm_def (peval_binop bop.bvapp (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)) *)
    (*   | bop.bvcons => fun t1 t2 => CanonTerm_def (peval_binop bop.bvcons t1 (CanonTerm_to_Term t2)) *)
    (*   | (bop.update_vector_subrange s l) => fun t1 t2 => CanonTerm_def (peval_binop (bop.update_vector_subrange s l) (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)) *)
    (*   | bop.relop rop => fun t1 t2 => peval_binop (bop.relop rop) (CanonTerm_to_Term t1) (CanonTerm_to_Term t2) *)
    (*   end. *)

    (* Lemma peval2_binop_sound {σ1 σ2 σ3 : Ty} {op : BinOp σ1 σ2 σ3} *)
    (*   {ct1 : CanonTerm σ1} {t1} {ct2 : CanonTerm σ2} {t2} : *)
    (*   CanonTermRep ct1 t1 -> *)
    (*   CanonTermRep ct2 t2 -> *)
    (*   CanonTermRep (peval2_binop op ct1 ct2) (term_binop op t1 t2). *)
    (* Proof. *)
    (*   destruct op; intros H1 H2; cbn [peval2_binop]. *)
    (*   - now eapply Term_Quote_bin_Valid. *)
    (*   - now eapply Term_Quote_bin_Valid. *)
    (*   - now eapply Term_Quote_bin_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound. *)
    (*     now eapply Term_Quote_def_Valid. *)
    (*   - now rewrite peval_binop_sound, H1, H2. *)
    (*   - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2). *)
    (*   - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2). *)
    (*   (* - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2). *) *)
    (*   (* - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2). *) *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound. *)
    (*     now eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound. *)
    (*     now eapply Term_Quote_def_Valid. *)
    (*   - now eapply Term_Quote_bin_Valid. *)
    (*   - now eapply Term_Quote_bin_Valid. *)
    (*   - now eapply Term_Quote_bin_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound. *)
    (*     now eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound. *)
    (*     now eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound. *)
    (*     now eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound. *)
    (*     now eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound. *)
    (*     now eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound. *)
    (*     now eapply Term_Quote_def_Valid. *)
    (*   - now rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), peval_binop_sound. *)
    (* Qed. *)

    (* Definition peval2_unop {σ1 σ2 : Ty} (op : UnOp σ1 σ2) : *)
    (*   CanonTerm σ1 -> CanonTerm σ2 := *)
    (*   match op in UnOp σ1 σ2 return CanonTerm σ1 -> CanonTerm σ2 with *)
    (*   (* | uop.inl => fun t1 => peval_unop uop.inl (CanonTerm_to_Term t1) *) *)
    (*   (* | uop.inr => fun t1 => peval_unop uop.inr (CanonTerm_to_Term t1) *) *)
    (*   | uop.neg => Term_Quote_unop (@PEopp _) *)
    (*   | uop.not => peval_unop uop.not *)
    (*   (* | uop.rev => fun t1 => peval_unop uop.rev (CanonTerm_to_Term t1) *) *)
    (*   | uop.sext => fun t1 => CanonTerm_def (peval_unop uop.sext (CanonTerm_to_Term t1)) *)
    (*   | uop.zext => fun t1 => CanonTerm_def (peval_unop uop.zext (CanonTerm_to_Term t1)) *)
    (*   | uop.get_slice_int => fun t1 => CanonTerm_def (peval_unop uop.get_slice_int (CanonTerm_to_Term t1)) *)
    (*   | uop.signed => fun t1 => CanonTerm_def (peval_unop uop.signed (CanonTerm_to_Term t1)) *)
    (*   | uop.unsigned => fun t1 => CanonTerm_def (peval_unop uop.unsigned (CanonTerm_to_Term t1)) *)
    (*   | uop.truncate m => fun t1 => CanonTerm_def (peval_unop (uop.truncate m) (CanonTerm_to_Term t1)) *)
    (*   | uop.vector_subrange s l => fun t1 => CanonTerm_def (peval_unop (uop.vector_subrange s l) (CanonTerm_to_Term t1)) *)
    (*   | uop.bvnot => fun t1 => CanonTerm_def (peval_unop uop.bvnot (CanonTerm_to_Term t1)) *)
    (*   | uop.bvdrop m => fun t1 => CanonTerm_def (peval_unop (uop.bvdrop m) (CanonTerm_to_Term t1)) *)
    (*   | uop.bvtake m => fun t1 => CanonTerm_def (peval_unop (uop.bvtake m) (CanonTerm_to_Term t1)) *)
    (*   | uop.negate => Term_Quote_unop (@PEopp _) *)
    (*   end. *)

    (* Lemma peval2_unop_sound {σ1 σ2 : Ty} {op : UnOp σ1 σ2} *)
    (*   {ct1 : CanonTerm σ1} {t1} : *)
    (*   CanonTermRep ct1 t1 -> *)
    (*   CanonTermRep (peval2_unop op ct1) (term_unop op t1). *)
    (* Proof. *)
    (*   destruct op; intros H1; cbn [peval2_unop]. *)
    (*   (* - now rewrite peval_unop_sound, <-(CanonTermRep_adeq H1). *) *)
    (*   (* - now rewrite peval_unop_sound, <-(CanonTermRep_adeq H1). *) *)
    (*   - now eapply Term_Quote_unop_Valid. *)
    (*   - now rewrite peval_unop_sound, <-(CanonTermRep_adeq H1). *)
    (*   (* - now rewrite peval_unop_sound, <-(CanonTermRep_adeq H1). *) *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound. *)
    (*     eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound. *)
    (*     eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound. *)
    (*     eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound. *)
    (*     eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound. *)
    (*     eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound. *)
    (*     eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound. *)
    (*     eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound. *)
    (*     eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound. *)
    (*     eapply Term_Quote_def_Valid. *)
    (*   - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound. *)
    (*     eapply Term_Quote_def_Valid. *)
    (*   - now eapply Term_Quote_unop_Valid. *)
    (* Qed. *)

    (*
     * peval2 runs the ring solver normalizer on ring expressions of type `bvec n` and `int` and
     * runs custom partial evaluation functions on other terms.
     *
     * In order to maximize sharing identical unknown subterms in quoted ring expressions, we keep
     * them in quoting monad form (`RQuote σ`, where we have access to already-quoted unknown subterms)
     * until they are destructed using a non-ring operator.
     * To this end, `CanonTerm σ` is `RQuote σ` for `σ = ty.int` or `σ = ty.bvec n` but it is `Term Σ σ`
     * for other types.
     * Once quoted terms are destructed using a non-ring expression, the quoting monad and ring solver normalizer are
     * run by CanonTerm_to_Term.
     *)
    (* Fixpoint peval2 [σ] (t : Term Σ σ) : CanonTerm σ := *)
    (*   match t with *)
    (*   | term_var ς                 => CanonTerm_def (term_var ς) *)
    (*   | term_val _ v               => peval2_val v *)
    (*   | term_relval _ v            => peval2_relval v *)
    (*   | term_binop op t1 t2        => peval2_binop op (peval2 t1) (peval2 t2) *)
    (*   | term_unop op t             => peval2_unop op (peval2 t) *)
    (*   (* | term_tuple ts              => term_tuple (env.map (fun b t => CanonTerm_to_Term (peval2 t)) ts) *) *)
    (*   (* | term_union U K t           => peval_union (CanonTerm_to_Term (peval2 t)) *) *)
    (*   (* | term_record R ts           => peval_record R (env.map (fun b t => CanonTerm_to_Term (peval2 t)) ts) *) *)
    (*   end. *)

    (* Lemma peval2_sound [σ] (t : Term Σ σ) : *)
    (*   CanonTermRep (peval2 t) t. *)
    (* Proof. *)
    (*   induction t; cbn. *)
    (*   - now eapply CanonTerm_def_sound. *)
    (*   - eapply peval2_val_sound. *)
    (*   - now eapply peval2_binop_sound. *)
    (*   - now eapply peval2_unop_sound. *)
    (*   (* - apply proper_term_tuple. *) *)
    (*   (*   induction IH; [reflexivity|]; cbn. *) *)
    (*   (*   apply proper_env_snoc; first trivial. *) *)
    (*   (*   now apply CanonTermRep_adeq. *) *)
    (*   (* - etransitivity; [apply peval_union_sound|apply proper_term_union]. *) *)
    (*   (*   now apply CanonTermRep_adeq. *) *)
    (*   (* - rewrite peval_record_sound. *) *)
    (*   (*   apply proper_term_record. *) *)
    (*   (*   induction IH; cbn; [reflexivity|]. *) *)
    (*   (*   apply proper_namedenv_snoc; first trivial. *) *)
    (*   (*   now apply CanonTermRep_adeq. *) *)
    (* Qed. *)


    (* This is the top-level partial evaluation function.
     * It delegates to peval2 to do the real work, but only does so when it
     * reaches a term whose type cannot be meta-level polymorphic.
     *
     * Specifically, it does not run peval2 on variables, values and (recursively) list elements.
     * These terms cannot be reduced further anyway, but also their type may be polymorphically
     * quantified in Gallina.
     * Passing such terms to peval2 would make peval2 pattern match on their type, which would produce
     * a neutral Gallina term that Rocq cannot evaluate further, which in turn quickly leads to huge VCs.
     * An example verification that depends on this is
     * `valid_contract_length` in test/Example.v
     *
     * The types of other terms is fixed anyway (for example the type of term_binop is fixed for all binops
     * except bop.cons) and pattern matching on the type will reduce fine.
     *)
    (* Fixpoint peval [σ] (t : Term Σ σ) : Term Σ σ := *)
    (*   let res_poly := *)
    (*     match t in Term _ σ return option (Term Σ σ) with *)
    (*     | term_var x => Some (term_var x) *)
    (*     | term_val σ v => Some (term_val _ v) *)
    (*     | @term_binop _ σ1 σ2 _ op t1 t2 => *)
    (*         (match op in BinOp σ1 σ2 σ3 return Term Σ σ1 -> Term Σ σ2 -> option (Term Σ σ3) with *)
    (*          | bop.cons => fun t1 t2 => Some (peval_binop' bop.cons (peval t1) (peval t2)) *)
    (*          | _ => fun _ _ => None *)
    (*          end) t1 t2 *)
    (*     | _ => None *)
    (*     end in *)
    (*       match res_poly with *)
    (*         Some t => t *)
    (*       | None => t *)
    (*       end. *)

    Fixpoint peval' [σ] (t : Term Σ σ) : Term Σ σ :=
      match t with
      | term_var ς                 => term_var ς
      | term_val _ v               => term_val _ v
      | term_relval _ rv           => term_relval _ rv
      | term_binop op t1 t2        => peval_binop op (peval' t1) (peval' t2)
      | term_unop op t             => peval_unop op (peval' t)
      | term_tuple ts              => term_tuple (env.map (fun b => @peval' b) ts)
      | term_union U K t           => peval_union (peval' t)
      | term_record R ts           => peval_record R (env.map (fun b => peval' (σ := type b)) ts)
      end.

    Definition peval [σ] : Term Σ σ -> Term Σ σ :=
      match σ return Term Σ σ -> Term Σ σ with
      | ty.bvec n => fun t => peval' (* (CanonTerm_to_Term (Term_to_CanonTerm *) t(* )) *)
      | _ => @peval' _
      end.

    Lemma peval'_sound [σ] (t : Term Σ σ) :
      peval' t ≡ t.
    Proof.
      induction t; cbn.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - etransitivity; [apply peval_binop_sound|now apply proper_term_binop].
      - etransitivity; [apply peval_unop_sound|now apply proper_term_unop].
      - apply proper_term_tuple.
        induction IH; [reflexivity|]; cbn.
        now apply proper_env_snoc.
      - etransitivity; [apply peval_union_sound|now apply proper_term_union].
      - rewrite peval_record_sound.
        apply proper_term_record.
        induction IH; cbn; [reflexivity|].
        now apply proper_namedenv_snoc.
    Qed.

    Lemma peval_sound [σ] (t : Term Σ σ) :
      peval t ≡ t.
    Proof.
      destruct σ; try apply peval'_sound; cbn [peval].
      (* rewrite peval'_sound. *)
      (* now rewrite Term_to_CanonTerm_to_Term. *)
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


