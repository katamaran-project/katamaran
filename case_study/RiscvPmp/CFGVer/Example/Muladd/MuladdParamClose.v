(* ========================================================================= *)
(* Example/Muladd/MuladdParamClose.v -- PARAMETRIC-mlen line: a GENERIC closer for the      *)
(* residuals angelic block entries leave .                   *)
(*                                                                            *)
(*   bv_lin    a bitvector (in)equation -> Z via bv.unsigned (add, shiftl,    *)
(*             shiftr, land-with-ones-mask, same-width sext), every variable  *)
(*             bounded, then Z.to_euclidean_division_equations; lia.  Mod and *)
(*             div by constants are what lia can then take.                   *)
(*   rv_leaf   a residual formula over RelVals: destruct the public ones      *)
(*             (secLeak), reduce evalRel on SyncVal, bv_lin.                  *)
(*   mb_search the inst_symprop tree (∧ ∨ ∀ →) of a residual: both sides of   *)
(*             every angelic choice are tried; a leaf must close.             *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Coq Require Import ZArith NArith Lia.

Lemma unsigned_shiftl_c {m k} (x : bv m) (c : bv k) :
  bv.unsigned (bv.shiftl x c) = ((bv.unsigned x * 2 ^ bv.unsigned c) mod 2 ^ Z.of_nat m)%Z.
Proof.
  unfold bv.shiftl. rewrite bv.unsigned_of_Z. unfold bv.truncz.
  rewrite Z.shiftl_mul_pow2; [reflexivity|]. unfold bv.unsigned; lia.
Qed.

Lemma unsigned_shiftr_c {m k} (x : bv m) (c : bv k) :
  bv.unsigned (bv.shiftr x c) = ((bv.unsigned x / 2 ^ bv.unsigned c) mod 2 ^ Z.of_nat m)%Z.
Proof.
  unfold bv.shiftr. rewrite bv.unsigned_of_Z. unfold bv.truncz.
  rewrite Z.shiftr_div_pow2; [reflexivity|]. unfold bv.unsigned; lia.
Qed.

Lemma unsigned_land_ones {m} (a c : bv m) (n : N) :
  bv.bin c = N.ones n ->
  bv.unsigned (bv.land a c) = (bv.unsigned a mod 2 ^ Z.of_N n)%Z.
Proof.
  intros Hc. unfold bv.land, bv.unsigned. rewrite Hc. rewrite N.land_ones.
  rewrite bv.bin_of_N_small.
  - rewrite N2Z.inj_mod. rewrite N2Z.inj_pow. reflexivity.
  - eapply N.le_lt_trans; [apply N.Div0.mod_le|].
    pose proof (bv.unsigned_bounds a) as B. unfold bv.unsigned in B.
    apply N2Z.inj_lt. rewrite N2Z.inj_pow. cbn [Z.of_N] in *. rewrite nat_N_Z. lia.
Qed.

(* the same-width sign extension a `lw` produces is the identity *)
Lemma sext_id32 (b : bv 32) p : @bv.sext 32 b 32 p = b.
Proof.
  apply bv.unsigned_inj. unfold bv.sext. cbn [bv.leview]. unfold bv.sext'.
  etransitivity; [exact (bv.unsigned_app b _)|]. destruct (bv.msb b); cbn; lia.
Qed.

Ltac bv_lin_rw :=
  repeat first
    [ rewrite bv.unsigned_add | rewrite bv.unsigned_mul | rewrite unsigned_shiftl_c | rewrite unsigned_shiftr_c
    | rewrite (unsigned_land_ones _ _ 30); [|reflexivity]
    | rewrite (unsigned_land_ones _ _ 31); [|reflexivity]
    | rewrite sext_id32 ].
Ltac bv_lin_rw_in H :=
  repeat first
    [ rewrite bv.unsigned_add in H | rewrite bv.unsigned_mul in H | rewrite unsigned_shiftl_c in H | rewrite unsigned_shiftr_c in H
    | rewrite (unsigned_land_ones _ _ 30) in H; [|reflexivity]
    | rewrite (unsigned_land_ones _ _ 31) in H; [|reflexivity]
    | rewrite sext_id32 in H ].

Ltac bv_consts :=
  repeat match goal with
  | |- context [(2 ^ ?k)%Z] => let v := eval vm_compute in (2 ^ k)%Z in change (2 ^ k)%Z with v
  | H : context [(2 ^ ?k)%Z] |- _ => let v := eval vm_compute in (2 ^ k)%Z in change (2 ^ k)%Z with v in H
  | |- context [bv.bin (@bv.of_N ?m ?n)] =>
      let v := eval vm_compute in (bv.bin (@bv.of_N m n)) in change (bv.bin (@bv.of_N m n)) with v
  | H : context [bv.bin (@bv.of_N ?m ?n)] |- _ =>
      let v := eval vm_compute in (bv.bin (@bv.of_N m n)) in change (bv.bin (@bv.of_N m n)) with v in H
  (* the literal 0 a clem_nonzero premise carries (n ≠ bv.zero), otherwise an
     opaque atom to lia (PLAN-rsa, br_ccopy's header phase) *)
  | |- context [bv.bin (@bv.zero ?m)] => change (bv.bin (@bv.zero m)) with 0%N
  | H : context [bv.bin (@bv.zero ?m)] |- _ => change (bv.bin (@bv.zero m)) with 0%N in H
  end.

(* bv.ult/bv.ule are stated on bv.bin (N), so the unsigned rewrites never
   reach inside them: move them to unsigned comparisons first *)
Lemma ult_Z {n} (a b : bv n) : bv.ult a b -> (bv.unsigned a < bv.unsigned b)%Z.
Proof. unfold bv.ult, bv.unsigned. lia. Qed.
Lemma ule_Z {n} (a b : bv n) : bv.ule a b -> (bv.unsigned a <= bv.unsigned b)%Z.
Proof. unfold bv.ule, bv.unsigned. lia. Qed.
Lemma Z_ult {n} (a b : bv n) : (bv.unsigned a < bv.unsigned b)%Z -> bv.ult a b.
Proof. unfold bv.ult, bv.unsigned. lia. Qed.
Lemma Z_ule {n} (a b : bv n) : (bv.unsigned a <= bv.unsigned b)%Z -> bv.ule a b.
Proof. unfold bv.ule, bv.unsigned. lia. Qed.

Lemma SyncVal_inj {A} (a b : A) : ty.SyncVal a = ty.SyncVal b -> a = b.
Proof. intros H. injection H. auto. Qed.

Ltac bv_rel_to_Z :=
  try unfold ty.valToRelVal in *;
  try apply Z_ult; try apply Z_ule;
  repeat match goal with
  | H : bv.ult _ _ |- _ => apply ult_Z in H
  | H : bv.ule _ _ |- _ => apply ule_Z in H
  | H : bv.ult ?a ?b -> False |- _ =>
      let H' := fresh "Hn" in pose proof (fun E => H (Z_ult a b E)) as H'; clear H
  | H : bv.ule ?a ?b -> False |- _ =>
      let H' := fresh "Hn" in pose proof (fun E => H (Z_ule a b E)) as H'; clear H
  | H : @eq (RelVal _) _ _ |- _ => apply SyncVal_inj in H
  end;
  (* an equation over `Val (ty.bvec n)` is one over `bv n`, but the patterns
     below match syntactically: restate it *)
  repeat match goal with
  | H : @eq ?T ?a ?b |- _ =>
      lazymatch T with bv _ => fail | _ =>
        let T' := eval hnf in T in
        lazymatch T' with bv ?n => change (@eq (bv n) a b) in H end end
  | H : @eq ?T ?a ?b -> False |- _ =>
      lazymatch T with bv _ => fail | _ =>
        let T' := eval hnf in T in
        lazymatch T' with bv ?n => change (@eq (bv n) a b -> False) in H end end
  end.

Ltac bv_lin :=
  bv_rel_to_Z;
  try (apply bv.unsigned_inj);
  try (match goal with |- _ <> _ => let E := fresh "E" in intro E; apply (f_equal bv.unsigned) in E end);
  (* bv (dis)equations in hypotheses go to Z too *)
  repeat match goal with
  | H : @eq (bv ?n) ?a ?b |- _ =>
      apply (f_equal bv.unsigned) in H; revert H
  | H : @eq (bv ?n) ?a ?b -> False |- _ =>
      let H' := fresh "Hne" in
      pose proof (fun E => H (bv.unsigned_inj a b E)) as H'; clear H; revert H'
  | H : ~ (@eq (bv ?n) ?a ?b) |- _ =>
      let H' := fresh "Hne" in
      pose proof (fun E => H (bv.unsigned_inj a b E)) as H'; clear H; revert H'
  end; intros;
  bv_lin_rw;
  repeat match goal with H : _ |- _ => progress (bv_lin_rw_in H) end;
  unfold bv.truncz, bv.ult, bv.ule in *;
  repeat match goal with x : bv _ |- _ =>
    lazymatch goal with _ : (0 <= bv.unsigned x < _)%Z |- _ => fail
                      | _ => pose proof (bv.unsigned_bounds x) end end;
  unfold bv.unsigned in *; cbn [bv.bin] in *; bv_consts; cbn [Z.of_N] in *;
  Z.to_euclidean_division_equations; lia.

(* A pair equation whose two sides are each public needs only its LEFT
   components: f_equal / RV_ext would prove the same bv equation twice *)
Lemma rv_eq_of_proj {σ} (x y : RelVal σ) :
  ty.projLeftRV x = ty.projRightRV x -> ty.projLeftRV y = ty.projRightRV y ->
  ty.projLeftRV x = ty.projLeftRV y -> x = y.
Proof.
  intros Hx Hy H. apply ty.RV_ext; [exact H|].
  rewrite <- Hx. rewrite <- Hy. exact H.
Qed.

Ltac rv_leaf :=
  cbn -[Erasure.inst_symprop] in *;
  (* a public RelVal is a pair whose sides agree: substitute that *)
  repeat match goal with v : RelVal _, H : RiscvPmpSignature.secLeak ?v |- _ =>
    is_var v; let l := fresh "l" in let r := fresh "r" in
    destruct v as [l r]; hnf in H; cbn in H; subst r end;
  (* every other RelVal is a pair too (one constructor: no case split), so
     evalRel reduces on it *)
  repeat match goal with v : RelVal _ |- _ =>
    is_var v; let l := fresh "l" in let r := fresh "r" in destruct v as [l r] end;
  cbn -[Erasure.inst_symprop bv.add bv.mul bv.shiftl bv.shiftr bv.land bv.sext bv.unsigned bv.of_N bv.ult bv.ule] in *;
  (* a relop/bool hypothesis is pointwise too, `P_l /\ P_r`: bv_lin only
     reads top-level facts, so split them (2026-10-07) *)
  repeat match goal with H : ?A /\ ?A |- _ => destruct H as [H _]
                       | H : _ /\ _ |- _ => destruct H end;
  (* likewise a RelVal equality hypothesis, into its projections; NOT
     ty.rv_split, whose bare cbn unfolds the bv operations bv_lin needs *)
  repeat match goal with H : @eq (RelVal _) _ _ |- _ =>
    pose proof (f_equal ty.projLeftRV H); pose proof (f_equal ty.projRightRV H); clear H end;
  cbn -[Erasure.inst_symprop bv.add bv.mul bv.shiftl bv.shiftr bv.land bv.sext bv.unsigned bv.of_N bv.ult bv.ule] in *;
  (* the destructs above turn EVERY RelVal into two bv variables, most of them
     unused here (two are 928 bits wide); bv_lin bounds every bv in context,
     so drop the unused ones: per-leaf lia 2.1 s -> 0.59 s on LoopI, the
     pre-pair cost (2026-10-07) *)
  repeat match goal with x : bv _ |- _ => clear x end;
  (* relops and bool formulas hold pointwise: one leaf per projection *)
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        (* an evar constrained only by publicness: any public value (the
           final Unshelve gives SyncVal 0 too).  f_equal; bv_lin found it in
           ~26 s per leaf on the parametric muladd tail (2026-10-01) *)
        | lazymatch goal with
          | |- RiscvPmpSignature.secLeak ?v =>
              is_evar v; unify v (ty.SyncVal (@bv.zero xlenbits)); reflexivity
          | |- ty.projLeftRV ?v = ty.projRightRV ?v =>
              is_evar v; unify v (ty.SyncVal (@bv.zero xlenbits)); reflexivity
          end
        | assumption | reflexivity
        (* both sides public (equal components, checked SYNTACTICALLY so a
           secret side fails fast): one bv equation, not two (2026-10-30) *)
        | (apply rv_eq_of_proj;
           [ cbn -[Erasure.inst_symprop bv.add bv.mul bv.shiftl bv.shiftr bv.land bv.sext bv.unsigned bv.of_N bv.ult bv.ule];
             lazymatch goal with |- ?a = ?a => reflexivity end
           | cbn -[Erasure.inst_symprop bv.add bv.mul bv.shiftl bv.shiftr bv.land bv.sext bv.unsigned bv.of_N bv.ult bv.ule];
             lazymatch goal with |- ?a = ?a => reflexivity end
           | cbn -[Erasure.inst_symprop bv.add bv.mul bv.shiftl bv.shiftr bv.land bv.sext bv.unsigned bv.of_N bv.ult bv.ule];
             bv_lin ])
        | (f_equal; bv_lin) | bv_lin
        (* a RelVal equality whose side f_equal cannot open (a folded
           ty.valToRelVal): per projection *)
        | (apply ty.RV_ext;
           cbn -[Erasure.inst_symprop bv.add bv.mul bv.shiftl bv.shiftr bv.land bv.sext bv.unsigned bv.of_N bv.ult bv.ule];
           bv_lin)
        (* a dead branch: refute its hypotheses *)
        | (exfalso; bv_lin) ].

(* An angelic block entry whose variable the executor could not eliminate
   (its equation is `SyncVal a = c + ?v`, not `?v = t`): instantiate all the
   existentials, fix them from their defining equations, then search. *)
Lemma rv_bvadd_solve {n} (a c d : bv n) : bv.add c d = bv.zero ->
  @ty.SyncVal (bv n) a = bop.evalRel (σ1 := ty.bvec n) (σ2 := ty.bvec n) bop.bvadd
    (ty.SyncVal c) (ty.SyncVal (bv.add a d)).
Proof.
  intros Hd. cbn. f_equal;
    (rewrite (@bv.add_comm _ a); rewrite bv.add_assoc; rewrite Hd; by rewrite bv.add_zero_l).
Qed.

(* The same for any RelVal on the left, NonSyncVal included: the ∃ case
   must not destruct the public variables first -- destruct generalizes the
   goal, which there is the whole rest of the program. *)
Lemma rv_bvadd_solve_rel {n} (a : RelVal (ty.bvec n)) (c d : bv n) : bv.add c d = bv.zero ->
  a = bop.evalRel (σ1 := ty.bvec n) (σ2 := ty.bvec n) bop.bvadd
        (ty.SyncVal c) (bop.evalRel (σ1 := ty.bvec n) (σ2 := ty.bvec n) bop.bvadd a (ty.SyncVal d)).
Proof.
  intros Hd.
  assert (E : forall x : bv n, x = bv.add c (bv.add x d)).
  { intros x. rewrite (@bv.add_comm _ x). rewrite bv.add_assoc. rewrite Hd. by rewrite bv.add_zero_l. }
  destruct a as [x y]; cbn; f_equal; apply E.
Qed.

(* the witness constant is computed here, so the evar gets a literal *)
Ltac mb_eq_evar :=
  lazymatch goal with
  | |- ty.SyncVal ?a = bop.evalRel bop.bvadd (ty.SyncVal ?c) ?v =>
      is_evar v; let d := eval vm_compute in (bv.negate c) in
      apply (@rv_bvadd_solve _ a c d); vm_compute; reflexivity
  | |- ?a = bop.evalRel bop.bvadd (ty.SyncVal ?c) ?v =>
      is_evar v; let d := eval vm_compute in (bv.negate c) in
      apply (@rv_bvadd_solve_rel _ a c d); vm_compute; reflexivity
  (* `a = t + ?v`, t NOT a literal (an angelic arr match against
     [e - n; n; e] with k a pointer variable gives `k = -n + ?e`): ?v := a - t.
     Guarded by `a` not an evar, so the generic cases below keep their old
     behaviour; the equation is left as an ordinary leaf (it holds once the
     public variables are destructed, not before: SyncVal + NonSyncVal is a
     NonSyncVal).  -1 is computed to a literal at the evar's width, which
     bv_lin needs. *)
  | |- ?a = bop.evalRel bop.bvadd ?t ?v =>
      tryif is_evar a then reflexivity else
      (is_evar v;
       let T := type of v in let T' := eval cbn in T in
       lazymatch T' with
       | RelVal (ty.bvec ?n) =>
           let m1 := eval vm_compute in (bv.negate (@bv.one n)) in
           unify v (bop.evalRel bop.bvadd a (bop.evalRel bop.bvmul (ty.SyncVal m1) t))
       end)
  | |- ?x = ?t => is_evar x; reflexivity
  | |- ?t = ?x => is_evar x; reflexivity
  end.

Ltac mb_search :=
  lazymatch goal with
  | |- exists _, _ =>
      (* no `cbn in *` and no destructs: the goal holds the whole rest
         of the program.  Only the ∃'s small erasure atoms are reduced *)
      (* fix the evars from ALL defining equations before searching any
         conjunct: an equation can mention evars only LATER conjuncts
         define (an angelic arr match against [e - n; n; e] yields
         `k = -n + e` before `n = l` and `e = k + l`), 2026-10-02 *)
      (repeat eexists; repeat split;
       try (lazymatch goal with
            | |- Erasure.inst_eformula' _ _ => cbn -[Erasure.inst_symprop ty.SyncVal]
            | |- Erasure.inst_eq _ _ => cbn -[Erasure.inst_symprop ty.SyncVal] end);
       try mb_eq_evar); mb_search
  | |- _ /\ _ => split; mb_search
  | |- True => exact I
  | |- forall _, _ => intro; mb_search
  | |- _ \/ _ => first [ left; mb_search | right; mb_search ]
  | |- _ => solve [ rv_leaf ]
  end.

(* the whole discharge of a parametric VC with angelic block entries *)
Ltac solve_mb_vc :=
  intros; vm_compute; solve_vc;
  try solve_symbase_fetch;
  cbn [Erasure.inst_symprop];
  (* the hypotheses solve_vc introduced, reduced ONCE per goal: rv_leaf's
     `cbn in *` otherwise redoes them at every leaf (~5 s each on the
     parametric muladd tail: 49.5 -> 21 s once; 2026-10-01) *)
  cbn -[Erasure.inst_symprop] in * |- ;
  mb_search.
