(* Regression tests for the linear-difference solver rules S1 (decide) and
   S2 (isolate the innermost unit variable), PLAN-bv-arith-solver O2.

   Each row runs the real solver entry point `simplify_formula` on one
   formula in a small world and checks the OUTCOME CLASS by `vm_compute`:
   refuted (the path is dead), valid (the formula is dropped), or open (it
   survives, possibly rewritten).  Rows come from the plan's O0 table.

   The NEGATIVE rows are soundness controls: each one is a satisfiable or
   non-entailed formula, and must come out `Open`.  If one turns into
   `Refuted` or `Valid`, a rule decides something it must not -- read that as
   a soundness alarm, never fix it by editing the expected value. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
Import GenericSolver DList.

Local Notation "a ⊕ b" := (term_binop bop.bvadd a b) (at level 50, left associativity).
Local Notation "a ⊗ b" := (term_binop bop.bvmul a b) (at level 40, left associativity).

(* five public bv variables; [ctx.in_at] counts from the END, so k is 0
   (innermost) and q is 4 *)
Definition ΣT : LCtx :=
  [ctx] ▻ "q"∷ty_xlenbits ▻ "x"∷ty_xlenbits ▻ "c"∷ty_xlenbits ▻ "T"∷ty_xlenbits ▻ "k"∷ty_xlenbits.
Definition tz (z : Z) : Term ΣT ty_xlenbits := term_val ty_xlenbits (bv.of_Z z).
Definition vq : Term ΣT ty_xlenbits := term_var "q".
Definition vx : Term ΣT ty_xlenbits := term_var "x".
Definition vc : Term ΣT ty_xlenbits := term_var "c".
Definition vT : Term ΣT ty_xlenbits := term_var "T".
Definition vk : Term ΣT ty_xlenbits := term_var "k".

Definition wT (C : PathCondition ΣT) : World := {| wctx := ΣT; wco := C |}.

Inductive outcome := Refuted | Valid | Open.
Definition classify {w : World} (d : DList w) : outcome :=
  match DList.run d with
  | None => Refuted
  | Some ctx.nil => Valid
  | Some _ => Open
  end.
(* the variable an S2 rewrite puts on the left: `Some (in_at x)` for a single
   surviving `x = _` *)
Definition iso_lhs {w : World} (d : DList w) : option nat :=
  match DList.run d with
  | Some (ctx.snoc ctx.nil (@formula_propeq _ σ a _)) => term_var_at a
  | _ => None
  end.

Definition sf (C : PathCondition ΣT) (f : Formula ΣT) : DList (wT C) :=
  simplify_formula (w := wT C) f.
Definition peq (a b : Term ΣT ty_xlenbits) : Formula ΣT := formula_propeq a b.
Definition req (a b : Term ΣT ty_xlenbits) : Formula ΣT := formula_relop bop.eq a b.
Definition rneq (a b : Term ΣT ty_xlenbits) : Formula ΣT := formula_relop bop.neq a b.

Definition CD0 : PathCondition ΣT := [ctx] ▻ formula_relop bop.neq vc (tz 0).

(* ---- S1: decide ---- *)
Definition s1_tests :=
  ( classify (sf [ctx] (peq vq (tz 0x180 ⊕ vq)))     (* mmq exit pc, propeq : Refuted *)
  , classify (sf [ctx] (req vq (tz 0x180 ⊕ vq)))     (* same, relop eq      : Refuted *)
  , classify (sf [ctx] (rneq (vx ⊕ tz 4) vx))        (* x + 4 <> x          : Valid *)
  , classify (sf [ctx] (peq (vx ⊕ tz 4) (tz 4 ⊕ vx))) (* commuted           : Valid *)
  , classify (sf [ctx] (req (tz 2 ⊗ vx ⊕ tz 3) (vx ⊕ vx ⊕ tz 3))) (* 2x+3 = x+x+3 : Valid *)
  , classify (sf [ctx] (rneq (vc ⊕ tz (-1) ⊗ vc ⊕ vx) (vx ⊕ tz 5))) (* c-c+x <> x+5 : Valid *)
  ).
Lemma s1_tests_ok : s1_tests = (Refuted, Refuted, Valid, Valid, Valid, Valid).
Proof. vm_compute. reflexivity. Qed.

(* ---- S1 negative controls: must stay Open ---- *)
Definition s1_neg :=
  ( classify (sf CD0 (peq (vT ⊕ vc) (tz 1 ⊕ vT)))    (* D0, only c <> 0 known *)
  , classify (sf CD0 (req (vT ⊕ vc) (tz 1 ⊕ vT)))    (* D0 as a relop *)
  , classify (sf [ctx] (rneq (vT ⊕ vc) (tz 1 ⊕ vT))) (* D0 neq: not entailed either *)
  , classify (sf [ctx] (peq (tz 2 ⊗ vk) (tz 4 ⊗ vx))) (* no unit coefficient *)
  , classify (sf [ctx] (req vk (vk ⊗ vx ⊕ tz 1)))    (* k inside another atom *)
  ).
Lemma s1_neg_ok : s1_neg = (Open, Open, Open, Open, Open).
Proof. vm_compute. reflexivity. Qed.

(* ---- S2: isolate the innermost unit variable, either orientation ---- *)
Definition s2_tests :=
  ( iso_lhs (sf [ctx] (peq vk (vT ⊕ tz (-1) ⊗ vc)))  (* mmq k = T - c   : k (0) *)
  , iso_lhs (sf [ctx] (peq (vT ⊕ tz (-1) ⊗ vc) vk))  (* reversed        : k (0) *)
  , iso_lhs (sf [ctx] (peq vx (vk ⊕ tz 4)))          (* x = k + 4       : k (0) *)
  , iso_lhs (sf [ctx] (peq (tz 2 ⊗ vk) vT))          (* k non-unit      : T (1) *)
  , iso_lhs (sf CD0 (peq (vT ⊕ vc) (tz 1 ⊕ vT)))      (* D0: c = 1       : c (2) *)
  ).
Lemma s2_tests_ok : s2_tests = (Some 0, Some 0, Some 0, Some 1, Some 2).
Proof. vm_compute. reflexivity. Qed.

(* ---- S2 over a SUBTRACTION: the variable to isolate sits under a bvsub ----
   canon_term prints a negative coefficient as `bvsub`, so the difference of
   `q = T + (k - x)` comes back as a chain like `q -ᵇ T -ᵇ k +ᵇ x`.  Before
   lin_view read QSub/QNeg it took `q -ᵇ T -ᵇ k` as ONE atom, so k was hidden
   and S2 isolated x instead.  That is the RsaCcopy loop-back incident (an
   existential under a bvsub, a universal isolated instead).  The rows are
   checked on the raw lin_iso, so no fallback rule can mask a regression.
   The emitted right-hand side must also be FREE of bvsub/negate, because the
   closers (bv_lin) cannot read them. *)
Local Notation "a ⊖ b" := (term_binop bop.bvsub a b) (at level 50, left associativity).
Fixpoint sub_free (f : nat) (t : Term ΣT ty_xlenbits) : bool :=
  match f with
  | O => true
  | S f => match q_view t with
           | QSub _ _ | QNeg _ => false
           | QAdd a b | QMul a b => sub_free f a && sub_free f b
           | QShl a _ => sub_free f a
           | _ => true
           end
  end.
Definition iso_raw (t1 t2 : Term ΣT ty_xlenbits) : option (option nat * bool) :=
  option_map (fun '(a, b) => (term_var_at a, sub_free 64 b)) (lin_iso t1 t2).
Definition s2_sub_tests :=
  ( iso_raw vq (vT ⊕ (vk ⊖ vx))                     (* k only under a bvsub : k (0) *)
  , iso_raw (vx ⊖ vk) (vT ⊖ vc)                     (* both sides bvsub      : k (0) *)
  , iso_raw (tz 0 ⊖ vk) vq                          (* k under a negation    : k (0) *)
  , iso_lhs (sf [ctx] (peq vq (vT ⊕ (vk ⊖ vx))))    (* via simplify_formula  : k (0) *)
  ).
Lemma s2_sub_tests_ok :
  s2_sub_tests = (Some (Some 0, true), Some (Some 0, true), Some (Some 0, true), Some 0).
Proof. vm_compute. reflexivity. Qed.
