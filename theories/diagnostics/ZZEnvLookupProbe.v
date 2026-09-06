(* PLAN-env-trie Phase 0 SPIKE -- throwaway, not in _CoqProject.
   Question (GATE 0): does a random-access replacement for env.lookup survive
   vm_compute, i.e. are there eq_rect transports left in the reduced path, and
   does it beat the linear walk on allocated_words at 200 entries / 10k lookups?

   Design under test is *not* PLAN §3's Ctx-indexed skew RAL but the cheaper
   variant: a nat-indexed skew-binary RAL of `sigT D`, with the binder equality
   recovered by a decidable test.  This removes every Ctx-shape transport by
   construction (the RAL's shape is a plain nat), leaving exactly ONE transport
   to test -- the B-equality eq_rect -- which is the whole point of the gate. *)

From Coq Require Import NArith.NArith Lists.List.
From Katamaran Require Import Prelude Context Environment.
Import ctx.notations.
Import ListNotations.

(* ---- toy binding type and heterogeneous domain -------------------------- *)
Definition B : Set := N.
Inductive Dty : B -> Set := dmk : forall b : B, nat -> Dty b.
Definition D : B -> Set := Dty.
Definition meas {b} (d : D b) : nat := match d with dmk _ n => n end.

(* ---- skew-binary random-access list over sigT D ------------------------- *)
Inductive tree : Set :=
| tleaf : sigT D -> tree
| tnode : sigT D -> tree -> tree -> tree.

Definition ral : Set := list (nat * tree).

(* w is the size of t (always 2^k-1). index 0 = root. *)
Fixpoint tlookup (t : tree) (w : nat) (i : nat) {struct t} : option (sigT D) :=
  match t with
  | tleaf a => match i with O => Some a | S _ => None end
  | tnode a l r =>
      match i with
      | O => Some a
      | S i' => let h := Nat.div2 w in
                if Nat.ltb i' h then tlookup l h i'
                else tlookup r h (Nat.sub i' h)
      end
  end.

Fixpoint rlookup (r : ral) (i : nat) {struct r} : option (sigT D) :=
  match r with
  | nil => None
  | cons (w, t) r' => if Nat.ltb i w then tlookup t w i else rlookup r' (Nat.sub i w)
  end.

Definition rcons (a : sigT D) (r : ral) : ral :=
  match r with
  | cons (w1, t1) (cons (w2, t2) rest) =>
      if Nat.eqb w1 w2 then cons (S (Nat.add w1 w2), tnode a t1 t2) rest
      else cons (1, tleaf a) r
  | _ => cons (1, tleaf a) r
  end.

(* index 0 must be the NEWEST binding, matching ctx.in_at. *)
Fixpoint to_fast {G : Ctx B} (E : env.Env D G) : ral :=
  match E with
  | env.nil => @nil (nat * tree)
  | env.snoc E' b d => rcons (@existT B D b d) (to_fast E')
  end.

(* The two "impossible" branches fall back on the linear walk, so the function
   is total without an inhabitant of D b; under vm_compute they are never
   entered, and they are what makes the Phase-1 agreement lemma provable. *)
Definition flookup {G : Ctx B} (E : env.Env D G) (r : ral) {b} (bIn : b ∈ G) : D b :=
  match rlookup r (ctx.in_at bIn) with
  | Some (existT b' d) =>
      match N.eq_dec b' b with
      | left e => eq_rect b' D d b e
      | right _ => env.lookup E bIn
      end
  | None => env.lookup E bIn
  end.

(* ---- benchmark rig ------------------------------------------------------ *)
Fixpoint mkctx (n : nat) : Ctx B :=
  match n with
  | O => ctx.nil
  | S k => ctx.snoc (mkctx k) (N.of_nat k)
  end.

Definition NN : nat := 200.
Definition G200 : Ctx B := Eval vm_compute in mkctx NN.
Definition E200 : env.Env D G200 := env.tabulate (fun b _ => dmk b (S (N.to_nat b))).

Fixpoint esum {G} (E : env.Env D G) (acc : nat) {struct E} : nat :=
  match E with
  | env.nil => acc
  | env.snoc E' _ d => esum E' (match meas d with O => S acc | S _ => S acc end)
  end.

(* One round = one `tabulate` over |G| entries, each entry paying one lookup.
   This is exactly sub_comp's shape (env.map/tabulate + one lookup per entry). *)
Definition round_slow {G} (E : env.Env D G) : env.Env D G :=
  env.tabulate (fun b bIn => env.lookup E bIn).
(* NULL arm: same tabulate, no lookup at all -- isolates the tabulate floor
   that both arms pay, so the lookup term can be read off by subtraction. *)
Definition round_null {G} (E : env.Env D G) : env.Env D G :=
  env.tabulate (fun b _ => dmk b 1).
Definition round_fast {G} (E : env.Env D G) : env.Env D G :=
  let r := to_fast E in env.tabulate (fun b bIn => flookup E r bIn).

(* STRICT variant: the impossible branches return a WRONG value instead of
   falling back on the linear walk, so a blocked transport or an off-by-one
   index shows up as a wrong checksum instead of being silently masked. *)
Definition flookup_strict {G : Ctx B} (r : ral) {b} (bIn : b ∈ G) : D b :=
  match rlookup r (ctx.in_at bIn) with
  | Some (existT b' d) =>
      match N.eq_dec b' b with
      | left e => eq_rect b' D d b e
      | right _ => dmk b 0
      end
  | None => dmk b 0
  end.
Definition round_fast_strict {G} (E : env.Env D G) : env.Env D G :=
  let r := to_fast E in env.tabulate (fun b bIn => flookup_strict r bIn).

Definition ROUNDS : nat := 50.   (* 50 * 200 = 10 000 lookups *)
Definition bench_slow : nat := esum (Nat.iter ROUNDS round_slow E200) 0.
Definition bench_fast : nat := esum (Nat.iter ROUNDS round_fast E200) 0.
Definition check_slow : nat := esum (round_slow E200) 0.
Definition check_fast : nat := esum (round_fast_strict E200) 0.
Definition bench_null : nat := esum (Nat.iter ROUNDS round_null E200) 0.

(* ======================================================================== *)
(* Diagnosis arms added after the first sweep: the ratio SHRANK with n,     *)
(* which no log-vs-linear structure can do.  Suspect: `ctx.in_at` is a      *)
(* UNARY nat, so every comparison/subtraction inside the tree descent costs *)
(* O(index) rather than O(1).                                               *)
(* ======================================================================== *)

(* (i) raw spine walk: no ctx.view, no In-record rebuilding, type recovered
       once at the end by a decidable test. *)
Fixpoint walkl {G : Ctx B} (E : env.Env D G) (i : nat) {struct E} : option (sigT D) :=
  match E with
  | env.nil => None
  | env.snoc E' b d => match i with
                       | O => Some (@existT B D b d)
                       | S i' => walkl E' i'
                       end
  end.

Definition flookup_walk {G : Ctx B} (E : env.Env D G) {b} (bIn : b ∈ G) : D b :=
  match walkl E (ctx.in_at bIn) with
  | Some (existT b' d) =>
      match N.eq_dec b' b with
      | left e => eq_rect b' D d b e
      | right _ => env.lookup E bIn
      end
  | None => env.lookup E bIn
  end.
Definition round_walk {G} (E : env.Env D G) : env.Env D G :=
  env.tabulate (fun b bIn => flookup_walk E bIn).
Definition bench_walk : nat := esum (Nat.iter ROUNDS round_walk E200) 0.

(* (ii) the SAME skew RAL, but with BINARY (N) sizes and indices, so div2 /
       ltb / sub are O(log) instead of O(n). *)
Definition ralN : Set := list (N * tree).

Fixpoint tlookupN (t : tree) (w : N) (i : N) {struct t} : option (sigT D) :=
  match t with
  | tleaf a => if N.eqb i 0 then Some a else None
  | tnode a l r =>
      if N.eqb i 0 then Some a
      else let i' := N.pred i in
           let h := N.div2 w in
           if N.ltb i' h then tlookupN l h i' else tlookupN r h (N.sub i' h)
  end.

Fixpoint rlookupN (r : ralN) (i : N) {struct r} : option (sigT D) :=
  match r with
  | nil => None
  | cons (w, t) r' => if N.ltb i w then tlookupN t w i else rlookupN r' (N.sub i w)
  end.

Definition rconsN (a : sigT D) (r : ralN) : ralN :=
  match r with
  | cons (w1, t1) (cons (w2, t2) rest) =>
      if N.eqb w1 w2 then cons (N.succ (N.add w1 w2), tnode a t1 t2) rest
      else cons (1%N, tleaf a) r
  | _ => cons (1%N, tleaf a) r
  end.

Fixpoint to_fastN {G : Ctx B} (E : env.Env D G) : ralN :=
  match E with
  | env.nil => @nil (N * tree)
  | env.snoc E' b d => rconsN (@existT B D b d) (to_fastN E')
  end.

(* (iii) descent-isolation sweeps.  Both walk every index 0..NN-1 and count
        hits; the accumulator is `S`, which is O(1), so nothing but the
        lookup itself is being weighed.  No tabulate, no transport. *)
Fixpoint sweep_lin {G} (E : env.Env D G) (k : nat) (i : nat) (acc : nat) {struct k} : nat :=
  match k with
  | O => acc
  | S k' => sweep_lin E k' (S i) (match walkl E i with Some _ => S acc | None => acc end)
  end.

Fixpoint sweep_bin (r : ralN) (k : nat) (i : N) (acc : nat) {struct k} : nat :=
  match k with
  | O => acc
  | S k' => sweep_bin r k' (N.succ i) (match rlookupN r i with Some _ => S acc | None => acc end)
  end.

Fixpoint sweep_view {G} (E : env.Env D G) (k : nat) (i : nat) (acc : nat) {struct k} : nat :=
  match k with
  | O => acc
  | S k' => sweep_view E k' (S i) (match walkl E i with Some _ => S acc | None => acc end)
  end.

Definition bench_lin : nat :=
  Nat.iter ROUNDS (fun a => Nat.add (sweep_lin E200 NN 0 0) a) 0.
Definition bench_bin : nat :=
  let r := to_fastN E200 in
  Nat.iter ROUNDS (fun a => Nat.add (sweep_bin r NN 0%N 0) a) 0.

(* ======================================================================== *)
(* (iv) THE CANDIDATE THIS SPIKE ACTUALLY FOUND.                            *)
(* Same O(depth) algorithm as env.lookup, but recursing on the Env spine and *)
(* the raw `in_at` nat SIMULTANEOUSLY, so no `ctx.view` SnocView value and   *)
(* no predecessor MkIn record is built at any step.  The binder equality is  *)
(* not re-decided: it is the EXISTING `in_valid` proof, transported once at  *)
(* the base case.  No new data structure, no conversion, no eq_dec.         *)
(* ======================================================================== *)
Fixpoint lookup2 {G : Ctx B} (E : env.Env D G) {struct E} :
  forall (i : nat) (b : B), ctx.nth_is G i b -> D b :=
  match E in env.Env _ G return forall i b, ctx.nth_is G i b -> D b with
  | env.nil => fun i b (p : False) => match p with end
  | env.snoc E' b' d =>
      fun i =>
        match i return forall b, ctx.nth_is (_ ▻ b') i b -> D b with
        | O    => fun b p => eq_rect b' D d b p
        | S i' => fun b p => lookup2 E' i' b p
        end
  end.

Definition lookupI {G : Ctx B} (E : env.Env D G) {b} (bIn : b ∈ G) : D b :=
  lookup2 E (ctx.in_at bIn) b (ctx.in_valid bIn).

Definition round_idx {G} (E : env.Env D G) : env.Env D G :=
  env.tabulate (fun b bIn => lookupI E bIn).
Definition bench_idx : nat := esum (Nat.iter ROUNDS round_idx E200) 0.
Definition check_idx : nat := esum (round_idx E200) 0.

(* (v) same as lookup2 but with every argument taken UP FRONT and the match
       applied to the proof, to see whether the residual ~7.5 words/step is a
       per-step closure. *)
Fixpoint lookup5 {G : Ctx B} (E : env.Env D G) (i : nat) (b : B)
  (p : ctx.nth_is G i b) {struct E} : D b :=
  match E as E0 in env.Env _ G0 return ctx.nth_is G0 i b -> D b with
  | env.nil => fun p0 => match p0 return D b with end
  | env.snoc E' b' d =>
      match i as i0 return ctx.nth_is (_ ▻ b') i0 b -> D b with
      | O    => fun p0 => eq_rect b' D d b p0
      | S i' => fun p0 => lookup5 E' i' b p0
      end
  end p.

Definition lookupJ {G : Ctx B} (E : env.Env D G) {b} (bIn : b ∈ G) : D b :=
  lookup5 E (ctx.in_at bIn) b (ctx.in_valid bIn).
Definition round_idx2 {G} (E : env.Env D G) : env.Env D G :=
  env.tabulate (fun b bIn => lookupJ E bIn).
Definition bench_idx2 : nat := esum (Nat.iter ROUNDS round_idx2 E200) 0.

(* (vi) prices the eq_dec in the WALK arm: same walkl, but the recovered
       binder equality is thrown away and the payload faked, so the arm
       measures the spine walk ALONE.  Not a usable lookup -- an upper bound. *)
Definition flookup_nodec {G : Ctx B} (E : env.Env D G) {b} (bIn : b ∈ G) : D b :=
  match walkl E (ctx.in_at bIn) with
  | Some (existT _ d) => dmk b (meas d)
  | None => dmk b 0
  end.
Definition round_bare {G} (E : env.Env D G) : env.Env D G :=
  env.tabulate (fun b bIn => flookup_nodec E bIn).
Definition bench_bare : nat := esum (Nat.iter ROUNDS round_bare E200) 0.
