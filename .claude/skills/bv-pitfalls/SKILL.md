---
name: bv-pitfalls
description: >
  Bitvector (bv) proof gotchas in Katamaran: lia choking on 2^32-sized literals
  (goals bounded by bv.exp2 xlenbits), finding enum-membership lemmas
  (bv.finite.elem_of_enum, not "all_spec"), a blanket cbn unfolding the width
  index xlenbits into unary Peano numerals so bv-indexed lemmas stop matching
  syntactically, and bv.of_N_add's orientation (collapses add-of-two-of_Ns into
  one of_N-of-sum, not the reverse — easy to rewrite the wrong direction). Use
  reactively when a lia / rewrite / set / apply involving bv terms fails
  mysteriously — but ALSO PROACTIVELY, before hand-writing any new bv
  inequality/monotonicity proof (bv.ule, bv.uleb, bv.ugeb, bv.bin_add_small,
  bv.bin_of_N_small, bv.of_N_add), not only after a failure already happened.
  For the gmap-import Zify rewrite that breaks lia on bv.bin (bv.of_N x), see
  gmap-pitfalls.
---

# Bitvector (bv) pitfalls

## `lia` vs `bv.exp2 xlenbits` (= 2^32)

`lia` chokes evaluating the literal `4294967296`. Two escapes:

- Bound to a small literal, then transit:
  `assert (Hb : … < 1024) by lia; eapply N.lt_trans; [exact Hb|]; reflexivity.`
- Make the power opaque:
  `set (E := bv.exp2 xlenbits) in *; clearbody E; lia.`

(Related: after `From stdpp Require Import gmap`, `bv.bin (bv.of_N x)` gets
Zify-rewritten to `x mod 2^word` and breaks lia differently — that one is in the
**gmap-pitfalls** skill.)

### `Cannot find witness` with the right bound already in context

Third distinct mechanism behind the same message (the other two: the `bv.exp2`
literals above, and gmap's Zify rewrite). `cbn` unfolds `bv.unsigned` in the
GOAL to `Z.of_N (bv.bin a)`, while `bv.unsigned_bounds` states it FOLDED as
`bv.unsigned a` — so `lia` sees two unrelated atoms and cannot connect the
hypothesis to the goal, even though the hypothesis is exactly the bound needed.

```coq
(* fails: goal has Z.of_N (bv.bin a), hypothesis has bv.unsigned a *)
pose proof (bv.unsigned_bounds a). lia.
(* works: one atom on both sides *)
pose proof (bv.unsigned_bounds a); unfold bv.unsigned in *; lia.
```

`unfold bv.unsigned in *` (note `in *`, not just in the goal) is the fix; after
it, `lia` closes `0 <= Z.of_N (bv.bin a)` from `Z.of_N`'s non-negativity without
needing the bound at all. Pre-existing instance of the same idiom:
`relval_fetch_lower` in `RiscvPmp/CFGVer/Contracts.v` (`cbn; unfold bv.unsigned;
lia`). Cost of not knowing this, measured 2026-07-28: two full 5-minute
`Symbolic/Solver.v` compiles. Iterate such tactic fixes in rocq-mcp **preamble
mode** instead (~30 ms) — see the Tooling-gotchas block in the root `CLAUDE.md`.

## Enum membership: the lemma is `elem_of_enum`

`bv.finite.all_spec` does not exist. The lemma is
`bv.finite.elem_of_enum : ∀ [m] (x : bv m), x ∈ bv.finite.enum m`.
Typical use: `apply elem_of_list_to_set, bv.finite.elem_of_enum.`

## Blanket `cbn` unfolds the width index

`xlenbits := xlenbytes * byte` — a blanket `cbn` reduces it to a unary Peano
numeral `S (S (… O))`. Lemmas proved with the *folded* index then differ
**syntactically** (though convertibly): `set`/`rewrite` silently fail to match,
while `apply`/`exact` still work. When the goal must match an external bv-indexed
lemma, use `cbn -[xlenbits]`.

## `bv.of_N_add`'s orientation (easy to assume backwards)

`bv.of_N_add : bv.add (bv.of_N x) (bv.of_N y) = bv.of_N (x + y)` — it COLLAPSES a
sum of two `bv.of_N`s into one, not the reverse. `rewrite bv.of_N_add` only fires
on a `bv.add (bv.of_N _) (bv.of_N _)` subterm, turning it INTO `bv.of_N (_ + _)`
form — it will NOT expand an existing `bv.of_N (_ + _)` into a `bv.add`. If you
need that direction, `rewrite <- bv.of_N_add` — don't guess the lemma runs the
way its name suggests; check which side is `bv.add` before picking a direction.

## `bv.eqb` reflection: `cbn` and `destruct` both bite (2026-08-01)

Deciding a `bv` equality inside an `if` — e.g. a lookup function
`fun k => if bv.eqb k base then x else …` — fails two obvious ways:

- **A bare `cbn` unfolds `bv.eqb` itself** into `N.eqb (bv.bin _) (bv.bin _)`,
  after which a `rewrite` of any `bv.eqb`-stated lemma reports
  *"Found no subterm matching …"*. Restrict it: `cbn [words_of_list]` (name the
  function you actually want unfolded). Same family as the `cbn -[xlenbits]`
  trap above.
- **`destruct (bv.eqb_spec x y)` does NOT abstract a closed scrutinee.** When
  `bv.eqb x y` sits inside an `if` in the goal rather than being the goal's own
  index, `destruct` on the `reflect` leaves the `if` untouched and you get
  *"Unable to unify x with (if bv.eqb base base then x else …)"*. Decide the
  boolean FIRST and rewrite:

```coq
Lemma bv_eqb_refl {n} (x : bv n) : bv.eqb x x = true.
Proof. unfold bv.eqb. apply N.eqb_refl. Qed.

Lemma bv_eqb_neq {n} (x y : bv n) : x <> y -> bv.eqb x y = false.
Proof. intros Hne. destruct (bv.eqb_spec x y) as [Heq|_]; [contradiction|reflexivity]. Qed.
```

(Those two DO work by `destruct`, because there the `bv.eqb` application IS the
goal's index rather than a subterm of an `if`.)

**`congruence` chokes on `bv`.** `bv` is a record carrying a proof field, and
`congruence` fails on goals that look immediate — e.g. deriving `False` from
`m !! a = Some i` and `m !! a = None` after substituting a `bv` equality. Go
through `discriminate` instead: `intros Heq. subst a0. rewrite Hfresh in Hlk.
discriminate.`
