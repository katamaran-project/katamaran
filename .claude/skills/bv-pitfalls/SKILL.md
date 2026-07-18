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
