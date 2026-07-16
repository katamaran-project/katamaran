---
name: gmap-pitfalls
description: >
  Pitfalls of stdpp's gmap in Rocq proofs (observed in Katamaran, mechanisms
  generic). Use when a destruct / remember / rewrite / set on a gmap lookup
  (m !! k) reports "found no subterm" or binds a variable while leaving the match
  unreduced (then downstream tactics like refine_bind diverge or iApply hangs); or
  when lia inexplicably fails with "Cannot find witness" on a trivial linear goal in
  a file that does From stdpp Require Import gmap. NOT for Katamaran's instruction
  store design itself (cfgver-executor).
---

# stdpp gmap pitfalls

Two independent traps that both come from importing/using `gmap`.

## 1. `destruct (m !! k)` doesn't reduce the `match`

**Symptom:** the goal contains `match m !! k with Some _ => … | None => … end`
(often inside a relational `ℛ⟦⟧` or other dependent context). A plain
`destruct (m !! k)` binds the case variable but the `match` stays unreduced —
and `destruct`/`remember`/`rewrite`/`set` may outright report "found no subterm".
Downstream, a tactic unifying against the unreduced `match` (e.g. `refine_bind`)
diverges, which can look like a `Qed` hang.

**Mechanism:** the lookup term *inside the goal* carries hidden `Lookup`-typeclass
instance implicits; a freshly-typed `m !! k` elaborates its own instances and does
not match syntactically.

**Fix — capture the goal's exact scrutinee:**

```coq
lazymatch goal with
|- context[match ?x with Some _ => _ | None => _ end] => destruct x as [i|]
end.
```

## 2. `From stdpp Require Import gmap` breaks `lia`

**Symptom:** `lia` fails with "Cannot find witness" on a trivial linear `N` goal —
in a file that imports `gmap`.

**Mechanism:** the import activates a Zify rewrite that turns `bv.bin (bv.of_N x)`
into `x mod 2^word`; the huge modulus breaks lia's certificate search. (Bare
`bv.bin a` is fine — only the `bin ∘ of_N` composition triggers it.)

**Fix — make the atom opaque first:**

```coq
set (B := bv.bin (bv.of_N …)) in *; clearbody B. lia.
```
